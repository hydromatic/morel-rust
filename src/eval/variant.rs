// Licensed to Julian Hyde under one or more contributor license
// agreements.  See the NOTICE file distributed with this work
// for additional information regarding copyright ownership.
// Julian Hyde licenses this file to you under the Apache
// License, Version 2.0 (the "License"); you may not use this
// file except in compliance with the License.  You may obtain a
// copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing,
// software distributed under the License is distributed on an
// "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND,
// either express or implied.  See the License for the specific
// language governing permissions and limitations under the
// License.

//! Support for the `variant` built-in datatype and the `Variant`
//! structure.

use crate::compile::types::{Label, PrimitiveType, Type, TypeVariable};
use crate::eval::char::Char;
use crate::eval::int::Int;
use crate::eval::real::Real;
use crate::eval::val::Val;
use crate::syntax::parser::string_to_string_append;
use std::collections::BTreeMap;

/// Wraps a value with its inner type into a `Val::Variant`.
pub(crate) fn variant_of(inner_type: Type, value: Val) -> Val {
    Val::Variant(Box::new((inner_type, value)))
}

/// `Variant.UNIT`.
pub(crate) fn unit() -> Val {
    variant_of(Type::Primitive(PrimitiveType::Unit), Val::Unit)
}

/// Returns a fresh polymorphic type variable, used as the inner type
/// of `VARIANT_NONE` (which has type `'a option variant`).
fn fresh_var() -> Type {
    Type::Variable(TypeVariable::new(0))
}

/// `Variant.VARIANT_NONE`: returns a variant whose inner type is
/// `variant option` and whose value is `Val::Unit` (the runtime form
/// of `NONE`). The inner element type is `variant` rather than a fresh
/// `'a` to mirror morel-java.
pub(crate) fn none() -> Val {
    variant_of(
        Type::Data(
            "option".to_string(),
            vec![Type::Data("variant".to_string(), vec![])],
        ),
        Val::Unit,
    )
}

/// `Variant.VARIANT_SOME v`: wraps an existing variant `v` into a
/// variant whose inner type is `<v inner type> option` and whose value is
/// `SOME v.value`.
pub(crate) fn some(arg: Val) -> Val {
    let (inner_type, inner_val) = match arg {
        Val::Variant(boxed) => *boxed,
        _ => panic!("Expected variant, got {:?}", arg),
    };
    variant_of(
        Type::Data("option".to_string(), vec![inner_type]),
        Val::Some(Box::new(inner_val)),
    )
}

/// `Variant.LIST xs`: wraps a list of variants into a variant of type
/// `T list` where `T` is the common inner type if all elements share one,
/// otherwise `variant`. The unwrapped element values become the contents.
pub(crate) fn list(arg: Val) -> Val {
    collection(arg, |t| Type::List(Box::new(t)))
}

/// `Variant.BAG xs`: like [`list`] but produces a bag.
pub(crate) fn bag(arg: Val) -> Val {
    collection(arg, |t| Type::Bag(Box::new(t)))
}

/// `Variant.VECTOR xs`: like [`list`] but produces a vector. (Vectors
/// share the runtime list representation.)
pub(crate) fn vector(arg: Val) -> Val {
    // Vectors use Type::Data("vector", [elem]) since there is no
    // dedicated Type::Vector variant.
    collection(arg, |t| Type::Data("vector".to_string(), vec![t]))
}

fn collection(arg: Val, wrap_type: impl FnOnce(Type) -> Type) -> Val {
    let items: Vec<Val> = match arg {
        Val::List(items) => items,
        _ => panic!("Expected list of variants, got {:?}", arg),
    };
    let element_type = common_element_type(&items);
    // When the element type is a real type (not the fallback `variant`),
    // unwrap each element. When the elements are heterogeneous and we
    // fell back to `variant`, keep them wrapped — the displayer needs
    // the inner-type tag on each element.
    let is_fallback = matches!(
        &element_type,
        Type::Data(name, _) if name == "variant"
    );
    let elements: Vec<Val> = if is_fallback {
        items
    } else {
        items
            .into_iter()
            .map(|v| match v {
                Val::Variant(boxed) => boxed.1,
                _ => panic!("Expected variant element, got {:?}", v),
            })
            .collect()
    };
    variant_of(wrap_type(element_type), Val::List(elements))
}

/// Returns the common inner type of a list of variants. Folds the
/// element types through [`unify_types`]; if unification fails at any
/// point the result is `variant`. An empty list also yields `variant`,
/// matching morel-java.
fn common_element_type(items: &[Val]) -> Type {
    let mut iter = items.iter().filter_map(|v| match v {
        Val::Variant(boxed) => Some(&boxed.0),
        _ => None,
    });
    let Some(first) = iter.next() else {
        return Type::Data("variant".to_string(), vec![]);
    };
    let mut current = first.clone();
    for next in iter {
        match unify_types(&current, next) {
            Some(t) => current = t,
            None => return Type::Data("variant".to_string(), vec![]),
        }
    }
    current
}

/// Returns the most specific type compatible with both `t1` and `t2`,
/// or `None` if they are incompatible. Used by [`common_element_type`]
/// so that, e.g., `string list` and `variant list` (the type of an
/// empty list element) reconcile to `string list`.
fn unify_types(t1: &Type, t2: &Type) -> Option<Type> {
    if t1 == t2 {
        return Some(t1.clone());
    }
    let is_variant = |t: &Type| matches!(t, Type::Data(n, _) if n == "variant");
    if is_variant(t1) {
        return Some(t2.clone());
    }
    if is_variant(t2) {
        return Some(t1.clone());
    }
    match (t1, t2) {
        (Type::List(a), Type::List(b)) => {
            unify_types(a, b).map(|t| Type::List(Box::new(t)))
        }
        (Type::Bag(a), Type::Bag(b)) => {
            unify_types(a, b).map(|t| Type::Bag(Box::new(t)))
        }
        (Type::Data(n1, a1), Type::Data(n2, a2))
            if n1 == n2 && a1.len() == a2.len() =>
        {
            let unified: Option<Vec<Type>> = a1
                .iter()
                .zip(a2.iter())
                .map(|(x, y)| unify_types(x, y))
                .collect();
            unified.map(|args| Type::Data(n1.clone(), args))
        }
        _ => None,
    }
}

/// `Variant.RECORD pairs`: takes a list of `(label, variant)` pairs and
/// returns a variant whose inner type is a record with each field typed
/// according to the variant's inner type, and whose value is a list of
/// the unwrapped field values (the runtime representation of records).
pub(crate) fn record(arg: Val) -> Val {
    let pairs: Vec<Val> = match arg {
        Val::List(items) => items,
        _ => panic!("Expected list of (label, variant) pairs, got {:?}", arg),
    };
    if pairs.is_empty() {
        // An empty record is `unit` — matching morel-java.
        return unit();
    }
    let mut fields: BTreeMap<Label, Type> = BTreeMap::new();
    let mut values: Vec<(Label, Val)> = Vec::with_capacity(pairs.len());
    for pair in pairs {
        let (label, variant_val) = match pair {
            Val::List(parts) if parts.len() == 2 => {
                let mut iter = parts.into_iter();
                (iter.next().unwrap(), iter.next().unwrap())
            }
            _ => panic!("Expected pair of (label, variant), got {:?}", pair),
        };
        let label_str = match label {
            Val::String(s) => s,
            _ => panic!("Expected string label, got {:?}", label),
        };
        let label = Label::from(label_str);
        let (inner_type, inner_val) = expect_variant(&variant_val);
        fields.insert(label.clone(), inner_type.clone());
        values.push((label, inner_val.clone()));
    }
    // Records are stored at runtime as a list of values in the order of
    // sorted labels (matching how the BTreeMap iterates).
    let mut sorted: Vec<(Label, Val)> = values;
    sorted.sort_by(|a, b| a.0.cmp(&b.0));
    let value_list = Val::List(sorted.into_iter().map(|(_, v)| v).collect());
    variant_of(Type::Record(false, fields), value_list)
}

/// `Variant.CONSTANT name`: a constructor representing a nullary
/// constructor of a built-in datatype, identified by name. Supports
/// `NONE` (option), `LESS`/`EQUAL`/`GREATER` (order). Unknown names
/// fall back to a placeholder `Type::Named` representation that
/// pretty-prints crudely; full support for arbitrary user-defined
/// datatypes would require a runtime constructor table.
pub(crate) fn constant(arg: Val) -> Val {
    use std::cmp::Ordering;

    use crate::eval::order::Order;

    let name = match arg {
        Val::String(s) => s,
        _ => panic!("Expected string, got {:?}", arg),
    };
    match name.as_str() {
        "NONE" => none(),
        "LESS" => variant_of(
            Type::Data("order".to_string(), vec![]),
            Val::Order(Order(Ordering::Less)),
        ),
        "EQUAL" => variant_of(
            Type::Data("order".to_string(), vec![]),
            Val::Order(Order(Ordering::Equal)),
        ),
        "GREATER" => variant_of(
            Type::Data("order".to_string(), vec![]),
            Val::Order(Order(Ordering::Greater)),
        ),
        // `NIL` is the empty list — same as `LIST []`. Use `variant`
        // as the element type (matching `LIST []`) so a round-trip via
        // `Variant.print`/`parse` compares equal.
        "NIL" => variant_of(
            Type::List(Box::new(Type::Data("variant".to_string(), vec![]))),
            Val::List(vec![]),
        ),
        // Unknown constructor: store the name in `Type::Named` and use
        // `Val::Unit` as the value. Pretty-printing of `Type::Named`
        // emits the name. Full support requires a runtime constructor
        // table linking names to their parent datatypes.
        _ => variant_of(Type::Named(vec![], name.clone()), Val::Unit),
    }
}

/// `Variant.CONSTRUCT (name, payload)`: a constructor representing a
/// unary constructor of a built-in datatype, identified by name and
/// payload variant. Supports `SOME` (option), `INL`/`INR` (either),
/// and `DESC` (descending). Unknown names fall back to a placeholder
/// representation that pretty-prints the constructor name and the
/// payload variant as `NAME payload`.
pub(crate) fn construct(arg: Val) -> Val {
    use crate::eval::val::DESC_ORDINAL;

    let parts = match arg {
        Val::List(items) if items.len() == 2 => items,
        _ => panic!("Expected (name, variant) pair, got {:?}", arg),
    };
    let mut iter = parts.into_iter();
    let name = match iter.next().unwrap() {
        Val::String(s) => s,
        other => panic!("Expected string name, got {:?}", other),
    };
    let payload = iter.next().unwrap();
    match name.as_str() {
        "SOME" | "INL" | "INR" | "DESC" => {
            let (inner_type, inner_val) = match payload {
                Val::Variant(boxed) => *boxed,
                other => panic!("Expected variant payload, got {:?}", other),
            };
            match name.as_str() {
                "SOME" => variant_of(
                    Type::Data("option".to_string(), vec![inner_type]),
                    Val::Some(Box::new(inner_val)),
                ),
                "INL" => variant_of(
                    Type::Data(
                        "either".to_string(),
                        vec![inner_type, fresh_var()],
                    ),
                    Val::Inl(Box::new(inner_val)),
                ),
                "INR" => variant_of(
                    Type::Data(
                        "either".to_string(),
                        vec![fresh_var(), inner_type],
                    ),
                    Val::Inr(Box::new(inner_val)),
                ),
                "DESC" => variant_of(
                    Type::Data("descending".to_string(), vec![inner_type]),
                    Val::Constructor(DESC_ORDINAL, Box::new(inner_val)),
                ),
                _ => unreachable!(),
            }
        }
        // `CONS` builds a real list variant — `CONS (head, tail)` is
        // the same value as `LIST (head :: tail)`. Existing list
        // patterns then deconstruct it.
        "CONS" => cons(payload),
        // Unknown constructor: keep the payload wrapped as a variant so
        // its inner type/value print recursively in the fallback display.
        _ => variant_of(Type::Named(vec![], name.clone()), payload),
    }
}

/// `CONSTRUCT ("CONS", (head, tail))`: prepend `head` onto the list
/// inside `tail`, producing a real list variant. The payload is a
/// 2-element record/tuple variant whose second field is itself a list
/// variant.
fn cons(payload: Val) -> Val {
    let (payload_type, payload_val) = match payload {
        Val::Variant(boxed) => *boxed,
        other => panic!("CONS payload must be variant, got {:?}", other),
    };
    let parts = match payload_val {
        Val::List(parts) if parts.len() == 2 => parts,
        other => panic!("CONS payload must be a 2-tuple, got {:?}", other),
    };
    let mut iter = parts.into_iter();
    let head = iter.next().unwrap();
    let tail = iter.next().unwrap();
    let head_type = match &payload_type {
        Type::Tuple(ts) if ts.len() == 2 => ts[0].clone(),
        Type::Record(_, fields) if fields.len() == 2 => {
            fields.values().next().unwrap().clone()
        }
        _ => panic!(
            "CONS payload must be a 2-tuple or 2-field record, got {:?}",
            payload_type
        ),
    };
    let tail_items = match tail {
        Val::List(items) => items,
        other => panic!("CONS tail must be a list, got {:?}", other),
    };
    let mut new_items = Vec::with_capacity(tail_items.len() + 1);
    new_items.push(head);
    new_items.extend(tail_items);
    variant_of(Type::List(Box::new(head_type)), Val::List(new_items))
}

fn expect_variant(v: &Val) -> (&Type, &Val) {
    match v {
        Val::Variant(boxed) => (&boxed.0, &boxed.1),
        _ => panic!("Expected variant, got {:?}", v),
    }
}

/// `Variant.print v`: serializes a variant to a string of the form
/// `INT 42` / `LIST [STRING "a"]` / etc., such that
/// `Variant.parse (Variant.print v) = v`.
pub(crate) fn print(arg: Val) -> Val {
    let (inner_type, inner_val) = match arg {
        Val::Variant(boxed) => *boxed,
        _ => panic!("Expected variant, got {:?}", arg),
    };
    let mut buf = String::new();
    append(&mut buf, &inner_type, &inner_val);
    Val::String(buf)
}

/// Recursive helper for [`print()`]. Appends the variant representation
/// of a value of `inner_type` to `buf`.
fn append(buf: &mut String, inner_type: &Type, inner_val: &Val) {
    match inner_type {
        Type::Primitive(p) => append_primitive(buf, p, inner_val),
        Type::List(elem) => append_collection(buf, "LIST", elem, inner_val),
        Type::Bag(elem) => append_collection(buf, "BAG", elem, inner_val),
        Type::Data(name, args) if name == "vector" => {
            let elem =
                args.first().expect("vector type must have element type");
            append_collection(buf, "VECTOR", elem, inner_val);
        }
        Type::Data(name, args) if name == "option" => {
            let elem =
                args.first().expect("option type must have element type");
            match inner_val {
                Val::Unit => buf.push_str("VARIANT_NONE"),
                Val::Some(v) => {
                    buf.push_str("VARIANT_SOME ");
                    append(buf, elem, v);
                }
                _ => panic!("Expected option value, got {:?}", inner_val),
            }
        }
        Type::Data(name, _) if name == "order" => {
            use std::cmp::Ordering;

            use crate::eval::order::Order;
            let con_name = match inner_val {
                Val::Order(Order(o)) => match o {
                    Ordering::Less => "LESS",
                    Ordering::Equal => "EQUAL",
                    Ordering::Greater => "GREATER",
                },
                _ => panic!("Expected order value, got {:?}", inner_val),
            };
            buf.push_str("CONSTANT \"");
            buf.push_str(con_name);
            buf.push('"');
        }
        Type::Data(name, args) if name == "either" => match inner_val {
            Val::Inl(v) => {
                let elem = args.first().expect("either has 2 args");
                buf.push_str("CONSTRUCT (\"INL\", ");
                append(buf, elem, v);
                buf.push(')');
            }
            Val::Inr(v) => {
                let elem = args.get(1).expect("either has 2 args");
                buf.push_str("CONSTRUCT (\"INR\", ");
                append(buf, elem, v);
                buf.push(')');
            }
            _ => panic!("Expected either value, got {:?}", inner_val),
        },
        Type::Data(name, args) if name == "descending" => {
            let elem = args.first().expect("descending has 1 arg");
            let v = match inner_val {
                Val::Constructor(_, inner) => inner.as_ref(),
                _ => panic!("Expected descending value, got {:?}", inner_val),
            };
            buf.push_str("CONSTRUCT (\"DESC\", ");
            append(buf, elem, v);
            buf.push(')');
        }
        Type::Record(_, fields) => {
            let values = match inner_val {
                Val::List(vs) => vs,
                _ => panic!("Expected record value, got {:?}", inner_val),
            };
            buf.push_str("RECORD [");
            for (i, ((label, field_type), val)) in
                fields.iter().zip(values.iter()).enumerate()
            {
                if i > 0 {
                    buf.push_str(", ");
                }
                buf.push_str("(\"");
                string_to_string_append(&label.to_string(), buf);
                buf.push_str("\", ");
                append(buf, field_type, val);
                buf.push(')');
            }
            buf.push(']');
        }
        Type::Tuple(types) => {
            // Tuples are printed as records with numeric labels.
            let values = match inner_val {
                Val::List(vs) => vs,
                _ => panic!("Expected tuple value, got {:?}", inner_val),
            };
            buf.push_str("RECORD [");
            for (i, (field_type, val)) in
                types.iter().zip(values.iter()).enumerate()
            {
                if i > 0 {
                    buf.push_str(", ");
                }
                buf.push_str("(\"");
                buf.push_str(&(i + 1).to_string());
                buf.push_str("\", ");
                append(buf, field_type, val);
                buf.push(')');
            }
            buf.push(']');
        }
        // Unknown named types: CONSTANT (Val::Unit) or CONSTRUCT
        // (Val::Variant payload). We don't have full datatype lookup,
        // so emit `CONSTANT "name"` / `CONSTRUCT ("name", payload)`.
        Type::Named(_, name) => match inner_val {
            Val::Unit => {
                buf.push_str("CONSTANT \"");
                buf.push_str(name);
                buf.push('"');
            }
            Val::Variant(boxed) => {
                let (payload_type, payload_val) = boxed.as_ref();
                buf.push_str("CONSTRUCT (\"");
                buf.push_str(name);
                buf.push_str("\", ");
                append(buf, payload_type, payload_val);
                buf.push(')');
            }
            _ => panic!(
                "Variant.print: unexpected value {:?} for named type {:?}",
                inner_val, name
            ),
        },
        _ => panic!(
            "Variant.print: unsupported inner type {:?} for value {:?}",
            inner_type, inner_val
        ),
    }
}

fn append_primitive(buf: &mut String, p: &PrimitiveType, value: &Val) {
    match (p, value) {
        (PrimitiveType::Unit, Val::Unit) => buf.push_str("UNIT"),
        (PrimitiveType::Bool, Val::Bool(b)) => {
            buf.push_str("BOOL ");
            buf.push_str(if *b { "true" } else { "false" });
        }
        (PrimitiveType::Int, Val::Int(i)) => {
            buf.push_str("INT ");
            buf.push_str(&Int::_to_string(*i));
        }
        (PrimitiveType::Real, Val::Real(r)) => {
            buf.push_str("REAL ");
            buf.push_str(&Real::to_string(*r));
        }
        (PrimitiveType::Char, Val::Char(c)) => {
            buf.push_str("CHAR #\"");
            buf.push_str(&Char::to_c_string(*c));
            buf.push('"');
        }
        (PrimitiveType::String, Val::String(s)) => {
            buf.push_str("STRING \"");
            string_to_string_append(s, buf);
            buf.push('"');
        }
        _ => panic!("Variant.print: type/value mismatch {:?} / {:?}", p, value),
    }
}

fn append_collection(
    buf: &mut String,
    keyword: &str,
    elem_type: &Type,
    value: &Val,
) {
    let items = match value {
        Val::List(items) => items,
        _ => panic!("Expected list value, got {:?}", value),
    };
    buf.push_str(keyword);
    buf.push_str(" [");
    for (i, item) in items.iter().enumerate() {
        if i > 0 {
            buf.push_str(", ");
        }
        // The list elements are stored unwrapped; recurse with the
        // element type to produce the variant form.
        append(buf, elem_type, item);
    }
    buf.push(']');
}

/// `Variant.parse s`: the inverse of [`print()`]. Parses a string of
/// the construction-expression format (e.g. `"LIST [INT 1, INT 2]"`)
/// and returns the corresponding variant value.
pub(crate) fn parse(arg: Val) -> Val {
    let s = match arg {
        Val::String(s) => s,
        _ => panic!("Expected string, got {:?}", arg),
    };
    let mut p = Parser::new(&s);
    p.skip_ws();
    let v = p.parse_variant();
    p.skip_ws();
    if !p.at_end() {
        panic!("Trailing input at position {} of {:?}", p.pos, p.input);
    }
    v
}

/// Recursive-descent parser for the variant construction-expression
/// format produced by [`print()`].
struct Parser<'a> {
    input: &'a str,
    bytes: &'a [u8],
    pos: usize,
}

impl<'a> Parser<'a> {
    fn new(input: &'a str) -> Self {
        Self {
            input,
            bytes: input.as_bytes(),
            pos: 0,
        }
    }

    fn at_end(&self) -> bool {
        self.pos >= self.bytes.len()
    }

    fn peek(&self) -> Option<u8> {
        self.bytes.get(self.pos).copied()
    }

    fn skip_ws(&mut self) {
        while let Some(b) = self.peek() {
            if b.is_ascii_whitespace() {
                self.pos += 1;
            } else {
                break;
            }
        }
    }

    fn try_consume(&mut self, lit: &str) -> bool {
        let bytes = lit.as_bytes();
        if self.bytes[self.pos..].starts_with(bytes) {
            self.pos += bytes.len();
            true
        } else {
            false
        }
    }

    fn expect(&mut self, lit: &str) {
        if !self.try_consume(lit) {
            panic!(
                "Expected {:?} at position {} of {:?}",
                lit, self.pos, self.input
            );
        }
    }

    /// Parses an identifier (a sequence of `_`, letters, or digits) and
    /// advances past it. Used to read constructor names and field names.
    fn parse_ident(&mut self) -> &'a str {
        let start = self.pos;
        while let Some(b) = self.peek() {
            if b == b'_' || b.is_ascii_alphanumeric() {
                self.pos += 1;
            } else {
                break;
            }
        }
        &self.input[start..self.pos]
    }

    /// Parses a `"..."` string literal, returning the unescaped contents.
    fn parse_string_literal(&mut self) -> String {
        self.expect("\"");
        let mut out = String::new();
        while let Some(b) = self.peek() {
            match b {
                b'"' => {
                    self.pos += 1;
                    return out;
                }
                b'\\' => {
                    self.pos += 1;
                    let c = self.peek().unwrap_or_else(|| {
                        panic!(
                            "Incomplete escape at position {} of {:?}",
                            self.pos, self.input
                        )
                    });
                    self.pos += 1;
                    out.push(match c {
                        b'n' => '\n',
                        b't' => '\t',
                        b'r' => '\r',
                        b'\\' => '\\',
                        b'"' => '"',
                        other => other as char,
                    });
                }
                _ => {
                    out.push(b as char);
                    self.pos += 1;
                }
            }
        }
        panic!(
            "Unterminated string literal at position {} of {:?}",
            self.pos, self.input
        );
    }

    /// Parses a `#"..."` char literal.
    fn parse_char_literal(&mut self) -> char {
        self.expect("#\"");
        let c = match self.peek() {
            Some(b'\\') => {
                self.pos += 1;
                let escape = self.peek().expect("incomplete escape");
                self.pos += 1;
                match escape {
                    b'n' => '\n',
                    b't' => '\t',
                    b'r' => '\r',
                    b'\\' => '\\',
                    b'"' => '"',
                    other => other as char,
                }
            }
            Some(b) => {
                self.pos += 1;
                b as char
            }
            None => panic!("Incomplete char literal"),
        };
        self.expect("\"");
        c
    }

    /// Parses an integer or real literal. Recognizes the leading `~`
    /// for negation and a single `.` for reals.
    fn parse_number(&mut self) -> Val {
        let start = self.pos;
        if self.peek() == Some(b'~') {
            self.pos += 1;
        }
        while let Some(b) = self.peek() {
            if b.is_ascii_digit() {
                self.pos += 1;
            } else {
                break;
            }
        }
        let mut is_real = false;
        if self.peek() == Some(b'.') {
            is_real = true;
            self.pos += 1;
            while let Some(b) = self.peek() {
                if b.is_ascii_digit() {
                    self.pos += 1;
                } else {
                    break;
                }
            }
        }
        // Optional 'e' exponent.
        if matches!(self.peek(), Some(b'e' | b'E')) {
            is_real = true;
            self.pos += 1;
            if self.peek() == Some(b'~') {
                self.pos += 1;
            }
            while let Some(b) = self.peek() {
                if b.is_ascii_digit() {
                    self.pos += 1;
                } else {
                    break;
                }
            }
        }
        let lit = &self.input[start..self.pos];
        if is_real {
            let cleaned = lit.replace('~', "-");
            Val::Real(
                cleaned.parse::<f32>().unwrap_or_else(|_| {
                    panic!("Invalid real literal {:?}", lit)
                }),
            )
        } else {
            let cleaned = lit.replace('~', "-");
            Val::Int(
                cleaned.parse::<i32>().unwrap_or_else(|_| {
                    panic!("Invalid int literal {:?}", lit)
                }),
            )
        }
    }

    /// Parses one variant value.
    fn parse_variant(&mut self) -> Val {
        self.skip_ws();
        // Bare literals — Variant.parse "~5" and friends are valid input.
        match self.peek() {
            Some(b'~') | Some(b'0'..=b'9') => {
                let n = self.parse_number();
                return match n {
                    Val::Int(_) => {
                        variant_of(Type::Primitive(PrimitiveType::Int), n)
                    }
                    Val::Real(_) => {
                        variant_of(Type::Primitive(PrimitiveType::Real), n)
                    }
                    _ => unreachable!(),
                };
            }
            Some(b'"') => {
                let s = self.parse_string_literal();
                return variant_of(
                    Type::Primitive(PrimitiveType::String),
                    Val::String(s),
                );
            }
            Some(b'#') => {
                // CHAR literal #"c"
                let c = self.parse_char_literal();
                return variant_of(
                    Type::Primitive(PrimitiveType::Char),
                    Val::Char(c),
                );
            }
            _ => {}
        }
        let ident = self.parse_ident();
        match ident {
            "UNIT" => unit(),
            "BOOL" => {
                self.skip_ws();
                let val = if self.try_consume("true") {
                    Val::Bool(true)
                } else if self.try_consume("false") {
                    Val::Bool(false)
                } else {
                    panic!(
                        "Expected 'true' or 'false' at position {}",
                        self.pos
                    );
                };
                variant_of(Type::Primitive(PrimitiveType::Bool), val)
            }
            "INT" => {
                self.skip_ws();
                let n = match self.parse_number() {
                    Val::Int(n) => n,
                    other => panic!("Expected int, got {:?}", other),
                };
                variant_of(Type::Primitive(PrimitiveType::Int), Val::Int(n))
            }
            "REAL" => {
                self.skip_ws();
                let r = match self.parse_number() {
                    Val::Real(r) => r,
                    Val::Int(n) => n as f32,
                    other => panic!("Expected real, got {:?}", other),
                };
                variant_of(Type::Primitive(PrimitiveType::Real), Val::Real(r))
            }
            "CHAR" => {
                self.skip_ws();
                let c = self.parse_char_literal();
                variant_of(Type::Primitive(PrimitiveType::Char), Val::Char(c))
            }
            "STRING" => {
                self.skip_ws();
                let s = self.parse_string_literal();
                variant_of(
                    Type::Primitive(PrimitiveType::String),
                    Val::String(s),
                )
            }
            "LIST" => self.parse_collection(list),
            "BAG" => self.parse_collection(bag),
            "VECTOR" => self.parse_collection(vector),
            "VARIANT_NONE" => none(),
            "VARIANT_SOME" => {
                self.skip_ws();
                let inner = self.parse_variant();
                some(inner)
            }
            "RECORD" => self.parse_record_body(),
            "CONSTANT" => {
                self.skip_ws();
                let name = self.parse_string_literal();
                constant(Val::String(name))
            }
            "CONSTRUCT" => {
                self.skip_ws();
                self.expect("(");
                self.skip_ws();
                let name = self.parse_string_literal();
                self.skip_ws();
                self.expect(",");
                self.skip_ws();
                let payload = self.parse_variant();
                self.skip_ws();
                self.expect(")");
                construct(Val::List(vec![Val::String(name), payload]))
            }
            other => panic!(
                "Unknown variant constructor {:?} at position {}",
                other, self.pos
            ),
        }
    }

    fn parse_collection(&mut self, ctor: fn(Val) -> Val) -> Val {
        self.skip_ws();
        self.expect("[");
        self.skip_ws();
        let mut elements = Vec::new();
        if !self.try_consume("]") {
            loop {
                elements.push(self.parse_variant());
                self.skip_ws();
                if self.try_consume(",") {
                    self.skip_ws();
                    continue;
                }
                self.expect("]");
                break;
            }
        }
        ctor(Val::List(elements))
    }

    /// Parses the body of `RECORD [(label, variant), ...]` after the
    /// `RECORD` keyword has been consumed.
    fn parse_record_body(&mut self) -> Val {
        self.skip_ws();
        self.expect("[");
        self.skip_ws();
        let mut pairs = Vec::new();
        if !self.try_consume("]") {
            loop {
                self.skip_ws();
                self.expect("(");
                self.skip_ws();
                let label = self.parse_string_literal();
                self.skip_ws();
                self.expect(",");
                self.skip_ws();
                let variant = self.parse_variant();
                self.skip_ws();
                self.expect(")");
                self.skip_ws();
                pairs.push(Val::List(vec![Val::String(label), variant]));
                if self.try_consume(",") {
                    continue;
                }
                self.expect("]");
                break;
            }
        }
        record(Val::List(pairs))
    }
}
