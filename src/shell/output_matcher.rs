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

//! Compares two output strings for semantic equivalence, treating
//! bag values as unordered (multisets) and ignoring insignificant
//! whitespace differences.
//!
//! Ported from morel-java's `OutputMatcher`
//! (hydromatic/morel#334, commit 9430af3f).
//!
//! Output strings have the form `val name = value : type` or
//! `value : type`. The type suffix tells us which brackets
//! represent bags (unordered) vs lists (ordered).
//!
//! False negatives (where the values are equivalent but we can't
//! deduce it) are fine; false positives are not.

use crate::compile::type_parser;
use crate::compile::types::{Label, Type};
use std::collections::{BTreeMap, HashMap};
use std::panic::catch_unwind;
use std::str::from_utf8;

/// Compares two output strings modulo whitespace and bag reordering.
///
/// Parses the type annotation from the expected output (the text
/// after the top-level ` : `) and uses it to guide comparison.
/// Returns `false` if either string doesn't have the expected
/// `VALUE : TYPE` shape.
pub fn equivalent(actual: &str, expected: &str) -> bool {
    let t = match extract_type(expected) {
        Some(s) => s,
        None => return false,
    };
    let parsed_type = match catch_unwind(|| type_parser::string_to_type(&t)) {
        Ok(t) => *t,
        Err(_) => return false,
    };
    equivalent_with_type(&parsed_type, actual, expected)
}

/// Same as [`equivalent`] but with an explicit type (used by unit
/// tests where the type is known).
pub fn equivalent_with_type(
    type_: &Type,
    actual: &str,
    expected: &str,
) -> bool {
    let code0 = match extract_value(actual) {
        Some(s) => s,
        None => return false,
    };
    let code1 = match extract_value(expected) {
        Some(s) => s,
        None => return false,
    };
    code_equal(type_, &code0, &code1)
}

/// Extracts the type string from `VALUE : TYPE`: everything after
/// the last top-level ` : `. Returns `None` if missing.
fn extract_type(s: &str) -> Option<String> {
    let bytes = s.as_bytes();
    let n = bytes.len();
    let mut depth: i32 = 0;
    let mut in_string = false;
    let mut last_colon: Option<usize> = None;
    let mut i = 0;
    while i < n {
        let c = bytes[i] as char;
        if in_string {
            if c == '"' {
                in_string = false;
            } else if c == '\\' {
                i += 1;
            }
            i += 1;
            continue;
        }
        match c {
            '"' => in_string = true,
            '(' | '[' | '{' => depth += 1,
            ')' | ']' | '}' => depth -= 1,
            ':' if depth == 0
                && i > 0
                && bytes[i - 1] as char == ' '
                && i + 1 < n
                && bytes[i + 1] as char == ' ' =>
            {
                last_colon = Some(i);
            }
            _ => {}
        }
        i += 1;
    }
    let start = last_colon? + 2;
    if start > n {
        return None;
    }
    Some(s[start..].trim().to_string())
}

/// Compares two value strings (no `val x =` prefix, no `: type`
/// suffix) under the given type.
pub fn code_equal(type_: &Type, code0: &str, code1: &str) -> bool {
    let norm0 = normalize_whitespace(code0);
    let norm1 = normalize_whitespace(code1);
    let mut s0 = Scanner::new(&norm0);
    let mut s1 = Scanner::new(&norm1);
    let v0 = match parse_value(&mut s0, type_) {
        Some(v) => v,
        None => return false,
    };
    let v1 = match parse_value(&mut s1, type_) {
        Some(v) => v,
        None => return false,
    };
    values_equal(type_, &v0, &v1)
}

/// Parsed value tree: an atomic string, or a list of sub-values.
#[derive(Clone, Eq, PartialEq, Debug)]
enum Parsed {
    Atom(String),
    Seq(Vec<Parsed>),
}

/// Extracts the value portion from `val x = VALUE : TYPE` or
/// `VALUE : TYPE`. Returns the VALUE substring or `None` if it
/// can't find the top-level `: ` separator.
fn extract_value(s: &str) -> Option<String> {
    let bytes = s.as_bytes();
    let n = bytes.len();

    // Optional `val <name> = ` prefix — find the first `=`
    // followed by whitespace, and skip to after the whitespace.
    let mut value_start = 0usize;
    let eq_idx = index_of_eq_whitespace(s);
    if let Some(eq) = eq_idx
        && s[..eq].contains("val ")
    {
        let mut start = eq + 1;
        while start < n && is_whitespace_char(bytes[start] as char) {
            start += 1;
        }
        value_start = start;
    }

    // Find end of value: last top-level ` : `.
    let mut depth: i32 = 0;
    let mut in_string = false;
    let mut last_colon: Option<usize> = None;
    let mut i = 0;
    while i < n {
        let c = bytes[i] as char;
        if in_string {
            if c == '"' {
                in_string = false;
            } else if c == '\\' {
                i += 1;
            }
            i += 1;
            continue;
        }
        match c {
            '"' => in_string = true,
            '(' | '[' | '{' => depth += 1,
            ')' | ']' | '}' => depth -= 1,
            ':' if depth == 0
                && i > 0
                && bytes[i - 1] as char == ' '
                && i + 1 < n
                && bytes[i + 1] as char == ' ' =>
            {
                last_colon = Some(i);
            }
            _ => {}
        }
        i += 1;
    }
    let end = last_colon? - 1;
    if end < value_start {
        return None;
    }
    Some(s[value_start..end].to_string())
}

fn is_whitespace_char(c: char) -> bool {
    matches!(c, ' ' | '\n' | '\r' | '\t')
}

fn is_word_char(c: char) -> bool {
    c.is_alphanumeric() || c == '_' || c == '\'' || c == '~'
}

fn index_of_eq_whitespace(s: &str) -> Option<usize> {
    let bytes = s.as_bytes();
    (0..bytes.len().saturating_sub(1)).find(|&i| {
        bytes[i] as char == '=' && is_whitespace_char(bytes[i + 1] as char)
    })
}

/// Collapses any run of whitespace into a single space, keeping
/// spaces only where they separate word-like tokens or bracket a
/// record `{a=1}`-style `=`. String literals are preserved verbatim.
fn normalize_whitespace(s: &str) -> String {
    let mut buf = String::with_capacity(s.len());
    let bytes = s.as_bytes();
    let n = bytes.len();
    let mut in_string = false;
    let mut last_was_space = false;
    let mut i = 0;
    while i < n {
        let c = bytes[i] as char;
        if in_string {
            buf.push(c);
            if c == '"' {
                in_string = false;
            } else if c == '\\' && i + 1 < n {
                i += 1;
                buf.push(bytes[i] as char);
            }
            last_was_space = false;
            i += 1;
            continue;
        }
        match c {
            '"' => {
                if last_was_space && !buf.is_empty() {
                    buf.push(' ');
                }
                buf.push(c);
                in_string = true;
                last_was_space = false;
            }
            ' ' | '\n' | '\r' | '\t' => {
                last_was_space = true;
            }
            _ => {
                if last_was_space && !buf.is_empty() && needs_space(&buf, c) {
                    buf.push(' ');
                }
                buf.push(c);
                last_was_space = false;
            }
        }
        i += 1;
    }
    buf
}

/// Whether a space is needed between the last char in `buf` and the
/// next char `c` when collapsing whitespace.
fn needs_space(buf: &str, c: char) -> bool {
    let prev = match buf.chars().last() {
        Some(p) => p,
        None => return false,
    };
    if is_word_char(prev) && is_word_char(c) {
        return true;
    }
    if prev == '=' && !matches!(c, '{' | '[' | '(' | ')') {
        return true;
    }
    c == '=' && !matches!(prev, '>' | '<' | '!')
}

/// Parses a value of the given type from the scanner.
fn parse_value(sc: &mut Scanner, type_: &Type) -> Option<Parsed> {
    // Handle grouping parens around a non-tuple value:
    // e.g. `SOME ([1,2])` where the arg is a bag in parens.
    if sc.peek() == Some('(') && !matches!(type_, Type::Tuple(_)) {
        sc.consume_str("(")?;
        let v = parse_value(sc, type_)?;
        sc.consume_str(")")?;
        return Some(v);
    }

    let peeled = peel_alias(type_);
    match peeled {
        Type::List(elem) | Type::Bag(elem) => parse_list_elements(sc, elem),
        // `bag` parsed from a type string comes back as `Named(T,
        // "bag")`; treat it as a collection.
        Type::Named(args, name) if name == "bag" && args.len() == 1 => {
            parse_list_elements(sc, &args[0])
        }
        Type::Named(args, name) if name == "list" && args.len() == 1 => {
            parse_list_elements(sc, &args[0])
        }
        Type::Tuple(elem_types) => parse_tuple_elements(sc, elem_types),
        Type::Record(_, fields) => parse_record_to_tuple(sc, fields),
        Type::Data(name, args) => parse_datatype_value(sc, name, args),
        Type::Named(args, name)
            if name == "option" && args.len() == 1
                || name == "descending" && args.len() == 1 =>
        {
            parse_datatype_value(sc, name, args)
        }
        _ => parse_atom(sc).map(Parsed::Atom),
    }
}

/// Resolves through `Alias` wrappers to the underlying type.
fn peel_alias(t: &Type) -> &Type {
    match t {
        Type::Alias(_, inner, _) => peel_alias(inner),
        _ => t,
    }
}

fn parse_list_elements(sc: &mut Scanner, elem_type: &Type) -> Option<Parsed> {
    sc.consume_str("[")?;
    let mut elements = Vec::new();
    if sc.peek() != Some(']') {
        loop {
            elements.push(parse_value(sc, elem_type)?);
            if sc.peek() != Some(',') {
                break;
            }
            sc.consume_str(",")?;
        }
    }
    sc.consume_str("]")?;
    Some(Parsed::Seq(elements))
}

fn parse_tuple_elements(
    sc: &mut Scanner,
    elem_types: &[Type],
) -> Option<Parsed> {
    sc.consume_str("(")?;
    if sc.peek() == Some(')') {
        sc.consume_str(")")?;
        return Some(Parsed::Seq(Vec::new()));
    }
    let mut fields = Vec::with_capacity(elem_types.len());
    for (i, t) in elem_types.iter().enumerate() {
        if i > 0 {
            sc.consume_str(",")?;
        }
        fields.push(parse_value(sc, t)?);
    }
    sc.consume_str(")")?;
    Some(Parsed::Seq(fields))
}

/// Parses `{f1=v1, f2=v2, ...}` and returns the values reordered
/// into the field-name order of the given type.
fn parse_record_to_tuple(
    sc: &mut Scanner,
    fields: &BTreeMap<Label, Type>,
) -> Option<Parsed> {
    sc.consume_str("{")?;
    let mut field_map: HashMap<String, Parsed> = HashMap::new();
    if sc.peek() != Some('}') {
        loop {
            let name = sc.consume_word()?;
            sc.consume_str("=")?;
            // Find the field type in the BTreeMap by matching the
            // label's string form.
            let field_type = fields.iter().find_map(|(label, t)| {
                if label.to_string() == name {
                    Some(t)
                } else {
                    None
                }
            });
            let v = match field_type {
                Some(t) => parse_value(sc, t)?,
                None => Parsed::Atom(parse_atom(sc)?),
            };
            field_map.insert(name, v);
            if sc.peek() != Some(',') {
                break;
            }
            sc.consume_str(",")?;
        }
    }
    sc.consume_str("}")?;
    // Reorder in type's field order.
    let mut values = Vec::with_capacity(fields.len());
    for label in fields.keys() {
        let v = field_map.remove(&label.to_string())?;
        values.push(v);
    }
    Some(Parsed::Seq(values))
}

/// Parses a datatype value: `Constructor` or `Constructor arg`.
/// Returns a sequence of length 1 (nullary) or 2 (with arg).
fn parse_datatype_value(
    sc: &mut Scanner,
    name: &str,
    args: &[Type],
) -> Option<Parsed> {
    let constructor = sc.consume_word()?;
    let at_end = match sc.peek() {
        None => true,
        Some(c) => matches!(c, ',' | ')' | ']' | '}'),
    };
    if at_end {
        return Some(Parsed::Seq(vec![Parsed::Atom(constructor)]));
    }
    // Has an argument. Determine its type from the constructor.
    let arg_type = constructor_arg_type(name, args, &constructor);
    let arg_value = match arg_type {
        Some(t) => parse_value(sc, &t)?,
        None => Parsed::Atom(parse_atom(sc)?),
    };
    Some(Parsed::Seq(vec![Parsed::Atom(constructor), arg_value]))
}

/// Returns the argument type for a datatype's constructor, if known.
fn constructor_arg_type(
    name: &str,
    args: &[Type],
    constructor: &str,
) -> Option<Type> {
    match (name, constructor, args) {
        ("option", "SOME", [t]) => Some(t.clone()),
        ("option", "NONE", _) => None,
        ("descending", "DESC", [t]) => Some(t.clone()),
        // User-defined datatypes are not handled yet; fall through
        // to atom parsing.
        _ => None,
    }
}

/// Parses a single atom token: string, char, number, unit, or word.
fn parse_atom(sc: &mut Scanner) -> Option<String> {
    let c = sc.peek()?;
    if c == '#' {
        sc.consume_str("#")?;
        let s = sc.consume_string()?;
        Some(format!("#{}", s))
    } else if c == '"' {
        sc.consume_string()
    } else if c == '~' || c.is_ascii_digit() {
        sc.consume_number()
    } else if c == '(' && sc.peek_at(1) == Some(')') {
        sc.consume_str("(")?;
        sc.consume_str(")")?;
        Some("()".to_string())
    } else {
        sc.consume_word()
    }
}

/// Compares two parsed values under the given type.
fn values_equal(type_: &Type, a: &Parsed, b: &Parsed) -> bool {
    match peel_alias(type_) {
        Type::Bag(elem) => bag_equal(elem, a, b),
        Type::List(elem) => list_equal(elem, a, b),
        Type::Named(args, name) if name == "bag" && args.len() == 1 => {
            bag_equal(&args[0], a, b)
        }
        Type::Named(args, name) if name == "list" && args.len() == 1 => {
            list_equal(&args[0], a, b)
        }
        Type::Tuple(elem_types) => tuple_equal(elem_types, a, b),
        Type::Record(_, fields) => {
            let types: Vec<Type> = fields.values().cloned().collect();
            tuple_equal(&types, a, b)
        }
        Type::Data(name, args) => datatype_equal(name, args, a, b),
        Type::Named(args, name)
            if name == "option" && args.len() == 1
                || name == "descending" && args.len() == 1 =>
        {
            datatype_equal(name, args, a, b)
        }
        _ => a == b,
    }
}

fn list_equal(elem_type: &Type, a: &Parsed, b: &Parsed) -> bool {
    let (ea, eb) = match (a, b) {
        (Parsed::Seq(ea), Parsed::Seq(eb)) => (ea, eb),
        _ => return a == b,
    };
    if ea.len() != eb.len() {
        return false;
    }
    ea.iter()
        .zip(eb.iter())
        .all(|(x, y)| values_equal(elem_type, x, y))
}

fn tuple_equal(field_types: &[Type], a: &Parsed, b: &Parsed) -> bool {
    let (ea, eb) = match (a, b) {
        (Parsed::Seq(ea), Parsed::Seq(eb)) => (ea, eb),
        _ => return a == b,
    };
    if ea.len() != eb.len() || ea.len() != field_types.len() {
        return false;
    }
    ea.iter()
        .zip(eb.iter())
        .zip(field_types.iter())
        .all(|((x, y), t)| values_equal(t, x, y))
}

fn datatype_equal(name: &str, args: &[Type], a: &Parsed, b: &Parsed) -> bool {
    let (ea, eb) = match (a, b) {
        (Parsed::Seq(ea), Parsed::Seq(eb)) => (ea, eb),
        _ => return a == b,
    };
    if ea.len() != eb.len() || ea.is_empty() {
        return false;
    }
    if ea[0] != eb[0] {
        return false;
    }
    if ea.len() == 1 {
        return true;
    }
    let constructor = match &ea[0] {
        Parsed::Atom(c) => c.clone(),
        _ => return false,
    };
    let arg_type = match constructor_arg_type(name, args, &constructor) {
        Some(t) => t,
        None => return false,
    };
    values_equal(&arg_type, &ea[1], &eb[1])
}

/// Compares two sequences as multisets under `elem_type`.
fn bag_equal(elem_type: &Type, a: &Parsed, b: &Parsed) -> bool {
    let (ea, eb) = match (a, b) {
        (Parsed::Seq(ea), Parsed::Seq(eb)) => (ea, eb),
        _ => return a == b,
    };
    if ea.len() != eb.len() {
        return false;
    }
    // Greedy: for each element in `ea` remove one matching element
    // from a copy of `eb`.
    let mut remaining: Vec<&Parsed> = eb.iter().collect();
    for x in ea {
        let mut matched: Option<usize> = None;
        for (j, y) in remaining.iter().enumerate() {
            if values_equal(elem_type, x, y) {
                matched = Some(j);
                break;
            }
        }
        match matched {
            Some(j) => {
                remaining.remove(j);
            }
            None => return false,
        }
    }
    true
}

// ---- Scanner ----

/// Simple scanner over whitespace-normalized text.
struct Scanner<'a> {
    s: &'a [u8],
    pos: usize,
}

impl<'a> Scanner<'a> {
    fn new(s: &'a str) -> Self {
        Scanner {
            s: s.as_bytes(),
            pos: 0,
        }
    }

    fn peek(&mut self) -> Option<char> {
        self.skip_spaces();
        self.s.get(self.pos).map(|b| *b as char)
    }

    fn peek_at(&mut self, offset: usize) -> Option<char> {
        self.skip_spaces();
        self.s.get(self.pos + offset).map(|b| *b as char)
    }

    fn consume_str(&mut self, expected: &str) -> Option<()> {
        self.skip_spaces();
        let e = expected.as_bytes();
        if self.s.len() < self.pos + e.len() {
            return None;
        }
        if &self.s[self.pos..self.pos + e.len()] != e {
            return None;
        }
        self.pos += e.len();
        Some(())
    }

    fn consume_word(&mut self) -> Option<String> {
        self.skip_spaces();
        let start = self.pos;
        while let Some(&b) = self.s.get(self.pos) {
            if is_word_char(b as char) {
                self.pos += 1;
            } else {
                break;
            }
        }
        if self.pos == start {
            return None;
        }
        from_utf8(&self.s[start..self.pos])
            .ok()
            .map(ToString::to_string)
    }

    fn consume_string(&mut self) -> Option<String> {
        self.skip_spaces();
        if self.s.get(self.pos) != Some(&b'"') {
            return None;
        }
        let start = self.pos;
        self.pos += 1;
        while let Some(&b) = self.s.get(self.pos) {
            if b == b'"' {
                self.pos += 1;
                return from_utf8(&self.s[start..self.pos])
                    .ok()
                    .map(ToString::to_string);
            }
            if b == b'\\' {
                self.pos += 1;
            }
            self.pos += 1;
        }
        None
    }

    fn consume_number(&mut self) -> Option<String> {
        self.skip_spaces();
        let start = self.pos;
        if self.s.get(self.pos) == Some(&b'~') {
            self.pos += 1;
        }
        while let Some(&b) = self.s.get(self.pos) {
            if (b as char).is_ascii_digit() || b == b'.' {
                self.pos += 1;
            } else {
                break;
            }
        }
        if self.s.get(self.pos) == Some(&b'E')
            || self.s.get(self.pos) == Some(&b'e')
        {
            self.pos += 1;
            if self.s.get(self.pos) == Some(&b'~') {
                self.pos += 1;
            }
            while let Some(&b) = self.s.get(self.pos) {
                if (b as char).is_ascii_digit() {
                    self.pos += 1;
                } else {
                    break;
                }
            }
        }
        if self.pos == start {
            return None;
        }
        from_utf8(&self.s[start..self.pos])
            .ok()
            .map(ToString::to_string)
    }

    fn skip_spaces(&mut self) {
        while self.s.get(self.pos) == Some(&b' ') {
            self.pos += 1;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::compile::types::PrimitiveType;

    fn int() -> Type {
        Type::Primitive(PrimitiveType::Int)
    }
    fn string() -> Type {
        Type::Primitive(PrimitiveType::String)
    }
    fn int_bag() -> Type {
        Type::Bag(Box::new(int()))
    }
    fn int_list() -> Type {
        Type::List(Box::new(int()))
    }

    #[test]
    fn normalize_collapses_whitespace() {
        // Collapses any run of whitespace around punctuation.
        assert_eq!(normalize_whitespace("[1,  2,\n 3]"), "[1,2,3]");
        // Preserves (collapsed) spaces where they separate word-like
        // tokens — morel output never uses them around '=', so equal
        // inputs produce equal outputs.
        assert_eq!(normalize_whitespace("val  it  = 3"), "val it = 3");
        // String literals are preserved verbatim (including inner
        // spaces).
        assert_eq!(normalize_whitespace("\"a  b\""), "\"a  b\"");
    }

    #[test]
    fn bag_reorder_equivalent() {
        // "val it = [3,1,~2] : int bag" vs "[~2,1,3] : int bag"
        let a = "val it = [3,1,~2] : int bag";
        let b = "val it = [~2,1,3] : int bag";
        assert!(equivalent_with_type(&int_bag(), a, b));
    }

    #[test]
    fn list_reorder_not_equivalent() {
        let a = "val it = [3,1,2] : int list";
        let b = "val it = [1,2,3] : int list";
        assert!(!equivalent_with_type(&int_list(), a, b));
    }

    #[test]
    fn bag_reorder_equivalent_no_type_arg() {
        let a = "val it = [3,1,~2] : int bag";
        let b = "val it = [~2,1,3] : int bag";
        assert!(equivalent(a, b));
    }

    #[test]
    fn list_reorder_not_equivalent_no_type_arg() {
        let a = "val it = [3,1,2] : int list";
        let b = "val it = [1,2,3] : int list";
        assert!(!equivalent(a, b));
    }

    #[test]
    fn whitespace_tolerant() {
        let a = "val it = [3,1,~2] : int bag";
        let b = "val it = [3,\n   1,  ~2] : int bag";
        assert!(equivalent_with_type(&int_bag(), a, b));
    }

    #[test]
    fn tuple_containing_bag() {
        let tuple_type = Type::Tuple(vec![int_bag(), string()]);
        let a = "val it = ([1,2],\"hello\") : int bag * string";
        let b = "val it = ([2,1],\"hello\") : int bag * string";
        assert!(equivalent_with_type(&tuple_type, a, b));
    }

    #[test]
    fn record_with_bag_field() {
        let mut fields = BTreeMap::new();
        fields.insert(Label::from("name"), string());
        fields.insert(Label::from("values"), int_bag());
        let rec = Type::Record(false, fields);
        let a = "val r = {name=\"test\",values=[30,10,20]} \
                 : {name:string, values:int bag}";
        let b = "val r = {name=\"test\",values=[10,20,30]} \
                 : {name:string, values:int bag}";
        assert!(equivalent_with_type(&rec, a, b));
    }

    #[test]
    fn option_of_bag() {
        let t = Type::Data("option".into(), vec![int_bag()]);
        let a = "val it = SOME [5,10] : int bag option";
        let b = "val it = SOME [10,5] : int bag option";
        assert!(equivalent_with_type(&t, a, b));
        // Group parens around the bag body also OK.
        let c = "val it = SOME ([10,5]) : int bag option";
        assert!(equivalent_with_type(&t, a, c));
    }

    #[test]
    fn bag_of_bags() {
        let t = Type::Bag(Box::new(int_bag()));
        let a = "val it = [[3],[1, 2]] : int bag bag";
        let b = "val it = [[2,1],[3]] : int bag bag";
        assert!(equivalent_with_type(&t, a, b));
    }

    #[test]
    fn not_equivalent_wrong_element() {
        let a = "val it = [1,2,3] : int bag";
        let b = "val it = [1,2,4] : int bag";
        assert!(!equivalent_with_type(&int_bag(), a, b));
    }

    #[test]
    fn not_equivalent_wrong_size() {
        let a = "val it = [1,2,3] : int bag";
        let b = "val it = [1,2] : int bag";
        assert!(!equivalent_with_type(&int_bag(), a, b));
    }
}
