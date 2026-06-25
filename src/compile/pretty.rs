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

use crate::compile::library;
use crate::compile::lindig::{
    self, Doc, align, beside, fill, flatten, group, hard_line, line, nest,
    render, text, union,
};
use crate::compile::tabular;
use crate::compile::types::Label;
use crate::compile::types::{Op, PrimitiveType, Type, TypeVariable};
use crate::eval::code::Impl;
use crate::eval::date;
use crate::eval::real::Real;
use crate::eval::val::Val;
use crate::shell::prop::Output as PropOutput;
use crate::syntax::parser::{
    append_bare_id, append_id, char_to_string, string_to_string_append,
};
use std::collections::{BTreeMap, HashMap};
use std::fmt::{self, Write};
use std::rc::Rc;

/// Text used to print a relation (a foreign/progressive list value) that
/// is not eagerly materialised.
const RELATION: &str = "<relation>";

/// Prints values prettily.
pub struct Pretty {
    line_width: i32,
    output: PropOutput,
    print_length: i32,
    print_depth: i32,
    string_depth: i32,
    /// Column width at which tabular mode folds long strings across
    /// lines. `< 1` (the default) disables folding.
    string_fold: i32,
    newline: char,
    /// Maps constructor name → argument type. Used to format record
    /// arguments with field names (e.g. `Foo {a=1,b="x"}` instead
    /// of `Foo (1,"x")`).
    constructor_arg_types: HashMap<String, Type>,
    /// Maps datatype name → list of constructor names. Used to look
    /// up a constructor's name from its ordinal.
    datatype_constructors: HashMap<String, Vec<String>>,
}

impl Type {
    /// Removes any "forall" qualifier of a type. Does not renumber
    /// the remaining type variables, and therefore can avoid cloning.
    ///
    /// Examples:
    /// - `forall 'a. 'a list` → `'a list`
    /// - `forall 'a 'b. 'b list` → `'b list`
    pub fn unqualified_quick(&self) -> &Type {
        let mut current_type = self;

        // Strip all forall qualifiers
        while let Type::Forall(inner_type, _size) = current_type {
            current_type = inner_type;
        }

        current_type
    }

    /// Renumbers type variables.
    ///
    /// Examples:
    //  - `'b list -> 'a list`
    //  - `('b * 'a * 'b)  ->  ('a * 'b * 'a)`
    //  - `('a * 'c * 'a)  ->  ('a * 'b * 'a)`
    pub fn renumbered(&self) -> Type {
        TypeVarRenumberer::new().visit(self)
    }
}

impl Pretty {
    pub fn new(
        line_width: i32,
        output: PropOutput,
        print_length: i32,
        print_depth: i32,
        string_depth: i32,
        string_fold: i32,
        constructor_arg_types: HashMap<String, Type>,
        datatype_constructors: HashMap<String, Vec<String>>,
    ) -> Self {
        Self {
            line_width,
            output,
            print_length,
            print_depth,
            string_depth,
            string_fold,
            newline: '\n',
            constructor_arg_types,
            datatype_constructors,
        }
    }

    /// Prints a binding `val name = value : type` to a buffer, choosing
    /// line breaks with the Wadler-Leijen layout engine
    /// ([`crate::compile::lindig`]).
    pub fn pretty(
        &self,
        buf: &mut String,
        type_: &Type,
        value: &Val,
    ) -> Result<(), fmt::Error> {
        if let Val::Typed(b) = value {
            let (name, v, t) = &**b;
            // In tabular mode, a value whose type is a list of records
            // prints as a table. The tabular printer may decline at
            // runtime (e.g. when "printDepth" is too low to show the
            // rows); then, and for every other value, use the classic
            // printer.
            if !matches!(self.output, PropOutput::Classic)
                && tabular::can_print(t)
                && matches!(v, Val::List(_))
                && self.pretty_tabular(buf, name, t, v)
            {
                return Ok(());
            }
            self.pretty_classic(buf, name, t, v);
            return Ok(());
        }
        // Fallback: render a bare value.
        let doc = self.value_doc(type_, value, 0);
        buf.push_str(&render(self.width(), doc));
        Ok(())
    }

    /// Page width passed to the renderer. Rendering at `lineWidth - 1`
    /// matches SML/NJ's right margin: its Oppen printer allows one more
    /// column than ours before breaking.
    fn width(&self) -> i32 {
        if self.line_width < 0 {
            i32::MAX
        } else {
            self.line_width - 1
        }
    }

    /// Renders a binding in classic (the default, non-tabular) style.
    fn pretty_classic(
        &self,
        buf: &mut String,
        name: &str,
        type_: &Type,
        value: &Val,
    ) {
        let mut prefix = String::from("val ");
        // The binding name is printed without reserved-word quoting, matching
        // SML/NJ and morel-java (e.g. `val it = ...`, not `val `it` = ...`).
        append_bare_id(&mut prefix, name);
        prefix.push_str(" =");
        // The value is one level below the binding, so start at depth 1: at
        // "printDepth" 0 the whole value prints as "#", matching SML/NJ.
        let value_doc = self.value_doc(type_, value, 1);
        // A "variant" value prints its declared type with a " variant"
        // suffix, e.g. "INT 3 : int variant".
        let type_body = if let Val::Variant(boxed) = value {
            let display = boxed.as_ref().0.unqualified_quick().renumbered();
            beside(self.type_doc(&display, 0, 0), text(" variant"))
        } else {
            let display = type_.unqualified_quick().renumbered();
            self.type_doc(&display, 0, 0)
        };
        // The value stays on the "val ... =" line only if it fits there
        // entirely flat; otherwise the whole value moves to its own line,
        // indented by 2, where it is free to wrap. Likewise the type stays
        // on the value's last line if it fits flat there, otherwise it
        // moves to its own line. The "wide" alternative is flattened so the
        // decision is made on the value (or type) as a whole, not deferred
        // to its internal line breaks. This matches how SML/NJ lays out a
        // binding.
        let value_part = union(
            beside(text(" "), flatten(&value_doc)),
            nest(2, beside(hard_line(), value_doc)),
        );
        let type_part = union(
            beside(text(" : "), flatten(&type_body)),
            nest(2, beside(hard_line(), beside(text(": "), type_body))),
        );
        let doc = beside(text(&prefix), beside(value_part, type_part));
        buf.push_str(&render(self.width(), doc));
    }

    /// Tries to render a binding as a table, for "output = tabular". On
    /// success the table is written to `buf`, followed by a "val name :
    /// type" line, and returns true. If the tabular printer declines,
    /// leaves `buf` unchanged and returns false.
    fn pretty_tabular(
        &self,
        buf: &mut String,
        name: &str,
        type_: &Type,
        value: &Val,
    ) -> bool {
        let start = buf.len();
        let printed = tabular::print(
            buf,
            0,
            type_,
            value,
            self.print_depth,
            self.print_length,
            self.string_depth,
            self.string_fold,
            self.newline,
        );
        if !printed {
            buf.truncate(start);
            return false;
        }
        let mut line = String::from("val ");
        append_bare_id(&mut line, name);
        line.push_str(" : ");
        // A "variant" value prints its declared type with a " variant"
        // suffix.
        let (display, suffix) = match value {
            Val::Variant(boxed) => (
                boxed.as_ref().0.unqualified_quick().renumbered(),
                " variant",
            ),
            _ => (type_.unqualified_quick().renumbered(), ""),
        };
        line.push_str(&render(i32::MAX, self.type_doc(&display, 0, 0)));
        line.push_str(suffix);
        buf.push_str(&line);
        true
    }

    /// Substitutes `Type::Variable(i)` with `args[i]` throughout a type.
    fn instantiate(type_: &Type, args: &[Rc<Type>]) -> Type {
        match type_ {
            // lint: sort until '#}' where '##Type::'
            Type::Bag(t) => Type::Bag(Rc::new(Self::instantiate(t, args))),
            Type::Data(name, ts) => Type::Data(
                name.clone(),
                ts.iter()
                    .map(|t| Rc::new(Self::instantiate(t, args)))
                    .collect(),
            ),
            Type::Fn(a, b) => Type::Fn(
                Rc::new(Self::instantiate(a, args)),
                Rc::new(Self::instantiate(b, args)),
            ),
            Type::List(t) => Type::List(Rc::new(Self::instantiate(t, args))),
            Type::Record(p, fields) => Type::Record(
                *p,
                fields
                    .iter()
                    .map(|(k, v)| {
                        (k.clone(), Rc::new(Self::instantiate(v, args)))
                    })
                    .collect(),
            ),
            Type::Tuple(ts) => Type::Tuple(
                ts.iter()
                    .map(|t| Rc::new(Self::instantiate(t, args)))
                    .collect(),
            ),
            Type::Variable(tv) if tv.id < args.len() => (*args[tv.id]).clone(),
            // #}
            _ => type_.clone(),
        }
    }

    // -- Value documents ------------------------------------------------

    /// Builds a Doc for a value of the given type.
    fn value_doc(&self, type_ref: &Type, value: &Val, depth: i32) -> Doc {
        // Strip any alias.
        let mut current_type = type_ref;
        while let Type::Alias(_, inner, _) = current_type {
            current_type = inner;
        }

        // A "variant" value prints its wrapped value with the wrapped
        // (inner) type.
        if let Val::Variant(boxed) = value {
            let (inner_type, inner_val) = boxed.as_ref();
            return self.value_doc(inner_type, inner_val, depth);
        }

        if self.print_depth >= 0 && depth > self.print_depth {
            return text("#");
        }

        match current_type {
            // lint: sort until '#}' where '##Type::'
            Type::Bag(element_type) => {
                if matches!(value, Val::File(_)) {
                    text(RELATION)
                } else {
                    self.seq_doc(
                        "[",
                        "]",
                        self.element_docs(
                            element_type,
                            value.expect_list(),
                            depth,
                        ),
                    )
                }
            }
            Type::Data(name, args) => {
                self.data_type_doc(name, args, value, depth)
            }
            Type::Fn(_, _) => text("fn"),
            Type::Forall(inner, _size) => {
                self.value_doc(inner, value, depth + 1)
            }
            Type::List(element_type) => {
                // A data file appearing as a directory entry stays as
                // `Val::File`; render it as `<relation>` rather than
                // eagerly materialising every row.
                if matches!(value, Val::File(_)) {
                    text(RELATION)
                } else {
                    self.seq_doc(
                        "[",
                        "]",
                        self.element_docs(
                            element_type,
                            value.expect_list(),
                            depth,
                        ),
                    )
                }
            }
            Type::Named(args, name) => {
                self.named_value_doc(name, args, value, depth)
            }
            Type::Primitive(prim_type) => self.primitive_doc(prim_type, value),
            Type::Record(_progressive, arg_name_types) => {
                self.record_value_doc(arg_name_types, value, depth)
            }
            Type::Tuple(arg_types) => {
                let list = value.expect_list();
                let mut elements = Vec::with_capacity(arg_types.len());
                for (element_type, element_value) in arg_types.iter().zip(list)
                {
                    elements.push(self.value_doc(
                        element_type,
                        element_value,
                        depth + 1,
                    ));
                }
                self.seq_doc("(", ")", elements)
            }
            Type::Variable(_) => {
                // Type variable: no structural info, print value directly.
                text(&value.to_string())
            }
            // #}
            _ => text(&value.to_string()),
        }
    }

    /// Builds a Doc for a record value.
    fn record_value_doc(
        &self,
        arg_name_types: &BTreeMap<Label, Rc<Type>>,
        value: &Val,
        depth: i32,
    ) -> Doc {
        let field_depth = depth + 1;
        // A `Val::File` carries its own state; map each type field through
        // to the matching child file. Unknown child entries render as
        // `Val::Unit` so the field list stays aligned with the type.
        if let Val::File(file) = value {
            use crate::eval::file::FileState;
            let entries: Vec<(String, Val)> = match &*file.state.borrow() {
                FileState::Directory { entries } => entries
                    .iter()
                    .map(|(l, c)| (l.to_string(), Val::File(Rc::clone(c))))
                    .collect(),
                _ => Vec::new(),
            };
            let mut fields = Vec::with_capacity(arg_name_types.len());
            for (name, field_type) in arg_name_types {
                let val2 = entries
                    .iter()
                    .find(|(n, _)| *n == name.to_string())
                    .map_or(Val::Unit, |(_, v)| v.clone());
                let mut prefix = String::new();
                append_id(&mut prefix, &name.to_string());
                prefix.push('=');
                fields.push(beside(
                    text(&prefix),
                    self.value_doc(field_type, &val2, field_depth),
                ));
            }
            return self.seq_doc("{", "}", fields);
        }
        // Single-field records are stored as bare values, not wrapped in
        // Val::List.
        let list_owned;
        let list = if let Val::List(l) = value {
            l.as_slice()
        } else {
            list_owned = [value.clone()];
            &list_owned
        };
        let mut fields = Vec::with_capacity(arg_name_types.len());
        for ((name, field_type), val2) in arg_name_types.iter().zip(list) {
            let mut prefix = String::new();
            append_id(&mut prefix, &name.to_string());
            prefix.push('=');
            fields.push(beside(
                text(&prefix),
                self.value_doc(field_type, val2, field_depth),
            ));
        }
        self.seq_doc("{", "}", fields)
    }

    /// Builds a Doc for an arbitrary named type used as a placeholder for
    /// unknown `CONSTANT`/`CONSTRUCT` constructors: `name` is the
    /// constructor name and the value is either `Val::Unit` (nullary
    /// `CONSTANT`) or a `Val::Variant` payload (unary `CONSTRUCT`).
    fn named_value_doc(
        &self,
        name: &str,
        _args: &[Rc<Type>],
        value: &Val,
        depth: i32,
    ) -> Doc {
        match value {
            Val::Unit => text(name),
            Val::Variant(boxed) => {
                let (inner_type, inner_val) = boxed.as_ref();
                let need_parens = !matches!(inner_type, Type::Primitive(_));
                let inner = self.value_doc(inner_type, inner_val, depth);
                let inner = if need_parens {
                    beside(text("("), beside(inner, text(")")))
                } else {
                    inner
                };
                beside(text(name), beside(text(" "), inner))
            }
            _ => {
                beside(text(name), beside(text(" "), text(&value.to_string())))
            }
        }
    }

    /// Builds a Doc for a value of a data type: a "bag" or "vector" lays
    /// out like a list, an opaque value prints directly, and a
    /// constructor application prints its name followed by its (possibly
    /// parenthesized) argument.
    fn data_type_doc(
        &self,
        name: &str,
        args: &[Rc<Type>],
        value: &Val,
        depth: i32,
    ) -> Doc {
        if name == "descending"
            && let Val::Constructor(_, inner) = value
        {
            return beside(
                text("DESC "),
                self.value_doc(&args[0], inner, depth),
            );
        }
        if name == "time"
            && let Val::Time(t) = value
        {
            // `time` values display as their nanosecond count.
            return text(&t.to_string());
        }
        if name == "date"
            && let Val::Date(d, o) = value
        {
            return text(&date::format_iso(*d, *o));
        }
        // A "doc" (pretty-printer document) is abstract; print it as "-",
        // as Standard ML prints a value of an abstract type.
        if name == "doc" {
            return text("-");
        }
        // Datatypes whose constructor values are `Val::Constructor(tag, _)`
        // with a dense `base - i` ordinal scheme (weekday, month, exn,
        // range): map back through the `BuiltInDatatype` registry to print
        // the constructor name, then the argument (if any).
        if let Val::Constructor(tag, inner) = value
            && let Some(d) = library::BuiltInDatatype::from_name(name)
            && let Some(label) = d.constructor_name_for_tag(*tag)
        {
            if **inner == Val::Unit {
                return text(label);
            }
            let inner_type = match (d, label) {
                (library::BuiltInDatatype::Exn, "Fail") => {
                    Type::Primitive(PrimitiveType::String)
                }
                (
                    library::BuiltInDatatype::Range,
                    "CLOSED" | "CLOSED_OPEN" | "OPEN" | "OPEN_CLOSED",
                ) => Type::Tuple(vec![args[0].clone(), args[0].clone()]),
                (
                    library::BuiltInDatatype::ContinuousSet
                    | library::BuiltInDatatype::DiscreteSet,
                    _,
                ) => Type::List(Rc::new(Type::Data(
                    "range".to_string(),
                    vec![args[0].clone()],
                ))),
                _ => (*args[0]).clone(),
            };
            return beside(
                text(label),
                beside(text(" "), self.value_doc(&inner_type, inner, depth)),
            );
        }
        match value {
            Val::Fn(f) => {
                // Nullary built-in constructors and constants (e.g.
                // `EQUAL`, `LESS`, `Jan`, `Mon`) reach here as bare
                // function references; their display is just their name.
                if !matches!(f.get_impl(), Impl::E0(_)) {
                    panic!("Expected list, got non-nullary Val::Fn({:?})", f);
                }
                text(f.name())
            }
            Val::Order(o) => text(o.name()),
            Val::Inl(v) => {
                beside(text("INL "), self.con_arg_doc(&args[0], v, depth))
            }
            Val::Inr(v) => {
                beside(text("INR "), self.con_arg_doc(&args[1], v, depth))
            }
            Val::Some(v) => {
                beside(text("SOME "), self.con_arg_doc(&args[0], v, depth))
            }
            Val::Unit => {
                if name == "option" {
                    text("NONE")
                } else {
                    panic!("Expected list")
                }
            }
            Val::Constructor(ordinal, inner) => {
                if let Some(constructors) = self.datatype_constructors.get(name)
                {
                    let con_name = &constructors[*ordinal];
                    if **inner == Val::Unit {
                        text(con_name)
                    } else if let Some(arg_type) =
                        self.constructor_arg_types.get(con_name)
                    {
                        let instantiated = Self::instantiate(arg_type, args);
                        beside(
                            text(con_name),
                            beside(
                                text(" "),
                                self.con_arg_doc(&instantiated, inner, depth),
                            ),
                        )
                    } else {
                        beside(
                            text(con_name),
                            beside(text(" "), text(&inner.to_string())),
                        )
                    }
                } else {
                    text(&value.to_string())
                }
            }
            Val::List(list) => {
                if name == "vector" {
                    beside(
                        text("#"),
                        self.seq_doc(
                            "[",
                            "]",
                            self.element_docs(&args[0], list, depth),
                        ),
                    )
                } else if name == "bag" {
                    self.seq_doc(
                        "[",
                        "]",
                        self.element_docs(&args[0], list, depth),
                    )
                } else {
                    // Built-in constructed datatype stored as a list
                    // `["TyCon", arg]` (e.g. a synthetic constructor).
                    let ty_con_name = list[0].expect_string();
                    if list.len() < 2 {
                        text(&ty_con_name)
                    } else {
                        let arg = &list[1];
                        let need_parens = matches!(arg, Val::List(_));
                        let arg_doc = self.value_doc(
                            &Type::Primitive(PrimitiveType::String),
                            arg,
                            depth + 1,
                        );
                        let arg_doc = if need_parens {
                            beside(text("("), beside(arg_doc, text(")")))
                        } else {
                            arg_doc
                        };
                        beside(text(&ty_con_name), beside(text(" "), arg_doc))
                    }
                }
            }
            _ => panic!("Expected list"),
        }
    }

    /// Formats `inner`, the argument of a constructor application,
    /// wrapping it in parentheses when it is itself a (non-nullary)
    /// constructor application — e.g. the inner `SOME 7` of `SOME (SOME
    /// 7)`, or `INL x`, `INR x`, `C x`.
    fn con_arg_doc(&self, type_ref: &Type, inner: &Val, depth: i32) -> Doc {
        let paren = matches!(inner, Val::Some(_) | Val::Inl(_) | Val::Inr(_))
            || matches!(inner, Val::Constructor(_, c) if **c != Val::Unit);
        let doc = self.value_doc(type_ref, inner, depth);
        if paren {
            beside(text("("), beside(doc, text(")")))
        } else {
            doc
        }
    }

    /// Builds Docs for list elements, applying the `printLength` limit.
    fn element_docs(
        &self,
        element_type: &Type,
        list: &[Val],
        depth: i32,
    ) -> Vec<Doc> {
        let mut docs = Vec::new();
        for (i, o) in list.iter().enumerate() {
            if self.print_length >= 0 && i >= self.print_length as usize {
                docs.push(text("..."));
                break;
            }
            docs.push(self.value_doc(element_type, o, depth + 1));
        }
        docs
    }

    /// Builds a Doc for a bracketed sequence (a list, record, or tuple).
    /// Renders flat as `(a,b,c)`, and when it does not fit, with each
    /// element on its own line, aligned under the first.
    fn seq_doc(&self, open: &str, close: &str, docs: Vec<Doc>) -> Doc {
        if docs.is_empty() {
            return text(&format!("{}{}", open, close));
        }
        // Elements fill across lines: as many as fit share a line, and each
        // element is treated as a unit (a record in a list of records stays
        // together, and the list wraps between records). There is no space
        // after the comma, the way SML/NJ prints list, tuple, and record
        // values. Continuation lines align under the first element.
        let n = docs.len();
        let mut items = Vec::with_capacity(n);
        for (i, d) in docs.into_iter().enumerate() {
            if i < n - 1 {
                items.push(beside(d, text(",")));
            } else {
                items.push(d);
            }
        }
        beside(
            text(open),
            beside(align(fill(&lindig::empty(), &items)), text(close)),
        )
    }

    /// Builds a string for a primitive leaf value, then wraps it as text.
    fn primitive_doc(&self, prim_type: &PrimitiveType, value: &Val) -> Doc {
        let mut s = String::new();
        let _ = self.pretty_primitive(&mut s, prim_type, value);
        text(&s)
    }

    fn pretty_primitive(
        &self,
        buf: &mut String,
        prim_type: &PrimitiveType,
        value: &Val,
    ) -> Result<(), fmt::Error> {
        match prim_type {
            // lint: sort until '#}' where '##PrimitiveType::'
            PrimitiveType::Char => {
                if let Val::Char(c) = value {
                    let s = char_to_string(*c);
                    write!(buf, "#\"{}\"", s)?;
                }
            }
            PrimitiveType::Int => {
                let mut i = value.expect_int();
                if i < 0 {
                    if i == i32::MIN {
                        buf.push_str("~2147483648");
                        return Ok(());
                    }
                    buf.push('~');
                    i = -i;
                }
                write!(buf, "{}", i)?;
            }
            PrimitiveType::Real => {
                if let Val::Real(f) = value {
                    buf.push_str(&Real::to_string(*f));
                }
            }
            PrimitiveType::String => {
                if let Val::String(s) = value {
                    buf.push('"');
                    if self.string_depth >= 0
                        && s.len() > self.string_depth as usize
                    {
                        string_to_string_append(
                            &s[..self.string_depth as usize],
                            buf,
                        );
                        buf.push('#');
                    } else {
                        string_to_string_append(s, buf);
                    }
                    buf.push('"');
                }
            }
            PrimitiveType::Unit => {
                buf.push_str("()");
            }
            _ => {
                write!(buf, "{}", value)?;
            }
        }
        Ok(())
    }

    // -- Type documents -------------------------------------------------

    /// Builds a Doc for a type. Record types fill their fields across
    /// lines (as many per line as fit, aligned under the first field), the
    /// way SML/NJ wraps a wide record type; other composite types follow
    /// type-operator precedence, adding parentheses where needed.
    fn type_doc(&self, type_ref: &Type, left: u8, right: u8) -> Doc {
        match type_ref {
            // lint: sort until '#}' where '##Type::'
            Type::Alias(name, _inner, _args) => text(name),
            Type::Bag(element_type) => self.collection_type_doc(
                type_ref,
                left,
                right,
                element_type,
                "bag",
            ),
            Type::Data(name, args) | Type::Named(args, name) => {
                self.named_type_doc(name, args, left, right)
            }
            Type::Fn(param_type, result_type) => {
                if wraps(Op::FN, left, right) {
                    return parenthesize(self.type_doc(type_ref, 0, 0));
                }
                // A function type breaks before "->", which leads the
                // continuation line (indented one column, like a record or
                // tuple type). We use an explicit union rather than
                // "group": "group" would defer to an inner breakable
                // structure and leave this "->" flat. Flattening the wide
                // branch makes the fit test honest, so the outermost "->"
                // that does not fit breaks first, matching SML/NJ.
                let param_doc = self.type_doc(param_type, left, Op::FN.left);
                let result_doc =
                    self.type_doc(result_type, Op::FN.right, right);
                union(
                    flatten(&beside(
                        param_doc.clone(),
                        beside(text(" -> "), result_doc.clone()),
                    )),
                    align(nest(
                        1,
                        beside(
                            param_doc,
                            beside(
                                hard_line(),
                                beside(text("-> "), result_doc),
                            ),
                        ),
                    )),
                )
            }
            Type::Forall(inner, _size) => self.type_doc(inner, left, right),
            Type::List(element_type) => self.collection_type_doc(
                type_ref,
                left,
                right,
                element_type,
                "list",
            ),
            Type::Primitive(p) => text(p.as_str()),
            Type::Record(progressive, arg_name_types) => {
                let mut fields = Vec::new();
                for (name, field_type) in arg_name_types {
                    let mut prefix = String::new();
                    append_id(&mut prefix, &name.to_string());
                    prefix.push(':');
                    fields.push(beside(
                        text(&prefix),
                        self.type_doc(field_type, 0, 0),
                    ));
                }
                if *progressive {
                    fields.push(text("..."));
                }
                // Fields fill across lines, joined by ", " when packed.
                // SML/NJ indents continuation lines of a record type to one
                // column past the first field, so we align and then nest by
                // one.
                let n = fields.len();
                let mut field_items = Vec::with_capacity(n);
                for (i, d) in fields.into_iter().enumerate() {
                    if i < n - 1 {
                        field_items.push(beside(d, text(",")));
                    } else {
                        field_items.push(d);
                    }
                }
                let fields_doc = fill(&text(" "), &field_items);
                beside(text("{"), beside(align(nest(1, fields_doc)), text("}")))
            }
            Type::Tuple(arg_types) => {
                if wraps(Op::TUPLE, left, right) {
                    return parenthesize(self.type_doc(type_ref, 0, 0));
                }
                // A tuple type fills across lines like SML/NJ, breaking
                // before "*": the "*" leads the continuation line.
                let len = arg_types.len();
                let mut product_items = Vec::with_capacity(len);
                for (i, arg_type) in arg_types.iter().enumerate() {
                    // `*` is non-associative — `(t1 * t2) * t3`,
                    // `t1 * (t2 * t3)`, and `t1 * t2 * t3` are three distinct
                    // types — so any tuple-typed element is parenthesized.
                    let arg_doc = if matches!(&**arg_type, Type::Tuple(_)) {
                        parenthesize(self.type_doc(arg_type, 0, 0))
                    } else {
                        let left1 = if i == 0 { left } else { Op::TUPLE.right };
                        let right1 =
                            if i == len - 1 { right } else { Op::TUPLE.left };
                        self.type_doc(arg_type, left1, right1)
                    };
                    product_items.push(if i == 0 {
                        arg_doc
                    } else {
                        beside(text("* "), arg_doc)
                    });
                }
                // Continuation lines indent one column past the first
                // element, as SML/NJ does.
                align(nest(1, fill(&text(" "), &product_items)))
            }
            Type::Variable(ty_var) => text(&ty_var.name()),
        }
    }

    /// Builds a Doc for a named type application, e.g. `int option`,
    /// `(int, string) sum`, or a nullary type such as `doc`. Rendered flat
    /// (the application itself introduces no line breaks), the way SML/NJ
    /// prints a type's "moniker".
    fn named_type_doc(
        &self,
        name: &str,
        args: &[Rc<Type>],
        left: u8,
        _right: u8,
    ) -> Doc {
        let doc = match args.len() {
            0 => text(name),
            1 => {
                let arg = self.type_doc(&args[0], left, Op::APPLY.left);
                beside(arg, beside(text(" "), text(name)))
            }
            _ => {
                let mut inner = text("(");
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 {
                        inner = beside(inner, text(","));
                    }
                    inner = beside(inner, self.type_doc(arg, 0, 0));
                }
                beside(inner, beside(text(") "), text(name)))
            }
        };
        flatten(&doc)
    }

    /// Builds a Doc for a "list" or "bag" type, e.g. `int list`.
    fn collection_type_doc(
        &self,
        type_: &Type,
        left: u8,
        right: u8,
        element_type: &Type,
        type_name: &str,
    ) -> Doc {
        if wraps(Op::APPLY, left, right) {
            return parenthesize(self.type_doc(type_, 0, 0));
        }
        let element_doc = self.type_doc(element_type, left, Op::APPLY.left);
        // The "list"/"bag" keyword may break onto its own line when the
        // element type does not leave room for it.
        align(beside(element_doc, group(beside(line(), text(type_name)))))
    }
}

/// Returns whether an operator at the given outer precedences needs to be
/// parenthesized.
fn wraps(op: Op, left: u8, right: u8) -> bool {
    left > op.left || right > op.right
}

fn parenthesize(doc: Doc) -> Doc {
    beside(text("("), beside(doc, text(")")))
}

/// Visitor for renumbering type variables
struct TypeVarRenumberer {
    var_map: HashMap<usize, Type>,
}

impl TypeVarRenumberer {
    fn new() -> Self {
        Self {
            var_map: HashMap::new(),
        }
    }

    fn visit_list(&mut self, types: &[Rc<Type>]) -> Vec<Rc<Type>> {
        types.iter().map(|t| Rc::new(self.visit(t))).collect()
    }

    fn visit(&mut self, type_ref: &Type) -> Type {
        match type_ref {
            // lint: sort until '#}' where '##Type::'
            Type::Alias(name, type_, args) => Type::Alias(
                name.clone(),
                Rc::new(self.visit(type_)),
                self.visit_list(args.as_slice()),
            ),
            Type::Bag(inner) => Type::Bag(Rc::new(self.visit(inner))),
            Type::Data(name, args) => {
                Type::Data(name.clone(), self.visit_list(args.as_slice()))
            }
            Type::Fn(param_type, result_type) => Type::Fn(
                Rc::new(self.visit(param_type)),
                Rc::new(self.visit(result_type)),
            ),
            Type::Forall(type_, size) => {
                Type::Forall(Rc::new(self.visit(type_)), *size)
            }
            Type::List(inner) => Type::List(Rc::new(self.visit(inner))),
            Type::Named(types, name) => {
                let types2 = self.visit_list(types.as_slice());
                Type::Named(types2, name.clone())
            }
            Type::Primitive(_) => {
                // Primitive types don't contain type variables
                type_ref.clone()
            }
            Type::Record(progressive, arg_name_types) => Type::Record(
                *progressive,
                arg_name_types
                    .iter()
                    .map(|(name, t)| (name.clone(), Rc::new(self.visit(t))))
                    .collect(),
            ),
            Type::Tuple(arg_types) => Type::Tuple(
                arg_types.iter().map(|t| Rc::new(self.visit(t))).collect(),
            ),
            Type::Variable(type_var) => {
                // Get or create a renumbered type variable
                let i = self.var_map.len();
                self.var_map
                    .entry(type_var.id)
                    .or_insert_with(|| Type::Variable(TypeVariable::new(i)))
                    .clone()
            }
        }
    }
}
