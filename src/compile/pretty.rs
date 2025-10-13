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

use crate::compile::library::BuiltInFunction;
use crate::compile::types::{Op, PrimitiveType, Type, TypeVariable};
use crate::eval::real::Real;
use crate::eval::val::Val;
use crate::shell::prop::Output as PropOutput;
use crate::syntax::parser::{
    append_id, char_to_string, string_to_string_append,
};
use std::collections::HashMap;
use std::fmt::Write;
use std::iter::zip;

/// Prints values prettily.
pub struct Pretty {
    line_width: i32,
    output: PropOutput,
    print_length: i32,
    print_depth: i32,
    string_depth: i32,
    newline: char,
}

impl Type {
    fn is_collection(&self) -> bool {
        match &self {
            Type::List(_) => true,
            Type::Data(name, _) => name == "bag",
            _ => false,
        }
    }

    fn is_progressive(&self) -> bool {
        match self {
            Type::Record(progressive, _) => *progressive,
            _ => false,
        }
    }

    fn arg(&self, index: usize) -> Option<&Type> {
        match self {
            Type::List(inner) if index == 0 => Some(inner),
            Type::Data(_name, args) => args.get(index),
            _ => None,
        }
    }

    fn moniker(&self) -> String {
        match &self {
            // lint: sort until '#}' where '##Type::'
            Type::Alias(_, _, _) => "alias".to_string(),
            Type::Data(name, _) => name.clone(),
            Type::Fn(_, _) => "function".to_string(),
            Type::Forall(_, _) => "forall".to_string(),
            Type::List(_) => "list".to_string(),
            Type::Primitive(prim) => format!("{:?}", prim).to_lowercase(),
            Type::Record(_, _) => "record".to_string(),
            Type::Tuple(_) => "tuple".to_string(),
            _ => todo!("{:?}", self),
        }
    }

    /// Removes any "forall" qualifier of a type and renumbers the remaining
    /// type variables.
    ///
    /// Examples:
    /// - `forall 'a. 'a list` → `'a list`
    /// - `forall 'a 'b. 'b list` → `'a list`
    /// - `forall 'a 'b 'c. 'c * 'a -> {x:'a, y:'c}` → `'a * 'b -> {x:'b,
    ///   y:'a}`
    pub fn unqualified(&self) -> Type {
        let mut current_type = self;

        // Strip all forall qualifiers
        while let Type::Forall(inner_type, _size) = current_type {
            current_type = inner_type;
        }

        // If no forall was stripped, return the original
        if std::ptr::eq(current_type, self) {
            return self.clone();
        }

        self.renumbered()
    }

    /// Removes any "forall" qualifier of a type.
    ///
    /// Unlike [Type::unqualified], does not renumber the remaining
    /// type variables, and therefore can avoid cloning.
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

/// Boolean is used as a placeholder in several cases where we don't print the
/// type but print (say) a raw string ":".
static BOOL: Type = Type::Primitive(PrimitiveType::Bool);

impl Pretty {
    pub fn new(
        line_width: i32,
        output: PropOutput,
        print_length: i32,
        print_depth: i32,
        string_depth: i32,
    ) -> Self {
        Self {
            line_width,
            output,
            print_length,
            print_depth,
            string_depth,
            newline: '\n',
        }
    }

    /// Prints a value to a buffer.
    pub fn pretty(
        &self,
        buf: &mut String,
        type_: &Type,
        value: &Val,
    ) -> Result<(), std::fmt::Error> {
        let line_end = if self.line_width < 0 {
            -1
        } else {
            buf.len() as i32 + self.line_width
        };
        self.pretty1(buf, 0, &mut [line_end], 0, type_, value, 0, 0)
    }

    /// Prints a value to a buffer. If the first attempt goes beyond line_end,
    /// back-tracks, adds a newline and indent, and tries again one time.
    fn pretty_raw(
        &self,
        buf: &mut String,
        indent: usize,
        line_end: &mut [i32],
        depth: i32,
        value: &str,
    ) -> Result<(), std::fmt::Error> {
        self.pretty1(
            buf,
            indent,
            line_end,
            depth,
            &BOOL,
            &Val::Raw(value.to_string()),
            0,
            0,
        )
    }

    /// Prints a value to a buffer. If the first attempt goes beyond line_end,
    /// back-tracks, adds a newline and indent, and tries again one time.
    fn pretty1(
        &self,
        buf: &mut String,
        indent: usize,
        line_end: &mut [i32],
        depth: i32,
        type_ref: &Type,
        value: &Val,
        left: u8,
        right: u8,
    ) -> Result<(), std::fmt::Error> {
        let start = buf.len();
        let end = line_end[0];

        self.pretty2(
            buf, indent, line_end, depth, type_ref, value, left, right,
        )?;

        if end >= 0 && buf.len() as i32 > end {
            // Reset to start, remove trailing whitespace, add a newline
            buf.truncate(start);
            while !buf.is_empty()
                && (buf.ends_with(' ') || buf.ends_with(self.newline))
            {
                buf.pop();
            }
            if !buf.is_empty() {
                buf.push(self.newline);
            }

            line_end[0] = if self.line_width < 0 {
                -1
            } else {
                buf.len() as i32 + self.line_width
            };
            self.indent(buf, indent);
            self.pretty2(
                buf, indent, line_end, depth, type_ref, value, left, right,
            )?;
        }
        Ok(())
    }

    fn indent(&self, buf: &mut String, indent: usize) {
        for _ in 0..indent {
            buf.push(' ');
        }
    }

    fn pretty2(
        &self,
        buf: &mut String,
        indent: usize,
        line_end: &mut [i32],
        depth: i32,
        type_ref: &Type,
        value: &Val,
        left: u8,
        right: u8,
    ) -> Result<(), std::fmt::Error> {
        // Strip any alias
        let mut current_type = type_ref;
        while let Type::Alias(_, inner, _) = current_type {
            current_type = inner;
        }

        match value {
            Val::Typed(b) => {
                let (name, v2, t2) = &**b;
                let mut buf2 = String::from("val ");
                append_id(&mut buf2, name.as_str());

                if self.custom_print(buf, indent, line_end, depth, t2, v2)? {
                    line_end[0] = -1; // no limit
                    self.pretty_raw(buf, indent, line_end, depth, &buf2)?;
                } else {
                    buf2.push_str(" = ");
                    self.pretty_raw(buf, indent, line_end, depth, &buf2)?;
                    self.pretty1(
                        buf,
                        indent + 2,
                        line_end,
                        depth + 1,
                        t2,
                        v2,
                        0,
                        0,
                    )?;
                }
                buf.push(' ');
                self.pretty1(
                    buf,
                    indent + 2,
                    line_end,
                    depth,
                    &BOOL,
                    &Val::new_type(": ", &t2.renumbered()),
                    0,
                    0,
                )?;
                return Ok(());
            }
            Val::Named(b) => {
                let (name, inner_value) = &**b;
                append_id(buf, name);
                buf.push('=');
                self.pretty1(
                    buf,
                    indent,
                    line_end,
                    depth,
                    current_type,
                    inner_value,
                    0,
                    0,
                )?;
                return Ok(());
            }
            Val::Labeled(b) => {
                let (label, type_) = &**b;
                let mut prefix = String::new();
                append_id(&mut prefix, &label.to_string());
                prefix.push(':');
                self.pretty1(
                    buf,
                    indent,
                    line_end,
                    depth,
                    current_type,
                    &Val::new_type(&prefix, type_),
                    0,
                    0,
                )?;
                return Ok(());
            }
            Val::Type(b) => {
                let (prefix, type_) = &**b;
                return self.pretty_type(
                    buf, indent, line_end, depth, prefix, type_, left, right,
                );
            }
            _ => {}
        }

        if self.print_depth >= 0 && depth > self.print_depth {
            buf.push('#');
            return Ok(());
        }

        match current_type {
            // lint: sort until '#}' where '##Type::'
            Type::Data(name, arg_types) => {
                self.pretty_data_type(
                    buf, indent, line_end, depth, name, arg_types, value,
                )?;
            }
            Type::Fn(_, _) => {
                buf.push_str("fn");
            }
            Type::Forall(type_, _size) => {
                self.pretty2(
                    buf,
                    indent,
                    line_end,
                    depth + 1,
                    type_,
                    value,
                    0,
                    0,
                )?;
            }
            Type::List(element_type) => {
                self.print_list(
                    buf,
                    indent,
                    line_end,
                    depth,
                    element_type,
                    value.expect_list(),
                )?;
            }
            Type::Primitive(prim_type) => {
                self.pretty_primitive(buf, prim_type, value)?;
            }
            Type::Record(_progressive, arg_name_types) => {
                let list = value.expect_list();
                buf.push('{');
                let start = buf.len();
                for ((name, field_type), val2) in zip(arg_name_types, list) {
                    if buf.len() > start {
                        buf.push(',');
                    }
                    self.pretty1(
                        buf,
                        indent + 1,
                        line_end,
                        depth + 1,
                        field_type,
                        &Val::new_named(&name.to_string(), val2.clone()),
                        0,
                        0,
                    )?;
                }
                buf.push('}');
            }
            Type::Tuple(arg_types) => {
                let list = value.expect_list();
                buf.push('(');
                let start = buf.len();
                for (element_type, element_value) in zip(arg_types, list) {
                    if buf.len() > start {
                        buf.push(',');
                    }
                    self.pretty1(
                        buf,
                        indent + 1,
                        line_end,
                        depth + 1,
                        element_type,
                        element_value,
                        0,
                        0,
                    )?;
                }
                buf.push(')');
            }
            _ => todo!("{:?}", current_type),
        }
        Ok(())
    }

    fn custom_print(
        &self,
        buf: &mut String,
        _indent: usize,
        _line_end: &mut [i32],
        _depth: i32,
        type_ref: &Type,
        value: &Val,
    ) -> Result<bool, std::fmt::Error> {
        if !matches!(self.output, PropOutput::Classic)
            && self.can_print_tabular(type_ref)
            && let Val::List(records) = value
            && let Some(Type::Record(_, arg_name_types)) = type_ref.arg(0)
        {
            let headers: Vec<String> =
                arg_name_types.keys().map(ToString::to_string).collect();
            let mut widths: Vec<usize> =
                headers.iter().map(String::len).collect();

            // Convert records to string representations
            let mut string_records = Vec::new();
            for record in records {
                if let Val::List(fields) = record {
                    let string_row: Vec<String> =
                        fields.iter().map(|f| format!("{:?}", f)).collect();
                    // Update column widths
                    for (i, s) in string_row.iter().enumerate() {
                        if i < widths.len() && widths[i] < s.len() {
                            widths[i] = s.len();
                        }
                    }
                    string_records.push(string_row);
                }
            }

            self.row(buf, &headers, &widths, ' ');
            let empty_row: Vec<String> =
                headers.iter().map(|_| String::new()).collect();
            self.row(buf, &empty_row, &widths, '-');
            for record in &string_records {
                self.row(buf, record, &widths, ' ');
            }
            buf.push(self.newline);
            return Ok(true);
        }
        Ok(false)
    }

    fn can_print_tabular(&self, type_ref: &Type) -> bool {
        type_ref.is_collection()
            && type_ref
                .arg(0)
                .is_some_and(|arg| matches!(arg, Type::Record(_, _)))
            && self.can_print_tabular2(type_ref.arg(0).unwrap())
    }

    fn can_print_tabular2(&self, type_ref: &Type) -> bool {
        if let Type::Record(_, arg_name_types) = type_ref {
            arg_name_types
                .values()
                .all(|t| matches!(t, Type::Primitive(_)))
        } else {
            false
        }
    }

    fn row(
        &self,
        buf: &mut String,
        values: &[String],
        widths: &[usize],
        pad: char,
    ) {
        let start = buf.len();
        for (value, &width) in zip(values, widths) {
            if buf.len() > start {
                buf.push(' ');
            }
            let target_len = buf.len() + width;
            buf.push_str(value);
            self.pad_to(buf, target_len, pad);
        }

        // Remove trailing spaces
        while buf.ends_with(' ') {
            buf.pop();
        }
        buf.push(self.newline);
    }

    fn pad_to(&self, buf: &mut String, desired_length: usize, pad: char) {
        while buf.len() < desired_length {
            buf.push(pad);
        }
    }

    fn pretty_primitive(
        &self,
        buf: &mut String,
        prim_type: &PrimitiveType,
        value: &Val,
    ) -> Result<(), std::fmt::Error> {
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

    fn pretty_data_type(
        &self,
        buf: &mut String,
        indent: usize,
        line_end: &mut [i32],
        depth: i32,
        name: &str,
        args: &[Type],
        value: &Val,
    ) -> Result<(), std::fmt::Error> {
        let list = match &value {
            Val::Fn(f) => {
                let name = match f {
                    BuiltInFunction::OrderEqual => "EQUAL",
                    BuiltInFunction::OrderGreater => "GREATER",
                    BuiltInFunction::OrderLess => "LESS",
                    _ => panic!("Expected list"),
                };
                return self.pretty_raw(buf, indent, line_end, depth, name);
            }
            Val::List(list) => list,
            Val::Order(o) => {
                return self.pretty_raw(buf, indent, line_end, depth, o.name());
            }
            Val::Some(v) => {
                self.pretty_raw(buf, indent, line_end, depth, "SOME ")?;
                return self
                    .pretty1(buf, indent, line_end, depth, &args[0], v, 0, 0);
            }
            Val::Unit => {
                if name == "option" {
                    return self
                        .pretty_raw(buf, indent, line_end, depth, "NONE");
                }
                panic!("Expected list")
            }
            _ => panic!("Expected list"),
        };
        if name == "vector" {
            let arg_type = args.first().unwrap();
            buf.push('#');
            return self
                .print_list(buf, indent, line_end, depth, arg_type, list);
        }
        if name == "bag" {
            let arg_type = args.first().unwrap();
            return self
                .print_list(buf, indent, line_end, depth, arg_type, list);
        }
        let ty_con_name = list.first().unwrap().expect_string();
        buf.push_str(&ty_con_name);
        if let Some(arg) = list.get(1) {
            // This is a parameterized constructor. (For example, NONE is
            // not parameterized, SOME x is parameterized with x.)
            buf.push(' ');
            let need_parentheses = matches!(arg, Val::List(_));
            if need_parentheses {
                buf.push('(');
            }
            self.pretty2(
                buf,
                indent,
                line_end,
                depth + 1,
                &Type::Primitive(PrimitiveType::String),
                arg,
                0,
                0,
            )?;
            if need_parentheses {
                buf.push(')');
            }
        }
        Ok(())
    }

    fn pretty_type(
        &self,
        buf: &mut String,
        indent: usize,
        line_end: &mut [i32],
        depth: i32,
        prefix: &str,
        type_ref: &Type,
        left: u8,
        right: u8,
    ) -> Result<(), std::fmt::Error> {
        if match type_ref {
            Type::Fn(_, _) => left > Op::FN.left || right > Op::FN.right,
            Type::Tuple(_) => left > Op::TUPLE.left || right > Op::TUPLE.right,
            _ => false,
        } {
            self.pretty_raw(buf, indent, line_end, depth, "(")?;
            self.pretty_type(
                buf, indent, line_end, depth, prefix, type_ref, 0, 0,
            )?;
            self.pretty_raw(buf, indent, line_end, depth, ")")?;
            return Ok(());
        }

        buf.push_str(if buf.ends_with(' ') {
            prefix.trim_start()
        } else {
            prefix
        });
        let indent2 = indent + prefix.len();

        match type_ref {
            // lint: sort until '#}' where '##Type::'
            Type::Fn(param_type, result_type) => {
                const OP: Op = Op::FN;
                let v_param = Val::new_type("", param_type);
                self.pretty1(
                    buf, indent2, line_end, depth, &BOOL, &v_param, left,
                    OP.left,
                )?;
                let v_result = Val::new_type(" -> ", result_type);
                self.pretty1(
                    buf, indent2, line_end, depth, &BOOL, &v_result, OP.right,
                    right,
                )
            }
            Type::List(element_type) => self.pretty_collection_type(
                buf,
                indent2,
                line_end,
                depth,
                type_ref,
                "list",
                element_type,
                left,
                right,
            ),
            Type::Named(args, name) | Type::Data(name, args) => {
                const OP: Op = Op::APPLY;
                if args.len() == 1 {
                    let v_arg = Val::new_type("", &args[0]);
                    self.pretty1(
                        buf, indent2, line_end, depth, &BOOL, &v_arg, left,
                        OP.right,
                    )?;
                    buf.push(' ');
                } else if args.len() > 1 {
                    // Handle multiple args like (int * string) option
                    for (i, arg) in args.iter().enumerate() {
                        if i > 0 {
                            buf.push_str(" * ");
                        }
                        let v_arg = Val::new_type("", arg);
                        self.pretty1(
                            buf, indent2, line_end, depth, &BOOL, &v_arg, left,
                            0,
                        )?;
                    }
                    buf.push(' ');
                }
                self.pretty_raw(buf, indent2, line_end, depth, name)
            }
            Type::Primitive(p) => {
                self.pretty_raw(buf, indent2, line_end, depth, p.as_str())
            }
            Type::Record(progressive, arg_name_types) => {
                buf.push('{');
                let start = buf.len();
                for (name, element_type) in arg_name_types {
                    if buf.len() > start {
                        buf.push_str(", ");
                    }
                    self.pretty1(
                        buf,
                        indent2 + 1,
                        line_end,
                        depth,
                        &BOOL,
                        &Val::new_labeled(name, element_type),
                        0,
                        0,
                    )?;
                }
                if *progressive {
                    if buf.len() > start {
                        buf.push_str(", ");
                    }
                    self.pretty_raw(buf, indent2 + 1, line_end, depth, "...")?;
                }
                buf.push('}');
                Ok(())
            }
            Type::Tuple(arg_types) => {
                const OP: Op = Op::TUPLE;
                let start = buf.len();
                for (i, arg_type) in arg_types.iter().enumerate() {
                    if buf.len() > start {
                        self.pretty_raw(buf, indent2, line_end, depth, " * ")?;
                    }
                    self.pretty1(
                        buf,
                        indent2,
                        line_end,
                        depth,
                        &BOOL,
                        &Val::new_type("", arg_type),
                        if i == 0 { left } else { OP.right },
                        if i == arg_types.len() - 1 {
                            right
                        } else {
                            OP.left
                        },
                    )?;
                }
                Ok(())
            }
            Type::Variable(ty_var) => {
                let s = ty_var.name();
                self.pretty_raw(buf, indent2, line_end, depth, s.as_str())
            }
            _ => {
                todo!("unknown type {:?}", type_ref)
            }
        }
    }

    fn print_list(
        &self,
        buf: &mut String,
        indent: usize,
        line_end: &mut [i32],
        depth: i32,
        element_type: &Type,
        list: &[Val],
    ) -> Result<(), std::fmt::Error> {
        buf.push('[');
        let start = buf.len();
        for (i, value) in list.iter().enumerate() {
            if buf.len() > start {
                buf.push(',');
            }
            if self.print_length >= 0 && i >= self.print_length as usize {
                self.pretty_raw(buf, indent + 1, line_end, depth + 1, "...")?;
                break;
            } else {
                self.pretty1(
                    buf,
                    indent + 1,
                    line_end,
                    depth + 1,
                    element_type,
                    value,
                    0,
                    0,
                )?;
            }
        }
        buf.push(']');
        Ok(())
    }

    fn pretty_collection_type(
        &self,
        buf: &mut String,
        indent2: usize,
        line_end: &mut [i32],
        depth: i32,
        type_: &Type,
        type_name: &str,
        element_type: &Type,
        left: u8,
        right: u8,
    ) -> Result<(), std::fmt::Error> {
        if left > Op::LIST.left || right > Op::LIST.right {
            self.pretty_raw(buf, indent2, line_end, depth, "(")?;
            self.pretty_collection_type(
                buf,
                indent2,
                line_end,
                depth,
                type_,
                type_name,
                element_type,
                0,
                0,
            )?;
            self.pretty_raw(buf, indent2, line_end, depth, ")")?;
            return Ok(());
        }
        self.pretty1(
            buf,
            indent2,
            line_end,
            depth,
            type_,
            &Val::new_type("", element_type),
            left,
            Op::LIST.left,
        )?;
        buf.push(' ');
        buf.push_str(type_name);
        Ok(())
    }
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

    fn visit_list(&mut self, types: &[Type]) -> Vec<Type> {
        types.iter().map(|t| self.visit(t)).collect()
    }

    fn visit(&mut self, type_ref: &Type) -> Type {
        match type_ref {
            // lint: sort until '#}' where '##Type::'
            Type::Alias(name, type_, args) => Type::Alias(
                name.clone(),
                Box::new(self.visit(type_)),
                self.visit_list(args.as_slice()),
            ),
            Type::Data(name, args) => {
                Type::Data(name.clone(), self.visit_list(args.as_slice()))
            }
            Type::Fn(param_type, result_type) => Type::Fn(
                Box::new(self.visit(param_type)),
                Box::new(self.visit(result_type)),
            ),
            Type::Forall(type_, size) => {
                Type::Forall(Box::new(self.visit(type_)), *size)
            }
            Type::List(inner) => Type::List(Box::new(self.visit(inner))),
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
                    .map(|(name, t)| (name.clone(), self.visit(t)))
                    .collect(),
            ),
            Type::Tuple(arg_types) => {
                Type::Tuple(self.visit_list(arg_types.as_slice()))
            }
            Type::Variable(type_var) => {
                // Get or create a renumbered type variable
                let i = self.var_map.len();
                self.var_map
                    .entry(type_var.id)
                    .or_insert_with(|| Type::Variable(TypeVariable::new(i)))
                    .clone()
            }
            _ => todo!("{:?}", type_ref),
        }
    }
}
