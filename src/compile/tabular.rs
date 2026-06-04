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

//! Prints a collection of records as a table. Used by
//! `crate::compile::pretty` when the output mode is `tabular` and the
//! value's type is tabular-printable (see `can_print`).
//!
//! Supports nested collections: a record field may itself be a
//! collection of primitives, or a collection of records (recursively, to
//! any depth). Tuples are treated as records with fields named `"1"`,
//! `"2"`, etc. Numeric (`int`, `real`) columns right-align their data;
//! headers stay left-aligned.
//!
//! Mirrors morel-java's `TabularPrinter`. The renderer works in two
//! passes: a recursive walk stringifies each scalar once into a `Cell`
//! tree while measuring leaf widths in a parallel `Section` tree, then
//! the cells are rendered line by line (a row's height is the max of its
//! children's line counts).
//!
//! See <https://github.com/hydromatic/morel/issues/376>.

use crate::compile::types::{Label, PrimitiveType, Type};
use crate::eval::real::Real;
use crate::eval::val::Val;
use crate::syntax::parser::char_to_string;
use std::rc::Rc;

const ELLIPSIS: &str = "...";

/// Returns whether a type can be rendered as a table: a collection (list
/// or bag) of records or tuples, every field of which is itself a
/// tabular-printable field type (see `can_print_field`).
pub fn can_print(type_: &Type) -> bool {
    if !is_collection(type_) {
        return false;
    }
    match element_type(type_) {
        Some(elem) if is_record_like(elem) => can_print_record(elem),
        _ => false,
    }
}

/// Renders a tabular value into `buf`. Returns `true` on success.
/// Returns `false` (without writing to `buf`) when `print_depth` would
/// force the outer collection's elements to be rendered as `#` — the
/// caller then falls back to classic so the same `#` appears there.
#[allow(clippy::too_many_arguments)]
pub fn print(
    buf: &mut String,
    depth: i32,
    type_: &Type,
    value: &Val,
    print_depth: i32,
    print_length: i32,
    string_depth: i32,
    string_fold: i32,
    newline: char,
) -> bool {
    if print_depth >= 0 && depth + 1 > print_depth {
        return false;
    }
    let elem = match element_type(type_) {
        Some(e) => e,
        None => return false,
    };
    let mut root = Section::for_record("", elem);
    let root_cell =
        root.build_cell(value, print_length, string_depth, string_fold);
    root.finalize_widths();

    let header_lines = root
        .children
        .iter()
        .map(Section::header_depth)
        .max()
        .unwrap_or(0);
    for line in 0..header_lines {
        let parts: Vec<String> =
            root.children.iter().map(|c| c.header_cell(line)).collect();
        push_line(buf, &parts.join(" "), newline);
    }
    let seps: Vec<String> =
        root.children.iter().map(Section::separator).collect();
    push_line(buf, &seps.join(" "), newline);

    for line in render_cell(&root_cell, &root) {
        push_line(buf, &line, newline);
    }
    buf.push(newline);
    true
}

/// Appends `line` (trailing spaces stripped) and a newline.
fn push_line(buf: &mut String, line: &str, newline: char) {
    buf.push_str(line.trim_end_matches(' '));
    buf.push(newline);
}

fn can_print_record(record_like: &Type) -> bool {
    field_name_types(record_like)
        .iter()
        .all(|(_, t)| can_print_field(t))
}

/// Whether a type is acceptable as a tabular field: a primitive, a
/// collection of primitives, or a collection of records/tuples whose
/// fields are recursively tabular-printable.
fn can_print_field(type_: &Type) -> bool {
    if matches!(type_, Type::Primitive(_)) {
        return true;
    }
    if option_scalar(type_).is_some() {
        return true;
    }
    if is_collection(type_)
        && let Some(elem) = element_type(type_)
    {
        if matches!(elem, Type::Primitive(_)) {
            return true;
        }
        if is_record_like(elem) {
            return can_print_record(elem);
        }
    }
    false
}

// ---------------------------------------------------------------------------
// Type helpers
// ---------------------------------------------------------------------------

fn is_collection(type_: &Type) -> bool {
    matches!(type_, Type::List(_) | Type::Bag(_))
        || matches!(type_, Type::Data(name, _) if name == "bag")
}

fn element_type(type_: &Type) -> Option<&Type> {
    match type_ {
        Type::List(inner) | Type::Bag(inner) => Some(inner),
        Type::Data(name, args) if name == "bag" => {
            args.first().map(AsRef::as_ref)
        }
        _ => None,
    }
}

fn is_record_like(type_: &Type) -> bool {
    matches!(type_, Type::Record(_, _) | Type::Tuple(_))
}

/// If `type_` is `T option` where `T` is a primitive, returns `T`; otherwise
/// returns `None`. Such a field is rendered as a scalar column: `SOME x` as
/// `x`, and `NONE` as a blank cell.
fn option_scalar(type_: &Type) -> Option<&PrimitiveType> {
    if let Type::Data(name, args) = type_
        && name == "option"
        && let Some(arg) = args.first()
        && let Type::Primitive(p) = arg.as_ref()
    {
        return Some(p);
    }
    None
}

/// Renders the value of a `string option` cell so that it cannot be confused
/// with the blank cell used for `NONE`. A string is shown as an SML string
/// literal (in double-quotes, with embedded double-quotes and backslashes
/// escaped) if it is empty or contains a double-quote; otherwise it is shown
/// verbatim (subject to `string_depth` truncation).
fn option_string(s: &str, string_depth: i32) -> String {
    if s.is_empty() || s.contains('"') {
        format!("\"{}\"", s.replace('\\', "\\\\").replace('"', "\\\""))
    } else {
        stringify_scalar(&Val::String(s.to_string()), string_depth)
    }
}

/// Returns the (name, type) pairs of a record-like type: named fields in
/// alphabetical order for a record, or positional names `"1"`, `"2"`, …
/// for a tuple.
fn field_name_types(type_: &Type) -> Vec<(String, Rc<Type>)> {
    match type_ {
        Type::Record(_, fields) => fields
            .iter()
            .map(|(k, v): (&Label, &Rc<Type>)| (k.to_string(), v.clone()))
            .collect(),
        Type::Tuple(elems) => elems
            .iter()
            .enumerate()
            .map(|(i, t)| ((i + 1).to_string(), t.clone()))
            .collect(),
        _ => Vec::new(),
    }
}

/// Extracts the field values of a record/tuple value. Records (including
/// single-field ones, when they appear as collection elements) are stored
/// as a `Val::List` with one entry per field; a bare value is treated as a
/// single field.
fn fields_of(value: &Val) -> Vec<Val> {
    match value {
        Val::List(fields) => fields.clone(),
        other => vec![other.clone()],
    }
}

fn list_elems(value: &Val) -> &[Val] {
    match value {
        Val::List(elems) => elems,
        _ => &[],
    }
}

// ---------------------------------------------------------------------------
// Section tree (column structure + widths)
// ---------------------------------------------------------------------------

#[derive(Copy, Clone, PartialEq)]
enum Kind {
    Scalar,
    ScalarList,
    RecordList,
}

struct Section {
    kind: Kind,
    name: String,
    right_align: bool,
    /// Whether a SCALAR value is wrapped in `option` (so `SOME x` prints as
    /// `x` and `NONE` as a blank cell).
    optional: bool,
    children: Vec<Section>,
    width: usize,
}

impl Section {
    fn leaf(
        kind: Kind,
        name: &str,
        right_align: bool,
        optional: bool,
    ) -> Section {
        Section {
            kind,
            name: name.to_string(),
            right_align,
            optional,
            children: Vec::new(),
            width: char_len(name),
        }
    }

    /// Builds a Section tree for a record-like (record or tuple) type.
    fn for_record(name: &str, record_like: &Type) -> Section {
        let children = field_name_types(record_like)
            .iter()
            .map(|(n, t)| Section::for_field(n, t))
            .collect();
        Section {
            kind: Kind::RecordList,
            name: name.to_string(),
            right_align: false,
            optional: false,
            children,
            width: char_len(name),
        }
    }

    /// Builds a Section for one field of a record-like type.
    fn for_field(name: &str, type_: &Type) -> Section {
        if let Type::Primitive(p) = type_ {
            return Section::leaf(Kind::Scalar, name, is_numeric(p), false);
        }
        if let Some(p) = option_scalar(type_) {
            // `T option` (T primitive): a scalar column where `SOME x`
            // prints as `x` and `NONE` as a blank cell.
            return Section::leaf(Kind::Scalar, name, is_numeric(p), true);
        }
        if let Some(elem) = element_type(type_) {
            if let Type::Primitive(p) = elem {
                return Section::leaf(
                    Kind::ScalarList,
                    name,
                    is_numeric(p),
                    false,
                );
            }
            if is_record_like(elem) {
                return Section::for_record(name, elem);
            }
        }
        // Unreachable when `can_print` has accepted the type.
        Section::leaf(Kind::Scalar, name, false, false)
    }

    /// Builds a `Cell` from a value, updating leaf widths as a side
    /// effect.
    fn build_cell(
        &mut self,
        value: &Val,
        print_length: i32,
        string_depth: i32,
        string_fold: i32,
    ) -> Cell {
        match self.kind {
            Kind::Scalar => {
                let s = if self.optional {
                    // `NONE` is `Val::Unit` (a blank cell); `SOME x` is
                    // `Val::Some(x)`. A `string option` value must be
                    // distinguishable from the blank `NONE` cell, so an
                    // empty or quote-containing string is shown as a
                    // quoted SML string literal.
                    match value {
                        Val::Some(inner) => match inner.as_ref() {
                            Val::String(str_val) => {
                                option_string(str_val, string_depth)
                            }
                            other => stringify_scalar(other, string_depth),
                        },
                        _ => String::new(),
                    }
                } else {
                    stringify_scalar(value, string_depth)
                };
                let lines = fold_string(&s, string_fold);
                for line in &lines {
                    self.width = self.width.max(char_len(line));
                }
                Cell::Lines(lines)
            }
            Kind::ScalarList => {
                let mut items = Vec::new();
                for (count, item) in list_elems(value).iter().enumerate() {
                    if print_length >= 0 && count >= print_length as usize {
                        items.push(ELLIPSIS.to_string());
                        self.width = self.width.max(ELLIPSIS.len());
                        break;
                    }
                    let s = stringify_scalar(item, string_depth);
                    for line in fold_string(&s, string_fold) {
                        self.width = self.width.max(char_len(&line));
                        items.push(line);
                    }
                }
                Cell::Lines(items)
            }
            Kind::RecordList => {
                let mut records = Vec::new();
                let mut truncated = false;
                let n = self.children.len();
                for (count, rec_val) in list_elems(value).iter().enumerate() {
                    if print_length >= 0 && count >= print_length as usize {
                        truncated = true;
                        break;
                    }
                    let fields = fields_of(rec_val);
                    let mut row_cells = Vec::with_capacity(n);
                    for i in 0..n {
                        let cell = self.children[i].build_cell(
                            fields.get(i).unwrap_or(&Val::Unit),
                            print_length,
                            string_depth,
                            string_fold,
                        );
                        row_cells.push(cell);
                    }
                    records.push(row_cells);
                }
                if truncated {
                    self.width = self.width.max(ELLIPSIS.len());
                }
                Cell::Records { records, truncated }
            }
        }
    }

    /// Finalizes widths bottom-up. A RECORD_LIST's width is the sum of
    /// its children's widths plus separators; if its name is wider, the
    /// slack is absorbed by the last child.
    fn finalize_widths(&mut self) {
        if self.kind != Kind::RecordList {
            return;
        }
        let mut sum = 0;
        for child in &mut self.children {
            child.finalize_widths();
            sum += child.width;
        }
        if !self.children.is_empty() {
            sum += self.children.len() - 1;
        }
        let name_len = char_len(&self.name);
        if name_len > sum {
            let extra = name_len - sum;
            self.children.last_mut().unwrap().grow_width(extra);
            sum = name_len;
        }
        self.width = sum;
    }

    fn grow_width(&mut self, extra: usize) {
        self.width += extra;
        if self.kind == Kind::RecordList
            && let Some(last) = self.children.last_mut()
        {
            last.grow_width(extra);
        }
    }

    fn header_depth(&self) -> usize {
        if self.kind != Kind::RecordList {
            return 1;
        }
        1 + self
            .children
            .iter()
            .map(Section::header_depth)
            .max()
            .unwrap_or(0)
    }

    /// Returns this section's header cell at `line`, exactly `width`
    /// characters wide.
    fn header_cell(&self, line: usize) -> String {
        if line == 0 {
            pad(&self.name, self.width, false)
        } else if self.kind == Kind::RecordList {
            let parts: Vec<String> = self
                .children
                .iter()
                .map(|c| c.header_cell(line - 1))
                .collect();
            parts.join(" ")
        } else {
            " ".repeat(self.width)
        }
    }

    fn separator(&self) -> String {
        if self.kind == Kind::RecordList {
            let parts: Vec<String> =
                self.children.iter().map(Section::separator).collect();
            parts.join(" ")
        } else {
            "-".repeat(self.width)
        }
    }
}

fn is_numeric(p: &PrimitiveType) -> bool {
    matches!(p, PrimitiveType::Int | PrimitiveType::Real)
}

// ---------------------------------------------------------------------------
// Cell tree (cached strings) + rendering
// ---------------------------------------------------------------------------

enum Cell {
    /// A scalar or scalar-list cell: one rendered line per (folded) item.
    Lines(Vec<String>),
    /// A nested record-list cell: one inner `Vec<Cell>` per nested
    /// record (one cell per field).
    Records {
        records: Vec<Vec<Cell>>,
        truncated: bool,
    },
}

/// Renders a cell into its lines, each padded (or right-aligned) to
/// `section.width`.
fn render_cell(cell: &Cell, section: &Section) -> Vec<String> {
    match cell {
        Cell::Lines(items) => items
            .iter()
            .map(|s| pad(s, section.width, section.right_align))
            .collect(),
        Cell::Records { records, truncated } => {
            let mut out = Vec::new();
            for rec in records {
                let child_lines: Vec<Vec<String>> = rec
                    .iter()
                    .zip(&section.children)
                    .map(|(c, s)| render_cell(c, s))
                    .collect();
                let height =
                    child_lines.iter().map(Vec::len).max().unwrap_or(0).max(1);
                for li in 0..height {
                    let parts: Vec<String> = child_lines
                        .iter()
                        .zip(&section.children)
                        .map(|(cl, cs)| {
                            cl.get(li)
                                .cloned()
                                .unwrap_or_else(|| " ".repeat(cs.width))
                        })
                        .collect();
                    out.push(parts.join(" "));
                }
            }
            if *truncated {
                out.push(pad(ELLIPSIS, section.width, false));
            }
            out
        }
    }
}

/// Pads `s` to `width`: right-aligned (pad on the left) when
/// `right_align`, otherwise left-aligned (pad on the right).
fn pad(s: &str, width: usize, right_align: bool) -> String {
    let len = char_len(s);
    if len >= width {
        return s.to_string();
    }
    let padding = " ".repeat(width - len);
    if right_align {
        format!("{}{}", padding, s)
    } else {
        format!("{}{}", s, padding)
    }
}

// ---------------------------------------------------------------------------
// Scalar stringification and string folding
// ---------------------------------------------------------------------------

/// The unquoted string form of a scalar value. Strings longer than
/// `string_depth` are truncated and marked with `#` (matching classic
/// mode).
fn stringify_scalar(value: &Val, string_depth: i32) -> String {
    match value {
        Val::Bool(b) => (if *b { "true" } else { "false" }).to_string(),
        Val::Char(c) => char_to_string(*c),
        Val::Int(i) => {
            if *i < 0 {
                if *i == i32::MIN {
                    "~2147483648".to_string()
                } else {
                    format!("~{}", -i)
                }
            } else {
                i.to_string()
            }
        }
        Val::Real(f) => Real::to_string(*f),
        Val::String(s) => {
            if string_depth >= 0 && char_len(s) > string_depth as usize {
                let prefix: String =
                    s.chars().take(string_depth as usize).collect();
                format!("{}#", prefix)
            } else {
                s.clone()
            }
        }
        _ => format!("{:?}", value),
    }
}

/// Folds `s` into lines no longer than `width`, breaking at whitespace
/// where possible and otherwise hard-breaking at the limit. Folding is
/// disabled (returns a single line) when `width <= 0` or `s` fits.
fn fold_string(s: &str, width: i32) -> Vec<String> {
    let chars: Vec<char> = s.chars().collect();
    let n = chars.len();
    if width <= 0 || n <= width as usize {
        return vec![s.to_string()];
    }
    let w = width as usize;
    let mut result = Vec::new();
    let mut pos = 0;
    while n - pos > w {
        let end = pos + w;
        // Last space at index <= end.
        let break_at = (0..=end).rev().find(|&i| chars[i] == ' ');
        match break_at {
            Some(b) if b > pos => {
                let line: String = chars[pos..b].iter().collect();
                result.push(line.trim_end_matches(' ').to_string());
                pos = b + 1;
                while pos < n && chars[pos] == ' ' {
                    pos += 1;
                }
            }
            _ => {
                // No usable break point; hard-break at width.
                result.push(chars[pos..end].iter().collect());
                pos = end;
            }
        }
    }
    if pos < n {
        result.push(chars[pos..].iter().collect());
    }
    result
}

fn char_len(s: &str) -> usize {
    s.chars().count()
}
