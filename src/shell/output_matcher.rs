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
use std::str::from_utf8;

/// Compares two output strings modulo whitespace and bag reordering.
///
/// Parses the type annotation from the expected output (the text
/// after the top-level ` : `) and uses it to guide comparison. If
/// the expected output has no type annotation, or the annotation
/// fails to parse (e.g. a built-in record type, or a type variable
/// not bound by an outer `forall`), falls back to whitespace-
/// normalized string equality. The fallback is conservative: it
/// only declares the strings equivalent when they normalize to the
/// same byte sequence.
pub fn equivalent(actual: &str, expected: &str) -> bool {
    match extract_type(expected) {
        Some(t) => match type_parser::try_string_to_type(&t) {
            Ok(parsed_type) => {
                equivalent_with_type(&parsed_type, actual, expected)
            }
            Err(_) => fallback_equal(actual, expected),
        },
        None => fallback_equal(actual, expected),
    }
}

/// Whitespace-normalized string comparison. Used by [`equivalent`]
/// when the type annotation is missing or malformed.
fn fallback_equal(actual: &str, expected: &str) -> bool {
    normalize_whitespace(actual) == normalize_whitespace(expected)
}

/// Same as [`equivalent`] but with an explicit type (used by unit
/// tests where the type is known).
pub fn equivalent_with_type(
    type_: &Type,
    actual: &str,
    expected: &str,
) -> bool {
    let (prefix0, code0) = match extract_prefix_and_value(actual) {
        Some(p) => p,
        None => return false,
    };
    let (prefix1, code1) = match extract_prefix_and_value(expected) {
        Some(p) => p,
        None => return false,
    };
    // The `val NAME = ` prefix (or absence thereof) is part of the
    // output; mismatching prefixes — different variable names, a
    // missing `val`, or a typo like `value` — must produce a
    // non-equivalent verdict regardless of how the value compares.
    if normalize_whitespace(&prefix0) != normalize_whitespace(&prefix1) {
        return false;
    }
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

/// Splits `val NAME = VALUE : TYPE` (or `VALUE : TYPE`) into the
/// `val NAME = ` prefix (empty when absent) and the `VALUE`
/// portion. Returns `None` if the top-level ` : ` separator is
/// missing.
fn extract_prefix_and_value(s: &str) -> Option<(String, String)> {
    let bytes = s.as_bytes();
    let n = bytes.len();

    // Optional `val NAME = ` prefix. Strict pattern (whitespace*
    // `val` whitespace+ ident whitespace* `=` whitespace*) — the
    // old substring check accepted `value queens =` because
    // "value" contains "val".
    let value_start = parse_val_prefix(s).unwrap_or(0);

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
    Some((
        s[..value_start].to_string(),
        s[value_start..end].to_string(),
    ))
}

fn is_whitespace_char(c: char) -> bool {
    matches!(c, ' ' | '\n' | '\r' | '\t')
}

fn is_word_char(c: char) -> bool {
    c.is_alphanumeric() || c == '_' || c == '\'' || c == '~'
}

/// Recognizes a `val NAME = ` prefix at the start of `s` and returns
/// the byte index just past the trailing whitespace, or `None` if
/// the input doesn't match. Whitespace is permitted around `val`
/// and `=`. The keyword `val` must be followed by ASCII whitespace
/// (so `value queens = …` is rejected).
fn parse_val_prefix(s: &str) -> Option<usize> {
    let bytes = s.as_bytes();
    let n = bytes.len();
    let mut i = 0;
    while i < n && is_whitespace_char(bytes[i] as char) {
        i += 1;
    }
    if i + 3 > n || &bytes[i..i + 3] != b"val" {
        return None;
    }
    i += 3;
    // `val` must be terminated by whitespace; this also rejects
    // identifiers that start with `val` such as `value`.
    if i >= n || !is_whitespace_char(bytes[i] as char) {
        return None;
    }
    while i < n && is_whitespace_char(bytes[i] as char) {
        i += 1;
    }
    let ident_start = i;
    while i < n && is_word_char(bytes[i] as char) {
        i += 1;
    }
    if i == ident_start {
        return None;
    }
    while i < n && is_whitespace_char(bytes[i] as char) {
        i += 1;
    }
    if i >= n || bytes[i] as char != '=' {
        return None;
    }
    i += 1;
    while i < n && is_whitespace_char(bytes[i] as char) {
        i += 1;
    }
    Some(i)
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

    // --- Fallback paths: type missing or unparseable ---------------

    #[test]
    fn type_unparseable_falls_back_to_string_equality() {
        // Built-in record syntax ({<:..., a:..., ...}) panics in
        // `type_parser`; equivalent() should fall back to a
        // whitespace-normalized string compare.
        let a = "val it = {a=1,b=2} : {<:int * int -> bool, a:int, b:int}";
        let b = "val it = {a=1,b=2} : {<:int * int -> bool, a:int, b:int}";
        assert!(equivalent(a, b));
    }

    #[test]
    fn type_unparseable_with_real_difference_returns_false() {
        let a = "val it = {a=1,b=2} : {<:int * int -> bool, a:int, b:int}";
        let b = "val it = {a=1,b=3} : {<:int * int -> bool, a:int, b:int}";
        assert!(!equivalent(a, b));
    }

    #[test]
    fn unknown_type_variable_falls_back_to_string_equality() {
        // 'a is not bound by a `forall` in the displayed type, so
        // `try_string_to_type` returns Err.
        let a = "val outer = fn : 'a -> 'a";
        let b = "val outer = fn : 'a -> 'a";
        assert!(equivalent(a, b));
    }

    #[test]
    fn unknown_type_variable_real_diff_returns_false() {
        let a = "val outer = fn : 'a -> 'a";
        let b = "val outer = fn : 'a -> 'b";
        assert!(!equivalent(a, b));
    }

    #[test]
    fn no_type_annotation_falls_back_to_string_equality() {
        assert!(equivalent("hello world", "hello world"));
        assert!(!equivalent("hello world", "hello there"));
    }

    #[test]
    fn no_type_annotation_whitespace_tolerant() {
        // Fallback applies the same whitespace normalization as the
        // happy path.
        assert!(equivalent("[1,  2, 3]", "[1, 2,  3]"));
        assert!(equivalent("val it = ()", "val  it  =  ()"));
    }

    #[test]
    fn type_parse_failure_does_not_panic_or_print() {
        // try_string_to_type returns Err on these — equivalent() is
        // expected to handle without panicking. A regression that
        // re-introduces `panic!` (and `catch_unwind` to swallow it)
        // would still pass this test by name, but Rust's default
        // panic hook would print a stack trace to stderr. We can't
        // assert "no stderr noise" cheaply without a stderr-capture
        // helper, so this is left as a smoke test.
        let _ = equivalent(
            "val it = {} : {<:int * int -> bool}",
            "val it = {} : {<:int * int -> bool}",
        );
        let _ = equivalent("val outer = fn : 'a -> 'a", "x");
        let _ = equivalent("x", "y");
    }

    // --- extract_type ----------------------------------------------

    #[test]
    fn extract_type_no_annotation_is_none() {
        assert_eq!(extract_type("hello"), None);
        assert_eq!(extract_type("val it = 3"), None);
        assert_eq!(extract_type(""), None);
    }

    #[test]
    fn extract_type_simple() {
        assert_eq!(extract_type("val it = 3 : int"), Some("int".to_string()),);
        assert_eq!(
            extract_type("val it = [1,2] : int list"),
            Some("int list".to_string()),
        );
    }

    #[test]
    fn extract_type_ignores_inner_colons() {
        // Colon inside a string literal must not be treated as a
        // type separator.
        assert_eq!(
            extract_type("val it = \"a:b\" : string"),
            Some("string".to_string()),
        );
        // Colon inside a record field type is at depth > 0; only
        // the top-level ` : ` separates value from type.
        assert_eq!(
            extract_type("val it = {a=1} : {a:int}"),
            Some("{a:int}".to_string()),
        );
    }

    // --- val-prefix sanity checks ----------------------------------

    #[test]
    fn variable_name_difference_caught() {
        // queens vs queens' — distinct identifiers, must NOT
        // collapse to equivalent.
        let a = "val queens' = fn : int -> int";
        let b = "val queens = fn : int -> int";
        assert!(!equivalent(a, b));
    }

    #[test]
    fn val_keyword_typo_caught() {
        // `value` ≠ `val`. The old "val " substring check accepted
        // this because "value" contains "val ".
        let a = "val queens' = fn : int -> int";
        let b = "value queens' = fn : int -> int";
        assert!(!equivalent(a, b));
    }

    #[test]
    fn missing_val_keyword_caught() {
        // Bare assignment without the `val` keyword.
        let a = "val it = 3 : int";
        let b = "it = 3 : int";
        assert!(!equivalent(a, b));
    }

    #[test]
    fn val_prefix_whitespace_tolerant() {
        // Different whitespace inside the `val NAME = ` prefix is
        // still equivalent (matches the rest of the matcher's
        // contract).
        let a = "val queens' = fn : int -> int";
        let b = "val queens'  =  fn : int -> int";
        assert!(equivalent(a, b));
    }

    #[test]
    fn parse_val_prefix_accepts_well_formed() {
        // Keyword `val`, whitespace, identifier, optional whitespace,
        // `=`, optional whitespace.
        assert_eq!(parse_val_prefix("val it = 3"), Some(9));
        assert_eq!(parse_val_prefix("val queens' = fn"), Some(14));
        assert_eq!(parse_val_prefix("val   x   =   3"), Some(14));
    }

    #[test]
    fn parse_val_prefix_rejects_lookalikes() {
        // `value` is not the keyword.
        assert_eq!(parse_val_prefix("value foo = 3"), None);
        // `val` immediately followed by an identifier character is
        // also rejected (it would be `vali` for example).
        assert_eq!(parse_val_prefix("vali = 3"), None);
        // Missing `=`.
        assert_eq!(parse_val_prefix("val foo bar"), None);
        // Missing identifier.
        assert_eq!(parse_val_prefix("val = 3"), None);
        // Bare expression — no `val`.
        assert_eq!(parse_val_prefix("3"), None);
    }
}
