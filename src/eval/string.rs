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

use crate::compile::library::{BuiltInExn, BuiltInFunction};
use crate::eval::char::Char;
use crate::eval::code::{EvalEnv, Frame, Span};
use crate::eval::order::Order;
use crate::eval::val::Val;
use crate::shell::main::MorelError;
use std::cmp::Ordering;

/// Support for the `string` built-in type and the `String` structure.
pub struct Str;

impl Str {
    // lint: sort until '#}' where '##pub'

    /// Computes the Morel expression `String.collate f (s1, s2)`.
    ///
    /// Performs lexicographic comparison of the two strings using the given
    /// ordering `f` on characters.
    pub(crate) fn collate(
        r: &mut EvalEnv,
        f: &mut Frame,
        func_val: &Val,
        s1: &str,
        s2: &str,
    ) -> Result<Order, MorelError> {
        let chars1: Vec<char> = s1.chars().collect();
        let chars2: Vec<char> = s2.chars().collect();

        for i in 0..chars1.len().min(chars2.len()) {
            // Apply a comparison function to both chars.
            let c1 = Val::Char(chars1[i]);
            let c2 = Val::Char(chars2[i]);

            let result = match func_val {
                Val::Code(fn_code) => {
                    // User-defined function: apply to tuple
                    let tuple = Val::List(vec![c1, c2]);
                    fn_code.eval_f1(r, f, &tuple)?
                }
                Val::Fn(builtin_fn) => {
                    if *builtin_fn == BuiltInFunction::CharCompare {
                        Val::Order(Char::compare(
                            c1.expect_char(),
                            c2.expect_char(),
                        ))
                    } else {
                        panic!(
                            "Unsupported built-in function for collate: {:?}",
                            builtin_fn
                        );
                    }
                }
                _ => {
                    panic!("Expected function for collate, got {:?}", func_val)
                }
            };

            let order = result.expect_order();
            if order.0 != Ordering::Equal {
                return Ok(order);
            }
        }

        // All compared characters are equal, so now compare lengths.
        Ok(Order(chars1.len().cmp(&chars2.len())))
    }

    /// Computes the Morel expression `String.compare (s1, s2)`.
    ///
    /// Does a lexicographic comparison of the two strings using the ordering
    /// `Char.compare` on the characters. Returns `LESS`, `EQUAL`, or `GREATER`,
    /// if `s1` is less than, equal to, or greater than `s2`, respectively.
    pub(crate) fn compare(s1: &str, s2: &str) -> Order {
        Order(s1.cmp(s2))
    }

    /// Computes the Morel expression `String.concat l`.
    ///
    /// Returns the concatenation of all the strings in `l`.
    pub(crate) fn concat(strings: &[Val]) -> String {
        strings
            .iter()
            .map(Val::expect_string)
            .collect::<Vec<_>>()
            .join("")
    }

    /// Computes the Morel expression `String.concatWith sep l`.
    ///
    /// Returns the concatenation of the strings in the list `l` using the
    /// string `sep` as a separator.
    pub(crate) fn concat_with(sep: &str, strings: &[Val]) -> String {
        strings
            .iter()
            .map(Val::expect_string)
            .collect::<Vec<_>>()
            .join(sep)
    }

    /// Computes the Morel expression `String.explode s`.
    ///
    /// Returns the list of characters in the string `s`.
    pub(crate) fn explode(s: &str) -> Vec<Val> {
        s.chars().map(Val::Char).collect()
    }

    /// Computes the Morel expression `String.extract (s, i, NONE)` or
    /// `String.extract (s, i, SOME j)`.
    ///
    /// Returns the substring of `s` from the `i`-th character to the end of
    /// the string, or (if `j` is specified) the substring of `s` from the
    /// `i`-th character for length `j`.
    /// May throw [BuiltInExn::Subscript].
    pub(crate) fn extract(
        s: &str,
        i: i32,
        j_opt: Option<i32>,
        span: &Span,
    ) -> Result<Val, MorelError> {
        let chars: Vec<char> = s.chars().collect();
        if i < 0
            || j_opt.unwrap_or(0) < 0
            || (i + j_opt.unwrap_or(0)) as usize > chars.len()
        {
            return Err(MorelError::Runtime(
                BuiltInExn::Subscript,
                span.clone(),
            ));
        }
        let start = i as usize;
        let end = if let Some(j) = j_opt {
            (i + j) as usize
        } else {
            chars.len()
        };
        Ok(Val::String(chars[start..end].iter().collect()))
    }

    /// Computes the Morel expression `String.fields f s`.
    ///
    /// Returns a list of fields derived from `s` from left to right. A field
    /// is a (possibly empty) maximal substring of `s` not containing any
    /// delimiter. A delimiter is a character satisfying the predicate `f`.
    pub(crate) fn fields(
        r: &mut EvalEnv,
        f: &mut Frame,
        func: &Val,
        s: &str,
    ) -> Result<Val, MorelError> {
        let mut fields = Vec::new();
        let mut current_field = String::new();

        for c in s.chars() {
            let is_delimiter = func.apply_f1(r, f, &Val::Char(c))?;
            if is_delimiter.expect_bool() {
                // This is a delimiter
                // Always save the current field (even if empty)
                fields.push(Val::String(current_field.clone()));
                current_field.clear();
            } else {
                // Not a delimiter, add to current field
                current_field.push(c);
            }
        }

        // Always add the last field (even if empty)
        fields.push(Val::String(current_field));

        Ok(Val::List(fields))
    }

    /// Computes the Morel expression `String.implode l`.
    ///
    /// Generates the string containing the characters in the list `l`.
    pub(crate) fn implode(chars: &[Val]) -> String {
        chars.iter().map(Val::expect_char).collect()
    }

    /// Computes the Morel expression `String.isPrefix s1 s2`.
    ///
    /// Returns `true` if the string `s1` is a prefix of the string `s2`.
    pub(crate) fn is_prefix(s1: &str, s2: &str) -> bool {
        s2.starts_with(s1)
    }

    /// Computes the Morel expression `String.isSubstring s1 s2`.
    ///
    /// Returns `true` if the string `s1` is a substring of the string `s2`.
    pub(crate) fn is_substring(s1: &str, s2: &str) -> bool {
        s2.contains(s1)
    }

    /// Computes the Morel expression `String.isSuffix s1 s2`.
    ///
    /// Returns `true` if the string `s1` is a suffix of the string `s2`.
    pub(crate) fn is_suffix(s1: &str, s2: &str) -> bool {
        s2.ends_with(s1)
    }

    /// Computes the Morel expression `String.map f s`.
    ///
    /// Applies function `f` to each element of `s` from left to right,
    /// returning the resulting string.
    pub(crate) fn map(
        r: &mut EvalEnv,
        f: &mut Frame,
        func: &Val,
        s: &str,
    ) -> Result<Val, MorelError> {
        let chars: Result<String, _> = s
            .chars()
            .map(|c| {
                let result = func.apply_f1(r, f, &Val::Char(c))?;
                Ok(result.expect_char())
            })
            .collect();
        Ok(Val::String(chars?))
    }

    /// Computes the Morel expression `String.sub`.
    ///
    /// `sub (s, i)` returns the `i`(th) character of `s`, counting from zero.
    /// This raises `Subscript` if `i` &lt; 0 or |`s`| &le; `i`.
    pub(crate) fn sub(
        s: &str,
        index: i32,
        span: &Span,
    ) -> Result<Val, MorelError> {
        let chars: Vec<char> = s.chars().collect();
        if index < 0 || index as usize >= chars.len() {
            Err(MorelError::Runtime(BuiltInExn::Subscript, span.clone()))
        } else {
            Ok(Val::Char(chars[index as usize]))
        }
    }

    /// Computes the Morel expression `String.substring (s, i, j)`.
    ///
    /// Returns the substring of `s` from the `i`-th character for length `j`.
    /// May throw [BuiltInExn::Subscript].
    pub(crate) fn substring(
        s: &str,
        i: i32,
        j: i32,
        span: &Span,
    ) -> Result<Val, MorelError> {
        let chars: Vec<char> = s.chars().collect();
        let start = i as usize;
        let end = (i + j) as usize;

        if i < 0 || j < 0 || end > chars.len() {
            return Err(MorelError::Runtime(
                BuiltInExn::Subscript,
                span.clone(),
            ));
        }

        Ok(Val::String(chars[start..end].iter().collect()))
    }

    /// Computes the Morel expression `String.tokens f s`.
    ///
    /// Returns a list of tokens derived from `s` from left to right. A token
    /// is a non-empty maximal substring of `s` not containing any delimiter.
    /// A delimiter is a character satisfying the predicate `f`. Two tokens may
    /// be separated by more than one delimiter.
    pub(crate) fn tokens(
        r: &mut EvalEnv,
        f: &mut Frame,
        func: &Val,
        s: &str,
    ) -> Result<Val, MorelError> {
        let mut tokens = Vec::new();
        let mut current_token = String::new();

        for c in s.chars() {
            let is_delimiter = func.apply_f1(r, f, &Val::Char(c))?;
            if is_delimiter.expect_bool() {
                // This is a delimiter
                if !current_token.is_empty() {
                    tokens.push(Val::String(current_token.clone()));
                    current_token.clear();
                }
            } else {
                // Not a delimiter, add to current token
                current_token.push(c);
            }
        }

        // Don't forget the last token if it's non-empty
        if !current_token.is_empty() {
            tokens.push(Val::String(current_token));
        }

        Ok(Val::List(tokens))
    }

    /// Computes the Morel expression `String.translate f s`.
    ///
    /// Returns the string generated from `s` by mapping each character in `s`
    /// by `f`. Equivalent to `concat(List.map f (explode s))`.
    pub(crate) fn translate(
        r: &mut EvalEnv,
        f: &mut Frame,
        func: &Val,
        s: &str,
    ) -> Result<Val, MorelError> {
        let mut result = String::new();
        for c in s.chars() {
            let str_val = func.apply_f1(r, f, &Val::Char(c))?;
            result.push_str(&str_val.expect_string());
        }
        Ok(Val::String(result))
    }
}
