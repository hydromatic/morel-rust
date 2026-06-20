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

//! Runtime implementation of the `Word` structure: Standard ML's
//! unsigned 64-bit `word` type. Values are stored as [`u64`]; arithmetic
//! and comparison use unsigned (wrapping) semantics.

use crate::eval::int::{format_radix, radix_base};
use crate::eval::val::Val;
use std::sync::LazyLock;

/// Standard ML's `word` is 64 bits wide in Morel.
pub(crate) const WORD_SIZE: i32 = 64;

/// `Word.fmt radix w`: formats `w` in the given radix, with no `0wx`
/// prefix. Hexadecimal digits are upper-case.
pub(crate) fn fmt(radix: &Val, w: u64) -> String {
    let base = radix_base(radix);
    let digits = format_radix(w, base);
    if base == 16 {
        digits.to_uppercase()
    } else {
        digits
    }
}

/// `Word.toString w`: equivalent to `Word.fmt HEX w` (upper-case hex,
/// no prefix).
pub(crate) fn to_string(w: u64) -> String {
    format_radix(w, 16).to_uppercase()
}

/// `Word.fromString s`: parses an optional leading-whitespace, optional
/// `0x`/`0X`/`0wx`/`0wX` prefix, then one or more hexadecimal digits.
/// Returns `None` if no hexadecimal digits are found.
pub(crate) fn from_string(s: &str) -> Option<u64> {
    static RE: LazyLock<regex::Regex> = LazyLock::new(|| {
        regex::Regex::new(r"^\s*(?:0[wW]?[xX])?([0-9a-fA-F]+)").unwrap()
    });
    let caps = RE.captures(s)?;
    u64::from_str_radix(&caps[1], 16).ok()
}

/// `Word.<<` (logical shift left): shifts of 64 or more yield 0.
pub(crate) fn shift_left(w: u64, n: u64) -> u64 {
    if n >= 64 { 0 } else { w << n }
}

/// `Word.>>` (logical shift right): shifts of 64 or more yield 0.
pub(crate) fn shift_right(w: u64, n: u64) -> u64 {
    if n >= 64 { 0 } else { w >> n }
}

/// `Word.~>>` (arithmetic shift right): sign-replicating. The shift
/// amount is taken modulo 64, matching Java's `long >> n`.
pub(crate) fn arith_shift_right(w: u64, n: u64) -> u64 {
    ((w as i64) >> (n & 63)) as u64
}
