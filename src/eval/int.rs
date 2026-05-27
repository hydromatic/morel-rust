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

use crate::eval::order::Order;
use crate::eval::val::{RADIX_BIN, RADIX_DEC, RADIX_HEX, RADIX_OCT, Val};

/// Support for the `int` type and `Int` structure.
pub struct Int {}

impl Int {
    pub(crate) fn compare(n1: i32, n2: i32) -> Order {
        Order(n1.cmp(&n2))
    }

    /// Computes the Morel expression `Int.fmt radix i`. The radix
    /// argument is the runtime representation of a `StringCvt.radix`
    /// constructor (`BIN | OCT | DEC | HEX`). Negatives are prefixed
    /// with `~`; hex digits above 9 use upper-case `A..F`.
    pub(crate) fn fmt(radix: &Val, i: i32) -> String {
        let base = radix_base(radix);
        let abs = (i as i64).unsigned_abs();
        let mut digits = format_radix(abs, base);
        if base == 16 {
            digits = digits.to_uppercase();
        }
        if i < 0 {
            format!("~{}", digits)
        } else {
            digits
        }
    }

    /// Performs Standard ML's `div` operation.
    ///
    /// SML division truncates towards
    /// negative infinity (floor division).
    pub(crate) fn div(a: i32, b: i32) -> i32 {
        if (a >= 0) == (b >= 0) {
            a / b
        } else {
            (a / b) - if a % b != 0 { 1 } else { 0 }
        }
    }

    pub(crate) fn from_string(s: &str) -> Option<i32> {
        let s_converted = s.replace('~', "-");
        s_converted.parse::<i32>().ok()
    }

    /// Performs Standard ML's `mod` operation.
    ///
    /// SML modulo: `(a div b) * b + (a mod b) = a`
    /// and (`a mod b`) has the same sign as `b` (or is zero).
    pub(crate) fn _mod(a: i32, b: i32) -> i32 {
        let r = a % b;
        if r != 0 && (a >= 0) != (b >= 0) {
            r + b
        } else {
            r
        }
    }

    pub(crate) fn sign(n: i32) -> i32 {
        if n > 0 {
            1
        } else if n < 0 {
            -1
        } else {
            0
        }
    }

    pub(crate) fn _to_string(i: i32) -> String {
        if i < 0 {
            format!("~{}", (i as i64).unsigned_abs())
        } else {
            i.to_string()
        }
    }
}

/// Returns the numeric base for a `StringCvt.radix` constructor value.
fn radix_base(radix: &Val) -> u32 {
    match radix {
        Val::Constructor(RADIX_BIN, _) => 2,
        Val::Constructor(RADIX_OCT, _) => 8,
        Val::Constructor(RADIX_DEC, _) => 10,
        Val::Constructor(RADIX_HEX, _) => 16,
        other => panic!("expected radix constructor, got {:?}", other),
    }
}

fn format_radix(mut n: u64, base: u32) -> String {
    if n == 0 {
        return "0".to_string();
    }
    let mut digits = Vec::new();
    while n > 0 {
        let d = (n % base as u64) as u8;
        digits.push(if d < 10 { b'0' + d } else { b'a' + (d - 10) });
        n /= base as u64;
    }
    digits.reverse();
    String::from_utf8(digits).unwrap()
}
