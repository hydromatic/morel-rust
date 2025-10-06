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

/// Support for the `int` type and `Int` structure.
pub struct Int {}

impl Int {
    pub(crate) fn compare(n1: i32, n2: i32) -> Order {
        Order(n1.cmp(&n2))
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
            format!("~{}", -i)
        } else {
            i.to_string()
        }
    }
}
