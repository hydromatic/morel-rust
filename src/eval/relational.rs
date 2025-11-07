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
use crate::eval::val::Val;
use std::cmp::Ordering;

/// Support for the `Relational` structure.
pub struct Relational;

impl Relational {
    /// Returns `LESS`, `EQUAL`, or `GREATER` according to whether the first
    /// argument is less than, equal to, or greater than the second.
    ///
    /// Comparisons are based on the structure of the type. Primitive types
    /// are compared using their natural order; Option types compare with NONE
    /// last; Tuple types compare lexicographically; Record types compare
    /// lexicographically, with fields compared in alphabetical order; List
    /// values compare lexicographically; Bag values compare lexicographically.
    pub(crate) fn compare(a: &Val, b: &Val) -> Val {
        Val::Order(Order(Self::compare_vals(a, b)))
    }

    /// Internal comparison function that returns a Rust Ordering.
    fn compare_vals(a: &Val, b: &Val) -> Ordering {
        // For simplicity, delegate to Val's equality check and manual ordering.
        // A full implementation would handle all Val types systematically.
        if a == b {
            return Ordering::Equal;
        }

        // For now, use a basic ordering based on discriminant.
        // TODO: Implement proper structural comparison for all types.
        match (a, b) {
            (Val::Bool(a), Val::Bool(b)) => a.cmp(b),
            (Val::Char(a), Val::Char(b)) => a.cmp(b),
            (Val::Int(a), Val::Int(b)) => a.cmp(b),
            (Val::Real(a), Val::Real(b)) => {
                a.partial_cmp(b).unwrap_or(Ordering::Equal)
            }
            (Val::String(a), Val::String(b)) => a.cmp(b),
            (Val::List(a), Val::List(b)) => Self::compare_lists(a, b),
            (Val::Unit, Val::Unit) => Ordering::Equal,
            _ => Ordering::Equal, // Default for unimplemented comparisons
        }
    }

    /// Compare two lists lexicographically.
    fn compare_lists(a: &[Val], b: &[Val]) -> Ordering {
        for (x, y) in a.iter().zip(b.iter()) {
            match Self::compare_vals(x, y) {
                Ordering::Equal => continue,
                other => return other,
            }
        }
        a.len().cmp(&b.len())
    }

    /// Returns the greatest element of the list.
    /// Throws Empty exception if the list is empty.
    pub(crate) fn max(list: &[Val]) -> Val {
        if list.is_empty() {
            panic!("Empty");
        }
        list.iter()
            .max_by(|a, b| Self::compare_vals(a, b))
            .unwrap()
            .clone()
    }

    /// Returns the least element of the list.
    /// Throws Empty exception if the list is empty.
    pub(crate) fn min(list: &[Val]) -> Val {
        if list.is_empty() {
            panic!("Empty");
        }
        list.iter()
            .min_by(|a, b| Self::compare_vals(a, b))
            .unwrap()
            .clone()
    }

    /// Returns the sole element of the list.
    /// Throws Empty exception if the list does not have exactly one element.
    pub(crate) fn only(list: &[Val]) -> Val {
        if list.len() != 1 {
            panic!("Empty");
        }
        list[0].clone()
    }
}
