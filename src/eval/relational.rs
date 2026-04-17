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

use crate::eval::comparator::{Comparator, NaturalComparator};
use crate::eval::order::Order;
use crate::eval::val::Val;

/// Support for the `Relational` structure.
pub struct Relational;

impl Relational {
    /// Fallback comparison using `NaturalComparator`. Prefer
    /// type-directed `Code::Compare` when the type is known at
    /// compile time.
    pub(crate) fn compare(a: &Val, b: &Val) -> Val {
        Val::Order(Order(NaturalComparator.compare(a, b)))
    }

    /// Fallback max using `NaturalComparator`.
    pub(crate) fn max(list: &[Val]) -> Val {
        use crate::eval::comparator::NaturalComparator;
        if list.is_empty() {
            panic!("Empty");
        }
        list.iter()
            .max_by(|a, b| NaturalComparator.compare(a, b))
            .unwrap()
            .clone()
    }

    /// Fallback min using `NaturalComparator`.
    pub(crate) fn min(list: &[Val]) -> Val {
        use crate::eval::comparator::NaturalComparator;
        if list.is_empty() {
            panic!("Empty");
        }
        list.iter()
            .min_by(|a, b| NaturalComparator.compare(a, b))
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
