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

use std::cmp::Ordering;

/// Support for Morel's `order` enum type.
///
/// The representation is the same as Rust's built-in [Ordering] type.
#[derive(Debug, Clone, PartialEq)]
pub struct Order(pub Ordering);

impl Order {
    pub(crate) fn from_i32(i: i32) -> Self {
        Order(i8_to_ordering(i as i8))
    }

    pub(crate) const LESS: u8 = Ordering::Less as u8;
    pub(crate) const EQUAL: u8 = Ordering::Equal as u8;
    pub(crate) const GREATER: u8 = Ordering::Greater as u8;

    pub fn name(&self) -> &'static str {
        match self.0 {
            Ordering::Less => "LESS",
            Ordering::Equal => "EQUAL",
            Ordering::Greater => "GREATER",
        }
    }
}

fn i8_to_ordering(value: i8) -> Ordering {
    match value {
        -1 => Ordering::Less,
        0 => Ordering::Equal,
        1 => Ordering::Greater,
        _ => panic!("Invalid i8 value for Ordering conversion"),
    }
}
