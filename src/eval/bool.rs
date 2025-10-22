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

/// Support for the `bool` primitive type and the `Bool` structure.
pub struct Bool;

impl Bool {
    // lint: sort until '#}' where '##pub'

    /// Computes the Morel expression `Bool.implies (b1, b2)`.
    ///
    /// Returns `true` if `b1` is `false` or `b2` is `true`.
    pub(crate) fn implies(b1: bool, b2: bool) -> bool {
        !b1 || b2
    }

    /// Computes the Morel expression `Bool.not b`.
    ///
    /// Returns the logical negation of the boolean value `b`.
    pub(crate) fn not(b: bool) -> bool {
        !b
    }

    /// Computes the Morel expression `Bool.toString b`.
    ///
    /// Returns the string representation of `b`, either "true" or "false".
    #[allow(clippy::wrong_self_convention)]
    pub(crate) fn to_string(b: bool) -> String {
        if b { "true" } else { "false" }.to_string()
    }
}
