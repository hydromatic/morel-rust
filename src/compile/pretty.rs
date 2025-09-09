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

use crate::compile::types::Type;
use crate::shell::prop::Output;

/// Prints values prettily.
pub struct Pretty;

impl Pretty {
    pub(crate) fn new(
        _p1: i32,
        _p2: Output,
        _p3: i32,
        _p4: i32,
        _p5: i32,
    ) -> Self {
        todo!()
    }

    pub(crate) fn pretty(&self, _p0: &mut str, _p1: Type, _p2: &()) {
        todo!()
    }
}

/// Wrapper that indicates that a value should be printed with its type.
///
/// For example:
///
/// ```sml
/// val name = value : type
/// ```
pub struct TypedVal;

impl TypedVal {
    pub(crate) fn new(_p0: String, _p1: &Option<TypedVal>, _p2: Type) -> Self {
        todo!()
    }
}
