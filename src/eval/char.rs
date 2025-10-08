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

use crate::compile::library::BuiltInExn;
use crate::eval::code::Span;
use crate::eval::val::Val;
use crate::shell::main::MorelError;

/// Support for the `char` primitive type and the `Char` structure.
pub struct Char;

impl Char {
    /// Implements Morel `Char.chr i`. May throw [BuiltInExn::Chr].
    pub(crate) fn chr(i: i32, span: &Span) -> Result<Val, MorelError> {
        if !(0..=255).contains(&i) {
            Err(MorelError::Runtime(BuiltInExn::Chr, span.clone()))
        } else {
            Ok(Val::Char(i as u8 as char))
        }
    }
}
