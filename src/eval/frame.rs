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

use crate::compile::type_env::Binding;
use std::fmt::Write;

/// Definition of a frame.
///
/// It is mainly used at compile time, but we include it in code
/// (e.g. [crate::eval::code::Code::BindSlot],
/// [crate::eval::code::Code::GetLocal],
/// [crate::eval::code::Code::Fn],
/// [crate::eval::code::Code::CreateClosure])
/// because it aids debugging.
#[derive(Clone, PartialEq, Debug)]
pub struct FrameDef {
    pub bound_vars: Vec<Binding>,
    pub local_vars: Vec<Binding>,
    pub description: String,
}

impl FrameDef {
    /// Creates a frame definition.
    pub fn new(bound_vars: &[Binding], local_vars: &[Binding]) -> Self {
        FrameDef {
            bound_vars: bound_vars.to_vec(),
            local_vars: local_vars.to_vec(),
            description: Self::generate_description(bound_vars, local_vars),
        }
    }

    /// Generates a description like 'x,y;a,b' where x, y are variables bound
    /// by the closure and a, b are variables defined locally.
    fn generate_description(
        bound_vars: &[Binding],
        local_vars: &[Binding],
    ) -> String {
        let mut s = String::new();
        let mut sep = "";
        bound_vars.iter().for_each(|binding| {
            write!(s, "{}{}", sep, binding.id.name).unwrap();
            sep = ",";
        });
        s.push(';');
        sep = "";
        local_vars.iter().for_each(|binding| {
            write!(s, "{}{}", sep, binding.id.name).unwrap();
            sep = ",";
        });
        s
    }

    /// Returns the index within the current frame of a variable with a given
    /// name. Panics if not found.
    pub(crate) fn var_index(&self, name: &str) -> usize {
        if let Some(i) = self.bound_vars.iter().position(|v| v.id.name == name)
        {
            i
        } else if let Some(i) =
            self.local_vars.iter().position(|v| v.id.name == name)
        {
            self.bound_vars.len() + i
        } else {
            panic!("variable {} not found in frame {:?}", name, self)
        }
    }
}
