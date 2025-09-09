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

use std::fmt::{Display, Formatter};

/// Runtime value.
#[derive(Debug, Clone, PartialEq)]
pub enum Val {
    Unit,
    Bool(bool),
    Char(char),
    Int(i32),
    Real(f32),
    String(String),
    List(Vec<Val>),
}

// REVIEW Should we use `Into` or `From` traits?
impl Val {
    pub(crate) fn as_bool(&self) -> bool {
        match &self {
            Val::Bool(b) => *b,
            _ => panic!("Not a bool"),
        }
    }

    pub(crate) fn as_int(&self) -> i32 {
        match &self {
            Val::Int(i) => *i,
            _ => panic!("Not an int"),
        }
    }

    pub(crate) fn as_string(&self) -> String {
        match &self {
            Val::String(s) => s.clone(),
            _ => panic!("Not an string"),
        }
    }
}

impl Display for Val {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match &self {
            Val::Unit => write!(f, "()"),
            Val::Bool(b) => write!(f, "{}", b),
            Val::Char(c) => write!(f, "{}", c),
            Val::Int(i) => write!(f, "{}", i),
            Val::Real(r) => write!(f, "{}", r),
            Val::String(s) => write!(f, "\"{}\"", s),
            Val::List(l) => {
                let mut first = true;
                write!(f, "[")?;
                for v in l {
                    if first {
                        first = false;
                    } else {
                        write!(f, ", ")?;
                    }
                    v.fmt(f)?;
                }
                write!(f, "]")
            }
        }
    }
}
