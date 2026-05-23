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

//! Error type for the Datalog frontend. Counterpart to morel-java's
//! `DatalogException`.

use std::error::Error;
use std::fmt::{self, Display, Formatter};

/// Anything that can go wrong when parsing, analyzing, translating, or
/// evaluating a Datalog program.
#[derive(Clone, Eq, PartialEq, Debug)]
pub enum DatalogError {
    Parse(String),
    Analysis(String),
}

impl DatalogError {
    pub fn parse(msg: impl Into<String>) -> Self {
        DatalogError::Parse(msg.into())
    }
}

impl Display for DatalogError {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            DatalogError::Parse(s) => write!(f, "Parse error: {}", s),
            DatalogError::Analysis(s) => write!(f, "Analysis error: {}", s),
        }
    }
}

impl Error for DatalogError {}
