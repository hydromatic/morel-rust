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

/// Error types for shell operations
#[derive(Debug)]
pub enum Error {
    IoError(std::io::Error),
    ParseError(String),
    CompileError(String),
    RuntimeError(String),
    FileNotFound(String),
}

impl From<std::io::Error> for Error {
    fn from(err: std::io::Error) -> Self {
        Error::IoError(err)
    }
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Error::IoError(e) => write!(f, "IO Error: {}", e),
            Error::ParseError(e) => write!(f, "Parse Error: {}", e),
            Error::CompileError(e) => write!(f, "Compile Error: {}", e),
            Error::RuntimeError(e) => write!(f, "Runtime Error: {}", e),
            Error::FileNotFound(e) => write!(f, "File not found: {}", e),
        }
    }
}

impl std::error::Error for Error {}