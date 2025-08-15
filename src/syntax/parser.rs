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

use crate::syntax::ast::{ExprKind, Span, Statement, StatementKind};
use std::fmt::Error;
use std::rc::Rc;

pub type ParseResult<T> = Result<T, Error>;

/// Parses a Morel statement and returns its AST.
///
/// The statement may be preceded by whitespace and/or comments;
/// the statement must end with a semicolon.
pub fn parse_statement(input: &str) -> ParseResult<Statement> {
    let rc_input_str: Rc<str> = input.to_string().into();
    Ok(Statement {
        kind: StatementKind::Expr(ExprKind::Ordinal),
        span: Span::zero(rc_input_str.clone()),
    })
}
