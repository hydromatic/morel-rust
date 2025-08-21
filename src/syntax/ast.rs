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

use std::rc::Rc;

/// A location in the source text.
#[derive(Debug, Clone)]
pub struct Span {
    input: Rc<str>,
    /// # Safety
    ///
    /// Must be a valid character boundary index into `input`.
    start: usize,
    /// # Safety
    ///
    /// Must be a valid character boundary index into `input`.
    end: usize,
}

impl Span {
    /// Creates the 'null' scan for a source document.
    pub fn zero(input: Rc<str>) -> Span {
        Span {
            input,
            start: 0,
            end: 0,
        }
    }

    /// Merges another span into this.
    pub fn merge(&mut self, other: &Span) {
        if self.input != other.input {
            panic!("Cannot merge spans from different inputs");
        }
        self.start = self.start.min(other.start);
        self.end = self.end.max(other.end);
    }
}

/// Trait possessed by all abstract syntax tree (AST) nodes
pub trait MorelNode {
    /// Returns the string representation of the AST node.
    fn unparse(&self, s: &mut String);
}

/// Abstract syntax tree (AST) of a statement (expression or declaration).
pub struct Statement {
    pub kind: StatementKind,
    pub span: Span,
}

impl MorelNode for Statement {
    fn unparse(&self, s: &mut String) {
        match &self.kind {
            StatementKind::Expr(x) => x.unparse(s),
        }
    }
}

/// Kind of statement.
#[derive(Debug, Clone)]
pub enum StatementKind {
    Expr(ExprKind<Expr>),
}

/// Abstract syntax tree (AST) of an expression.
#[derive(Debug, Clone)]
pub struct Expr {
    pub kind: ExprKind<Expr>,
    pub span: Span,
}

/// Kind of expression.
#[derive(Debug, Clone)]
pub enum ExprKind<SubExpr> {
    Current,
    Ordinal,
    Negate(Box<SubExpr>),
}

impl<SubExpr> ExprKind<SubExpr> {
    pub(crate) fn unparse(&self, s: &mut String) {}
}
