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

#![allow(unused_imports)]
use crate::parser::parser::Rule;
use pest::Span;
use pest::error::Error;
use pest::iterators::Pair;
use pest::iterators::Pairs;

/// Trait possessed by all abstract syntax tree (AST) nodes
/// (declarations and expressions).
#[allow(dead_code)]
pub trait Ast {
    /// Returns the string representation of the AST node.
    fn unparse(&self, s: &mut String);

    // Returns the span of the AST node.
    fn span(&self) -> &Span<'_>;
}

/// Tagged union of expressions and declarations.
#[allow(dead_code)]
pub enum Node<'a> {
    Expr(Expr<'a>),
    Decl(Decl<'a>),
}

/// Abstract syntax tree (AST) of a declaration.
#[allow(dead_code)]
pub enum Decl<'a> {
    ValDecl(Span<'a>, ValDecl_<'a>),
}

/// Abstract syntax tree (AST) of an expression.
#[allow(dead_code)]
pub enum Expr<'a> {
    Identifier(Span<'a>, String),
    IntegerLiteral(Span<'a>, String),
    StringLiteral(Span<'a>, String),
}

/// Abstract syntax tree (AST) of a pattern.
#[allow(dead_code)]
pub enum Pat<'a> {
    IdPat(Span<'a>, String),
}

impl Ast for Node<'_> {
    fn unparse(&self, s: &mut String) {
        match self {
            Node::Expr(x) => x.unparse(s),
            Node::Decl(x) => x.unparse(s),
        }
    }

    fn span(&self) -> &Span<'_> {
        match self {
            Node::Expr(x) => x.span(),
            Node::Decl(x) => x.span(),
        }
    }
}

impl Ast for Expr<'_> {
    fn unparse(&self, s: &mut String) {
        match self {
            Expr::Identifier(_, name) => {
                s.push_str(name.as_str());
            }
            Expr::IntegerLiteral(_, value) => {
                s.push_str(value.as_str());
            }
            Expr::StringLiteral(_, value) => {
                // TODO: Handle escapes
                s.push_str(&format!("\"{}\"", value));
            }
        }
    }

    fn span(&self) -> &Span<'_> {
        match self {
            Expr::Identifier(span, _) => span,
            Expr::IntegerLiteral(span, _) => span,
            Expr::StringLiteral(span, _) => span,
        }
    }
}

impl Ast for Decl<'_> {
    fn unparse(&self, s: &mut String) {
        match self {
            Decl::ValDecl(_, val_decl) => {
                s.push_str("val ");
                val_decl.pat.unparse(s);
                s.push_str(" = ");
                val_decl.expr.unparse(s);
            }
        }
    }

    fn span(&self) -> &Span<'_> {
        match self {
            Decl::ValDecl(span, ..) => span,
        }
    }
}

impl Ast for Pat<'_> {
    fn unparse(&self, s: &mut String) {
        match self {
            Pat::IdPat(_, x) => s.push_str(x.as_str()),
        }
    }

    fn span(&self) -> &Span<'_> {
        match self {
            Pat::IdPat(span, _) => span,
        }
    }
}

#[allow(dead_code)]
pub struct ValDecl_<'a> {
    pub pat: Pat<'a>,
    pub expr: Expr<'a>,
}

/// Builds a program (expression or declaration) from parsed pairs.
#[allow(dead_code)]
pub fn build_program(pair: Pair<'_, Rule>) -> Node<'_> {
    match pair.as_rule() {
        Rule::statement => build_statement(sub(pair)),
        _ => todo!("Unexpected rule: {:?}", pair.as_rule()),
    }
}

/// Builds a statement (expression or declaration) from parsed pairs.
#[allow(dead_code)]
pub fn build_statement(pair: Pair<'_, Rule>) -> Node<'_> {
    match pair.as_rule() {
        Rule::decl => Node::Decl(build_decl(sub(pair))),
        Rule::expr => Node::Expr(build_expr(sub(pair))),
        _ => todo!("Unexpected rule: {:?}", pair.as_rule()),
    }
}

/// Builds an expression from parsed pairs.
pub fn build_expr(pair: Pair<'_, Rule>) -> Expr<'_> {
    match pair.as_rule() {
        Rule::literal => build_literal(sub(pair)),
        Rule::identifier => Expr::Identifier(
            pair.as_span(),
            build_identifier(pair.into_inner().next().unwrap()),
        ),
        _ => todo!("Unexpected rule: {:?}", pair.as_rule()),
    }
}

/// Builds a literal from parsed pairs.
pub fn build_literal(pair: Pair<'_, Rule>) -> Expr<'_> {
    match pair.as_rule() {
        Rule::numeric_literal => {
            Expr::IntegerLiteral(pair.as_span(), pair.as_str().to_string())
        }
        Rule::string_literal => {
            Expr::StringLiteral(pair.as_span(), pair.as_str().to_string())
        }
        _ => todo!("Unexpected rule: {:?}", pair.as_rule()),
    }
}

/// Builds a declaration from parsed pairs.
pub fn build_decl(pair: Pair<Rule>) -> Decl {
    match pair.as_rule() {
        Rule::val_decl => {
            let span = pair.as_span();
            let mut pairs = pair.into_inner();
            let pat = build_pat(sub2(&mut pairs, Rule::pat));
            let expr = build_expr(sub2(&mut pairs, Rule::expr));
            Decl::ValDecl(span, ValDecl_ { pat, expr })
        }
        _ => {
            todo!("Unexpected rule: {:?}", pair.as_rule());
        }
    }
}

/// Builds a pattern from parsed pairs.
pub fn build_pat(pair: Pair<'_, Rule>) -> Pat<'_> {
    match pair.as_rule() {
        Rule::identifier => {
            Pat::IdPat(pair.as_span(), pair.as_str().to_string())
        }
        _ => {
            todo!("Unexpected rule: {:?}", pair.as_rule());
        }
    }
}

/// Converts an identifier to a string.
pub fn build_identifier(pair: Pair<Rule>) -> String {
    match pair.as_rule() {
        Rule::quoted_identifier => pair.as_str().to_string(),
        Rule::unquoted_identifier => pair.as_str().to_string(),
        _ => todo!("Unexpected rule: {:?}", pair.as_rule()),
    }
}

/// Asserts that a node has a given rule, then returns its sole child.
pub fn sub(pair: Pair<Rule>) -> Pair<Rule> {
    pair.into_inner().next().unwrap()
}

pub fn sub2<'i>(pairs: &mut Pairs<'i, Rule>, rule: Rule) -> Pair<'i, Rule> {
    let pair = pairs.next().unwrap();
    if pair.as_rule() == rule {
        sub(pair)
    } else {
        panic!("Expected rule {:?}, found {:?}", rule, pair.as_rule());
    }
}
