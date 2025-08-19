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

use crate::syntax::parser::Rule;
use pest::iterators::Pair;
use std::fmt::Write;
use std::rc::Rc;

/// A location in the source text
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
    pub(crate) fn make(input: Rc<str>, sp: pest::Span) -> Self {
        Span {
            input,
            start: sp.start(),
            end: sp.end(),
        }
    }
    /// Takes the union of the two spans. Assumes that the spans come from the same input.
    /// This will also capture any input between the spans.
    pub fn union(&self, other: &Span) -> Self {
        use std::cmp::{max, min};
        Span {
            input: self.input.clone(),
            start: min(self.start, other.start),
            end: max(self.start, other.start),
        }
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

impl Statement {
    /// Creates a statement with the given kind and span.
    pub fn of(span: Span, kind: StatementKind) -> Self {
        Statement { kind, span }
    }
}

impl MorelNode for Statement {
    fn unparse(&self, s: &mut String) {
        match &self.kind {
            StatementKind::Expr(x) => x.unparse(s),
            StatementKind::Decl(x) => x.unparse(s),
        }
    }
}

/// Kind of statement.
#[derive(Debug, Clone)]
pub enum StatementKind {
    Expr(ExprKind<Expr>),
    Decl(DeclKind),
}

/// Abstract syntax tree (AST) of an expression.
#[derive(Debug, Clone)]
pub struct Expr {
    kind: Box<ExprKind<Expr>>,
    span: Span,
}

pub type UnspannedExpr = ExprKind<Expr>;

impl Expr {
    /// Creates an expression with the given kind and span.
    pub fn of(span: Span, kind: ExprKind<Expr>) -> Self {
        Expr {
            kind: Box::new(kind),
            span,
        }
    }
}

/// Kind of expression.
#[derive(Debug, Clone)]
pub enum ExprKind<SubExpr> {
    // Literals
    IntLiteral(String),
    RealLiteral(String),
    StringLiteral(String),
    CharLiteral(String),
    BoolLiteral(bool),
    UnitLiteral,

    // Identifiers and selectors
    Identifier(String),
    RecordSelector(String),
    Current,
    Ordinal,

    // Binary operations
    Plus(Box<Expr>, Box<SubExpr>),
    Minus(Box<SubExpr>, Box<SubExpr>),
    Times(Box<SubExpr>, Box<SubExpr>),
    Divide(Box<SubExpr>, Box<SubExpr>),
    Div(Box<SubExpr>, Box<SubExpr>),
    Mod(Box<SubExpr>, Box<SubExpr>),
    Caret(Box<SubExpr>, Box<SubExpr>),

    // Comparison operations
    Equal(Box<SubExpr>, Box<SubExpr>),
    NotEqual(Box<SubExpr>, Box<SubExpr>),
    LessThan(Box<SubExpr>, Box<SubExpr>),
    LessThanOrEqual(Box<SubExpr>, Box<SubExpr>),
    GreaterThan(Box<SubExpr>, Box<SubExpr>),
    GreaterThanOrEqual(Box<SubExpr>, Box<SubExpr>),

    // List operations
    Cons(Box<SubExpr>, Box<SubExpr>),
    Append(Box<SubExpr>, Box<SubExpr>),

    // Logical operations
    AndAlso(Box<SubExpr>, Box<SubExpr>),
    OrElse(Box<SubExpr>, Box<SubExpr>),
    Implies(Box<SubExpr>, Box<SubExpr>),

    // Relational operations
    Elem(Box<SubExpr>, Box<SubExpr>),
    NotElem(Box<SubExpr>, Box<SubExpr>),

    // Unary operations
    Negate(Box<SubExpr>, Box<SubExpr>),

    // Function operations
    Apply(Box<SubExpr>, Box<SubExpr>),
    O(Box<SubExpr>, Box<SubExpr>), // function composition

    // Aggregate operations
    Aggregate(Box<SubExpr>, Box<SubExpr>), // expr over expr

    // Control structures
    If(Box<SubExpr>, Box<SubExpr>, Box<SubExpr>),
    Case(Box<SubExpr>, Vec<CaseArm>),
    Let(Vec<DeclKind>, Box<SubExpr>),
    Fn(Vec<FunMatch>),

    // Data structures
    Tuple(Vec<Expr>),
    List(Vec<Expr>),
    Record(Vec<NamedExpr>),

    // Relational expressions
    From(Box<FromExpr>),

    // Type annotation
    Annotated(Box<SubExpr>, Type),
}

impl ExprKind<Expr> {
    pub fn spanned(self, span: Span) -> Expr {
        Expr { kind: Box::new(self), span }
    }
}

impl ExprKind<Expr> {
    pub fn to_statement(&self, span: Span) -> Statement {
        Statement::of(span, StatementKind::Expr(self.clone()))
    }
}

/// Named expression for records and relational operations
#[derive(Debug, Clone)]
pub struct NamedExpr {
    pub name: Option<String>,
    pub expr: Expr,
}

/// Arm of a case expression
#[derive(Debug, Clone)]
pub struct CaseArm {
    pub pat: Pat,
    pub expr: Expr,
}

/// Function match in a fn expression
#[derive(Debug, Clone)]
pub struct FunMatch {
    pub pat: Pat,
    pub expr: Expr,
}

/// From expression structure
#[derive(Debug, Clone)]
pub struct FromExpr {
    pub from_items: Vec<FromItem>,
    pub where_clause: Option<Box<Expr>>,
    pub group_clause: Option<Vec<NamedExpr>>,
    pub compute_clause: Option<Vec<NamedExpr>>,
    pub order_clause: Option<Vec<Expr>>,
    pub yield_clause: Option<Box<Expr>>,
}

/// From item (pattern in expression)
#[derive(Debug, Clone)]
pub struct FromItem {
    pub pat: Pat,
    pub expr: Expr,
}

/// Abstract syntax tree (AST) of a pattern.
#[derive(Debug, Clone)]
pub enum Pat {
    Wildcard,
    Identifier(String),
    IntLiteral(String),
    RealLiteral(String),
    StringLiteral(String),
    CharLiteral(String),
    BoolLiteral(bool),
    Tuple(Vec<Pat>),
    List(Vec<Pat>),
    Record(Vec<PatField>),
    Cons(Box<Pat>, Box<Pat>),
    Constructor(String, Option<Box<Pat>>),
    As(Box<Pat>, String),
    Annotated(Box<Pat>, Type),
}

/// Pattern field in record patterns
#[derive(Debug, Clone)]
pub struct PatField {
    pub name: String,
    pub pat: Option<Pat>,
}

/// Abstract syntax tree (AST) of a declaration.
#[derive(Debug, Clone)]
pub struct Decl {
    kind: Box<DeclKind>,
    span: Span,
}

impl Decl {
    /// Creates an expression with the given kind and span.
    pub fn of(span: Span, kind: DeclKind) -> Self {
        Decl { kind: Box::new(kind), span }
    }
}

/// Kind of declaration.
#[derive(Debug, Clone)]
pub enum DeclKind {
    Val(Vec<ValBind>),
    Fun(Vec<FunBind>),
    Type(Vec<TypeBind>),
    Datatype(Vec<DatatypeBind>),
}

impl DeclKind {
    pub fn spanned(self, span: Span) -> Decl {
        Decl { kind: Box::new(self), span }
    }

    pub fn to_statement(&self, span: Span) -> Statement {
        Statement::of(span, StatementKind::Decl(self.clone()))
    }
}

/// Value binding
#[derive(Debug, Clone)]
pub struct ValBind {
    pub rec: bool,
    pub pat: Pat,
    pub type_annotation: Option<Type>,
    pub expr: Expr,
}

/// Function binding
#[derive(Debug, Clone)]
pub struct FunBind {
    pub name: String,
    pub matches: Vec<FunMatch>,
}

/// Type binding
#[derive(Debug, Clone)]
pub struct TypeBind {
    pub type_vars: Vec<String>,
    pub name: String,
    pub type_expr: Type,
}

/// Datatype binding
#[derive(Debug, Clone)]
pub struct DatatypeBind {
    pub type_vars: Vec<String>,
    pub name: String,
    pub constructors: Vec<ConBind>,
}

/// Constructor binding
#[derive(Debug, Clone)]
pub struct ConBind {
    pub name: String,
    pub type_expr: Option<Type>,
}

/// Abstract syntax tree (AST) of a type.
#[derive(Debug, Clone)]
pub enum Type {
    Var(String),
    Con(String),
    Fn(Box<Type>, Box<Type>),
    Tuple(Vec<Type>),
    Record(Vec<TypeField>),
    App(Box<Type>, Vec<Type>),
}

/// Type field in record types
#[derive(Debug, Clone)]
pub struct TypeField {
    pub name: String,
    pub type_expr: Type,
}

impl MorelNode for ExprKind<Expr> {
    fn unparse(&self, s: &mut String) {
        match self {
            ExprKind::Identifier(name) => s.push_str(name),
            ExprKind::IntLiteral(value) => s.push_str(value),
            ExprKind::RealLiteral(value) => s.push_str(value),
            ExprKind::StringLiteral(value) => {
                write!(s, "\"{}\"", value).unwrap()
            }
            ExprKind::CharLiteral(value) => {
                write!(s, "#\"{}\"", value).unwrap()
            }
            ExprKind::BoolLiteral(value) => {
                s.push_str(if *value { "true" } else { "false" })
            }
            ExprKind::UnitLiteral => s.push_str("()"),
            _ => s.push_str("<expr>"), // TODO: implement for all variants
        }
    }
}

impl MorelNode for DeclKind {
    fn unparse(&self, s: &mut String) {
        match self {
            DeclKind::Val(binds) => {
                s.push_str("val ");
                if let Some(first_bind) = binds.first() {
                    if first_bind.rec {
                        s.push_str("rec ");
                    }
                    first_bind.pat.unparse(s);
                    if let Some(ref type_annotation) =
                        first_bind.type_annotation
                    {
                        s.push_str(": ");
                        match type_annotation {
                            Type::Con(name) => s.push_str(name),
                            _ => s.push_str("<type>"),
                        }
                    }
                    s.push_str(" = ");
                    first_bind.expr.kind.unparse(s);
                }
            }
            _ => s.push_str("<decl>"),
        }
    }
}

impl MorelNode for Pat {
    fn unparse(&self, s: &mut String) {
        match self {
            Pat::Identifier(name) => s.push_str(name),
            Pat::Wildcard => s.push('_'),
            _ => s.push_str("<pat>"),
        }
    }
}

/// Builds a statement (expression or declaration) from parsed pairs.
pub fn build_statement(pair: Pair<Rule>) -> StatementKind {
    let inner = pair.into_inner().next().unwrap();
    match inner.as_rule() {
        // Rule::expr => StatementKind::Expr(build_expr(inner)),
        // Rule::decl => StatementKind::Decl(build_decl(inner)),
        _ => panic!("Unexpected rule in statement: {:?}", inner.as_rule()),
    }
}

/// Builds an expression from parsed pairs.
pub fn build_expr(pair: Pair<Rule>) -> Expr {
    match pair.as_rule() {
        // Rule::expr => {
        //     let inner = pair.into_inner().next().unwrap();
        //     build_expr(inner)
        // }
        // Rule::expr_annotated => {
        //     let inner = pair.into_inner().next().unwrap();
        //     build_expr(inner)
        // }
        // Rule::expr_implies => {
        //     let inner = pair.into_inner().next().unwrap();
        //     build_expr(inner)
        // }
        // Rule::expr_orelse => {
        //     let inner = pair.into_inner().next().unwrap();
        //     build_expr(inner)
        // }
        // Rule::expr_andalso => {
        //     let inner = pair.into_inner().next().unwrap();
        //     build_expr(inner)
        // }
        // Rule::expr_o => {
        //     let inner = pair.into_inner().next().unwrap();
        //     build_expr(inner)
        // }
        // Rule::expr_relational => {
        //     let inner = pair.into_inner().next().unwrap();
        //     build_expr(inner)
        // }
        // Rule::expr_cons => {
        //     let inner = pair.into_inner().next().unwrap();
        //     build_expr(inner)
        // }
        // Rule::expr_additive => {
        //     let inner = pair.into_inner().next().unwrap();
        //     build_expr(inner)
        // }
        // Rule::expr_multiplicative => {
        //     let inner = pair.into_inner().next().unwrap();
        //     build_expr(inner)
        // }
        // Rule::expr_over => {
        //     let inner = pair.into_inner().next().unwrap();
        //     build_expr(inner)
        // }
        // Rule::expr_unary => {
        //     let inner = pair.into_inner().next().unwrap();
        //     build_expr(inner)
        // }
        // Rule::expr_application => {
        //     let inner = pair.into_inner().next().unwrap();
        //     build_expr(inner)
        // }
        // Rule::expr_postfix => {
        //     let inner = pair.into_inner().next().unwrap();
        //     build_expr(inner)
        // }
        // Rule::atom => {
        //     let inner = pair.into_inner().next().unwrap();
        //     build_expr(inner)
        // }
        // Rule::literal => build_literal(pair),
        // Rule::identifier => {
        //     let span = Span::make(&pair.as_span());
        //     Expr::of(span, ExprKind::Identifier(pair.as_str().to_string()))
        // }
        _ => {
            todo!()
            // ExprKind::Identifier(
            //     span,
            //     format!("<unknown_expr:{:?}>", pair.as_rule()),
            // )
        }
    }
}

/// Builds a literal from parsed pairs.
pub fn build_literal(pair: Pair<Rule>) -> Expr {
    match pair.as_rule() {
        // Rule::literal => {
        //     let inner = pair.into_inner().next().unwrap();
        //     build_literal(inner)
        // }
        // Rule::numeric_literal => {
        //     let inner = pair.into_inner().next().unwrap();
        //     build_literal(inner)
        // }
        // Rule::non_negative_integer_literal | Rule::negative_integer_literal => {
        //     let span = Span::from_span(&pair.as_span());
        //     Expr::of(span, ExprKind::IntLiteral(pair.as_str().to_string()))
        // }
        // Rule::real_literal | Rule::scientific_literal => {
        //     let span = Span::from_span(&pair.as_span());
        //     Expr::of(span, ExprKind::RealLiteral(pair.as_str().to_string()))
        // }
        // Rule::string_literal => {
        //     let span = Span::from_span(&pair.as_span());
        //     let content = pair.as_str();
        //     let unquoted = &content[1..content.len() - 1];
        //     Expr::of(span, ExprKind::StringLiteral(unquoted.to_string()))
        // }
        // Rule::char_literal => {
        //     let span = Span::from_span(&pair.as_span());
        //     let content = pair.as_str();
            // // Remove #" and "
            // let unquoted = &content[2..content.len() - 1];
            // Expr::of(span, ExprKind::CharLiteral(unquoted.to_string()))
        // }
        // Rule::bool_literal => {
        //     let span = Span::from_span(&pair.as_span());
        //     let value = pair.as_str() == "true";
        //     Expr::of(span, ExprKind::BoolLiteral(value))
        // }
        // Rule::unit_literal => {
        //     let span = Span::from_span(&pair.as_span());
        //     Expr::of(span, ExprKind::UnitLiteral)
        // }
        _ => {
            todo!()
        }
    }
}

/// Builds a declaration from parsed pairs.
pub fn build_decl(pair: Pair<Rule>) -> Decl {
    let inner = pair.into_inner().next().unwrap();
    match inner.as_rule() {
        // Rule::val_decl => {
            // let span = Span::from_span(&pair.as_span());
            // Decl::of(span, build_val_decl(inner))
        // },
        _ => panic!("Unexpected declaration rule: {:?}", inner.as_rule()),
    }
}

/// Builds a value declaration from parsed pairs.
pub fn build_val_decl(pair: Pair<Rule>) -> DeclKind {
    let mut inner = pair.into_inner();

    // The grammar should produce: "val" pat [":" type_expr] ["=" expr]
    // We need to process all the inner parts
    let mut has_rec = false;
    let mut pat = None;
    let mut type_annotation = None;
    let mut expr = None;

    while let Some(part) = inner.next() {
        match part.as_rule() {
            Rule::val_bind => {
                // Process the val_bind rule
                let mut val_inner = part.into_inner();
                while let Some(val_part) = val_inner.next() {
                    match val_part.as_rule() {
                        Rule::pat => pat = Some(build_pat(val_part)),
                        Rule::type_expr => {
                            type_annotation = Some(build_type(val_part))
                        }
                        Rule::expr => expr = Some(build_expr(val_part)),
                        _ if val_part.as_str() == "rec" => has_rec = true,
                        _ => {} // Skip other tokens like "=" and ":"
                    }
                }
            }
            Rule::pat => pat = Some(build_pat(part)),
            Rule::type_expr => type_annotation = Some(build_type(part)),
            Rule::expr => expr = Some(build_expr(part)),
            _ if part.as_str() == "rec" => has_rec = true,
            _ => {} // Skip tokens like "val", "=", ":"
        }
    }

    let val_bind = ValBind {
        rec: has_rec,
        pat: pat.unwrap_or_else(|| todo!()),
        type_annotation,
        expr: expr.unwrap_or_else(|| todo!()),
    };

    DeclKind::Val(vec![val_bind])
}

/// Builds a pattern from parsed pairs.
pub fn build_pat(pair: Pair<Rule>) -> Pat {
    match pair.as_rule() {
        Rule::pat => {
            // Recursively handle pattern rules
            let inner = pair.into_inner().next().unwrap();
            build_pat(inner)
        }
        Rule::pat_annotated => {
            let inner = pair.into_inner().next().unwrap();
            build_pat(inner)
        }
        Rule::pat_as => {
            let inner = pair.into_inner().next().unwrap();
            build_pat(inner)
        }
        Rule::pat_cons => {
            let inner = pair.into_inner().next().unwrap();
            build_pat(inner)
        }
        Rule::pat_atom => {
            let inner = pair.into_inner().next().unwrap();
            build_pat(inner)
        }
        Rule::id_pat => {
            let inner = pair.into_inner().next().unwrap();
            build_pat(inner)
        }
        Rule::identifier => {
            Pat::Identifier(pair.as_str().to_string())
        }
        _ => {
            Pat::Identifier(format!("<unknown_pat:{:?}>", pair.as_rule()))
        }
    }
}

/// Builds a type from parsed pairs.
pub fn build_type(pair: Pair<Rule>) -> Type {
    Type::Con(pair.as_str().to_string())
}
