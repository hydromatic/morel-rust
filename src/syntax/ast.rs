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

use crate::syntax::ast;
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

impl MorelNode for StatementKind {
    fn unparse(&self, s: &mut String) {
        match self {
            StatementKind::Expr(e) => e.unparse(s),
            StatementKind::Decl(d) => d.unparse(s),
        }
    }
}

/// Abstract syntax tree (AST) of an expression.
#[derive(Debug, Clone)]
pub struct Expr {
    pub kind: ExprKind<Expr>,
    pub span: Span,
}

pub type UnspannedExpr = ExprKind<Expr>;

/// Kind of expression.
#[derive(Debug, Clone)]
pub enum ExprKind<SubExpr> {
    Literal(Literal),
    Identifier(String),
    RecordSelector(String),
    Current,
    Ordinal,

    // Infix binary operators
    Plus(Box<Expr>, Box<SubExpr>),
    Minus(Box<SubExpr>, Box<SubExpr>),
    Times(Box<SubExpr>, Box<SubExpr>),
    Divide(Box<SubExpr>, Box<SubExpr>),
    Div(Box<SubExpr>, Box<SubExpr>),
    Mod(Box<SubExpr>, Box<SubExpr>),
    Caret(Box<SubExpr>, Box<SubExpr>),
    Compose(Box<SubExpr>, Box<SubExpr>),
    Equal(Box<SubExpr>, Box<SubExpr>),    // '='
    NotEqual(Box<SubExpr>, Box<SubExpr>), // '<>'
    LessThan(Box<SubExpr>, Box<SubExpr>), // '<'
    LessThanOrEqual(Box<SubExpr>, Box<SubExpr>), // '<='
    GreaterThan(Box<SubExpr>, Box<SubExpr>), // '>'
    GreaterThanOrEqual(Box<SubExpr>, Box<SubExpr>), // '>='
    Elem(Box<SubExpr>, Box<SubExpr>),     // 'elem'
    NotElem(Box<SubExpr>, Box<SubExpr>),  // 'notelem'
    AndAlso(Box<SubExpr>, Box<SubExpr>),  // 'andalso'
    OrElse(Box<SubExpr>, Box<SubExpr>),   // 'orelse'
    Implies(Box<SubExpr>, Box<SubExpr>),  // 'implies'
    Aggregate(Box<SubExpr>, Box<SubExpr>), // 'over'
    Cons(Box<SubExpr>, Box<SubExpr>),     // '::'
    Append(Box<SubExpr>, Box<SubExpr>),   // '@'

    Negate(Box<SubExpr>),              // unary negation
    Apply(Box<SubExpr>, Box<SubExpr>), // apply function to argument

    // Control structures
    If(Box<SubExpr>, Box<SubExpr>, Box<SubExpr>),
    Case(Box<SubExpr>, Vec<(ast::Pat, SubExpr)>),
    Let(Vec<Decl>, Box<SubExpr>),
    Fn(Vec<(Pat, Expr)>),

    // Constructors for data structures
    Tuple(Vec<Expr>),       // e.g. `(x, y, z)`
    List(Vec<Expr>),        // e.g. `[x, y, z]`
    Record(Vec<NamedExpr>), // e.g. `{ r with x = 1, y = 2 }`, `{x = 1, y}`

    // Relational expressions
    From(Vec<Step>),

    // Type annotation
    Annotated(Box<SubExpr>, Box<Type>),
}

impl ExprKind<Expr> {
    pub fn spanned(&self, span: &Span) -> Expr {
        Expr {
            kind: self.clone(),
            span: span.clone(),
        }
    }

    pub fn wrap2(self, e1: &Expr, e2: &Expr) -> Expr {
        self.spanned(&e1.span.union(&e2.span))
    }

    pub fn wrap3(self, e1: &Expr, e2: &Expr, e3: &Expr) -> Expr {
        self.spanned(&e1.span.union(&e2.span).union(&e3.span))
    }

    pub fn wrap_case(self, e: &Expr, arms: Vec<(ast::Pat, ast::Expr)>) -> Expr {
        self.wrap_matches(&e.span, arms)
    }

    pub fn wrap_matches(
        self,
        span0: &Span,
        arms: Vec<(ast::Pat, ast::Expr)>,
    ) -> Expr {
        let mut span = span0.clone();
        for arm in arms {
            span.merge(&arm.0.span);
            span.merge(&arm.1.span);
        }
        self.spanned(&span)
    }

    pub fn wrap_list(self, e: &Expr, decls: &Vec<Decl>) -> Expr {
        let mut span = e.span.clone();
        for decl in decls {
            span.merge(&decl.span);
        }
        self.spanned(&span)
    }
}

/// Abstract syntax tree (AST) of a literal.
///
/// Is used in expressions and patterns, via [`ExprKind::Literal`] and
/// [`PatKind::Literal`].
#[derive(Debug, Clone)]
pub struct Literal {
    pub kind: LiteralKind,
    pub span: Span,
}

impl Literal {}

/// Kind of literal.
#[derive(Debug, Clone)]
pub enum LiteralKind {
    Int(String),
    Real(String),
    String(String),
    Char(String),
    Bool(bool),
    Unit,
}

impl LiteralKind {
    pub fn spanned(self, span: &Span) -> Literal {
        Literal {
            kind: self.clone(),
            span: span.clone(),
        }
    }
}

/// Named expression for records and relational operations
#[derive(Debug, Clone)]
pub struct NamedExpr {
    pub name: Option<String>,
    pub expr: Expr,
}

/// Abstract syntax tree (AST) of a step in a query.
#[derive(Debug, Clone)]
pub struct Step {
    pub kind: StepKind,
    pub span: Span,
}

impl Step {}

/// Kind of step in a query.
#[derive(Debug, Clone)]
pub enum StepKind {
    /// Scan or join step, e.g.
    /// `from p in e`, `p in e on c`, or `join p in e on c`.
    Join(Pat, Box<Expr>, Option<Box<Expr>>),
    From,
    Where,
    Group,
    Order,
    Yield,
}

impl StepKind {
    pub fn spanned(&self, span: &Span) -> Step {
        Step {
            kind: self.clone(),
            span: span.clone(),
        }
    }
}

/// Abstract syntax tree (AST) of a pattern.
#[derive(Debug, Clone)]
pub struct Pat {
    pub kind: PatKind,
    pub span: Span,
}

/// Kind of pattern.
///
/// A few names have evolved from Morel-Java.
/// `Constructor` is equivalent to `class ConPat` or `class Con0Pat`;
/// `Cons` is equivalent to `class ConsPat` in Morel-Java.
#[derive(Debug, Clone)]
pub enum PatKind {
    Wildcard,
    Identifier(String),
    Literal(Literal),
    Tuple(Vec<Pat>),
    List(Vec<Pat>),
    Record(Vec<PatField>, bool),
    Cons(Box<Pat>, Box<Pat>), // e.g. `x :: xs`
    Constructor(String, Option<Box<Pat>>), // e.g. `Empty` or `Leaf x`
    As(Box<Pat>, String),
    Annotated(Box<Pat>, Type),
}

impl PatKind {
    pub fn spanned(&self, span: &Span) -> Pat {
        Pat {
            kind: self.clone(),
            span: span.clone(),
        }
    }

    pub fn wrap2(self, e1: &Expr, e2: &Expr) -> Pat {
        self.spanned(&e1.span.union(&e2.span))
    }

    pub fn wrap3(self, e1: &Expr, e2: &Expr, e3: &Expr) -> Pat {
        self.spanned(&e1.span.union(&e2.span).union(&e3.span))
    }
}

/// Abstract syntax tree (AST) of a field in a record pattern.
/// It can be labeled, anonymous, or ellipsis.
/// For example, `{ label = x, y, ... }` has one of each.
#[derive(Debug, Clone)]
pub enum PatField {
    Labeled(Span, String, Box<Pat>), // e.g. `named = x`
    Anonymous(Span, Box<Pat>),       // e.g. `y`
    Ellipsis(Span),                  // e.g. `...`
}

/// Abstract syntax tree (AST) of a declaration.
#[derive(Debug, Clone)]
pub struct Decl {
    pub kind: DeclKind,
    pub span: Span,
}

impl Decl {}

/// Kind of declaration.
#[derive(Debug, Clone)]
pub enum DeclKind {
    Val(bool, Vec<ValBind>),
    Fun(Vec<FunBind>),
    Type(Vec<TypeBind>),
    Datatype(Vec<DatatypeBind>),
}

impl DeclKind {
    pub fn spanned(&self, span: &Span) -> Decl {
        Decl {
            kind: self.clone(),
            span: span.clone(),
        }
    }
}

/// Value binding
#[derive(Debug, Clone)]
pub struct ValBind {
    pub pat: Pat,
    pub type_annotation: Option<Type>,
    pub expr: Expr,
}

impl ValBind {
    /// Creates a value binding with the given pattern, type annotation, and expression.
    pub fn of(pat: Pat, type_annotation: Option<Type>, expr: Expr) -> Self {
        ValBind {
            pat,
            type_annotation,
            expr,
        }
    }
}

/// Function binding
#[derive(Debug, Clone)]
pub struct FunBind {
    pub span: Span,
    pub name: String,
    pub matches: Vec<(Pat, Expr)>,
}

/// Type binding
#[derive(Debug, Clone)]
pub struct TypeBind {
    pub span: Span,
    pub type_vars: Vec<String>,
    pub name: String,
    pub type_expr: Type,
}

/// Datatype binding
#[derive(Debug, Clone)]
pub struct DatatypeBind {
    pub span: Span,
    pub type_vars: Vec<String>,
    pub name: String,
    pub constructors: Vec<ConBind>,
}

/// Constructor binding
#[derive(Debug, Clone)]
pub struct ConBind {
    pub span: Span,
    pub name: String,
    pub type_expr: Option<Type>,
}

/// Abstract syntax tree (AST) of a type.
#[derive(Debug, Clone)]
pub struct Type {
    pub kind: TypeKind,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub enum TypeKind {
    Var(String),
    Con(String),
    Fn(Box<Type>, Box<Type>),
    Tuple(Vec<Type>),
    Record(Vec<TypeField>),
    App(Box<Type>, Vec<Type>),
}

impl TypeKind {
    pub(crate) fn spanned(&self, span: &Span) -> Type {
        Type {
            kind: self.clone(),
            span: span.clone(),
        }
    }
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
            ExprKind::Literal(value) => value.kind.unparse(s),
            _ => s.push_str("<expr>"), // TODO: implement for all variants
        }
    }
}

impl MorelNode for LiteralKind {
    fn unparse(&self, s: &mut String) {
        match self {
            LiteralKind::Int(value) => s.push_str(value),
            LiteralKind::Real(value) => s.push_str(value),
            LiteralKind::String(value) => write!(s, "\"{}\"", value).unwrap(),
            LiteralKind::Char(value) => write!(s, "#\"{}\"", value).unwrap(),
            LiteralKind::Bool(value) => {
                s.push_str(if *value { "true" } else { "false" })
            }
            LiteralKind::Unit => s.push_str("()"),
            _ => s.push_str("<expr>"), // TODO: implement for all variants
        }
    }
}

impl MorelNode for DeclKind {
    fn unparse(&self, s: &mut String) {
        match self {
            DeclKind::Val(rec, binds) => {
                s.push_str("val ");
                if let Some(first_bind) = binds.first() {
                    if *rec {
                        s.push_str("rec ");
                    }
                    first_bind.pat.kind.unparse(s);
                    if let Some(ref type_annotation) =
                        first_bind.type_annotation
                    {
                        s.push_str(": ");
                        match &type_annotation.kind {
                            TypeKind::Con(name) => s.push_str(name),
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

impl MorelNode for PatKind {
    fn unparse(&self, s: &mut String) {
        match self {
            PatKind::Identifier(name) => s.push_str(name),
            PatKind::Wildcard => s.push('_'),
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
        pat: pat.unwrap_or_else(|| todo!()),
        type_annotation,
        expr: expr.unwrap_or_else(|| todo!()),
    };

    DeclKind::Val(has_rec, vec![val_bind])
}

fn build_pat(p0: Pair<Rule>) -> Pat {
    todo!()
}

/// Builds a type from parsed pairs.
pub fn build_type(pair: Pair<Rule>) -> Type {
    todo!()
}
