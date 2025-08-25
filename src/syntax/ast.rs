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
use std::fmt::Write;
use std::rc::Rc;

/// A location in the source text.
#[derive(Debug, Clone, PartialEq)]
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
    /// Creates the 'null' span for a source document.
    pub fn zero(input: Rc<str>) -> Self {
        Span {
            input,
            start: 0,
            end: 0,
        }
    }

    /// Creates a span.
    pub fn make(input: Rc<str>, sp: pest::Span) -> Self {
        Span {
            input,
            start: sp.start(),
            end: sp.end(),
        }
    }

    /// Creates the union of two spans.
    pub fn union(&self, other: &Span) -> Self {
        use std::cmp::{max, min};
        let input = self.input.clone();
        let start = min(self.start, other.start);
        let end = max(self.start, other.start);
        Span { input, start, end }
    }

    /// Merges another span into this.
    /// Requires that the spans come from the same input.
    pub fn merge(&mut self, other: &Span) {
        if self.input != other.input {
            panic!("Cannot merge spans from different inputs");
        }
        self.start = self.start.min(other.start);
        self.end = self.end.max(other.end);
    }
}

/// Trait possessed by all abstract syntax tree (AST) nodes.
pub trait MorelNode {
    /// Returns the string representation of the AST node.
    fn unparse(&self, s: &mut String);

    /// Returns the span.
    fn span(&self) -> &Span;

    /// Returns a copy of the AST node with a new span.
    fn with_span(&self, span: &Span) -> Self;
}

/// Abstract syntax tree (AST) of a statement (expression or declaration).
#[derive(Debug, Clone)]
pub struct Statement {
    pub kind: StatementKind,
    pub span: Span,
}

impl MorelNode for Statement {
    fn unparse(&self, s: &mut String) {
        match &self.kind {
            StatementKind::Expr(x) => x.spanned(&self.span).unparse(s),
            StatementKind::Decl(x) => x.spanned(&self.span).unparse(s),
        }
    }

    fn span(&self) -> &Span {
        &self.span
    }

    fn with_span(&self, span: &Span) -> Self {
        Statement {
            kind: self.kind.clone(),
            span: span.clone(),
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
    pub kind: ExprKind<Expr>,
    pub span: Span,
}

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
    Case(Box<SubExpr>, Vec<(Pat, SubExpr)>),
    Let(Vec<Decl>, Box<SubExpr>),
    Fn(Vec<(Pat, Expr)>),

    // Constructors for data structures
    Tuple(Vec<Expr>), // e.g. `(x, y, z)`
    List(Vec<Expr>),  // e.g. `[x, y, z]`
    Record(Option<Box<Expr>>, Vec<LabeledExpr>), // e.g. `{r with x = 1, y}`

    // Relational expressions
    From(Vec<Step>),
    Exists(Vec<Step>),
    Forall(Vec<Step>),

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
/// Used in expressions and patterns, via [`ExprKind::Literal`] and
/// [`PatKind::Literal`].
#[derive(Debug, Clone)]
pub struct Literal {
    pub kind: LiteralKind,
    pub span: Span,
}

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
    pub fn spanned(&self, span_: &Span) -> Literal {
        let kind = self.clone();
        let span = span_.clone();
        Literal { kind, span }
    }
}

/// Label within a record expression or record pattern.
#[derive(Debug, Clone)]
pub struct Label {
    pub span: Span,
    pub name: String,
}

impl Label {
    pub(crate) fn new(name: &str, span: &Span) -> Label {
        Label {
            span: span.clone(),
            name: name.to_string(),
        }
    }
}

/// Labeled expression in a record.
#[derive(Debug, Clone)]
pub struct LabeledExpr {
    pub label: Option<Label>,
    pub expr: Box<Expr>,
}

impl LabeledExpr {
    pub fn new(label: Option<Label>, expr: Box<Expr>) -> Self {
        LabeledExpr { label, expr }
    }
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
    Compute(Box<Expr>),
    Distinct,
    Into(Box<Expr>),
    Join(Box<Pat>),
    JoinEq(Box<Pat>, Box<Expr>, Option<Box<Expr>>),
    JoinIn(Box<Pat>, Box<Expr>, Option<Box<Expr>>),
    Except(bool, Vec<Expr>),
    From,
    Group(Box<Expr>, Option<Box<Expr>>),
    Intersect(bool, Vec<Expr>),
    Order(Box<Expr>),
    Require(Box<Expr>),
    Skip(Box<Expr>),
    Take(Box<Expr>),
    Through(Box<Pat>, Box<Expr>),
    Union(bool, Vec<Expr>),
    Unorder,
    Where(Box<Expr>),
    Yield(Box<Expr>),
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
    As(String, Box<Pat>),
    Constructor(String, Option<Box<Pat>>), // e.g. `Empty` or `Leaf x`
    Literal(Literal),
    Tuple(Vec<Pat>),
    List(Vec<Pat>),
    Record(Vec<PatField>, bool),
    Cons(Box<Pat>, Box<Pat>), // e.g. `x :: xs`
    Annotated(Box<Pat>, Box<Type>),
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
    Val(bool, bool, Vec<ValBind>),
    Fun(Vec<FunBind>),
    Over(String),
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

/// Value binding.
#[derive(Debug, Clone)]
pub struct ValBind {
    pub pat: Pat,
    pub type_annotation: Option<Type>,
    pub expr: Expr,
}

impl ValBind {
    /// Creates a value binding with the given pattern, type annotation, and
    /// expression.
    pub fn of(pat: Pat, type_annotation: Option<Type>, expr: Expr) -> Self {
        ValBind {
            pat,
            type_annotation,
            expr,
        }
    }
}

/// Function binding.
///
/// E.g. `fun f 0 = 1 | f n = n * f (n - 1)`
/// is a function binding with name `f` and two matches.
#[derive(Debug, Clone)]
pub struct FunBind {
    pub span: Span,
    pub name: String,
    pub matches: Vec<FunMatch>,
}

/// Function match.
///
/// E.g. `f 0: int = 1` are `f n = n * f (n - 1)`
/// are each matches with one pattern. The first has a type.
#[derive(Debug, Clone)]
pub struct FunMatch {
    pub span: Span,
    pub name: String,
    pub pats: Vec<Pat>,
    pub type_: Option<Box<Type>>,
    pub expr: Box<Expr>,
}

/// Type binding.
#[derive(Debug, Clone)]
pub struct TypeBind {
    pub span: Span,
    pub type_vars: Vec<String>,
    pub name: String,
    pub type_: Type,
}

/// Datatype binding.
#[derive(Debug, Clone)]
pub struct DatatypeBind {
    pub span: Span,
    pub type_vars: Vec<String>,
    pub name: String,
    pub constructors: Vec<ConBind>,
}

/// Constructor binding.
#[derive(Debug, Clone)]
pub struct ConBind {
    pub span: Span,
    pub name: String,
    pub type_: Option<Type>,
}

/// Abstract syntax tree (AST) of a type.
#[derive(Debug, Clone)]
pub struct Type {
    pub kind: TypeKind,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub enum TypeKind {
    Unit,
    Id(String),
    Var(String),
    Con(String),
    Fn(Box<Type>, Box<Type>),
    Tuple(Vec<Type>),
    Record(Vec<TypeField>),
    App(Vec<Type>, Box<Type>),
    Expression(Box<Expr>),
}

impl TypeKind {
    pub fn spanned(&self, span: &Span) -> Type {
        Type {
            kind: self.clone(),
            span: span.clone(),
        }
    }
}

/// Type field in record types.
#[derive(Debug, Clone)]
pub struct TypeField {
    pub label: Label,
    pub type_: Type,
}

impl MorelNode for Expr {
    fn unparse(&self, s: &mut String) {
        match &self.kind {
            ExprKind::Identifier(name) => s.push_str(name),
            ExprKind::Literal(value) => value.unparse(s),
            _ => s.push_str("<expr>"), // TODO: implement for all variants
        }
    }

    fn span(&self) -> &Span {
        &self.span
    }

    fn with_span(&self, span: &Span) -> Self {
        Expr {
            kind: self.kind.clone(),
            span: span.clone(),
        }
    }
}

impl MorelNode for Literal {
    fn unparse(&self, s: &mut String) {
        match &self.kind {
            LiteralKind::Int(value) => s.push_str(value),
            LiteralKind::Real(value) => s.push_str(value),
            LiteralKind::String(value) => write!(s, "\"{}\"", value).unwrap(),
            LiteralKind::Char(value) => write!(s, "#\"{}\"", value).unwrap(),
            LiteralKind::Bool(value) => {
                s.push_str(if *value { "true" } else { "false" })
            }
            LiteralKind::Unit => s.push_str("()"),
        }
    }

    fn span(&self) -> &Span {
        &self.span
    }

    fn with_span(&self, span: &Span) -> Self {
        Literal {
            kind: self.kind.clone(),
            span: span.clone(),
        }
    }
}

impl MorelNode for Decl {
    fn unparse(&self, s: &mut String) {
        match &self.kind {
            DeclKind::Val(rec, inst, binds) => {
                s.push_str("val ");
                if let Some(first_bind) = binds.first() {
                    if *rec {
                        s.push_str("rec ");
                    }
                    first_bind.pat.unparse(s);
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
                    first_bind.expr.unparse(s);
                }
            }
            _ => s.push_str("<decl>"),
        }
    }

    fn span(&self) -> &Span {
        &self.span
    }

    fn with_span(&self, span: &Span) -> Self {
        Decl {
            kind: self.kind.clone(),
            span: span.clone(),
        }
    }
}

impl MorelNode for Pat {
    fn unparse(&self, s: &mut String) {
        match &self.kind {
            PatKind::Identifier(name) => s.push_str(name),
            PatKind::Wildcard => s.push('_'),
            _ => s.push_str("<pat>"),
        }
    }

    fn span(&self) -> &Span {
        &self.span
    }

    fn with_span(&self, span: &Span) -> Self {
        Pat {
            kind: self.kind.clone(),
            span: span.clone(),
        }
    }
}

impl Type {
    pub fn with_span(&self, span: &Span) -> Type {
        if span.eq(&self.span) {
            return self.clone();
        }
        Type {
            kind: self.kind.clone(),
            span: span.clone(),
        }
    }
}

impl MorelNode for Type {
    fn unparse(&self, s: &mut String) {
        todo!()
    }

    fn span(&self) -> &Span {
        &self.span
    }

    fn with_span(&self, span: &Span) -> Self {
        self.with_span(span)
    }
}
