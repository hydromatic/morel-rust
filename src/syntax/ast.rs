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

use crate::compile::library::BuiltInFunction;
use crate::eval::val::Val;
use crate::syntax::ast;
use std::fmt::{Debug, Display, Formatter, Result as FmtResult};
use std::ops::Deref;
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

    /// Sums the spans of elements.
    pub fn sum<T>(elements: &[T], extract: fn(&T) -> Span) -> Option<Span> {
        let mut span = None;
        for p in elements {
            let span2 = extract(p);
            span = match span {
                None => Some(span2),
                Some(span1) => Some(span1.union(&span2)),
            }
        }
        span
    }

    /// Converts this Span to a Pest span.
    pub fn to_pest_span(&self) -> pest::Span<'_> {
        pest::Span::new(self.input.deref(), self.start, self.end).unwrap()
    }
}

/// Trait possessed by all abstract syntax tree (AST) nodes.
pub trait MorelNode {
    /// Returns the span.
    fn span(&self) -> Span;

    /// Returns a copy of the AST node with a new span.
    fn with_span(&self, span: &Span) -> Self;

    /// Returns the unique id of this node.
    /// This id is used to retrieve the node's type after unification.
    fn id(&self) -> Option<i32>;
}

/// Abstract syntax tree (AST) of a statement (expression or declaration).
#[derive(Debug, Clone)]
pub struct Statement {
    pub kind: StatementKind,
    pub span: Span,
    pub id: Option<i32>,
}

impl MorelNode for Statement {
    fn span(&self) -> Span {
        self.span.clone()
    }

    fn with_span(&self, span: &Span) -> Self {
        Statement {
            span: span.clone(),
            ..self.clone()
        }
    }

    fn id(&self) -> Option<i32> {
        self.id
    }
}

/// Kind of statement.
#[derive(Debug, Clone)]
pub enum StatementKind {
    Expr(ExprKind<Expr>),
    Decl(DeclKind),
}

impl Display for StatementKind {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        match &self {
            StatementKind::Expr(e) => write!(f, "{}", e),
            StatementKind::Decl(d) => write!(f, "{}", d),
        }
    }
}

/// Abstract syntax tree (AST) of an expression.
#[derive(Debug, Clone)]
pub struct Expr {
    pub kind: ExprKind<Expr>,
    pub span: Span,
    pub id: Option<i32>,
}

impl Expr {
    #[allow(dead_code)]
    fn from_statement(statement: &Statement) -> Self {
        match &statement.kind {
            StatementKind::Expr(e) => Expr {
                kind: e.clone(),
                span: statement.span.clone(),
                id: statement.id,
            },
            _ => panic!("expected expression"),
        }
    }
}

impl Display for Expr {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        std::fmt::Display::fmt(&self.kind, f)
    }
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

    Negate(Box<SubExpr>), // unary negation
    /// `Apply(f, a)` represents `f a`, applying a function to an argument.
    Apply(Box<SubExpr>, Box<SubExpr>),

    // Control structures
    If(Box<SubExpr>, Box<SubExpr>, Box<SubExpr>),
    Case(Box<SubExpr>, Vec<Match>),
    Let(Vec<Decl>, Box<SubExpr>),
    Fn(Vec<Match>),

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
            id: None,
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

impl Display for ExprKind<Expr> {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        match &self {
            // lint: sort until '#}' where '##ExprKind::'
            ExprKind::Aggregate(a0, a1) => {
                write!(f, "({} over {})", a0, a1)
            }
            ExprKind::AndAlso(a0, a1) => {
                write!(f, "({} andalso {})", a0, a1)
            }
            ExprKind::Annotated(e, typ) => write!(f, "{}: {}", e, typ),
            ExprKind::Append(a0, a1) => write!(f, "({} @ {})", a0, a1),
            ExprKind::Apply(fx, arg) => write!(f, "{} {}", fx, arg),
            ExprKind::Caret(a0, a1) => write!(f, "({} ^ {})", a0, a1),
            ExprKind::Case(e, arms) => {
                write!(f, "case {} of ", e)?;
                for (i, match_) in arms.iter().enumerate() {
                    if i > 0 {
                        write!(f, " | ")?;
                    }
                    write!(f, "{} => {}", match_.pat, match_.expr)?;
                }
                Ok(())
            }
            ExprKind::Compose(a0, a1) => write!(f, "({} o {})", a0, a1),
            ExprKind::Cons(a0, a1) => write!(f, "({} :: {})", a0, a1),
            ExprKind::Current => write!(f, "current"),
            ExprKind::Div(a0, a1) => write!(f, "({} div {})", a0, a1),
            ExprKind::Divide(a0, a1) => write!(f, "({} / {})", a0, a1),
            ExprKind::Elem(a0, a1) => write!(f, "({} elem {})", a0, a1),
            ExprKind::Equal(a0, a1) => write!(f, "({} = {})", a0, a1),
            ExprKind::Exists(steps) => write!(f, "exists {:?}", steps),
            ExprKind::Fn(arms) => {
                write!(f, "fn ")?;
                for (i, match_) in arms.iter().enumerate() {
                    if i > 0 {
                        write!(f, " | ")?;
                    }
                    write!(f, "{} => {}", match_.pat, match_.expr)?;
                }
                Ok(())
            }
            ExprKind::Forall(steps) => write!(f, "forall {:?}", steps),
            ExprKind::From(steps) => write!(f, "from {:?}", steps),
            ExprKind::GreaterThan(a0, a1) => write!(f, "({} > {})", a0, a1),
            ExprKind::GreaterThanOrEqual(a0, a1) => {
                write!(f, "({} >= {})", a0, a1)
            }
            ExprKind::Identifier(name) => write!(f, "{}", name),
            ExprKind::If(cond, then_, else_) => {
                write!(f, "if {} then {} else {}", cond, then_, else_)
            }
            ExprKind::Implies(a0, a1) => {
                write!(f, "({} implies {})", a0, a1)
            }
            ExprKind::LessThan(a0, a1) => write!(f, "({} < {})", a0, a1),
            ExprKind::LessThanOrEqual(a0, a1) => {
                write!(f, "({} <= {})", a0, a1)
            }
            ExprKind::Let(decls, body) => {
                write!(f, "let ")?;
                for decl in decls {
                    write!(f, "{}; ", decl)?;
                }
                write!(f, "in {}", body)
            }
            ExprKind::List(elems) => {
                let elems_str = elems
                    .iter()
                    .map(|e| format!("{}", e))
                    .collect::<Vec<_>>()
                    .join(", ");
                write!(f, "[{}]", elems_str)
            }
            ExprKind::Literal(lit) => write!(f, "{}", lit),
            ExprKind::Minus(a0, a1) => write!(f, "({} - {})", a0, a1),
            ExprKind::Mod(a0, a1) => write!(f, "({} mod {})", a0, a1),
            ExprKind::Negate(e) => write!(f, "-{}", e),
            ExprKind::NotElem(a0, a1) => {
                write!(f, "({} notelem {})", a0, a1)
            }
            ExprKind::NotEqual(a0, a1) => write!(f, "({} <> {})", a0, a1),
            ExprKind::OrElse(a0, a1) => write!(f, "({} orelse {})", a0, a1),
            ExprKind::Ordinal => write!(f, "ordinal"),
            ExprKind::Plus(a0, a1) => write!(f, "({} + {})", a0, a1),
            ExprKind::Record(base, fields) => {
                let mut s = String::new();
                if let Some(b) = base {
                    s.push_str(&format!("{} with ", b));
                }
                let fields_str = fields
                    .iter()
                    .map(|f| format!("{}", f.expr))
                    .collect::<Vec<_>>()
                    .join(", ");
                write!(f, "{{{}}}", s + &fields_str)
            }
            ExprKind::RecordSelector(name) => write!(f, "#{}", name),
            ExprKind::Times(a0, a1) => write!(f, "({} * {})", a0, a1),
            ExprKind::Tuple(elems) => {
                let elems_str = elems
                    .iter()
                    .map(|e| format!("{}", e))
                    .collect::<Vec<_>>()
                    .join(", ");
                write!(f, "({})", elems_str)
            }
        }
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
    pub id: Option<i32>,
}

impl Display for Literal {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        std::fmt::Display::fmt(&self.kind, f)
    }
}

/// Kind of literal.
#[derive(Debug, Clone)]
pub enum LiteralKind {
    Fn(BuiltInFunction),
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
        let id = None;
        Literal { kind, span, id }
    }
}

impl Display for LiteralKind {
    fn fmt(&self, f: &mut Formatter) -> FmtResult {
        match &self {
            // lint: sort until '#}' where '##LiteralKind::'
            LiteralKind::Bool(b) => write!(f, "{}", b)?,
            LiteralKind::Char(s) => write!(f, "{}", s)?,
            LiteralKind::Fn(built_in) => write!(f, "{:?}", built_in)?,
            LiteralKind::Int(s) => write!(f, "{}", s)?,
            LiteralKind::Real(s) => write!(f, "{}", s)?,
            LiteralKind::String(s) => write!(f, "{}", s)?,
            LiteralKind::Unit => write!(f, "()")?,
        };
        Ok(())
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
    pub expr: Expr,
}

impl LabeledExpr {
    pub fn new(label: Option<Label>, expr: &Expr) -> Self {
        LabeledExpr {
            label,
            expr: expr.clone(),
        }
    }
}

/// Match in a `case` or `fn` expression.
#[derive(Debug, Clone)]
pub struct Match {
    pub pat: Pat,
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
    pub id: Option<i32>,
}

impl Pat {
    /// Returns the name of this pattern, if it is an identifier or `as`,
    /// otherwise None.
    pub fn name(&self) -> Option<String> {
        match &self.kind {
            PatKind::Identifier(name) | PatKind::As(name, _) => {
                Some(name.clone())
            }
            _ => None,
        }
    }

    pub(crate) fn bind_recurse(
        &self,
        val: &Val,
        consumer: &mut dyn FnMut(Box<Pat>, &Val),
    ) {
        match &self.kind {
            PatKind::Identifier(_name) => {
                consumer(Box::new(self.clone()), val);
            }
            _ => {
                todo!("{}", self.kind);
            }
        }
    }

    /// Calls a given function for each atomic identifier in this pattern.
    pub(crate) fn for_each_id_pat(&self, consumer: &mut impl FnMut(i32, &str)) {
        match &self.kind {
            // lint: sort until '#}' where '##PatKind::'
            PatKind::Identifier(name) => {
                (*consumer)(self.id.unwrap(), name.as_str())
            }
            PatKind::Record(pat_fields, _) => {
                for field in pat_fields {
                    match field {
                        PatField::Labeled(_, _, p) => {
                            p.for_each_id_pat(consumer)
                        }
                        PatField::Anonymous(_, p) => {
                            p.for_each_id_pat(consumer)
                        }
                        PatField::Ellipsis(_) => {}
                    }
                }
            }
            PatKind::Tuple(pats) => {
                pats.iter().for_each(|p| p.for_each_id_pat(consumer))
            }
            _ => todo!("{}", self.kind),
        }
    }
}

impl Display for Pat {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        std::fmt::Display::fmt(&self.kind, f)
    }
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
    pub fn spanned(&self, span_: &Span) -> Pat {
        let kind = self.clone();
        let span = span_.clone();
        let id = None;
        Pat { kind, span, id }
    }

    pub fn wrap2(self, e1: &Expr, e2: &Expr) -> Pat {
        self.spanned(&e1.span.union(&e2.span))
    }

    pub fn wrap3(self, e1: &Expr, e2: &Expr, e3: &Expr) -> Pat {
        self.spanned(&e1.span.union(&e2.span).union(&e3.span))
    }
}

impl Display for PatKind {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        match &self {
            // lint: sort until '#}' where '##PatKind::'
            PatKind::Annotated(pat, typ) => write!(f, "{}: {}", pat, typ),
            PatKind::Identifier(name) => write!(f, "{}", name),
            PatKind::Literal(lit) => write!(f, "{:?}", lit),
            PatKind::Record(fields, ellipsis) => {
                let fields_str = fields
                    .iter()
                    .map(|field| match field {
                        PatField::Labeled(_, name, pat) => {
                            format!("{} = {}", name, pat)
                        }
                        PatField::Anonymous(_, pat) => format!("{}", pat),
                        PatField::Ellipsis(_) => "...".to_string(),
                    })
                    .collect::<Vec<_>>()
                    .join(", ");
                if *ellipsis {
                    write!(f, "{{{}, ...}}", fields_str)
                } else {
                    write!(f, "{{{}}}", fields_str)
                }
            }
            PatKind::Tuple(pats) => {
                let pats_str = pats
                    .iter()
                    .map(|p| format!("{}", p))
                    .collect::<Vec<_>>()
                    .join(", ");
                write!(f, "({})", pats_str)
            }
            _ => write!(f, "<unknown pat>"),
        }
    }
}

/// Abstract syntax tree (AST) of a field in a record pattern.
/// It can be labeled, anonymous, or ellipsis.
/// For example, `{ label = x, y, ... }` has one of each.
#[derive(Debug, Clone)]
pub enum PatField {
    Labeled(Span, String, Pat), // e.g. `named = x`
    Anonymous(Span, Pat),       // e.g. `y`
    Ellipsis(Span),             // e.g. `...`
}

/// Abstract syntax tree (AST) of a declaration.
#[derive(Debug, Clone)]
pub struct Decl {
    pub kind: DeclKind,
    pub span: Span,
    pub id: Option<i32>,
}

impl Decl {
    pub(crate) fn for_each_id_pat(&self, mut p0: impl FnMut(i32, &str)) {
        match &self.kind {
            DeclKind::Val(_rec, _inst, val_binds) => {
                for val_bind in val_binds {
                    val_bind.pat.for_each_id_pat(&mut p0)
                }
            }
            _ => todo!(),
        }
    }

    pub fn from_statement(statement: &Statement) -> Self {
        match &statement.kind {
            StatementKind::Decl(d) => Decl {
                span: statement.span.clone(),
                kind: d.clone(),
                id: statement.id,
            },
            _ => panic!("expected declaration"),
        }
    }
}

impl Display for Decl {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        std::fmt::Display::fmt(&self.kind, f)
    }
}

/// Kind of declaration.
#[derive(Debug, Clone)]
pub enum DeclKind {
    /// `Val(rec, inst, binds)` represents a value declaration such as
    /// `val rec x = 0 and f = fn i => f(i - 1)`.
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
            id: None,
        }
    }
}

impl Display for DeclKind {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        match self {
            // lint: sort until '#}' where '##DeclKind::'
            DeclKind::Datatype(datatypes) => {
                write!(f, "datatype ")?;
                fmt_list(f, datatypes, "; ")
            }
            DeclKind::Fun(funs) => {
                write!(f, "fun ")?;
                fmt_list(f, funs, " | ")
            }
            DeclKind::Over(name) => write!(f, "over {}", name),
            DeclKind::Type(types) => {
                write!(f, "type ")?;
                fmt_list(f, types, "; ")
            }
            DeclKind::Val(rec, inst, binds) => {
                write!(f, "val ")?;
                if *rec {
                    write!(f, "rec ")?;
                }
                if *inst {
                    write!(f, "inst ")?;
                }
                fmt_list(f, binds, " and ")
            }
        }
    }
}

/// Value binding.
#[derive(Debug, Clone)]
pub struct ValBind {
    pub pat: Pat,
    pub type_annotation: Option<Box<Type>>,
    pub expr: Expr,
}

impl ValBind {
    /// Creates a value binding with the given pattern, type annotation, and
    /// expression.
    pub fn of(pat: &Pat, type_annotation: Option<Type>, expr: &Expr) -> Self {
        ValBind {
            pat: pat.clone(),
            type_annotation: type_annotation.map(Box::new),
            expr: expr.clone(),
        }
    }

    pub fn span(&self) -> Span {
        self.pat.span.union(&self.expr.span)
    }
}

impl Display for ValBind {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "{} = {}", self.pat, self.expr)
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

impl Display for FunBind {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(
            f,
            "fun {} {}",
            self.name,
            self.matches
                .iter()
                .map(|m| format!("{}", m))
                .collect::<Vec<_>>()
                .join(" | ")
        )
    }
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
    pub expr: Expr,
}

impl Display for FunMatch {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        let pats_str = self
            .pats
            .iter()
            .map(|p| format!("{}", p))
            .collect::<Vec<_>>()
            .join(", ");
        write!(f, "{}: {} = {}", self.name, pats_str, self.expr)
    }
}

/// Type binding.
#[derive(Debug, Clone)]
pub struct TypeBind {
    pub span: Span,
    pub type_vars: Vec<String>,
    pub name: String,
    pub type_: Type,
}

impl Display for TypeBind {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "{}: {}", self.name, self.type_)
    }
}

/// Datatype binding.
#[derive(Debug, Clone)]
pub struct DatatypeBind {
    pub span: Span,
    pub type_vars: Vec<String>,
    pub name: String,
    pub constructors: Vec<ConBind>,
}

impl Display for DatatypeBind {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        let constructors_str = self
            .constructors
            .iter()
            .map(|c| format!("{}", c))
            .collect::<Vec<_>>()
            .join(", ");
        write!(f, "{}: {}", self.name, constructors_str)
    }
}

/// Constructor binding.
#[derive(Debug, Clone)]
pub struct ConBind {
    pub span: Span,
    pub name: String,
    pub type_: Option<Type>,
}

impl Display for ConBind {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(
            f,
            "{}{}",
            self.name,
            match &self.type_ {
                Some(t) => format!(": {}", t),
                None => "".to_string(),
            }
        )
    }
}

/// Abstract syntax tree (AST) of a type.
#[derive(Debug, Clone, PartialEq)]
pub struct Type {
    pub kind: TypeKind,
    pub span: Span,
    pub id: Option<i32>,
}

impl Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> FmtResult {
        match &self.kind {
            // lint: sort until '#}' where '##TypeKind::'
            TypeKind::App(args, t) => {
                let args_str = args
                    .iter()
                    .map(|a| format!("{}", a))
                    .collect::<Vec<_>>()
                    .join(", ");
                write!(f, "{}<{}>", t, args_str)
            }
            TypeKind::Con(name) => write!(f, "{}", name),
            TypeKind::Expression(expr) => write!(f, "<expr:{}>", expr),
            TypeKind::Fn(t1, t2) => write!(f, "({} -> {})", t1, t2),
            TypeKind::Id(name) => write!(f, "{}", name),
            TypeKind::Record(fields) => {
                let fields_str = fields
                    .iter()
                    .map(|field| {
                        format!("{}: {}", field.label.name, field.type_)
                    })
                    .collect::<Vec<_>>()
                    .join(", ");
                write!(f, "{{{}}}", fields_str)
            }
            TypeKind::Tuple(types) => {
                let types_str = types
                    .iter()
                    .map(|t| format!("{}", t))
                    .collect::<Vec<_>>()
                    .join(", ");
                write!(f, "({})", types_str)
            }
            TypeKind::Unit => write!(f, "()"),
            TypeKind::Var(name) => write!(f, "{}", name),
        }
    }
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
    /// `App(args, t)` applies a parameterized type.
    /// For example, `int list` applies the `list` parameterized
    /// type to `int`.
    App(Vec<Type>, Box<Type>),
    Expression(Box<Expr>),
}

impl TypeKind {
    pub fn spanned(&self, span: &Span) -> Type {
        Type {
            kind: self.clone(),
            span: span.clone(),
            id: None,
        }
    }
}

impl Eq for TypeKind {}

impl PartialEq for TypeKind {
    fn eq(&self, other: &Self) -> bool {
        #[allow(clippy::enum_glob_use)]
        use TypeKind::*;
        match (self, other) {
            // lint: sort until '#}' where '##\('
            (Con(a), Con(b)) => a == b,
            (Fn(a, c), Fn(b, d)) => a.kind == b.kind && c.kind == d.kind,
            (Id(a), Id(b)) => a == b,
            (Unit, Unit) => true,
            (Var(a), Var(b)) => a == b,
            _ => false, // TODO
        }
    }
}

/// Type scheme.
pub struct TypeScheme {
    pub var_count: usize,
    pub type_: Type,
}

impl Display for TypeScheme {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "forall {} {}", self.var_count, self.type_)
    }
}

/// Type field in record types.
#[derive(Debug, Clone)]
pub struct TypeField {
    pub label: Label,
    pub type_: Type,
}

impl MorelNode for Expr {
    fn span(&self) -> Span {
        self.span.clone()
    }

    fn with_span(&self, span: &Span) -> Self {
        Expr {
            span: span.clone(),
            ..self.clone()
        }
    }

    fn id(&self) -> Option<i32> {
        self.id
    }
}

impl MorelNode for Literal {
    fn span(&self) -> Span {
        self.span.clone()
    }

    fn with_span(&self, span: &Span) -> Self {
        Literal {
            span: span.clone(),
            ..self.clone()
        }
    }

    fn id(&self) -> Option<i32> {
        self.id
    }
}

impl MorelNode for Decl {
    fn with_span(&self, span: &Span) -> Self {
        Decl {
            span: span.clone(),
            ..self.clone()
        }
    }

    fn span(&self) -> Span {
        self.span.clone()
    }

    fn id(&self) -> Option<i32> {
        self.id
    }
}

impl MorelNode for Pat {
    fn span(&self) -> Span {
        self.span.clone()
    }

    fn with_span(&self, span: &Span) -> Self {
        Pat {
            span: span.clone(),
            ..self.clone()
        }
    }

    fn id(&self) -> Option<i32> {
        self.id
    }
}

impl Type {
    pub fn with_span(&self, span: &Span) -> Type {
        if span.eq(&self.span) {
            return self.clone();
        }
        Type {
            span: span.clone(),
            ..self.clone()
        }
    }
}

impl MorelNode for Type {
    fn span(&self) -> Span {
        self.span.clone()
    }

    fn with_span(&self, span: &Span) -> Self {
        self.with_span(span)
    }

    fn id(&self) -> Option<i32> {
        self.id
    }
}

/// Formats a collection with a separator, handling the enumeration pattern.
fn fmt_list<T: Display>(
    f: &mut Formatter<'_>,
    items: &[T],
    separator: &str,
) -> FmtResult {
    for (i, item) in items.iter().enumerate() {
        if i > 0 {
            write!(f, "{}", separator)?;
        }
        write!(f, "{}", item)?;
    }
    Ok(())
}
