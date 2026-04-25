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
use crate::compile::types::Op;
use crate::eval::val::Val;
use crate::syntax::ast;
use std::fmt::{Debug, Display, Formatter, Result as FmtResult};
use std::ops::Deref;
use std::rc::Rc;

/// A location in the source text.
#[derive(Clone, PartialEq, Debug)]
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

    /// Creates an empty span.
    pub fn empty() -> Self {
        Self::zero("".into())
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
        let end = max(self.end, other.end);
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

    /// Returns the start position of the span.
    pub fn start_pos(&self) -> usize {
        self.start
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

    /// Returns the code fragment.
    pub fn code(&self) -> &str {
        &self.input[self.start..self.end]
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
#[derive(Clone, Debug)]
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
#[derive(Clone, Debug)]
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
#[derive(Clone, Debug)]
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

    /// Creates a trivial expression.
    ///
    /// When you just need an expression;
    /// say, to evaluate [ExprKind::clause].
    pub(crate) fn empty() -> Box<Expr> {
        Box::new(ExprKind::Ordinal.spanned(&Span::empty()))
    }

    /// Returns the implicit label for this expression if one can be
    /// derived. Returns `Some` for identifiers, record selectors, and a few
    /// other special cases; `None` otherwise.
    pub fn implicit_label_opt(&self) -> Option<String> {
        match &self.kind {
            // lint: sort until '#}' where '##ExprKind::'
            ExprKind::Aggregate(left, _) => left.implicit_label_opt(),
            ExprKind::Apply(left, _) => match &left.kind {
                ExprKind::RecordSelector(name) => Some(name.clone()),
                _ => None,
            },
            ExprKind::Current => Some("current".to_string()),
            ExprKind::Elements => Some("elements".to_string()),
            ExprKind::Identifier(name) => Some(name.clone()),
            ExprKind::Ordinal => Some("ordinal".to_string()),
            _ => None,
        }
    }
}

impl Display for Expr {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        Display::fmt(&self.kind, f)
    }
}

/// Kind of expression.
#[derive(Clone, Debug, strum_macros::EnumDiscriminants)]
#[strum_discriminants(
    name(ExprKindTag),
    derive(Hash, strum_macros::Display, strum_macros::EnumIter)
)]
pub enum ExprKind<SubExpr> {
    Literal(Literal),
    Identifier(String),
    /// Operator section: `op +`, `op ::`, etc.
    /// Converts an infix operator to a prefix function value.
    /// For example, `op +` is equivalent to `fn (x, y) => x + y`.
    OpSection(String),
    RecordSelector(String),
    Current,
    Ordinal,
    Elements,

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
    pub(crate) fn clause(&self) -> &str {
        match self {
            // lint: sort until '#}' where '##ExprKind::'
            ExprKind::Current => "current",
            ExprKind::Elements => "elements",
            ExprKind::Exists(_) => "exists",
            ExprKind::Forall(_) => "forall",
            ExprKind::From(_) => "from",
            _ => todo!("clause for {:?}", self),
        }
    }

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

    /// Returns the precedence operator for this expression kind, used when
    /// unparsing to decide whether the node needs surrounding parentheses.
    /// Atomic nodes (literals, identifiers, tuples, records, lists, and
    /// bracketed control structures) return [`Op::ATOM`].
    pub fn prec_op(&self) -> Op {
        match self {
            // lint: sort until '#}' where '##ExprKind::'
            ExprKind::Aggregate(..) => Op::OVER_OP,
            ExprKind::AndAlso(..) => Op::ANDALSO,
            ExprKind::Annotated(..) => Op::ANNOTATED_EXP,
            ExprKind::Append(..) => Op::APPEND,
            ExprKind::Apply(..) => Op::APPLY,
            ExprKind::Caret(..) => Op::CARET,
            ExprKind::Case(..) => Op::LOW_EXPR,
            ExprKind::Compose(..) => Op::COMPOSE,
            ExprKind::Cons(..) => Op::CONS,
            ExprKind::Current => Op::ATOM,
            ExprKind::Div(..) => Op::DIV_OP,
            ExprKind::Divide(..) => Op::DIVIDE,
            ExprKind::Elem(..) => Op::ELEM_OP,
            ExprKind::Elements => Op::ATOM,
            ExprKind::Equal(..) => Op::EQ_OP,
            ExprKind::Exists(..) => Op::LOW_EXPR,
            ExprKind::Fn(..) => Op::LOW_EXPR,
            ExprKind::Forall(..) => Op::LOW_EXPR,
            ExprKind::From(..) => Op::LOW_EXPR,
            ExprKind::GreaterThan(..) => Op::GT_OP,
            ExprKind::GreaterThanOrEqual(..) => Op::GE_OP,
            ExprKind::Identifier(..) => Op::ATOM,
            ExprKind::If(..) => Op::LOW_EXPR,
            ExprKind::Implies(..) => Op::IMPLIES,
            ExprKind::LessThan(..) => Op::LT_OP,
            ExprKind::LessThanOrEqual(..) => Op::LE_OP,
            ExprKind::Let(..) => Op::LOW_EXPR,
            ExprKind::List(..) => Op::ATOM,
            ExprKind::Literal(..) => Op::ATOM,
            ExprKind::Minus(..) => Op::MINUS,
            ExprKind::Mod(..) => Op::MOD_OP,
            ExprKind::Negate(..) => Op::ATOM,
            ExprKind::NotElem(..) => Op::NOT_ELEM_OP,
            ExprKind::NotEqual(..) => Op::NE_OP,
            ExprKind::OpSection(..) => Op::ATOM,
            ExprKind::OrElse(..) => Op::ORELSE,
            ExprKind::Ordinal => Op::ATOM,
            ExprKind::Plus(..) => Op::PLUS,
            ExprKind::Record(..) => Op::ATOM,
            ExprKind::RecordSelector(..) => Op::ATOM,
            ExprKind::Times(..) => Op::TIMES_OP,
            ExprKind::Tuple(..) => Op::ATOM,
        }
    }

    /// Unparses this expression to `f`, wrapping sub-expressions in parens
    /// only where required by the surrounding precedence `left` / `right`.
    pub fn unparse(
        &self,
        f: &mut Formatter<'_>,
        left: u8,
        right: u8,
    ) -> FmtResult {
        match self {
            // lint: sort until '#}' where '##ExprKind::'
            ExprKind::Aggregate(a0, a1) => {
                infix(f, a0, Op::OVER_OP, a1, left, right)
            }
            ExprKind::AndAlso(a0, a1) => {
                infix(f, a0, Op::ANDALSO, a1, left, right)
            }
            ExprKind::Annotated(e, typ) => {
                let op = Op::ANNOTATED_EXP;
                write_sub(f, e, left, op.left)?;
                f.write_str(op.sep)?;
                write!(f, "{}", typ)
            }
            ExprKind::Append(a0, a1) => {
                infix(f, a0, Op::APPEND, a1, left, right)
            }
            ExprKind::Apply(fx, arg) => {
                infix(f, fx, Op::APPLY, arg, left, right)
            }
            ExprKind::Caret(a0, a1) => infix(f, a0, Op::CARET, a1, left, right),
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
            ExprKind::Compose(a0, a1) => {
                infix(f, a0, Op::COMPOSE, a1, left, right)
            }
            ExprKind::Cons(a0, a1) => infix(f, a0, Op::CONS, a1, left, right),
            ExprKind::Current => f.write_str("current"),
            ExprKind::Div(a0, a1) => infix(f, a0, Op::DIV_OP, a1, left, right),
            ExprKind::Divide(a0, a1) => {
                infix(f, a0, Op::DIVIDE, a1, left, right)
            }
            ExprKind::Elem(a0, a1) => {
                infix(f, a0, Op::ELEM_OP, a1, left, right)
            }
            ExprKind::Elements => f.write_str("elements"),
            ExprKind::Equal(a0, a1) => infix(f, a0, Op::EQ_OP, a1, left, right),
            ExprKind::Exists(steps) => write_query(f, "exists", steps),
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
            ExprKind::Forall(steps) => write_query(f, "forall", steps),
            ExprKind::From(steps) => write_query(f, "from", steps),
            ExprKind::GreaterThan(a0, a1) => {
                infix(f, a0, Op::GT_OP, a1, left, right)
            }
            ExprKind::GreaterThanOrEqual(a0, a1) => {
                infix(f, a0, Op::GE_OP, a1, left, right)
            }
            ExprKind::Identifier(name) => f.write_str(name),
            ExprKind::If(cond, then_, else_) => {
                write!(f, "if {} then {} else {}", cond, then_, else_)
            }
            ExprKind::Implies(a0, a1) => {
                infix(f, a0, Op::IMPLIES, a1, left, right)
            }
            ExprKind::LessThan(a0, a1) => {
                infix(f, a0, Op::LT_OP, a1, left, right)
            }
            ExprKind::LessThanOrEqual(a0, a1) => {
                infix(f, a0, Op::LE_OP, a1, left, right)
            }
            ExprKind::Let(decls, body) => {
                write!(f, "let ")?;
                for (i, decl) in decls.iter().enumerate() {
                    if i > 0 {
                        write!(f, "; ")?;
                    }
                    write!(f, "{}", decl)?;
                }
                write!(f, " in {} end", body)
            }
            ExprKind::List(elems) => {
                f.write_str("[")?;
                for (i, e) in elems.iter().enumerate() {
                    if i > 0 {
                        f.write_str(", ")?;
                    }
                    write_sub(f, e, 0, 0)?;
                }
                f.write_str("]")
            }
            ExprKind::Literal(lit) => write!(f, "{}", lit),
            ExprKind::Minus(a0, a1) => infix(f, a0, Op::MINUS, a1, left, right),
            ExprKind::Mod(a0, a1) => infix(f, a0, Op::MOD_OP, a1, left, right),
            ExprKind::Negate(e) => write!(f, "~{}", e),
            ExprKind::NotElem(a0, a1) => {
                infix(f, a0, Op::NOT_ELEM_OP, a1, left, right)
            }
            ExprKind::NotEqual(a0, a1) => {
                infix(f, a0, Op::NE_OP, a1, left, right)
            }
            ExprKind::OpSection(name) => write!(f, "op {}", name),
            ExprKind::OrElse(a0, a1) => {
                infix(f, a0, Op::ORELSE, a1, left, right)
            }
            ExprKind::Ordinal => f.write_str("ordinal"),
            ExprKind::Plus(a0, a1) => infix(f, a0, Op::PLUS, a1, left, right),
            ExprKind::Record(base, fields) => {
                f.write_str("{")?;
                if let Some(b) = base {
                    write!(f, "{} with ", b)?;
                }
                for (i, lf) in fields.iter().enumerate() {
                    if i > 0 {
                        f.write_str(", ")?;
                    }
                    match &lf.label {
                        Some(lbl) => write!(f, "{} = {}", lbl.name, lf.expr)?,
                        None => write!(f, "{}", lf.expr)?,
                    }
                }
                f.write_str("}")
            }
            ExprKind::RecordSelector(name) => write!(f, "#{}", name),
            ExprKind::Times(a0, a1) => {
                infix(f, a0, Op::TIMES_OP, a1, left, right)
            }
            ExprKind::Tuple(elems) => {
                f.write_str("(")?;
                for (i, e) in elems.iter().enumerate() {
                    if i > 0 {
                        f.write_str(", ")?;
                    }
                    write_sub(f, e, 0, 0)?;
                }
                f.write_str(")")
            }
        }
    }
}

/// Writes a sub-expression `e` to `f`, wrapping in parens iff the surrounding
/// precedence `left` / `right` exceeds the expression's own precedence.
fn write_sub(
    f: &mut Formatter<'_>,
    e: &Expr,
    left: u8,
    right: u8,
) -> FmtResult {
    let op = e.kind.prec_op();
    if left > op.left || op.right < right {
        f.write_str("(")?;
        e.kind.unparse(f, 0, 0)?;
        f.write_str(")")
    } else {
        e.kind.unparse(f, left, right)
    }
}

/// Writes an infix binary expression `a0 op a1`, wrapping sub-expressions
/// as required by `op`'s precedence.
fn infix(
    f: &mut Formatter<'_>,
    a0: &Expr,
    op: Op,
    a1: &Expr,
    left: u8,
    right: u8,
) -> FmtResult {
    let paren = left > op.left || op.right < right;
    if paren {
        f.write_str("(")?;
    }
    let (outer_left, outer_right) = if paren { (0, 0) } else { (left, right) };
    write_sub(f, a0, outer_left, op.left)?;
    f.write_str(op.sep)?;
    write_sub(f, a1, op.right, outer_right)?;
    if paren {
        f.write_str(")")?;
    }
    Ok(())
}

impl Display for ExprKind<Expr> {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        self.unparse(f, 0, 0)
    }
}

/// Abstract syntax tree (AST) of a literal.
///
/// Used in expressions and patterns, via [`ExprKind::Literal`] and
/// [`PatKind::Literal`].
#[derive(Clone, Debug)]
pub struct Literal {
    pub kind: LiteralKind,
    pub span: Span,
    pub id: Option<i32>,
}

impl Display for Literal {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        Display::fmt(&self.kind, f)
    }
}

/// Kind of literal.
#[derive(Clone, Debug)]
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
#[derive(Clone, Debug)]
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
#[derive(Clone, Debug)]
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
#[derive(Clone, Debug)]
pub struct Match {
    pub pat: Pat,
    pub expr: Expr,
}

/// Abstract syntax tree (AST) of a step in a query.
#[derive(Clone, Debug)]
pub struct Step {
    pub kind: StepKind,
    pub span: Span,
}

impl Step {}

/// Kind of step in a query.
#[derive(Clone, Debug)]
pub enum StepKind {
    Compute(Box<Expr>),
    Distinct,
    Into(Box<Expr>),

    /// A scan (e.g., "e in emps", "e") or scan-and-join (e.g., "left join d in
    /// depts on e.deptno = d.deptno") in a `from` expression.
    ///
    /// `Scan(p, e, Some(c))` represents `join p in e on c`;
    /// `Scan(p, e, None)` represents `join p in e` or `from p in e`.
    Scan(Box<Pat>, Box<Expr>, Option<Box<Expr>>),

    /// A scan where the pattern is bound to a single expression.
    ///
    /// `ScanEq(p, e)` represents `join p = e`.
    ScanEq(Box<Pat>, Box<Expr>),

    /// A scan over an extent (collection variable).
    ///
    /// `ScanExtent(p)` represents `join p` or `from p`.
    ScanExtent(Box<Pat>),

    Except(bool, Vec<Expr>),
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
    /// Returns the name of the clause. For use in error messages.
    pub(crate) fn clause(&self) -> &'static str {
        match self {
            // lint: sort until '#}'
            StepKind::Compute(_) => "compute",
            StepKind::Distinct => "distinct",
            StepKind::Except(_, _) => "except",
            StepKind::Group(_, _) => "group",
            StepKind::Intersect(_, _) => "intersect",
            StepKind::Into(_) => "into",
            StepKind::Order(_) => "order",
            StepKind::Require(_) => "require",
            StepKind::Scan(_, _, _) => "scan",
            StepKind::ScanEq(_, _) => "join",
            StepKind::ScanExtent(_) => "join",
            StepKind::Skip(_) => "skip",
            StepKind::Take(_) => "take",
            StepKind::Through(_, _) => "through",
            StepKind::Union(_, _) => "union",
            StepKind::Unorder => "unorder",
            StepKind::Where(_) => "where",
            StepKind::Yield(_) => "yield",
        }
    }

    pub fn spanned(&self, span: &Span) -> Step {
        Step {
            kind: self.clone(),
            span: span.clone(),
        }
    }

    /// Returns whether this is a scan-like step (first-class source in a
    /// query): a `from p in e`, `join p in e on cond`, `join p = e`, or
    /// `join p` step.
    pub fn is_scan(&self) -> bool {
        matches!(
            self,
            StepKind::Scan(..)
                | StepKind::ScanEq(..)
                | StepKind::ScanExtent(..)
        )
    }
}

impl Display for Step {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        Display::fmt(&self.kind, f)
    }
}

impl Display for StepKind {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        match self {
            // lint: sort until '#}' where '##StepKind::'
            StepKind::Compute(e) => write!(f, "compute {}", e),
            StepKind::Distinct => f.write_str("distinct"),
            StepKind::Except(distinct, args) => {
                write_set_step(f, "except", *distinct, args)
            }
            StepKind::Group(key, None) => write!(f, "group {}", key),
            StepKind::Group(key, Some(agg)) => {
                write!(f, "group {} compute {}", key, agg)
            }
            StepKind::Intersect(distinct, args) => {
                write_set_step(f, "intersect", *distinct, args)
            }
            StepKind::Into(e) => write!(f, "into {}", e),
            StepKind::Order(e) => write!(f, "order {}", e),
            StepKind::Require(e) => write!(f, "require {}", e),
            StepKind::Scan(pat, exp, None) => {
                write!(f, "{} in ", pat)?;
                write_sub(f, exp, Op::EQ_OP.right, 0)
            }
            StepKind::Scan(pat, exp, Some(cond)) => {
                write!(f, "{} in ", pat)?;
                write_sub(f, exp, Op::EQ_OP.right, 0)?;
                write!(f, " on {}", cond)
            }
            StepKind::ScanEq(pat, exp) => {
                write!(f, "{} = ", pat)?;
                write_sub(f, exp, Op::EQ_OP.right, 0)
            }
            StepKind::ScanExtent(pat) => write!(f, "{}", pat),
            StepKind::Skip(e) => write!(f, "skip {}", e),
            StepKind::Take(e) => write!(f, "take {}", e),
            StepKind::Through(pat, exp) => {
                write!(f, "through {} in {}", pat, exp)
            }
            StepKind::Union(distinct, args) => {
                write_set_step(f, "union", *distinct, args)
            }
            StepKind::Unorder => f.write_str("unorder"),
            StepKind::Where(e) => write!(f, "where {}", e),
            StepKind::Yield(e) => write!(f, "yield {}", e),
        }
    }
}

/// Writes a set-operation step (`union`, `intersect`, `except`).
fn write_set_step(
    f: &mut Formatter<'_>,
    keyword: &str,
    distinct: bool,
    args: &[Expr],
) -> FmtResult {
    f.write_str(keyword)?;
    for (i, arg) in args.iter().enumerate() {
        f.write_str(if i == 0 { " " } else { ", " })?;
        if distinct {
            f.write_str("distinct ")?;
        }
        write!(f, "{}", arg)?;
    }
    Ok(())
}

/// Writes the steps of a query (`from`, `exists`, `forall`), inserting the
/// appropriate separator between consecutive steps: `,` between consecutive
/// scans, `join` before a scan that follows a non-scan step, otherwise a
/// single space.
fn write_query(
    f: &mut Formatter<'_>,
    keyword: &str,
    steps: &[Step],
) -> FmtResult {
    f.write_str(keyword)?;
    let mut prev_scan = false;
    for (i, step) in steps.iter().enumerate() {
        let this_scan = step.kind.is_scan();
        if i == 0 {
            f.write_str(" ")?;
        } else if this_scan && prev_scan {
            f.write_str(", ")?;
        } else if this_scan {
            f.write_str(" join ")?;
        } else {
            f.write_str(" ")?;
        }
        write!(f, "{}", step)?;
        prev_scan = this_scan;
    }
    Ok(())
}

/// Abstract syntax tree (AST) of a pattern.
#[derive(Clone, Debug)]
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
            PatKind::Annotated(p, _) => p.for_each_id_pat(consumer),
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

    /// Returns the implicit label for this pattern, if one can be derived.
    /// Returns Some for identifiers and annotated patterns; None otherwise.
    pub fn implicit_label_opt(&self) -> Option<String> {
        match &self.kind {
            PatKind::Identifier(name) => Some(name.clone()),
            PatKind::Annotated(pat, _type) => pat.implicit_label_opt(),
            _ => None,
        }
    }
}

impl Display for Pat {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        Display::fmt(&self.kind, f)
    }
}

/// Kind of pattern.
///
/// A few names have evolved from Morel-Java.
/// `Constructor` is equivalent to `class ConPat` or `class Con0Pat`;
/// `Cons` is equivalent to `class ConsPat` in Morel-Java.
#[derive(Clone, Debug)]
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
            PatKind::Annotated(pat, typ) => write!(f, "{} : {}", pat, typ),
            PatKind::As(name, pat) => write!(f, "{} as {}", name, pat),
            PatKind::Cons(head, tail) => write!(f, "{} :: {}", head, tail),
            PatKind::Constructor(name, None) => f.write_str(name),
            PatKind::Constructor(name, Some(pat)) => {
                write!(f, "{} {}", name, pat)
            }
            PatKind::Identifier(name) => f.write_str(name),
            PatKind::List(pats) => {
                f.write_str("[")?;
                for (i, p) in pats.iter().enumerate() {
                    if i > 0 {
                        f.write_str(", ")?;
                    }
                    write!(f, "{}", p)?;
                }
                f.write_str("]")
            }
            PatKind::Literal(lit) => write!(f, "{}", lit),
            PatKind::Record(fields, ellipsis) => {
                f.write_str("{")?;
                let mut first = true;
                for field in fields {
                    if !first {
                        f.write_str(", ")?;
                    }
                    first = false;
                    match field {
                        PatField::Labeled(_, name, pat) => {
                            write!(f, "{} = {}", name, pat)?
                        }
                        PatField::Anonymous(_, pat) => write!(f, "{}", pat)?,
                        PatField::Ellipsis(_) => f.write_str("...")?,
                    }
                }
                if *ellipsis {
                    if !first {
                        f.write_str(", ")?;
                    }
                    f.write_str("...")?;
                }
                f.write_str("}")
            }
            PatKind::Tuple(pats) => {
                f.write_str("(")?;
                for (i, p) in pats.iter().enumerate() {
                    if i > 0 {
                        f.write_str(", ")?;
                    }
                    write!(f, "{}", p)?;
                }
                f.write_str(")")
            }
            PatKind::Wildcard => f.write_str("_"),
        }
    }
}

/// Abstract syntax tree (AST) of a field in a record pattern.
/// It can be labeled, anonymous, or ellipsis.
/// For example, `{ label = x, y, ... }` has one of each.
#[derive(Clone, Debug)]
pub enum PatField {
    Labeled(Span, String, Pat), // e.g. `named = x`
    Anonymous(Span, Pat),       // e.g. `y`
    Ellipsis(Span),             // e.g. `...`
}

/// Abstract syntax tree (AST) of a declaration.
#[derive(Clone, Debug)]
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
        Display::fmt(&self.kind, f)
    }
}

/// Kind of declaration.
#[derive(Clone, Debug)]
pub enum DeclKind {
    /// `Val(rec, inst, binds)` represents a value declaration such as
    /// `val rec x = 0 and f = fn i => f(i - 1)`.
    Val(bool, bool, Vec<ValBind>),
    Fun(Vec<FunBind>),
    Over(String),
    Type(Vec<TypeBind>),
    Datatype(Vec<DatatypeBind>),
    Signature(Vec<SigBind>),
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
            DeclKind::Signature(sigs) => fmt_list(f, sigs, " and "),
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
#[derive(Clone, Debug)]
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
#[derive(Clone, Debug)]
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
#[derive(Clone, Debug)]
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
#[derive(Clone, Debug)]
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
#[derive(Clone, Debug)]
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
#[derive(Clone, Debug)]
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

/// Signature binding.
/// For example, `signature STACK = sig ... end`.
#[derive(Clone, Debug)]
pub struct SigBind {
    pub span: Span,
    pub name: String,
    pub specs: Vec<Spec>,
}

impl Display for SigBind {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "signature {} = sig ", self.name)?;
        for spec in &self.specs {
            write!(f, "{}; ", spec)?;
        }
        write!(f, "end")
    }
}

/// Specification within a signature.
#[derive(Clone, Debug)]
pub struct Spec {
    pub kind: SpecKind,
    pub span: Span,
}

impl Display for Spec {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        Display::fmt(&self.kind, f)
    }
}

/// Kind of specification within a signature.
#[derive(Clone, Debug)]
pub enum SpecKind {
    /// Value specification: `val name : type [and name : type]*`
    Val(Vec<ValDesc>),
    /// Type specification: `type ['a] name [= type] [and ...]*`
    Type(Vec<TypeDesc>),
    /// Datatype specification: `datatype ['a] name = con [| con]* [and ...]*`
    Datatype(Vec<DatatypeDesc>),
    /// Exception specification: `exception name [of type] [and ...]*`
    Exception(Vec<ExnDesc>),
}

impl SpecKind {
    pub fn spanned(&self, span: &Span) -> Spec {
        Spec {
            kind: self.clone(),
            span: span.clone(),
        }
    }
}

impl Display for SpecKind {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        match self {
            SpecKind::Val(descs) => {
                write!(f, "val ")?;
                fmt_list(f, descs, " and ")
            }
            SpecKind::Type(descs) => {
                write!(f, "type ")?;
                fmt_list(f, descs, " and ")
            }
            SpecKind::Datatype(descs) => {
                write!(f, "datatype ")?;
                fmt_list(f, descs, " and ")
            }
            SpecKind::Exception(descs) => {
                write!(f, "exception ")?;
                fmt_list(f, descs, " and ")
            }
        }
    }
}

/// Value description in a signature.
/// For example, `empty : 'a stack`.
#[derive(Clone, Debug)]
pub struct ValDesc {
    pub span: Span,
    pub name: String,
    pub type_: Type,
}

impl Display for ValDesc {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "{} : {}", self.name, self.type_)
    }
}

/// Type description in a signature.
/// For example, `type 'a stack` or `type int_pair = int * int`.
#[derive(Clone, Debug)]
pub struct TypeDesc {
    pub span: Span,
    pub type_vars: Vec<String>,
    pub name: String,
    pub type_: Option<Type>,
}

impl Display for TypeDesc {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        if !self.type_vars.is_empty() {
            if self.type_vars.len() == 1 {
                write!(f, "{} ", self.type_vars[0])?;
            } else {
                write!(f, "(")?;
                fmt_list(f, &self.type_vars, ", ")?;
                write!(f, ") ")?;
            }
        }
        write!(f, "{}", self.name)?;
        if let Some(t) = &self.type_ {
            write!(f, " = {}", t)?;
        }
        Ok(())
    }
}

/// Datatype description in a signature.
/// For example, `datatype 'a tree = Leaf | Node of 'a * 'a tree * 'a tree`.
#[derive(Clone, Debug)]
pub struct DatatypeDesc {
    pub span: Span,
    pub type_vars: Vec<String>,
    pub name: String,
    pub constructors: Vec<ConDesc>,
}

impl Display for DatatypeDesc {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        if !self.type_vars.is_empty() {
            if self.type_vars.len() == 1 {
                write!(f, "{} ", self.type_vars[0])?;
            } else {
                write!(f, "(")?;
                fmt_list(f, &self.type_vars, ", ")?;
                write!(f, ") ")?;
            }
        }
        write!(f, "{} = ", self.name)?;
        fmt_list(f, &self.constructors, " | ")
    }
}

/// Constructor description in a datatype specification.
#[derive(Clone, Debug)]
pub struct ConDesc {
    pub span: Span,
    pub name: String,
    pub type_: Option<Type>,
}

impl Display for ConDesc {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "{}", self.name)?;
        if let Some(t) = &self.type_ {
            write!(f, " of {}", t)?;
        }
        Ok(())
    }
}

/// Exception description in a signature.
/// For example, `exception Empty` or `exception Error of string`.
#[derive(Clone, Debug)]
pub struct ExnDesc {
    pub span: Span,
    pub name: String,
    pub type_: Option<Type>,
}

impl Display for ExnDesc {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "{}", self.name)?;
        if let Some(t) = &self.type_ {
            write!(f, " of {}", t)?;
        }
        Ok(())
    }
}

/// Abstract syntax tree (AST) of a type.
#[derive(Clone, PartialEq, Debug)]
pub struct Type {
    pub kind: TypeKind,
    pub span: Span,
    pub id: Option<i32>,
}

impl Display for Type {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
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
            TypeKind::Composite(types) => {
                write!(f, "(")?;
                for (i, t) in types.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", t)?;
                }
                write!(f, ")")
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

#[derive(Clone, Debug)]
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
    /// `Composite(types)` is not really a type, just the argument to type
    /// application. For example, `(int, string) either` comes out of the parser
    /// as `App(Composite([int, string]), Id(either))`.
    Composite(Vec<Type>),
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
#[derive(Clone, Debug)]
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

    /// Expands any [TypeKind::Composite] types in the list to their
    /// constituent types.
    pub fn flatten(types: &[Type]) -> Vec<Type> {
        let mut result = Vec::new();
        Self::flatten_(types, &mut result);
        result
    }

    fn flatten_(types: &[Type], flat_types: &mut Vec<Type>) {
        for t in types {
            match &t.kind {
                TypeKind::Composite(types2) => {
                    Self::flatten_(types2, flat_types);
                }
                _ => {
                    flat_types.push(t.clone());
                }
            }
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
