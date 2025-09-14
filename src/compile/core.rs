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

use crate::compile::type_env::Id;
use crate::compile::types::Type;
use crate::eval::val::Val;
use std::fmt::{Debug, Display, Formatter, Result as FmtResult};
use std::ops::Deref;

/// Core tree of a statement (expression or declaration).
#[derive(Debug, Clone)]
pub struct Statement {
    pub kind: StatementKind,
}

/// Kind of statement.
#[derive(Debug, Clone)]
pub enum StatementKind {
    Expr(Expr),
    Decl(Decl),
}

impl Display for StatementKind {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        match &self {
            StatementKind::Expr(e) => write!(f, "{}", e),
            StatementKind::Decl(d) => write!(f, "{}", d),
        }
    }
}

/// Expression.
#[allow(clippy::vec_box)]
#[derive(Debug, Clone)]
pub enum Expr {
    Literal(Box<Type>, Val),
    Identifier(Box<Type>, String),

    /// `RecordSelector(type, slot)` is a function that returns the `slot`th
    /// field of a record or tuple. `type` is a function type, `record_type`
    /// -> `field_type`.
    RecordSelector(Box<Type>, usize),
    Current(Box<Type>),
    Ordinal(Box<Type>),

    // Infix binary operators
    Plus(Box<Type>, Box<Expr>, Box<Expr>),
    Aggregate(Box<Type>, Box<Expr>, Box<Expr>), // 'over'

    /// `Apply(f, a)` represents `f a`, applying a function to an argument.
    Apply(Box<Type>, Box<Expr>, Box<Expr>),

    // Control structures
    If(Box<Type>, Box<Expr>, Box<Expr>, Box<Expr>),
    Case(Box<Type>, Box<Expr>, Vec<Match>),
    Let(Box<Type>, Vec<Decl>, Box<Expr>),
    Fn(Box<Type>, Vec<Match>),

    // Constructors for data structures
    Tuple(Box<Type>, Vec<Box<Expr>>), // e.g. `(x, y, z)`
    List(Box<Type>, Vec<Box<Expr>>),  // e.g. `[x, y, z]`

    // Relational expressions
    From(Box<Type>, Vec<Step>),
    Exists(Box<Type>, Vec<Step>),
    Forall(Box<Type>, Vec<Step>),
}

impl Expr {
    /// Returns this expression's type.
    pub fn type_(&self) -> Box<Type> {
        match self {
            Expr::Literal(t, _) => t.clone(),
            Expr::Identifier(t, _) => t.clone(),
            Expr::RecordSelector(t, _) => t.clone(),
            Expr::Current(t) => t.clone(),
            Expr::Ordinal(t) => t.clone(),
            Expr::Plus(t, _, _) => t.clone(),
            Expr::Aggregate(t, _, _) => t.clone(),
            Expr::Apply(t, _, _) => t.clone(),
            Expr::If(t, _, _, _) => t.clone(),
            Expr::Case(t, _, _) => t.clone(),
            Expr::Let(t, _, _) => t.clone(),
            Expr::Fn(t, _) => t.clone(),
            Expr::Tuple(t, _) => t.clone(),
            Expr::List(t, _) => t.clone(),
            Expr::From(t, _) => t.clone(),
            Expr::Exists(t, _) => t.clone(),
            Expr::Forall(t, _) => t.clone(),
        }
    }
}

impl Display for Expr {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        match &self {
            Expr::Identifier(_t, name) => write!(f, "{}", name),
            Expr::Literal(_t, lit) => write!(f, "{}", lit),
            Expr::RecordSelector(_t, name) => write!(f, "#{}", name),
            Expr::Current(_t) => write!(f, "current"),
            Expr::Ordinal(_t) => write!(f, "ordinal"),
            Expr::Plus(_t, lhs, rhs) => write!(f, "({} + {})", lhs, rhs),
            Expr::Aggregate(_t, lhs, rhs) => {
                write!(f, "({} over {})", lhs, rhs)
            }
            Expr::Apply(_t, fx, arg) => write!(f, "{} {}", fx, arg),
            Expr::If(_t, cond, then_, else_) => {
                write!(f, "if {} then {} else {}", cond, then_, else_)
            }
            Expr::Case(_t, e, arms) => {
                write!(f, "case {} of ", e)?;
                for (i, match_) in arms.iter().enumerate() {
                    if i > 0 {
                        write!(f, " | ")?;
                    }
                    write!(f, "{} => {}", match_.pat, match_.expr)?;
                }
                Ok(())
            }
            Expr::Let(_t, decls, body) => {
                write!(f, "let ")?;
                for decl in decls {
                    write!(f, "{}; ", decl)?;
                }
                write!(f, "in {}", body)
            }
            Expr::Fn(_t, arms) => {
                write!(f, "fn ")?;
                for (i, match_) in arms.iter().enumerate() {
                    if i > 0 {
                        write!(f, " | ")?;
                    }
                    write!(f, "{} => {}", match_.pat, match_.expr)?;
                }
                Ok(())
            }
            Expr::Tuple(_t, elems) => {
                let elems_str = elems
                    .iter()
                    .map(|e| format!("{}", e))
                    .collect::<Vec<_>>()
                    .join(", ");
                write!(f, "({})", elems_str)
            }
            Expr::List(_t, elems) => {
                let elems_str = elems
                    .iter()
                    .map(|e| format!("{}", e))
                    .collect::<Vec<_>>()
                    .join(", ");
                write!(f, "[{}]", elems_str)
            }
            Expr::From(_t, steps) => write!(f, "from {:?}", steps),
            Expr::Exists(_t, steps) => write!(f, "exists {:?}", steps),
            Expr::Forall(_t, steps) => write!(f, "forall {:?}", steps),
        }
    }
}

/// Match in a `case`.
#[derive(Debug, Clone)]
pub struct Match {
    pub pat: Box<Pat>,
    pub expr: Box<Expr>,
}

/// Abstract syntax tree (AST) of a step in a query.
#[derive(Debug, Clone)]
pub struct Step {
    pub kind: StepKind,
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
    pub fn spanned(&self) -> Step {
        Step { kind: self.clone() }
    }
}

/// Pattern in core representation.
#[derive(Debug, Clone)]
pub enum Pat {
    Wildcard(Box<Type>),
    Identifier(Box<Type>, String),
    As(Box<Type>, String, Box<Pat>),
    Constructor(Box<Type>, String, Option<Box<Pat>>), // `Empty` or `Leaf x`
    Literal(Box<Type>, Val),
    Tuple(Box<Type>, Vec<Pat>),
    List(Box<Type>, Vec<Pat>),
    Record(Box<Type>, Vec<PatField>, bool),
    Cons(Box<Type>, Box<Pat>, Box<Pat>), // e.g. `x :: xs`
}

impl Pat {
    /// Returns the name of this pattern, if it is an identifier or `as`,
    /// otherwise None.
    pub fn name(&self) -> Option<String> {
        match self {
            Pat::Identifier(_, name) | Pat::As(_, name, _) => {
                Some(name.clone())
            }
            _ => None,
        }
    }

    /// Returns this pattern's type.
    pub fn type_(&self) -> Box<Type> {
        match self {
            Pat::Wildcard(t) => t.clone(),
            Pat::Identifier(t, _) => t.clone(),
            Pat::As(t, _, _) => t.clone(),
            Pat::Constructor(t, _, _) => t.clone(),
            Pat::Literal(t, _) => t.clone(),
            Pat::Tuple(t, _) => t.clone(),
            Pat::List(t, _) => t.clone(),
            Pat::Record(t, _, _) => t.clone(),
            Pat::Cons(t, _, _) => t.clone(),
        }
    }
    pub(crate) fn bind_recurse(
        &self,
        val: &Val,
        consumer: &mut dyn FnMut(Box<Pat>, &Val),
    ) {
        match self {
            Pat::Identifier(_, _name) => {
                consumer(Box::new(self.clone()), val);
            }
            _ => {
                todo!("{:?}", self);
            }
        }
    }
    /// Calls a given function for each atomic identifier in this pattern.
    /// Since core doesn't have IDs, we'll use 0 as a placeholder.
    pub(crate) fn for_each_id_pat(&self, consumer: &mut impl FnMut(&str)) {
        match self {
            Pat::Identifier(_, name) => (*consumer)(name.as_str()),
            Pat::Tuple(_, pats) => {
                pats.iter().for_each(|p| p.for_each_id_pat(consumer))
            }
            Pat::Record(_, pat_fields, _) => {
                for field in pat_fields {
                    match field {
                        PatField::Labeled(_, p) => p.for_each_id_pat(consumer),
                        PatField::Anonymous(p) => p.for_each_id_pat(consumer),
                        PatField::Ellipsis => {}
                    }
                }
            }
            _ => todo!("{:?}", self),
        }
    }
}

impl Display for Pat {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        match &self {
            Pat::Wildcard(_) => write!(f, "_"),
            Pat::Identifier(_, name) => write!(f, "{}", name),
            Pat::As(_, name, pat) => write!(f, "{} as {}", pat, name),
            Pat::Constructor(_, name, Some(pat)) => {
                write!(f, "{} {}", name, pat)
            }
            Pat::Constructor(_, name, None) => write!(f, "{}", name),
            Pat::Literal(_, val) => write!(f, "{}", val),
            Pat::Tuple(_, pats) => {
                let pats_str = pats
                    .iter()
                    .map(|p| format!("{}", p))
                    .collect::<Vec<_>>()
                    .join(", ");
                write!(f, "({})", pats_str)
            }
            Pat::List(_, pats) => {
                let pats_str = pats
                    .iter()
                    .map(|p| format!("{}", p))
                    .collect::<Vec<_>>()
                    .join(", ");
                write!(f, "[{}]", pats_str)
            }
            Pat::Cons(_, head, tail) => write!(f, "{} :: {}", head, tail),
            Pat::Record(_, fields, ellipsis) => {
                let fields_str = fields
                    .iter()
                    .map(|field| match field {
                        PatField::Labeled(name, pat) => {
                            format!("{} = {}", name, pat)
                        }
                        PatField::Anonymous(pat) => format!("{}", pat),
                        PatField::Ellipsis => "...".to_string(),
                    })
                    .collect::<Vec<_>>()
                    .join(", ");
                if *ellipsis {
                    write!(f, "{{{}, ...}}", fields_str)
                } else {
                    write!(f, "{{{}}}", fields_str)
                }
            }
        }
    }
}

/// Abstract syntax tree (AST) of a field in a record pattern.
/// It can be labeled, anonymous, or ellipsis.
/// For example, `{ label = x, y, ... }` has one of each.
#[derive(Debug, Clone)]
pub enum PatField {
    Labeled(String, Box<Pat>), // e.g. `named = x`
    Anonymous(Box<Pat>),       // e.g. `y`
    Ellipsis,                  // e.g. `...`
}

impl Decl {
    /// Invokes an action for each top-level binding.
    ///
    /// If a recursive val has multiple arms, each of those arms is a binding.
    /// If any of the arms binds a composite pattern, it is wrapped in an `as`.
    /// Consider:
    ///
    /// ```sml
    /// val w = 1
    /// and (x, y) = (2, 3)
    /// ```
    ///
    /// Translation introduces an extra `as` binding, `z`, to capture the
    /// composite pattern:
    ///
    /// ```sml
    /// val w = 1
    /// and (x, y) as z = (2, 3)
    /// ```
    ///
    /// `z` is marked *skipped* and the sub-bindings appear in the output.
    /// Thus, the output is
    ///
    /// ```text
    /// val w = 1 : int
    /// val x = 2 : int
    /// val y = 3 : int
    /// ```
    pub(crate) fn for_each_binding<F>(&self, action: &mut F)
    where
        F: FnMut(&Pat, &Expr, &Option<Box<Id>>),
    {
        match &self {
            Decl::NonRecVal(b) => call(action, b.deref()),
            Decl::RecVal(binds) => {
                for b in binds {
                    call(action, b);
                }
            }
            _ => {
                // Other kinds of declaration don't have bindings.
            }
        }

        fn call<F>(action: &mut F, b: &ValBind)
        where
            F: FnMut(&Pat, &Expr, &Option<Box<Id>>),
        {
            action(b.pat.as_ref(), b.expr.as_ref(), &b.overload_pat);
        }
    }

    pub(crate) fn for_each_id_pat(&self, mut p0: impl FnMut(&str)) {
        match self {
            Decl::NonRecVal(val_bind) => val_bind.pat.for_each_id_pat(&mut p0),
            Decl::RecVal(val_binds) => {
                for val_bind in val_binds {
                    val_bind.pat.for_each_id_pat(&mut p0)
                }
            }
            _ => todo!(),
        }
    }

    pub fn from_statement(statement: &Statement) -> Self {
        match &statement.kind {
            StatementKind::Decl(d) => d.clone(),
            _ => panic!("expected declaration"),
        }
    }
}

/// Declaration.
#[derive(Debug, Clone)]
pub enum Decl {
    /// Non-recursive value binding.
    NonRecVal(Box<ValBind>),
    /// Recursive value binding.
    RecVal(Vec<ValBind>),
    Over(String),
    Type(Vec<TypeBind>),
    Datatype(Vec<DatatypeBind>),
}

impl Display for Decl {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        match self {
            Decl::NonRecVal(bind) => write!(f, "val {}", bind),
            Decl::RecVal(binds) => {
                write!(f, "val rec ")?;
                fmt_list(f, binds, " and ")
            }
            Decl::Over(name) => write!(f, "over {}", name),
            Decl::Type(types) => {
                write!(f, "type ")?;
                fmt_list(f, types, "; ")
            }
            Decl::Datatype(datatypes) => {
                write!(f, "datatype ")?;
                fmt_list(f, datatypes, "; ")
            }
        }
    }
}

/// Value binding.
#[derive(Debug, Clone)]
pub struct ValBind {
    pub pat: Box<Pat>,
    pub t: Box<Type>,
    pub expr: Box<Expr>,
    pub overload_pat: Option<Box<Id>>,
}

impl ValBind {
    /// Creates a value binding with the given pattern, type annotation, and
    /// expression.
    pub fn of(pat: Box<Pat>, t: Box<Type>, expr: Box<Expr>) -> Self {
        ValBind {
            pat,
            t,
            expr,
            overload_pat: None,
        }
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
    pub name: String,
    pub pats: Vec<Pat>,
    pub type_: Option<Box<Type>>,
    pub expr: Box<Expr>,
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
