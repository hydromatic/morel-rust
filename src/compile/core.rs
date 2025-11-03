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

use crate::compile::inliner::Env;
use crate::compile::type_env::Id;
use crate::compile::types::Type;
use crate::eval::code::Span;
use crate::eval::val::Val;
use std::fmt::{Debug, Display, Formatter, Result as FmtResult};
use std::ops::Deref;

/// Core tree of a statement (expression or declaration).
#[derive(Clone, Debug)]
pub struct Statement {
    pub kind: StatementKind,
}

/// Kind of statement.
#[derive(Clone, Debug)]
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
#[derive(Clone, Debug)]
pub enum Expr {
    Literal(Box<Type>, Val),
    Identifier(Box<Type>, String),

    /// `RecordSelector(type, slot)` is a function that returns the `slot`th
    /// field of a record or tuple. `type` is a function type, `record_type`
    /// -> `field_type`.
    RecordSelector(Box<Type>, usize),
    Current(Box<Type>),
    Ordinal(Box<Type>),
    Aggregate(Box<Type>, Box<Expr>, Box<Expr>), // 'over'

    /// `Apply(f, a)` represents `f a`, applying a function to an argument.
    Apply(Box<Type>, Box<Expr>, Box<Expr>, Span),

    // Control structures. (There is no 'If'; use 'Case' instead.)
    Case(Box<Type>, Box<Expr>, Vec<Match>),
    Let(Box<Type>, Vec<Decl>, Box<Expr>),
    Fn(Box<Type>, Vec<Match>),

    // Constructors for data structures
    Tuple(Box<Type>, Vec<Expr>), // e.g. `(x, y, z)`
    List(Box<Type>, Vec<Expr>),  // e.g. `[x, y, z]`

    // Relational expressions
    From(Box<Type>, Vec<Step>),
    Exists(Box<Type>, Vec<Step>),
    Forall(Box<Type>, Vec<Step>),
}

impl Expr {
    /// Creates a tuple expression.
    pub(crate) fn new_tuple(args: &[Expr]) -> Self {
        let types = args.iter().map(|e| *e.type_()).collect::<Vec<_>>();
        let arg_type = Type::Tuple(types);
        Expr::Tuple(Box::new(arg_type), args.to_vec())
    }

    /// Returns this expression's type.
    pub fn type_(&self) -> Box<Type> {
        match self {
            Expr::Aggregate(t, _, _) => t.clone(),
            Expr::Apply(t, _, _, _) => t.clone(),
            Expr::Case(t, _, _) => t.clone(),
            Expr::Current(t) => t.clone(),
            Expr::Exists(t, _) => t.clone(),
            Expr::Fn(t, _) => t.clone(),
            Expr::Forall(t, _) => t.clone(),
            Expr::From(t, _) => t.clone(),
            Expr::Identifier(t, _) => t.clone(),
            Expr::Let(t, _, _) => t.clone(),
            Expr::List(t, _) => t.clone(),
            Expr::Literal(t, _) => t.clone(),
            Expr::Ordinal(t) => t.clone(),
            Expr::RecordSelector(t, _) => t.clone(),
            Expr::Tuple(t, _) => t.clone(),
        }
    }
}

impl Display for Expr {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        match &self {
            // lint: sort until '#}' where '##Expr::'
            Expr::Aggregate(_, a0, a1) => {
                write!(f, "({} over {})", a0, a1)
            }
            Expr::Apply(_, fx, arg, _) => write!(f, "{} {}", fx, arg),
            Expr::Case(_, e, arms) => {
                write!(f, "case {} of ", e)?;
                for (i, match_) in arms.iter().enumerate() {
                    if i > 0 {
                        write!(f, " | ")?;
                    }
                    write!(f, "{} => {}", match_.pat, match_.expr)?;
                }
                Ok(())
            }
            Expr::Current(_) => write!(f, "current"),
            Expr::Exists(_, steps) => write!(f, "exists {:?}", steps),
            Expr::Fn(_, arms) => {
                write!(f, "fn ")?;
                for (i, match_) in arms.iter().enumerate() {
                    if i > 0 {
                        write!(f, " | ")?;
                    }
                    write!(f, "{} => {}", match_.pat, match_.expr)?;
                }
                Ok(())
            }
            Expr::Forall(_, steps) => write!(f, "forall {:?}", steps),
            Expr::From(_, steps) => write!(f, "from {:?}", steps),
            Expr::Identifier(_, name) => write!(f, "{}", name),
            Expr::Let(_, decls, body) => {
                write!(f, "let ")?;
                for decl in decls {
                    write!(f, "{}; ", decl)?;
                }
                write!(f, "in {}", body)
            }
            Expr::List(_, elems) => {
                let elems_str = elems
                    .iter()
                    .map(|e| format!("{}", e))
                    .collect::<Vec<_>>()
                    .join(", ");
                write!(f, "[{}]", elems_str)
            }
            Expr::Literal(_, lit) => write!(f, "{}", lit),
            Expr::Ordinal(_) => write!(f, "ordinal"),
            Expr::RecordSelector(_, name) => write!(f, "#{}", name),
            Expr::Tuple(_, elems) => {
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

/// Match in a `case`.
#[derive(Clone, Debug)]
pub struct Match {
    pub pat: Pat,
    pub expr: Expr,
}

impl Display for Match {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "{} => {}", self.pat, self.expr)
    }
}

/// Abstract syntax tree (AST) of a step in a query.
#[derive(Clone, Debug)]
pub struct Step {
    pub kind: StepKind,
}

impl Step {}

/// Kind of step in a query.
#[derive(Clone, Debug)]
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
#[derive(Clone, PartialEq, Debug)]
pub enum Pat {
    Wildcard(Box<Type>),
    /// `Identifier(t, name)` is a pattern that matches any expression and
    /// binds it to an identifier. For example, `x`.
    Identifier(Box<Type>, String),
    /// `As(t, name, pat)` is a pattern that matches if its subpattern matches,
    /// and if so, binds the identifier. For example, `(x, y) as z`.
    As(Box<Type>, String, Box<Pat>),
    /// `Constructor(t, name, pat)` is a pattern that matches a constructor
    /// (with or without an argument). For example, `EMPTY` or `LEAF x` or
    /// `NODE (left, right)`.
    Constructor(Box<Type>, String, Option<Box<Pat>>),
    /// `Literal(t, val)` is a pattern that matches a literal, e.g. `1` or
    /// `"foo"`. It does not bind any values.
    Literal(Box<Type>, Val),
    /// `Tuple(t, pats)` is a pattern that matches a tuple. The match succeeds
    /// if all elements of a tuple match, e.g. `(x, y, z)` or `(1, _, z)`.
    Tuple(Box<Type>, Vec<Pat>),
    /// `Tuple(t, pats)` is a pattern that matches a list. The match succeeds
    /// if all elements of a list match, e.g. `[x, y, z]` or `[1, _, z]`. It
    /// can also be written `x :: y :: z :: nil`.
    List(Box<Type>, Vec<Pat>),
    /// `Record(t, fields, ellipsis)` is a pattern that matches a record. The
    /// match succeeds if all fields match. For example, `{a = 1, b = (p, q),
    /// ...}` bind `p` and `q` if successful.
    Record(Box<Type>, Vec<PatField>, bool),
    /// `Cons(t, head, tail)` is a pattern that matches a list. For example,
    /// `1 :: rest`.
    Cons(Box<Type>, Box<Pat>, Box<Pat>),
}

impl Pat {
    /// Returns the name of this pattern if it is an identifier or `as`,
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
            // lint: sort until '#}' where '##Pat::'
            Pat::As(t, _, _) => t.clone(),
            Pat::Cons(t, _, _) => t.clone(),
            Pat::Constructor(t, _, _) => t.clone(),
            Pat::Identifier(t, _) => t.clone(),
            Pat::List(t, _) => t.clone(),
            Pat::Literal(t, _) => t.clone(),
            Pat::Record(t, _, _) => t.clone(),
            Pat::Tuple(t, _) => t.clone(),
            Pat::Wildcard(t) => t.clone(),
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
            Pat::Tuple(_, pats) if pats.is_empty() => {
                // Unit pattern - no bindings to process
            }
            _ => {
                todo!("{:?}", self);
            }
        }
    }

    /// Calls a given function for each atomic identifier in this pattern.
    /// Since core doesn't have IDs, we'll use 0 as a placeholder.
    pub(crate) fn for_each_id_pat(
        &self,
        consumer: &mut impl FnMut((&Type, &str)),
    ) {
        match self {
            // lint: sort until '#}' where '##Pat::'
            Pat::Cons(_, head, tail) => {
                head.for_each_id_pat(consumer);
                tail.for_each_id_pat(consumer);
            }
            Pat::Constructor(_, _, pat) => {
                if let Some(p) = pat {
                    p.for_each_id_pat(consumer);
                }
            }
            Pat::Identifier(t, name) => (*consumer)((t, name.as_str())),
            Pat::Record(_, pat_fields, _) => {
                for field in pat_fields {
                    match field {
                        PatField::Labeled(_, p) => p.for_each_id_pat(consumer),
                        PatField::Anonymous(p) => p.for_each_id_pat(consumer),
                        PatField::Ellipsis => {}
                    }
                }
            }
            Pat::Tuple(_, pats) => {
                pats.iter().for_each(|p| p.for_each_id_pat(consumer))
            }
            _ => todo!("{:?}", self),
        }
    }
}

impl Display for Pat {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        match &self {
            // lint: sort until '#}' where '##Pat::'
            Pat::As(_, name, pat) => write!(f, "{} as {}", pat, name),
            Pat::Cons(_, head, tail) => write!(f, "{} :: {}", head, tail),
            Pat::Constructor(_, name, None) => write!(f, "{}", name),
            Pat::Constructor(_, name, Some(pat)) => {
                write!(f, "{} {}", name, pat)
            }
            Pat::Identifier(_, name) => write!(f, "{}", name),
            Pat::List(_, pats) => {
                let pats_str = pats
                    .iter()
                    .map(|p| format!("{}", p))
                    .collect::<Vec<_>>()
                    .join(", ");
                write!(f, "[{}]", pats_str)
            }
            Pat::Literal(_, val) => write!(f, "{}", val),
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
            Pat::Tuple(_, pats) => {
                let pats_str = pats
                    .iter()
                    .map(|p| format!("{}", p))
                    .collect::<Vec<_>>()
                    .join(", ");
                write!(f, "({})", pats_str)
            }
            Pat::Wildcard(_) => write!(f, "_"),
        }
    }
}

/// Abstract syntax tree (AST) of a field in a record pattern.
/// It can be labeled, anonymous, or ellipsis.
/// For example, `{ label = x, y, ... }` has one of each.
#[derive(Clone, PartialEq, Debug)]
pub enum PatField {
    Labeled(String, Box<Pat>), // e.g. `named = x`
    Anonymous(Box<Pat>),       // e.g. `y`
    Ellipsis,                  // e.g. `...`
}

/// Declaration.
#[derive(Clone, Debug)]
pub enum Decl {
    /// Non-recursive value binding.
    NonRecVal(Box<ValBind>),
    /// Recursive value binding.
    RecVal(Vec<ValBind>),
    Over(String),
    Type(Vec<TypeBind>),
    Datatype(Vec<DatatypeBind>),
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
            action(&b.pat, &b.expr, &b.overload_pat);
        }
    }

    pub(crate) fn for_each_id_pat(&self, mut p0: impl FnMut((&Type, &str))) {
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

    pub(crate) fn transform_env(&self, envs: &mut Vec<Env>) {
        match self {
            Decl::NonRecVal(val_bind) => {
                let mut to_add = Vec::new();
                val_bind.pat.for_each_id_pat(&mut |(t, name)| {
                    to_add.push((t.clone(), name.to_string()));
                });

                let base_idx = envs.len() - 1;
                for (i, (t, name)) in to_add.into_iter().enumerate() {
                    let idx = base_idx + i;
                    // Get a reference through index to avoid borrowing the
                    // entire vec
                    let env_ptr = &envs[idx] as *const Env;
                    unsafe {
                        let next_env = (*env_ptr).child_none(&name, &t);
                        envs.push(next_env);
                    }
                }
            }
            Decl::RecVal(_) => todo!(".transform_env() for RecVal"),
            Decl::Over(_) => {}
            Decl::Type(_) => {}
            Decl::Datatype(_) => {}
        }
    }
}

impl Display for Decl {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        match self {
            // lint: sort until '#}' where '##Decl::'
            Decl::Datatype(datatypes) => {
                write!(f, "datatype ")?;
                fmt_list(f, datatypes, "; ")
            }
            Decl::NonRecVal(bind) => write!(f, "val {}", bind),
            Decl::Over(name) => write!(f, "over {}", name),
            Decl::RecVal(binds) => {
                write!(f, "val rec ")?;
                fmt_list(f, binds, " and ")
            }
            Decl::Type(types) => {
                write!(f, "type ")?;
                fmt_list(f, types, "; ")
            }
        }
    }
}

/// Value binding.
#[derive(Clone, Debug)]
pub struct ValBind {
    pub pat: Pat,
    pub t: Type,
    pub expr: Expr,
    pub overload_pat: Option<Box<Id>>,
}

impl ValBind {
    /// Creates a value binding with the given pattern, type annotation, and
    /// expression.
    pub fn of(pat: &Pat, t: &Type, expr: &Expr) -> Self {
        ValBind {
            pat: pat.clone(),
            t: t.clone(),
            expr: expr.clone(),
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
#[derive(Clone, Debug)]
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
#[derive(Clone, Debug)]
pub struct FunMatch {
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
