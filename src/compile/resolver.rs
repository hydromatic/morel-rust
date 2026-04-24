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

use crate::compile::core::{
    ConBind as CoreConBind, DatatypeBind as CoreDatatypeBind, Decl as CoreDecl,
    Expr as CoreExpr, Match as CoreMatch, Pat as CorePat,
    PatField as CorePatField, StepKind as CoreStepKind,
    TypeBind as CoreTypeBind, ValBind as CoreValBind,
};
use crate::compile::from_builder::FromBuilder;
use crate::compile::inliner::Env;
use crate::compile::library;
use crate::compile::library::{BuiltIn, BuiltInFunction};
use crate::compile::postfix::{PostfixKind, postfix_dispatch};
use crate::compile::span::Span;
use crate::compile::type_resolver::{Resolved, TypeMap, Typed};
use crate::compile::types::{PrimitiveType, Type};
use crate::eval::val::Val;
use crate::syntax::ast::{
    DatatypeBind, Decl, DeclKind, Expr, ExprKind, Literal, LiteralKind, Match,
    Pat, PatField, PatKind, Step as AstStep, StepKind as AstStepKind,
    Type as AstType, TypeBind, TypeKind, ValBind,
};
use crate::syntax::parser;
use crate::unify::unifier::Var;
use std::cell::RefCell;
use std::collections::{HashSet, VecDeque};

/// Converts an AST to a Core tree.
pub fn resolve(resolved: &Resolved) -> (CoreDecl, Vec<(String, Span)>) {
    let resolver = Resolver::new(&resolved.type_map, resolved.base_line);
    let decl = resolver.resolve_decl(&resolved.decl);
    (decl, resolver.errors.into_inner())
}

/// Converts an AST to a Core tree.
///
/// There are several differences between AST and Core:
///
/// * AST nodes have [crate::syntax::ast::Span] and id (which indexes into a
///   [TypeMap]), where Core nodes have a [Type].
/// * AST has expression types for syntactic classes.
///   [ExprKind::Plus],
///   [ExprKind::Minus],
///   [ExprKind::Times],
///   [ExprKind::Divide],
///   [ExprKind::Div],
///   [ExprKind::Mod],
///   [ExprKind::Equal],
///   [ExprKind::NotEqual],
///   [ExprKind::LessThan],
///   [ExprKind::LessThanOrEqual],
///   [ExprKind::GreaterThan],
///   [ExprKind::GreaterThanOrEqual],
///   [ExprKind::Elem],
///   [ExprKind::NotElem],
///   [ExprKind::AndAlso],
///   [ExprKind::OrElse] all become [CoreExpr::Apply].
/// * Core has no 'if'. [ExprKind::If] becomes a [CoreExpr::Case].
/// * Core has no equivalent of [ExprKind::Annotated] and [PatKind::Annotated]
///   because every Core expression and pattern has a type.
/// * Core has no direct equivalent of [ExprKind::Record] or [PatKind::Record].
///   Records and tuples both become a [CoreExpr::Tuple] or [CorePat::Tuple].
/// * Core has no equivalent of [Literal]. A [CoreExpr::Literal] contains a
///   [Val].
/// * AST's [DeclKind::Val] and [DeclKind::Fun] become
///   [CoreDecl::NonRecVal] and [CoreDecl::RecVal].
pub struct Resolver<'a> {
    type_map: &'a TypeMap,
    base_line: usize,
    /// Errors detected during resolution (e.g. field-not-found).
    errors: RefCell<Vec<(String, Span)>>,
    /// Names of user-defined functions whose first parameter is
    /// (or contains) `self`, so the postfix dispatcher can rewrite
    /// `x.name arg` into a direct application to `name`. See
    /// hydromatic/morel#346.
    self_fns: RefCell<HashSet<String>>,
}

/// Helper struct representing a pattern-expression pair with position info.
#[derive(Clone, Debug)]
struct PatExpr {
    pat: CorePat,
    expr: CoreExpr,
    /// Source span covering the pattern and the expression. Used to
    /// report the location of a 'Bind' exception when the pattern fails
    /// to match the value.
    span: Option<Span>,
}

/// Resolved value declaration that mirrors the Java ResolvedValDecl.
#[derive(Clone, Debug)]
struct ResolvedValDecl {
    rec: bool,
    composite: bool,
    pat_exps: Vec<PatExpr>,
    pat: CorePat,
    expr: CoreExpr,
}

impl ResolvedValDecl {
    /// Converts this resolved declaration to a let expression.
    /// This is the Rust translation of the Java toExp method.
    fn to_exp(&self, result_expr: &CoreExpr) -> CoreExpr {
        if self.rec {
            // Recursive case: create RecVal with all bindings.
            let val_binds: Vec<CoreValBind> = self
                .pat_exps
                .iter()
                .map(|pat_exp| CoreValBind {
                    pat: pat_exp.pat.clone(),
                    t: *pat_exp.pat.type_(),
                    expr: pat_exp.expr.clone(),
                    overload_pat: None,
                    span: pat_exp.span.clone(),
                })
                .collect();

            let decl = CoreDecl::RecVal(val_binds);
            return CoreExpr::Let(
                result_expr.type_(),
                vec![decl],
                Box::new(result_expr.clone()),
            );
        } else if !self.composite && self.pat_exps.len() == 1 {
            // Simple non-recursive case: single identifier pattern.
            let pat_exp = &self.pat_exps[0];
            if let CorePat::Identifier(_, _) = pat_exp.pat {
                let val_bind = CoreValBind {
                    pat: pat_exp.pat.clone(),
                    t: *pat_exp.pat.type_(),
                    expr: pat_exp.expr.clone(),
                    overload_pat: None,
                    span: pat_exp.span.clone(),
                };

                let decl = CoreDecl::NonRecVal(Box::new(val_bind));
                return CoreExpr::Let(
                    result_expr.type_(),
                    vec![decl],
                    Box::new(result_expr.clone()),
                );
            }
        }

        // Complex pattern case: allocate intermediate variable.
        // Generate a unique name for the intermediate variable.
        let temp_name =
            format!("temp_var_{}", std::ptr::addr_of!(self) as usize);
        let expr_type = self.expr.type_();

        // Create intermediate identifier pattern.
        let temp_pat =
            CorePat::Identifier(expr_type.clone(), temp_name.clone());

        // Create the intermediate binding.
        let temp_val_bind = CoreValBind {
            pat: temp_pat.clone(),
            t: *expr_type.clone(),
            expr: self.expr.clone(),
            overload_pat: None,
            span: None,
        };

        // Create an identifier expression for the temp variable.
        let temp_id = Box::new(CoreExpr::Identifier(expr_type, temp_name));

        // Create the case expression to match the complex pattern.
        let match_ = CoreMatch {
            pat: self.pat.clone(),
            expr: result_expr.clone(),
        };

        let case_expr = Box::new(CoreExpr::Case(
            self.pat.type_(),
            temp_id,
            vec![match_],
            Span::new("stdIn"),
        ));

        // Create the let expression.
        let decl = CoreDecl::NonRecVal(Box::new(temp_val_bind));
        CoreExpr::Let(case_expr.type_(), vec![decl], case_expr)
    }
}

impl<'a> Resolver<'a> {
    /// Creates a new resolver with the given type map.
    pub fn new(type_map: &'a TypeMap, base_line: usize) -> Self {
        Self {
            type_map,
            base_line,
            errors: RefCell::new(Vec::new()),
            self_fns: RefCell::new(HashSet::new()),
        }
    }

    /// Records function names whose first parameter is `self`, so
    /// postfix calls against receivers of matching types can be
    /// rewritten into direct applications. Called from `resolve_decl`
    /// on each `DeclKind::Fun` and from `ExprKind::Let` before
    /// resolving the body.
    fn register_self_fns(&self, decls: &[Decl]) {
        for decl in decls {
            match &decl.kind {
                DeclKind::Fun(funs) => {
                    for fb in funs {
                        if fb.matches.iter().any(match_has_self_first_param) {
                            self.self_fns.borrow_mut().insert(fb.name.clone());
                        }
                    }
                }
                DeclKind::Val(_, _, val_binds) => {
                    // `fun name self = …` desugars to
                    // `val rec name = fn self => …`. Detect that
                    // shape: identifier pattern bound to a function
                    // expression whose first clause has `self` as its
                    // first pattern.
                    for vb in val_binds {
                        if let PatKind::Identifier(fn_name) = &vb.pat.kind
                            && fn_expr_has_self_first_param(&vb.expr)
                        {
                            self.self_fns.borrow_mut().insert(fn_name.clone());
                        }
                    }
                }
                _ => {}
            }
        }
    }

    /// Returns the type map for this resolver.
    pub fn type_map(&self) -> &TypeMap {
        self.type_map
    }

    /// Resolves an AST declaration to a core declaration.
    pub(crate) fn resolve_decl(&self, decl: &Decl) -> CoreDecl {
        match &decl.kind {
            // lint: sort until '#}' where '##DeclKind::'
            DeclKind::Datatype(datatype_binds) => CoreDecl::Datatype(
                datatype_binds
                    .iter()
                    .map(|db| self.resolve_datatype_bind(db))
                    .collect(),
            ),
            DeclKind::Fun(_) => {
                unreachable!("Should have been desugared already")
            }
            DeclKind::Over(name) => CoreDecl::Over(name.clone()),
            DeclKind::Signature(_) => {
                // Signatures are not yet implemented in the core language.
                // For now, we treat them as no-ops by creating a unit
                // binding.
                // TODO: Implement signature resolution once structures are
                // added.
                let unit_type = Box::new(Type::Primitive(PrimitiveType::Unit));
                CoreDecl::NonRecVal(Box::new(CoreValBind {
                    pat: CorePat::Tuple(unit_type.clone(), vec![]),
                    t: *unit_type.clone(),
                    expr: CoreExpr::Tuple(unit_type, vec![]),
                    overload_pat: None,
                    span: None,
                }))
            }
            DeclKind::Type(type_binds) => CoreDecl::Type(
                type_binds
                    .iter()
                    .map(|tb| self.resolve_type_bind(tb))
                    .collect(),
            ),
            DeclKind::Val(rec, _overload, val_binds) => {
                // Uses the new resolve_val_decl method.
                let resolved_val_decl = self.resolve_val_decl(val_binds, *rec);

                // Use the expression's type for the val binding.
                // For query expressions (From), the FromBuilder
                // computes the authoritative collection type
                // (List vs Bag) via the `ordered` flag (morel#273).
                let to_val_bind = |pe: &PatExpr| {
                    // For query expressions (From) whose type is a
                    // collection (List or Bag), use the expr's type
                    // which has the correct collection kind from
                    // FromBuilder's `ordered` flag (morel#273).
                    // For other expressions (including exists/forall
                    // which return bool), use the pat's type which
                    // preserves type aliases.
                    // Use FromBuilder's type only for queries that
                    // return a collection. Queries ending in Exists
                    // (returns bool), Compute (returns scalar), or
                    // Into (returns fn result) have non-collection
                    // output types.
                    // Use the expr's type when it's a collection and
                    // differs from the pat's type in list/bag wrapping.
                    // This handles both From expressions (with ordered
                    // flag from FromBuilder) and simplified queries
                    // (where build_simplify returns the scan expression
                    // directly, e.g. `from i in intBag yield i` →
                    // `intBag`).
                    let expr_type = pe.expr.type_();
                    let pat_type = pe.pat.type_();
                    // If type inference left the pattern type as an
                    // unresolved variable (e.g., the bound expression
                    // is a postfix method call that the inference pass
                    // couldn't recognize) but the resolved expression
                    // has a concrete type, prefer the expression type.
                    // See hydromatic/morel#346.
                    let t = match (expr_type.as_ref(), pat_type.as_ref()) {
                        (Type::Bag(_), Type::List(_)) => {
                            expr_type.as_ref().clone()
                        }
                        (Type::List(_) | Type::Bag(_), _)
                            if matches!(pe.expr, CoreExpr::From(_, _))
                                && !pe.expr.steps().is_some_and(|steps| {
                                    steps.iter().any(|s| {
                                        matches!(
                                            s.kind,
                                            CoreStepKind::Exists
                                                | CoreStepKind::Compute(_)
                                        )
                                    })
                                }) =>
                        {
                            expr_type.as_ref().clone()
                        }
                        (_, Type::Variable(_)) => expr_type.as_ref().clone(),
                        _ => *pat_type,
                    };
                    CoreValBind {
                        pat: pe.pat.clone().with_type(Box::new(t.clone())),
                        t,
                        expr: pe.expr.clone(),
                        overload_pat: None,
                        span: pe.span.clone(),
                    }
                };
                if resolved_val_decl.rec {
                    CoreDecl::RecVal(
                        resolved_val_decl
                            .pat_exps
                            .iter()
                            .map(to_val_bind)
                            .collect(),
                    )
                } else if resolved_val_decl.pat_exps.len() == 1 {
                    let pe = &resolved_val_decl.pat_exps[0];
                    CoreDecl::NonRecVal(Box::new(to_val_bind(pe)))
                } else {
                    // Multiple non-recursive bindings - convert to RecVal.
                    CoreDecl::RecVal(
                        resolved_val_decl
                            .pat_exps
                            .iter()
                            .map(to_val_bind)
                            .collect(),
                    )
                }
            }
        }
    }

    /// Resolves an AST expression to a core expression.
    pub fn resolve_expr(&self, expr: &Expr) -> CoreExpr {
        let t = self
            .effective_type(expr)
            .or_else(|| expr.get_type(self.type_map))
            .unwrap();
        let span =
            Span::from_pest_span(&expr.span.to_pest_span(), self.base_line);
        match &expr.kind {
            // lint: sort until '#}' where '##ExprKind::'
            ExprKind::Aggregate(a0, a1) => CoreExpr::Aggregate(
                t,
                Box::new(self.resolve_expr(a0)),
                Box::new(self.resolve_expr(a1)),
            ),
            ExprKind::AndAlso(a0, a1) => {
                self.call2(t, BuiltInFunction::BoolAndAlso, &span, a0, a1)
            }
            ExprKind::Annotated(expr, _) => self.resolve_expr(expr),
            ExprKind::Append(a0, a1) => {
                self.call2(t, BuiltInFunction::ListAt, &span, a0, a1)
            }
            ExprKind::Apply(func, arg) => {
                // Dispatch `abs x` to Int.abs or Real.abs when the
                // argument type is known. This matches `~ x` (ExprKind::
                // Negate) and lets Int.abs raise Overflow on minInt.
                if let ExprKind::Identifier(name) = &func.kind
                    && name == "abs"
                {
                    let arg_type = arg.get_type(self.type_map);
                    if let Some(ty) = arg_type {
                        match ty.as_ref() {
                            Type::Primitive(PrimitiveType::Int) => {
                                return self.call1(
                                    t,
                                    BuiltInFunction::IntAbs,
                                    arg,
                                    &span,
                                );
                            }
                            Type::Primitive(PrimitiveType::Real) => {
                                return self.call1(
                                    t,
                                    BuiltInFunction::RealAbs,
                                    arg,
                                    &span,
                                );
                            }
                            _ => {}
                        }
                    }
                }
                // Try postfix method-call rewriting
                // (hydromatic/morel#346). Pattern: outer Apply wraps an
                // inner `Apply(RecordSelector(name), recv)` that
                // couldn't be a field projection on `recv`.
                if let Some(core) = self.try_postfix_call(&t, func, arg, &span)
                {
                    return core;
                }
                CoreExpr::Apply(
                    t,
                    Box::new(self.resolve_expr(func)),
                    Box::new(self.resolve_expr(arg)),
                    Span::from_pest_span(
                        &expr.span.to_pest_span(),
                        self.base_line,
                    ),
                )
            }
            ExprKind::Caret(a0, a1) => {
                self.call2(t, BuiltInFunction::StringCaret, &span, a0, a1)
            }
            ExprKind::Case(case_expr, matches) => CoreExpr::Case(
                t,
                Box::new(self.resolve_expr(case_expr)),
                matches.iter().map(|m| self.resolve_match(m)).collect(),
                span.clone(),
            ),
            ExprKind::Cons(a0, a1) => {
                self.call2(t, BuiltInFunction::ListCons, &span, a0, a1)
            }
            ExprKind::Current => CoreExpr::Current(t),
            ExprKind::Div(a0, a1) => {
                self.call2(t, BuiltInFunction::IntDiv, &span, a0, a1)
            }
            ExprKind::Divide(a0, a1) => {
                self.call2(t, BuiltInFunction::RealDivide, &span, a0, a1)
            }
            ExprKind::Elem(a0, a1) => {
                self.call2(t, BuiltInFunction::ListElem, &span, a0, a1)
            }
            ExprKind::Elements => {
                // 'elements' is a pseudo-variable bound inside group/compute
                // steps. Resolve it as a plain identifier.
                CoreExpr::Identifier(t, "elements".to_string())
            }
            ExprKind::Equal(a0, a1) => {
                match a0.get_type(self.type_map).expect("type").as_ref() {
                    Type::Primitive(PrimitiveType::Int) => {
                        self.call2(t, BuiltInFunction::IntEq, &span, a0, a1)
                    }
                    Type::Primitive(PrimitiveType::Real) => {
                        self.call2(t, BuiltInFunction::RealEq, &span, a0, a1)
                    }
                    Type::Primitive(PrimitiveType::String) => {
                        self.call2(t, BuiltInFunction::StringEq, &span, a0, a1)
                    }
                    Type::Primitive(PrimitiveType::Char) => {
                        self.call2(t, BuiltInFunction::CharEq, &span, a0, a1)
                    }
                    Type::Primitive(PrimitiveType::Bool) => {
                        self.call2(t, BuiltInFunction::BoolEq, &span, a0, a1)
                    }
                    _ => self.call2(t, BuiltInFunction::GEq, &span, a0, a1),
                }
            }
            ExprKind::Exists(steps) => {
                // Translate "exists ..." as "from ... exists".
                // The final Exists step signals the compiler to use
                // ExistsRowSink.
                let mut builder = FromBuilder::new();
                for step in steps {
                    self.resolve_step(&mut builder, step);
                }

                // Add an Exists step to signal that we want an ExistsRowSink.
                builder.exists();

                builder
                    .build_simplify()
                    .expect("Failed to build EXISTS expression")
            }
            ExprKind::Fn(matches) => CoreExpr::Fn(
                t,
                matches.iter().map(|m| self.resolve_match(m)).collect(),
                span.clone(),
            ),
            ExprKind::Forall(steps) => {
                // Translate "forall ... require e" as
                // "not (exists ... where not e)".
                // The "require e" step is handled in resolve_step and
                // translated to "where not e", so we're checking if any
                // violation exists. If no violations exist, then all rows
                // satisfy the requirement.
                let mut builder = FromBuilder::new();
                for step in steps {
                    self.resolve_step(&mut builder, step);
                }

                // Add an Exists step to short-circuit on first violation.
                builder.exists();

                let from_expr = builder
                    .build_simplify()
                    .expect("Failed to build FORALL expression");

                // Apply "not" to the exists result.
                let fn_type = BuiltInFunction::BoolNot.get_type();
                let fn_literal = CoreExpr::Literal(
                    fn_type.clone(),
                    Val::Fn(BuiltInFunction::BoolNot),
                );
                CoreExpr::Apply(
                    t,
                    Box::new(fn_literal),
                    Box::new(from_expr),
                    span,
                )
            }
            ExprKind::From(steps) => self.resolve_query(steps),
            ExprKind::GreaterThan(a0, a1) => {
                match a0.get_type(self.type_map).expect("type").as_ref() {
                    Type::Primitive(PrimitiveType::Int) => {
                        self.call2(t, BuiltInFunction::IntGt, &span, a0, a1)
                    }
                    Type::Primitive(PrimitiveType::Real) => {
                        self.call2(t, BuiltInFunction::RealGt, &span, a0, a1)
                    }
                    Type::Primitive(PrimitiveType::String) => {
                        self.call2(t, BuiltInFunction::StringGt, &span, a0, a1)
                    }
                    Type::Primitive(PrimitiveType::Char) => {
                        self.call2(t, BuiltInFunction::CharGt, &span, a0, a1)
                    }
                    _ => todo!("resolve {:?}", a0),
                }
            }
            ExprKind::GreaterThanOrEqual(a0, a1) => {
                match a0.get_type(self.type_map).expect("type").as_ref() {
                    Type::Primitive(PrimitiveType::Int) => {
                        self.call2(t, BuiltInFunction::IntGe, &span, a0, a1)
                    }
                    Type::Primitive(PrimitiveType::Real) => {
                        self.call2(t, BuiltInFunction::RealGe, &span, a0, a1)
                    }
                    Type::Primitive(PrimitiveType::String) => {
                        self.call2(t, BuiltInFunction::StringGe, &span, a0, a1)
                    }
                    Type::Primitive(PrimitiveType::Char) => {
                        self.call2(t, BuiltInFunction::CharGe, &span, a0, a1)
                    }
                    _ => todo!("resolve {:?}", a0),
                }
            }
            ExprKind::Identifier(name) => {
                // Check if this identifier refers to a global built-in
                // function. Global constructors like DESC need to be
                // resolved to literals so they can be compiled properly.
                // However, if the identifier is locally bound (e.g.
                // as a function parameter or let binding), the local
                // binding shadows the built-in.
                let is_shadowed =
                    if let Some(local_type) = expr.get_type(self.type_map) {
                        // If the local type differs from the built-in's
                        // type, the identifier is shadowed by a local
                        // binding. A simple heuristic: if the built-in
                        // is a function type but the local type is not,
                        // it's shadowed.
                        !matches!(local_type.as_ref(), Type::Fn(_, _))
                            && library::lookup(name).is_some()
                    } else {
                        false
                    };
                if !is_shadowed && let Some(built_in) = library::lookup(name) {
                    match built_in {
                        BuiltIn::Fn(f) => {
                            // Convert the global function/constructor
                            // to a literal.
                            return CoreExpr::Literal(t, Val::Fn(f));
                        }
                        BuiltIn::Record(_) => {
                            // Records stay as identifiers.
                        }
                    }
                }
                // Local variable or shadowed built-in.
                CoreExpr::Identifier(t, name.clone())
            }
            ExprKind::If(cond, then_expr, else_expr) => {
                // Convert 'if cond then e1 else e2'
                // to 'case cond of true => e1 | _ => e2'.
                let cond_core = self.resolve_expr(cond);
                let then_core = self.resolve_expr(then_expr);
                let else_core = self.resolve_expr(else_expr);

                let bool_type = Box::new(Type::Primitive(PrimitiveType::Bool));
                let true_match = CoreMatch {
                    pat: CorePat::Literal(bool_type.clone(), Val::Bool(true)),
                    expr: then_core,
                };
                let false_match = CoreMatch {
                    pat: CorePat::Wildcard(bool_type.clone()),
                    expr: else_core,
                };

                CoreExpr::Case(
                    t,
                    Box::new(cond_core),
                    vec![true_match, false_match],
                    span.clone(),
                )
            }
            ExprKind::Implies(a0, a1) => {
                self.call2(t, BuiltInFunction::BoolImplies, &span, a0, a1)
            }
            ExprKind::LessThan(a0, a1) => {
                match a0.get_type(self.type_map).expect("type").as_ref() {
                    Type::Primitive(PrimitiveType::Int) => {
                        self.call2(t, BuiltInFunction::IntLt, &span, a0, a1)
                    }
                    Type::Primitive(PrimitiveType::Real) => {
                        self.call2(t, BuiltInFunction::RealLt, &span, a0, a1)
                    }
                    Type::Primitive(PrimitiveType::String) => {
                        self.call2(t, BuiltInFunction::StringLt, &span, a0, a1)
                    }
                    Type::Primitive(PrimitiveType::Char) => {
                        self.call2(t, BuiltInFunction::CharLt, &span, a0, a1)
                    }
                    _ => todo!("resolve {:?}", a0),
                }
            }
            ExprKind::LessThanOrEqual(a0, a1) => {
                match a0.get_type(self.type_map).expect("type").as_ref() {
                    Type::Primitive(PrimitiveType::Int) => {
                        self.call2(t, BuiltInFunction::IntLe, &span, a0, a1)
                    }
                    Type::Primitive(PrimitiveType::Real) => {
                        self.call2(t, BuiltInFunction::RealLe, &span, a0, a1)
                    }
                    Type::Primitive(PrimitiveType::String) => {
                        self.call2(t, BuiltInFunction::StringLe, &span, a0, a1)
                    }
                    Type::Primitive(PrimitiveType::Char) => {
                        self.call2(t, BuiltInFunction::CharLe, &span, a0, a1)
                    }
                    _ => todo!("resolve {:?}", a0),
                }
            }
            ExprKind::Let(decls, body) => {
                // Register any user-defined `fun name self …` before
                // resolving the body, so postfix calls in the body can
                // dispatch to them.
                self.register_self_fns(decls);
                let resolved_decls =
                    decls.iter().map(|d| self.resolve_decl(d)).collect();
                CoreExpr::Let(
                    t,
                    resolved_decls,
                    Box::new(self.resolve_expr(body)),
                )
            }
            ExprKind::List(elements) => CoreExpr::List(
                t,
                elements.iter().map(|e| self.resolve_expr(e)).collect(),
            ),
            ExprKind::Literal(l) => {
                CoreExpr::Literal(t, self.resolve_literal(l))
            }
            ExprKind::Minus(a0, a1) => {
                match a0.get_type(self.type_map).expect("type").as_ref() {
                    Type::Primitive(PrimitiveType::Int) => {
                        self.call2(t, BuiltInFunction::IntMinus, &span, a0, a1)
                    }
                    Type::Primitive(PrimitiveType::Real) => {
                        self.call2(t, BuiltInFunction::RealMinus, &span, a0, a1)
                    }
                    _ => self.call2(t, BuiltInFunction::GMinus, &span, a0, a1),
                }
            }
            ExprKind::Mod(a0, a1) => {
                self.call2(t, BuiltInFunction::IntMod, &span, a0, a1)
            }
            ExprKind::Negate(a0) => {
                match a0.get_type(self.type_map).expect("type").as_ref() {
                    Type::Primitive(PrimitiveType::Int) => {
                        self.call1(t, BuiltInFunction::IntNegate, a0, &span)
                    }
                    Type::Primitive(PrimitiveType::Real) => {
                        self.call1(t, BuiltInFunction::RealNegate, a0, &span)
                    }
                    _ => self.call1(t, BuiltInFunction::GNegate, a0, &span),
                }
            }
            ExprKind::NotElem(a0, a1) => {
                self.call2(t, BuiltInFunction::ListNotElem, &span, a0, a1)
            }
            ExprKind::NotEqual(a0, a1) => {
                match a0.get_type(self.type_map).expect("type").as_ref() {
                    Type::Primitive(PrimitiveType::Int) => {
                        self.call2(t, BuiltInFunction::IntNe, &span, a0, a1)
                    }
                    Type::Primitive(PrimitiveType::Real) => {
                        self.call2(t, BuiltInFunction::RealNe, &span, a0, a1)
                    }
                    Type::Primitive(PrimitiveType::String) => {
                        self.call2(t, BuiltInFunction::StringNe, &span, a0, a1)
                    }
                    Type::Primitive(PrimitiveType::Char) => {
                        self.call2(t, BuiltInFunction::CharNe, &span, a0, a1)
                    }
                    Type::Primitive(PrimitiveType::Bool) => {
                        self.call2(t, BuiltInFunction::BoolNe, &span, a0, a1)
                    }
                    _ => todo!("resolve {:?}", a0),
                }
            }
            ExprKind::OpSection(name) => {
                // Convert 'op <operator>' to a function literal
                // The type tells us which specific built-in to use
                self.op_section_to_literal(&t, name)
            }
            ExprKind::OrElse(a0, a1) => {
                self.call2(t, BuiltInFunction::BoolOrElse, &span, a0, a1)
            }
            ExprKind::Ordinal => CoreExpr::Ordinal(t),
            ExprKind::Plus(a0, a1) => {
                match a0.get_type(self.type_map).expect("type").as_ref() {
                    Type::Primitive(PrimitiveType::Int) => {
                        self.call2(t, BuiltInFunction::IntPlus, &span, a0, a1)
                    }
                    Type::Primitive(PrimitiveType::Real) => {
                        self.call2(t, BuiltInFunction::RealPlus, &span, a0, a1)
                    }
                    // Polymorphic / unconstrained type variable: use the
                    // generic dispatcher which resolves at runtime.
                    _ => self.call2(t, BuiltInFunction::GPlus, &span, a0, a1),
                }
            }
            ExprKind::Record(with_base, fields) => {
                match with_base {
                    None => {
                        // Plain record `{a=e1, b=e2}`: resolve each field in
                        // order and emit as a tuple.
                        let resolved_fields = fields
                            .iter()
                            .map(|f| self.resolve_expr(&f.expr))
                            .collect();
                        CoreExpr::Tuple(t, resolved_fields)
                    }
                    Some(base_expr) => {
                        // `{base_expr with a=e1, ...}`: for each field in the
                        // base record type (BTreeMap, so alphabetical order),
                        // use the override expression if provided, otherwise
                        // project the field from `base_expr`.
                        let base_type =
                            base_expr.get_type(self.type_map).unwrap();
                        let (_, base_fields) = base_type.expect_record();
                        let resolved_base = self.resolve_expr(base_expr);
                        let resolved_fields: Vec<CoreExpr> = base_fields
                            .iter()
                            .enumerate()
                            .map(|(slot, (label, field_type))| {
                                let label_str = label.to_string();
                                // Look for an override for this field name.
                                let override_expr = fields.iter().find(|f| {
                                    f.label
                                        .as_ref()
                                        .is_some_and(|l| l.name == label_str)
                                });
                                if let Some(ov) = override_expr {
                                    self.resolve_expr(&ov.expr)
                                } else {
                                    // Project this field from the base.
                                    let selector_type = Box::new(Type::Fn(
                                        base_type.clone(),
                                        Box::new(field_type.clone()),
                                    ));
                                    let selector = CoreExpr::RecordSelector(
                                        selector_type,
                                        slot,
                                    );
                                    CoreExpr::Apply(
                                        Box::new(field_type.clone()),
                                        Box::new(selector),
                                        Box::new(resolved_base.clone()),
                                        span.clone(),
                                    )
                                }
                            })
                            .collect();
                        // The result type is the same as the base type
                        // (overrides cannot change field types). Use
                        // base_type rather than `t` since `t` only
                        // reflects the override fields from type inference.
                        CoreExpr::Tuple(base_type, resolved_fields)
                    }
                }
            }
            ExprKind::RecordSelector(name) => {
                let (param_type, _) = t.expect_fn();
                if let Some(slot) = param_type.lookup_field(name) {
                    CoreExpr::RecordSelector(t, slot)
                } else {
                    let msg = if matches!(
                        param_type,
                        Type::Record(_, _) | Type::Tuple(_)
                    ) {
                        format!("no field '{}' in type '{}'", name, param_type)
                    } else {
                        format!(
                            "reference to field {} \
                             of non-record type {}",
                            name, param_type
                        )
                    };
                    self.errors.borrow_mut().push((msg, span.clone()));
                    CoreExpr::RecordSelector(t, 0)
                }
            }
            ExprKind::Times(a0, a1) => {
                match a0.get_type(self.type_map).expect("type").as_ref() {
                    Type::Primitive(PrimitiveType::Int) => {
                        self.call2(t, BuiltInFunction::IntTimes, &span, a0, a1)
                    }
                    Type::Primitive(PrimitiveType::Real) => {
                        self.call2(t, BuiltInFunction::RealTimes, &span, a0, a1)
                    }
                    _ => self.call2(t, BuiltInFunction::GTimes, &span, a0, a1),
                }
            }
            ExprKind::Tuple(elements) => CoreExpr::Tuple(
                t,
                elements.iter().map(|e| self.resolve_expr(e)).collect(),
            ),
            _ => todo!("Unimplemented expression kind: {:?}", expr.kind),
        }
    }

    fn call1(
        &self,
        t: Box<Type>,
        f: BuiltInFunction,
        a0: &Expr,
        span: &Span,
    ) -> CoreExpr {
        let fn_type = f.get_type();
        let fn_literal = CoreExpr::Literal(fn_type.clone(), Val::Fn(f));
        let c0 = self.resolve_expr(a0);
        CoreExpr::Apply(t, Box::new(fn_literal), Box::new(c0), span.clone())
    }

    fn call2(
        &self,
        t: Box<Type>,
        f: BuiltInFunction,
        span: &Span,
        a0: &Expr,
        a1: &Expr,
    ) -> CoreExpr {
        let fn_type = f.get_type();
        let fn_literal = CoreExpr::Literal(fn_type.clone(), Val::Fn(f));
        let c0 = self.resolve_expr(a0);
        let c1 = self.resolve_expr(a1);
        let arg = CoreExpr::new_tuple(&[c0, c1]);
        CoreExpr::Apply(t, Box::new(fn_literal), Box::new(arg), span.clone())
    }

    /// Detects the postfix method-call pattern
    /// `Apply(Apply(RecordSelector(name), recv), arg)` and, if the
    /// receiver isn't a record with that field, rewrites it to a call
    /// to the appropriate built-in. See hydromatic/morel#346.
    fn try_postfix_call(
        &self,
        t: &Type,
        func: &Expr,
        arg: &Expr,
        span: &Span,
    ) -> Option<CoreExpr> {
        let (method_name, recv) = match &func.kind {
            ExprKind::Apply(inner_fn, inner_arg) => match &inner_fn.kind {
                ExprKind::RecordSelector(name) => {
                    (name.clone(), inner_arg.as_ref())
                }
                _ => return None,
            },
            _ => return None,
        };
        let recv_type = self.effective_type(recv)?;
        // If the receiver is a record with this field, leave the tree
        // alone — that's an ordinary field projection applied to `arg`.
        if let Type::Record(_, fields) = recv_type.as_ref()
            && fields.keys().any(|k| k.to_string() == method_name)
        {
            return None;
        }
        if let Some((builtin, kind)) =
            postfix_dispatch(&method_name, recv_type.as_ref())
        {
            // Compute the return type from the built-in's signature —
            // type inference left the outer Apply's slot as an
            // unresolved variable because it couldn't unify the
            // receiver against a record. For methods whose parameter
            // list shares a type variable with the element type of
            // the receiver (notably Option.getOpt), use the argument's
            // concrete type as a fallback when the receiver is still
            // polymorphic.
            let arg_type = self.effective_type(arg);
            let return_t = postfix_return_type(
                builtin,
                kind,
                recv_type.as_ref(),
                arg_type.as_deref(),
            );
            return Some(
                self.build_postfix_call(
                    return_t, builtin, kind, recv, arg, span,
                ),
            );
        }
        // Not a built-in postfix. Try a user-defined function whose
        // first parameter is `self` (hydromatic/morel#346). The
        // function must be in scope, which we track via self_fns
        // populated from enclosing `let fun name self = …` decls.
        if self.self_fns.borrow().contains(&method_name) {
            return Some(self.build_user_postfix_call(
                &method_name,
                t,
                recv,
                arg,
                span,
            ));
        }
        None
    }

    /// Builds a direct call to a user-defined postfix function.
    /// `name` is the function identifier. Calling convention:
    ///
    /// * `arg` is `()` → `name recv` (unary `fun name self = …`).
    /// * `arg` is a tuple `(a, b, …)` → `name (recv, a, b, …)` —
    ///   recv is spliced as the first tuple element.
    /// * Otherwise → `name (recv, arg)`.
    fn build_user_postfix_call(
        &self,
        name: &str,
        t: &Type,
        recv: &Expr,
        arg: &Expr,
        span: &Span,
    ) -> CoreExpr {
        let c_recv = self.resolve_expr(recv);
        let c_arg = self.resolve_expr(arg);
        let t_box = Box::new(t.clone());
        let name_expr = CoreExpr::Identifier(t_box.clone(), name.to_string());
        let is_unit = matches!(
            &arg.kind,
            ExprKind::Literal(l) if matches!(l.kind, LiteralKind::Unit)
        );
        if is_unit {
            return CoreExpr::Apply(
                t_box,
                Box::new(name_expr),
                Box::new(c_recv),
                span.clone(),
            );
        }
        let mut parts = vec![c_recv];
        if let CoreExpr::Tuple(_, elems) = &c_arg {
            parts.extend(elems.iter().cloned());
        } else {
            parts.push(c_arg);
        }
        let tuple = CoreExpr::new_tuple(&parts);
        CoreExpr::Apply(
            t_box,
            Box::new(name_expr),
            Box::new(tuple),
            span.clone(),
        )
    }

    /// Recursively computes the "effective" type of an expression.
    /// Uses the type_map entry when resolved, but falls back to
    /// re-deriving the type through the postfix dispatcher for
    /// expressions whose type inference was left unresolved because
    /// the expression is itself a postfix call that the type
    /// resolver couldn't recognize as such.
    fn effective_type(&self, expr: &Expr) -> Option<Box<Type>> {
        if let Some(t) = expr.get_type(self.type_map)
            && !is_unresolved_type(&t)
        {
            return Some(t);
        }
        // Apply: is this a postfix method call? If so compute the
        // result type from the built-in signature and receiver.
        if let ExprKind::Apply(f, a) = &expr.kind
            && let ExprKind::Apply(inner_fn, inner_arg) = &f.kind
            && let ExprKind::RecordSelector(name) = &inner_fn.kind
        {
            let recv_type = self.effective_type(inner_arg)?;
            if let Some((builtin, kind)) =
                postfix_dispatch(name, recv_type.as_ref())
            {
                let arg_type = self.effective_type(a);
                return Some(postfix_return_type(
                    builtin,
                    kind,
                    recv_type.as_ref(),
                    arg_type.as_deref(),
                ));
            }
        }
        // Let: the let's effective type is the body's effective type.
        if let ExprKind::Let(_, body) = &expr.kind {
            return self.effective_type(body);
        }
        // Case: take the first branch's right-hand side type.
        if let ExprKind::Case(_, matches) = &expr.kind
            && let Some(m) = matches.first()
        {
            return self.effective_type(&m.expr);
        }
        // If: take the then-branch's type.
        if let ExprKind::If(_, then_expr, _) = &expr.kind {
            return self.effective_type(then_expr);
        }
        expr.get_type(self.type_map)
    }

    /// Builds the Core tree for a postfix call, given the dispatched
    /// built-in and its calling convention.
    fn build_postfix_call(
        &self,
        t: Box<Type>,
        f: BuiltInFunction,
        kind: PostfixKind,
        recv: &Expr,
        arg: &Expr,
        span: &Span,
    ) -> CoreExpr {
        let fn_type = f.get_type();
        let fn_literal = CoreExpr::Literal(fn_type.clone(), Val::Fn(f));
        let c_recv = self.resolve_expr(recv);
        match kind {
            PostfixKind::Unary => {
                // `recv.m ()` — ignore the unit arg and apply the
                // method to the receiver.
                CoreExpr::Apply(
                    t,
                    Box::new(fn_literal),
                    Box::new(c_recv),
                    span.clone(),
                )
            }
            PostfixKind::Tupled2 => {
                // `recv.m a` — build the tuple (recv, a) and apply.
                let c_arg = self.resolve_expr(arg);
                let tuple = CoreExpr::new_tuple(&[c_recv, c_arg]);
                CoreExpr::Apply(
                    t,
                    Box::new(fn_literal),
                    Box::new(tuple),
                    span.clone(),
                )
            }
            PostfixKind::Tupled3 => {
                // `recv.m (a, b)` — splice recv in as first tuple
                // element, producing (recv, a, b).
                let c_arg = self.resolve_expr(arg);
                let mut parts = vec![c_recv];
                if let CoreExpr::Tuple(_, elems) = c_arg {
                    parts.extend(elems);
                } else {
                    parts.push(c_arg);
                }
                let tuple = CoreExpr::new_tuple(&parts);
                CoreExpr::Apply(
                    t,
                    Box::new(fn_literal),
                    Box::new(tuple),
                    span.clone(),
                )
            }
            PostfixKind::Curried2 => {
                // `recv.m a` — build the curried call `m recv a`,
                // i.e. `Apply(Apply(m, recv), a)`. The intermediate
                // type after the first apply is `arg_t -> result_t`.
                let c_arg = self.resolve_expr(arg);
                let arg_t = c_arg.type_();
                let intermediate_t =
                    Box::new(Type::Fn(arg_t.clone(), t.clone()));
                let inner = CoreExpr::Apply(
                    intermediate_t,
                    Box::new(fn_literal),
                    Box::new(c_recv),
                    span.clone(),
                );
                CoreExpr::Apply(
                    t,
                    Box::new(inner),
                    Box::new(c_arg),
                    span.clone(),
                )
            }
        }
    }

    /// Resolves an AST literal to a core value.
    fn resolve_literal(&self, literal: &Literal) -> Val {
        match &literal.kind {
            // lint: sort until '#}' where '##LiteralKind::'
            LiteralKind::Bool(b) => Val::Bool(*b),
            LiteralKind::Char(c) => {
                Val::Char(parser::unquote_char_literal(c).unwrap())
            }
            LiteralKind::Fn(f) => Val::Fn(*f),
            LiteralKind::Int(i) => {
                Val::Int(i.replace("~", "-").parse().unwrap())
            }
            LiteralKind::Real(r) => {
                Val::Real(r.replace("~", "-").parse().unwrap())
            }
            LiteralKind::String(s) => {
                Val::String(parser::unquote_string(s).unwrap())
            }
            LiteralKind::Unit => Val::Unit,
        }
    }

    /// Resolves an AST pattern to a core pattern.
    fn resolve_pat(&self, pat: &Pat) -> CorePat {
        let t = pat.get_type(self.type_map).unwrap();

        match &pat.kind {
            // lint: sort until '#}' where '##PatKind::'
            PatKind::Annotated(inner_pat, ann_type) => {
                // For annotated patterns, resolve the inner pattern
                // since core patterns have embedded types.
                // If the annotation is a type alias, wrap the inner
                // pattern's type in Type::Alias (unless already
                // wrapped by the inner Identifier handler).
                let resolved = self.resolve_pat(inner_pat);
                if matches!(*resolved.type_(), Type::Alias(..)) {
                    // Already wrapped by get_type_with_alias
                    return resolved;
                }
                if let TypeKind::Id(name) = &ann_type.kind
                    && let Some(ann_id) = ann_type.id
                {
                    let var = Var { id: ann_id };
                    if self.type_map.var_alias_map.contains_key(&var) {
                        let inner_type = resolved.type_().clone();
                        let alias_type = Box::new(Type::Alias(
                            name.clone(),
                            inner_type,
                            vec![],
                        ));
                        return resolved.with_type(alias_type);
                    }
                }
                resolved
            }
            PatKind::As(name, sub_pat) => CorePat::As(
                t,
                name.clone(),
                Box::new(self.resolve_pat(sub_pat)),
            ),
            PatKind::Cons(head, tail) => CorePat::Cons(
                t,
                Box::new(self.resolve_pat(head)),
                Box::new(self.resolve_pat(tail)),
            ),
            PatKind::Constructor(name, opt_pat) => {
                // `nil` in a pattern is an empty-list literal.
                if name == "nil"
                    && opt_pat.is_none()
                    && matches!(*t, Type::List(_))
                {
                    return CorePat::List(t, vec![]);
                }
                let resolved_pat =
                    opt_pat.as_ref().map(|p| Box::new(self.resolve_pat(p)));
                CorePat::Constructor(t, name.clone(), resolved_pat)
            }
            PatKind::Identifier(name) => {
                // Check if the pattern's var carries a type alias
                // (e.g. from `val x = 6 : myInt` where the annotation
                // is on the expression, not the pattern).
                let t = if let Some(id) = pat.id {
                    self.type_map.get_type_with_alias(id).unwrap_or(t)
                } else {
                    t
                };
                CorePat::Identifier(t, name.clone())
            }
            PatKind::List(pats) => {
                let resolved_pats =
                    pats.iter().map(|p| self.resolve_pat(p)).collect();
                CorePat::List(t, resolved_pats)
            }
            PatKind::Literal(literal) => {
                CorePat::Literal(t, self.resolve_literal(literal))
            }
            PatKind::Record(fields, has_ellipsis) => {
                let resolved_fields =
                    fields.iter().map(|f| self.resolve_pat_field(f)).collect();
                CorePat::Record(t, resolved_fields, *has_ellipsis)
            }
            PatKind::Tuple(pats) => {
                let resolved_pats = pats.iter().map(|p| self.resolve_pat(p));
                CorePat::Tuple(t, resolved_pats.collect())
            }
            PatKind::Wildcard => CorePat::Wildcard(t),
        }
    }

    /// Resolves an AST pattern field to a core pattern field.
    fn resolve_pat_field(&self, field: &PatField) -> CorePatField {
        match field {
            PatField::Labeled(_, name, pat) => CorePatField::Labeled(
                name.clone(),
                Box::new(self.resolve_pat(pat)),
            ),
            PatField::Anonymous(_, pat) => {
                CorePatField::Anonymous(Box::new(self.resolve_pat(pat)))
            }
            PatField::Ellipsis(_) => CorePatField::Ellipsis,
        }
    }

    /// Resolves an AST value binding to a core value binding.
    /// Checks if a val-bind's expression has an alias annotation
    /// that should propagate to the pattern's type. Handles cases
    /// like `val list = [1: myInt]` where the first list element's
    /// annotation should make the list type `myInt list`.
    fn expr_alias_for_pat(&self, expr: &Expr, pat: &CorePat) -> Option<Type> {
        // Already aliased by resolve_pat? Skip.
        if matches!(*pat.type_(), Type::Alias(..)) {
            return None;
        }
        match &expr.kind {
            ExprKind::List(elems) if !elems.is_empty() => {
                // Check if the first element has an alias annotation.
                if let ExprKind::Annotated(_, ann_type) = &elems[0].kind
                    && let TypeKind::Id(name) = &ann_type.kind
                    && let Some(ann_id) = ann_type.id
                {
                    let var = Var { id: ann_id };
                    if self.type_map.var_alias_map.contains_key(&var)
                        && let Type::List(elem_type) = &*pat.type_()
                    {
                        return Some(Type::List(Box::new(Type::Alias(
                            name.clone(),
                            elem_type.clone(),
                            vec![],
                        ))));
                    }
                }
                None
            }
            _ => None,
        }
    }

    fn resolve_val_bind(&self, val_bind: &ValBind) -> CoreValBind {
        let pat = self.resolve_pat(&val_bind.pat);
        let expr = self.resolve_expr(&val_bind.expr);
        // Get type from type annotation if present, otherwise from type map.
        let type_ = if let Some(type_annotation) = &val_bind.type_annotation {
            Box::new(self.resolve_ast_type(type_annotation))
        } else {
            // Try to get type from the pattern or expression ID.
            if let Some(id) = val_bind.pat.id {
                self.type_map.get_type(id).unwrap_or_else(|| {
                    Box::new(Type::Primitive(PrimitiveType::Unit))
                })
            } else if let Some(id) = val_bind.expr.id {
                self.type_map.get_type(id).unwrap_or_else(|| {
                    Box::new(Type::Primitive(PrimitiveType::Unit))
                })
            } else {
                Box::new(Type::Primitive(PrimitiveType::Unit))
            }
        };

        let span = Some(Span::from_pest_span(
            &val_bind.pat.span.union(&val_bind.expr.span).to_pest_span(),
            self.base_line,
        ));
        CoreValBind {
            pat,
            t: *type_,
            expr,
            overload_pat: None,
            span,
        }
    }

    /// Resolves an AST type binding to a core type binding. The
    /// alias's right-hand side is converted to a core type via
    /// the same simple-shape recogniser used by the type-resolver.
    /// Unsupported shapes fall back to `unit`.
    fn resolve_type_bind(&self, type_bind: &TypeBind) -> CoreTypeBind {
        let core_type = crate::compile::type_resolver::ast_type_to_core_type(
            &type_bind.type_,
        )
        .unwrap_or(Type::Primitive(PrimitiveType::Unit));
        CoreTypeBind {
            type_vars: type_bind.type_vars.clone(),
            name: type_bind.name.clone(),
            type_: core_type,
        }
    }

    /// Resolves an AST datatype binding to a core datatype binding.
    fn resolve_datatype_bind(
        &self,
        datatype_bind: &DatatypeBind,
    ) -> CoreDatatypeBind {
        CoreDatatypeBind {
            type_vars: datatype_bind.type_vars.clone(),
            name: datatype_bind.name.clone(),
            constructors: datatype_bind
                .constructors
                .iter()
                .map(|con| {
                    let tvs = &datatype_bind.type_vars;
                    let core_type = con.type_.as_ref().and_then(|t| {
                        crate::compile::type_resolver
                            ::ast_type_to_core_type_with_vars(
                                t, tvs,
                            )
                    });
                    CoreConBind {
                        name: con.name.clone(),
                        type_: core_type,
                    }
                })
                .collect(),
        }
    }

    /// Resolves an AST type to a core type.
    fn resolve_ast_type(&self, _ast_type: &AstType) -> Type {
        // For now, just returns a basic type. This would need a proper
        // implementation to convert AST type to core type based on the
        // type resolver.
        Type::Primitive(PrimitiveType::Unit)
    }

    /// Resolves an AST match to a core match.
    fn resolve_match(&self, ast_match: &Match) -> CoreMatch {
        CoreMatch {
            pat: self.resolve_pat(&ast_match.pat),
            expr: self.resolve_expr(&ast_match.expr),
        }
    }

    /// Resolves a From query using FromBuilder for optimization.
    /// This is analogous to the Java FromResolver inner class.
    fn resolve_query(&self, steps: &[AstStep]) -> CoreExpr {
        // Check if the last step is Into.
        // If so, we need to apply the function to the query result.
        if let Some(last_step) = steps.last()
            && let AstStepKind::Into(func_expr) = &last_step.kind
        {
            // Process all steps except the last (Into).
            let mut builder = FromBuilder::new();
            for step in &steps[..steps.len() - 1] {
                self.resolve_step(&mut builder, step);
            }
            let from_result = builder
                .build_simplify()
                .expect("Failed to build From expression");

            // Apply the function to the query result.
            let func = self.resolve_expr(func_expr);

            // Get the result type from the type_map for the
            // function application.
            let result_type = func_expr
                .get_type(self.type_map)
                .expect("INTO function must have a type");

            // Apply the function: f(from_result).
            let span = Span::from_pest_span(
                &last_step.span.to_pest_span(),
                self.base_line,
            );
            return CoreExpr::Apply(
                result_type,
                Box::new(func),
                Box::new(from_result),
                span,
            );
        }

        // Normal query processing (no INTO).
        let mut builder = FromBuilder::new();

        for step in steps {
            self.resolve_step(&mut builder, step);
        }

        builder
            .build_simplify()
            .expect("Failed to build From expression")
    }

    /// Resolves a step in a query, adding it to a [FromBuilder].
    fn resolve_step(&self, builder: &mut FromBuilder, step: &AstStep) {
        match &step.kind {
            // lint: sort until '#}' where '##AstStepKind::'
            AstStepKind::Compute(expr) => {
                let resolved_expr = self.resolve_expr(expr);
                builder.compute(resolved_expr);
            }
            AstStepKind::Distinct => {
                builder.distinct();
            }
            AstStepKind::Except(distinct, exprs) => {
                let resolved_exprs: Vec<_> =
                    exprs.iter().map(|e| self.resolve_expr(e)).collect();
                builder.except(*distinct, resolved_exprs);
            }
            AstStepKind::Group(key_expr, aggregate_expr) => {
                // Resolve the group key expression.
                let resolved_key = self.resolve_expr(key_expr);

                // Resolve the aggregate expression if present.
                let resolved_aggregate =
                    aggregate_expr.as_ref().map(|e| self.resolve_expr(e));

                // Add the group step to the builder.
                builder.group(resolved_key, resolved_aggregate);
            }
            AstStepKind::Intersect(distinct, exprs) => {
                let resolved_exprs: Vec<_> =
                    exprs.iter().map(|e| self.resolve_expr(e)).collect();
                builder.intersect(*distinct, resolved_exprs);
            }
            AstStepKind::Into(_) => {
                // INTO is handled at the query level in resolve_query,
                // not as a step. This should not be reached during normal
                // processing.
                panic!(
                    "INTO step should be handled in resolve_query, \
                     not resolve_step"
                )
            }
            AstStepKind::Order(expr) => {
                let resolved_expr = self.resolve_expr(expr);
                builder.order(resolved_expr);
            }
            AstStepKind::Require(expr) => {
                // Translate "require e" as "where not e".
                // This is used in forall queries.
                let resolved_expr = self.resolve_expr(expr);
                let bool_type = Type::Primitive(PrimitiveType::Bool);
                let fn_type = BuiltInFunction::BoolNot.get_type();
                let fn_literal = CoreExpr::Literal(
                    fn_type.clone(),
                    Val::Fn(BuiltInFunction::BoolNot),
                );
                let span = Span::from_pest_span(
                    &step.span.to_pest_span(),
                    self.base_line,
                );
                let negated = CoreExpr::Apply(
                    Box::new(bool_type),
                    Box::new(fn_literal),
                    Box::new(resolved_expr),
                    span,
                );
                builder.where_(negated);
            }
            AstStepKind::Scan(pat, expr, condition) => {
                // Resolve the pattern and expression.
                let resolved_pat = self.resolve_pat(pat);
                let resolved_expr = self.resolve_expr(expr);

                // Resolve the condition if present.
                let resolved_condition =
                    condition.as_ref().map(|c| self.resolve_expr(c));

                // Add the scan step to the builder.
                builder.scan_with_condition(
                    resolved_pat,
                    resolved_expr,
                    resolved_condition,
                );
            }
            AstStepKind::ScanEq(pat, expr) => {
                // `join pat = expr` is a cross join with a singleton list.
                // Desugar to a scan over `[expr]`.
                let resolved_pat = self.resolve_pat(pat);
                let resolved_expr = self.resolve_expr(expr);
                let elem_type = resolved_expr.type_();
                let list_type =
                    Box::new(Type::List(Box::new(elem_type.as_ref().clone())));
                let singleton = CoreExpr::List(list_type, vec![resolved_expr]);
                builder.scan_with_condition(resolved_pat, singleton, None);
            }
            AstStepKind::Skip(expr) => {
                let resolved_expr = self.resolve_expr(expr);
                builder.skip(resolved_expr);
            }
            AstStepKind::Take(expr) => {
                let resolved_expr = self.resolve_expr(expr);
                builder.take(resolved_expr);
            }
            AstStepKind::Through(pat, expr) => {
                // Desugar "from ... through p in f"
                // to "from p in f (from ...)".
                let from_expr = builder
                    .build_simplify()
                    .expect("Failed to build From expression");
                builder.clear();
                let fn_expr = self.resolve_expr(expr);
                let resolved_pat = self.resolve_pat(pat);
                let result_type = match fn_expr.type_().as_ref() {
                    Type::Fn(_, result) => Box::new(result.as_ref().clone()),
                    t => panic!(
                        "through expression must be a function, got {:?}",
                        t
                    ),
                };
                let span = Span::from_pest_span(
                    &step.span.to_pest_span(),
                    self.base_line,
                );
                let apply = CoreExpr::Apply(
                    result_type,
                    Box::new(fn_expr),
                    Box::new(from_expr),
                    span,
                );
                builder.scan(resolved_pat, apply);
            }
            AstStepKind::Union(distinct, exprs) => {
                let resolved_exprs: Vec<_> =
                    exprs.iter().map(|e| self.resolve_expr(e)).collect();
                builder.union(*distinct, resolved_exprs);
            }
            AstStepKind::Unorder => {
                builder.unorder();
            }
            AstStepKind::Where(expr) => {
                let resolved_expr = self.resolve_expr(expr);
                builder.where_(resolved_expr);
            }
            AstStepKind::Yield(expr) => {
                let resolved_expr = self.resolve_expr(expr);
                builder.yield_(resolved_expr);
            }
            _ => {
                // For now, fall back to the old resolve_step for unsupported
                // step types.
                todo!("resolve_from_step: {:?}", step.kind)
            }
        }
    }

    /// Converts an AST literal to a core value.
    fn literal_val(literal: &Literal) -> Val {
        match &literal.kind {
            // lint: sort until '#}' where '##LiteralKind::'
            LiteralKind::Bool(x) => Val::Bool(*x),
            LiteralKind::Char(x) => {
                Val::Char(parser::unquote_char_literal(x).unwrap())
            }
            LiteralKind::Fn(_fn_literal) => {
                todo!("Implement Fn literal conversion")
            }
            LiteralKind::Int(x) => {
                Val::Int(x.replace("~", "-").parse().unwrap())
            }
            LiteralKind::Real(x) => {
                Val::Real(x.replace("~", "-").parse().unwrap())
            }
            LiteralKind::String(x) => {
                Val::String(parser::unquote_string(x).unwrap())
            }
            LiteralKind::Unit => Val::Unit,
        }
    }

    /// Resolves a value declaration, mirroring the Java resolveValDecl method.
    fn resolve_val_decl(
        &self,
        val_binds: &[ValBind],
        mut rec: bool,
    ) -> ResolvedValDecl {
        let composite = val_binds.len() > 1;

        // Flatten patterns and expressions.
        let mut pat_exps = Vec::new();

        for val_bind in val_binds {
            let mut core_pat = self.resolve_pat(&val_bind.pat);
            // Check if the expression has an alias annotation that
            // should propagate to the pattern type.
            if let Some(alias_type) =
                self.expr_alias_for_pat(&val_bind.expr, &core_pat)
            {
                core_pat = core_pat.with_type(Box::new(alias_type));
            }
            let core_expr = self.resolve_expr(&val_bind.expr);
            let span = Some(Span::from_pest_span(
                &val_bind.pat.span.union(&val_bind.expr.span).to_pest_span(),
                self.base_line,
            ));

            pat_exps.push(PatExpr {
                pat: core_pat,
                expr: core_expr,
                span,
            });
        }

        // Convert recursive to non-recursive if the bound variable is not
        // referenced in its definition. For example,
        //   val rec inc = fn i => i + 1
        // can be converted to
        //   val inc = fn i => i + 1
        // because "i + 1" does not reference "inc".
        rec = rec && !references(&pat_exps);

        // Transform "let val v1 = E1 and v2 = E2 in E end"
        // to "let val v = (v1, v2) in case v of (E1, E2) => E end"
        let (_pat0, _exp) = if composite {
            let pats: Vec<CorePat> =
                pat_exps.iter().map(|x| x.pat.clone()).collect();
            let exps: Vec<CoreExpr> =
                pat_exps.iter().map(|x| x.expr.clone()).collect();
            let exp = CoreExpr::new_tuple(&exps);
            let pat0 = CorePat::Tuple(exp.type_().clone(), pats);
            (pat0, exp)
        } else {
            let pat_exp = &pat_exps[0];
            (pat_exp.pat.clone(), pat_exp.expr.clone())
        };

        // Transform composite patterns.
        let (ref pat, expr) = if composite {
            // Create tuple pattern and expression.
            let pats: Vec<CorePat> =
                pat_exps.iter().map(|pe| pe.pat.clone()).collect();
            let exprs: Vec<CoreExpr> =
                pat_exps.iter().map(|pe| pe.expr.clone()).collect();

            // Create a tuple type based on the constituent types.
            let tuple_expr = CoreExpr::new_tuple(&exprs);
            let tuple_pat = CorePat::Tuple(tuple_expr.type_().clone(), pats);

            (tuple_pat, tuple_expr)
        } else {
            let pat_exp = &pat_exps[0];
            (pat_exp.pat.clone(), pat_exp.expr.clone())
        };

        ResolvedValDecl {
            rec,
            composite,
            pat_exps,
            pat: pat.clone(),
            expr,
        }
    }

    /// Creates a let expression from a resolved value declaration.
    /// This is the main entry point for the Java toExp equivalent.
    pub fn val_decl_to_let_expr(
        &self,
        val_binds: &[ValBind],
        is_rec: bool,
        result_expr: &CoreExpr,
    ) -> CoreExpr {
        let resolved_val_decl = self.resolve_val_decl(val_binds, is_rec);
        resolved_val_decl.to_exp(result_expr)
    }

    /// Handles complex patterns by creating intermediate variables.
    /// This mirrors the complex pattern handling in the Java code.
    pub fn handle_complex_pattern(
        &self,
        pat: &CorePat,
        expr: &CoreExpr,
        result_expr: &CoreExpr,
    ) -> CoreExpr {
        // Check if this is a simple identifier pattern.
        if let CorePat::Identifier(_, _) = pat {
            // Simple case - create direct let binding.
            let val_bind = CoreValBind {
                pat: pat.clone(),
                t: *pat.type_(),
                expr: expr.clone(),
                overload_pat: None,
                span: None,
            };

            let decl = CoreDecl::NonRecVal(Box::new(val_bind));
            return CoreExpr::Let(
                result_expr.type_(),
                vec![decl],
                Box::new(result_expr.clone()),
            );
        }

        // Complex pattern case - allocate intermediate variable.
        let temp_name = format!("temp_{}", std::ptr::addr_of!(pat) as usize);
        let expr_type = expr.type_();

        // Create intermediate identifier pattern.
        let temp_pat =
            CorePat::Identifier(expr_type.clone(), temp_name.clone());

        // Create intermediate binding.
        let temp_val_bind = CoreValBind {
            pat: temp_pat.clone(),
            t: *expr_type.clone(),
            expr: expr.clone(),
            overload_pat: None,
            span: None,
        };

        // Create identifier expression for temp variable.
        let temp_id = Box::new(CoreExpr::Identifier(expr_type, temp_name));

        // Create a case expression to match the complex pattern.
        let match_ = CoreMatch {
            pat: pat.clone(),
            expr: result_expr.clone(),
        };

        let case_expr = Box::new(CoreExpr::Case(
            pat.type_(),
            temp_id,
            vec![match_],
            Span::new("stdIn"),
        ));

        // Create the let expression.
        let decl = CoreDecl::NonRecVal(Box::new(temp_val_bind));
        CoreExpr::Let(case_expr.type_(), vec![decl], case_expr)
    }

    /// Converts an operator section to a function literal.
    /// After type resolution, we know the concrete type, so we can
    /// directly map to the specific built-in function.
    fn op_section_to_literal(&self, fn_type: &Type, op_name: &str) -> CoreExpr {
        match fn_type {
            Type::Multi(_types) => {
                // Overloaded function - create GNegate, GPlus, etc.
                let builtin = self.multi_op_to_builtin(op_name);
                let fn_val = Val::Fn(builtin);
                let fn_lit_type = builtin.get_type();
                CoreExpr::Literal(fn_lit_type, fn_val)
            }
            Type::Forall(_inner_type, _param_count) => {
                // Polymorphic function
                let builtin = self.multi_op_to_builtin(op_name);
                let fn_val = Val::Fn(builtin);
                let fn_lit_type = builtin.get_type();
                CoreExpr::Literal(fn_lit_type, fn_val)
            }
            Type::Fn(param_type, _result_type) => {
                let builtin = match param_type.as_ref() {
                    Type::Variable(_) => {
                        // Type variable means it's polymorphic
                        self.multi_op_to_builtin(op_name)
                    }
                    Type::Tuple(args) if args.len() == 2 => {
                        // Binary operator
                        match &args[0] {
                            Type::Variable(_) => {
                                self.multi_op_to_builtin(op_name)
                            }
                            _ => self.binary_op_to_builtin(op_name, &args[0]),
                        }
                    }
                    _ => {
                        // Unary operator
                        self.unary_op_to_builtin(op_name, param_type)
                    }
                };
                let fn_val = Val::Fn(builtin);
                let fn_lit_type = builtin.get_type();
                CoreExpr::Literal(fn_lit_type, fn_val)
            }
            _ => todo!("OpSection with non-function type: {:?}", fn_type),
        }
    }

    /// Maps a binary operator and type to the corresponding built-in
    /// function.
    fn binary_op_to_builtin(
        &self,
        op_name: &str,
        arg_type: &Type,
    ) -> BuiltInFunction {
        use BuiltInFunction::{
            IntDiv, IntGe, IntGt, IntLe, IntLt, IntMinus, IntMod, IntPlus,
            IntTimes, ListAt, ListCons, RealDivide, RealGe, RealGt, RealLe,
            RealLt, RealMinus, RealPlus, RealTimes, StringCaret, StringGe,
            StringGt, StringLe, StringLt,
        };
        match (op_name, arg_type) {
            // Integer operators
            ("+", Type::Primitive(PrimitiveType::Int)) => IntPlus,
            ("-", Type::Primitive(PrimitiveType::Int)) => IntMinus,
            ("*", Type::Primitive(PrimitiveType::Int)) => IntTimes,
            ("div", Type::Primitive(PrimitiveType::Int)) => IntDiv,
            ("mod", Type::Primitive(PrimitiveType::Int)) => IntMod,
            ("<", Type::Primitive(PrimitiveType::Int)) => IntLt,
            ("<=", Type::Primitive(PrimitiveType::Int)) => IntLe,
            (">", Type::Primitive(PrimitiveType::Int)) => IntGt,
            (">=", Type::Primitive(PrimitiveType::Int)) => IntGe,

            // Real operators
            ("+", Type::Primitive(PrimitiveType::Real)) => RealPlus,
            ("-", Type::Primitive(PrimitiveType::Real)) => RealMinus,
            ("*", Type::Primitive(PrimitiveType::Real)) => RealTimes,
            ("/", Type::Primitive(PrimitiveType::Real)) => RealDivide,
            ("<", Type::Primitive(PrimitiveType::Real)) => RealLt,
            ("<=", Type::Primitive(PrimitiveType::Real)) => RealLe,
            (">", Type::Primitive(PrimitiveType::Real)) => RealGt,
            (">=", Type::Primitive(PrimitiveType::Real)) => RealGe,

            // String operators
            ("^", Type::Primitive(PrimitiveType::String)) => StringCaret,
            ("<", Type::Primitive(PrimitiveType::String)) => StringLt,
            ("<=", Type::Primitive(PrimitiveType::String)) => StringLe,
            (">", Type::Primitive(PrimitiveType::String)) => StringGt,
            (">=", Type::Primitive(PrimitiveType::String)) => StringGe,

            // List operators - these work on any element type
            ("::", _) => ListCons,
            ("@", Type::List(_)) => ListAt,

            _ => todo!(
                "binary operator '{}' with type {:?} not supported",
                op_name,
                arg_type
            ),
        }
    }

    /// Maps a unary operator and type to the corresponding built-in
    /// function.
    fn unary_op_to_builtin(
        &self,
        op_name: &str,
        arg_type: &Type,
    ) -> BuiltInFunction {
        use BuiltInFunction::{BoolNot, IntNegate, RealNegate};
        match (op_name, arg_type) {
            ("~", Type::Primitive(PrimitiveType::Int)) => IntNegate,
            ("~", Type::Primitive(PrimitiveType::Real)) => RealNegate,
            ("not", Type::Primitive(PrimitiveType::Bool)) => BoolNot,
            _ => todo!(
                "unary operator '{}' with type {:?} not supported",
                op_name,
                arg_type
            ),
        }
    }

    /// Maps an overloaded operator to its general (polymorphic) built-in
    /// function.
    fn multi_op_to_builtin(&self, op_name: &str) -> BuiltInFunction {
        use BuiltInFunction::{
            GEq, GGe, GGt, GLe, GLt, GMinus, GNe, GNegate, GPlus, GTimes,
            ListCons,
        };
        match op_name {
            "~" => GNegate,
            "+" => GPlus,
            "*" => GTimes,
            "-" => GMinus,
            "<" => GLt,
            "<=" => GLe,
            ">" => GGt,
            ">=" => GGe,
            "=" => GEq,
            "<>" => GNe,
            "::" => ListCons,
            _ => todo!("overloaded operator '{}' not supported", op_name),
        }
    }
}

/// Returns whether any of the expressions in `exps` references any of
/// the variables defined in `pats`.
///
/// This method is used to decide whether it is safe to convert a recursive
/// declaration into a non-recursive one.
fn references(pat_exprs: &[PatExpr]) -> bool {
    let finder = ReferenceFinder::new(&Env::empty(), VecDeque::new());

    // Collect references from expressions
    for _pat_expr in pat_exprs {
        // TODO: Implement expression visitor pattern for collecting references
        // For now, we'll assume no references are found
    }

    // Collect definitions from patterns
    let mut def_set = HashSet::new();
    for pat_exp in pat_exprs {
        pat_exp
            .pat
            .for_each_id_pat(&mut |(_, name): (&Type, &str)| {
                def_set.insert(name.to_string());
            });
    }

    finder.ref_set.intersection(&def_set).count() > 0
}

struct ReferenceFinder {
    ref_set: HashSet<String>,
}

impl ReferenceFinder {
    fn new(_env: &Env, _from_stack: VecDeque<()>) -> Self {
        ReferenceFinder {
            ref_set: HashSet::new(),
        }
    }
}

/// Peels type aliases and Forall wrappers for the purpose of
/// postfix-method dispatch.
fn peel_type(t: &Type) -> &Type {
    match t {
        Type::Alias(_, inner, _) => peel_type(inner),
        Type::Forall(inner, _) => peel_type(inner),
        _ => t,
    }
}

/// Returns the result type of a postfix call, given the dispatched
/// built-in and the *concrete* receiver type. We need this because
/// type inference leaves the outer Apply's type variable unresolved
/// (the record-selector action only fires when the receiver is a
/// true record, not a built-in type).
fn postfix_return_type(
    builtin: BuiltInFunction,
    _kind: PostfixKind,
    recv_type: &Type,
    arg_type: Option<&Type>,
) -> Box<Type> {
    use BuiltInFunction::{
        BagDrop, BagHd, BagLength, BagNull, BagOnly, BagTake, BagTl, BoolNot,
        BoolToString, CharCompare, CharIsAlpha, CharIsDigit, CharOrd, CharPred,
        CharSucc, CharToLower, CharToString, CharToUpper, IntAbs, IntCompare,
        IntMax, IntMin, IntRem, IntSameSign, IntSign, IntToString, ListDrop,
        ListHd, ListLength, ListNth, ListNull, ListOnly, ListTake, ListTl,
        OptionGetOpt, OptionIsSome, OptionValOf, RealAbs, RealCeil,
        RealCompare, RealFloor, RealMax, RealMin, RealRem, RealSign,
        RealToString, RealTrunc, StringExplode, StringSize, StringSub,
        StringSubstring,
    };
    fn prim(p: PrimitiveType) -> Box<Type> {
        Box::new(Type::Primitive(p))
    }
    fn clone_box(t: &Type) -> Box<Type> {
        Box::new(t.clone())
    }
    /// Extracts the element type from a `T list` or `T bag`.
    fn elem_of(t: &Type) -> Box<Type> {
        match peel_type(t) {
            Type::List(e) | Type::Bag(e) => e.clone(),
            _ => Box::new(t.clone()),
        }
    }
    /// Builds an `order` type (the `order` datatype).
    fn order_ty() -> Box<Type> {
        Box::new(Type::Data("order".to_string(), vec![]))
    }
    match builtin {
        // Length-like: always int
        ListLength | BagLength | StringSize | CharOrd => {
            prim(PrimitiveType::Int)
        }
        // bool results
        ListNull | BagNull | BoolNot | CharIsAlpha | CharIsDigit => {
            prim(PrimitiveType::Bool)
        }
        // hd / only return element type
        ListHd | BagHd | ListOnly | BagOnly => elem_of(recv_type),
        // tl / drop / take return collection type
        ListTl | BagTl | ListDrop | ListTake | BagDrop | BagTake => {
            clone_box(recv_type)
        }
        // nth: (T list * int) -> T
        ListNth => elem_of(recv_type),
        // String
        StringSub => prim(PrimitiveType::Char),
        StringSubstring => prim(PrimitiveType::String),
        StringExplode => Box::new(Type::List(prim(PrimitiveType::Char))),
        // Int ops returning int
        IntAbs | IntMax | IntMin | IntRem | IntSign => prim(PrimitiveType::Int),
        IntSameSign => prim(PrimitiveType::Bool),
        IntToString | BoolToString | CharToString | RealToString => {
            prim(PrimitiveType::String)
        }
        // Int/Real compare return order
        IntCompare | RealCompare | CharCompare => order_ty(),
        // Real ops returning real
        RealAbs | RealMax | RealMin | RealRem | RealTrunc => {
            prim(PrimitiveType::Real)
        }
        // Real ops returning int
        RealCeil | RealFloor | RealSign => prim(PrimitiveType::Int),
        // Char transforms
        CharPred | CharSucc | CharToLower | CharToUpper => {
            prim(PrimitiveType::Char)
        }
        // Option methods
        OptionIsSome => prim(PrimitiveType::Bool),
        OptionValOf => {
            // option T → T
            match peel_type(recv_type) {
                Type::Data(_, args) if args.len() == 1 => {
                    Box::new(args[0].clone())
                }
                _ => clone_box(recv_type),
            }
        }
        OptionGetOpt => {
            // option T * T → T. If the receiver is still polymorphic
            // (e.g. `NONE.getOpt(0)`), fall back to the argument's
            // concrete type — the second argument and the result share
            // the element type variable.
            match peel_type(recv_type) {
                Type::Data(_, args)
                    if args.len() == 1 && !is_unresolved_type(&args[0]) =>
                {
                    return Box::new(args[0].clone());
                }
                _ => {}
            }
            if let Some(t) = arg_type
                && !is_unresolved_type(t)
            {
                return Box::new(t.clone());
            }
            // Fallback: peel whatever we have, even if it's a
            // variable.
            match peel_type(recv_type) {
                Type::Data(_, args) if args.len() == 1 => {
                    Box::new(args[0].clone())
                }
                _ => clone_box(recv_type),
            }
        }
        // Fallback: use the receiver's type (conservative).
        _ => clone_box(recv_type),
    }
}

/// Returns true if a type is still an unresolved unification variable
/// (i.e., type inference left it unconstrained).
fn is_unresolved_type(t: &Type) -> bool {
    matches!(t, Type::Variable(_))
}

/// Returns true if a `FunMatch`'s first parameter pattern is
/// named `self`, either directly (`fun f self = ...`) or as a
/// field of a record/tuple pattern
/// (`fun f (self, x, y) = ...`).
fn match_has_self_first_param(m: &crate::syntax::ast::FunMatch) -> bool {
    match m.pats.first() {
        Some(pat) => pat_has_self(pat),
        None => false,
    }
}

/// Returns true if a pattern is `self`, `self : T`, or a record /
/// tuple pattern containing a field named `self`.
fn pat_has_self(pat: &crate::syntax::ast::Pat) -> bool {
    use crate::syntax::ast::PatKind;
    match &pat.kind {
        PatKind::Identifier(name) => name == "self",
        PatKind::Annotated(inner, _) => pat_has_self(inner),
        PatKind::Record(fields, _) => fields.iter().any(|f| match f {
            PatField::Labeled(_, name, _) => name == "self",
            PatField::Anonymous(_, _) | PatField::Ellipsis(_) => false,
        }),
        PatKind::Tuple(elts) => elts.iter().any(pat_has_self),
        _ => false,
    }
}

/// Returns true if an expression is a function (`fn …`) whose first
/// clause has `self` as its first parameter pattern.  Also follows
/// through a single nested `fn` for curried functions.  Used to
/// recognise `fun name self = …` after it has been desugared to
/// `val rec name = fn self => …`.
fn fn_expr_has_self_first_param(expr: &Expr) -> bool {
    match &expr.kind {
        ExprKind::Fn(matches) => matches.iter().any(|m| pat_has_self(&m.pat)),
        _ => false,
    }
}
