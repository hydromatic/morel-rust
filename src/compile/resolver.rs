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

// Several resolver helpers (resolve_val_bind, resolve_ast_type,
// val_decl_to_let_expr, etc.) and PatExpr's composite/pat/expr
// fields remain after the New-1 resolver collapse — kept as
// future-use surface.
#![allow(dead_code)]

use crate::compile::core::{
    ConBind as CoreConBind, DatatypeBind as CoreDatatypeBind, Decl as CoreDecl,
    Expr as CoreExpr, Match as CoreMatch, Pat as CorePat,
    PatField as CorePatField, Step as CoreStep, StepKind as CoreStepKind,
    TypeBind as CoreTypeBind, ValBind as CoreValBind,
};
use crate::compile::expander;
use crate::compile::expander::and_all;
use crate::compile::free_finder::free_names_in;
use crate::compile::from_builder::FromBuilder;
use crate::compile::inliner::Env;
use crate::compile::library;
use crate::compile::library::{BuiltIn, BuiltInFunction};
use crate::compile::pat_coverage;
use crate::compile::postfix::{PostfixKind, peel_type, postfix_dispatch};
use crate::compile::record_modifiers::{self, Source};
use crate::compile::span::Span;
use crate::compile::type_resolver::{
    Resolved, TypeMap, Typed, ast_type_to_core_type,
    ast_type_to_core_type_with_vars,
};
use crate::compile::types;
use crate::compile::types::{
    Checks, Label, PrimitiveType, Type, TypeVariable, instantiate,
};
use crate::eval::code::LIBRARY;
use crate::eval::val::Val;
use crate::syntax::ast::{
    CastKind, DatatypeBind, Decl, DeclKind, Expr, ExprKind, FunMatch, Literal,
    LiteralKind, Match, Modifier, Pat, PatField, PatKind, Span as AstSpan,
    Step as AstStep, StepKind as AstStepKind, Type as AstType, TypeBind,
    TypeKind, ValBind,
};
use crate::syntax::parser;
use crate::unify::unifier::{ANON_CHECK_PREFIX, Var};
use std::cell::{Cell, RefCell};
use std::collections::{BTreeMap, HashMap, HashSet, VecDeque};
use std::rc::Rc;

/// Converts an AST to a Core tree.
pub fn resolve(resolved: &Resolved) -> (CoreDecl, Vec<(String, Span)>) {
    let session_fns = expander::FnEnv::new();
    resolve_with_session_fns(resolved, &session_fns)
}

/// Same as `resolve`, but seeds the predicate-inversion pass
/// with session-level function bindings from earlier statements.
pub fn resolve_with_session_fns(
    resolved: &Resolved,
    session_fns: &expander::FnEnv,
) -> (CoreDecl, Vec<(String, Span)>) {
    let empty_rec = expander::FnEnv::new();
    let (decl, _pre_fn_env, errors) =
        resolve_with_session_fns_rec(resolved, session_fns, &empty_rec);
    (decl, errors)
}

/// Same as [`resolve_with_session_fns`], but additionally accepts
/// a parallel `rec_session_fns` map of pre-expander fn bodies for
/// Phase 2 of recursive predicate inversion.
///
/// Returns the post-expander decl, the pre-expander `fn p => body`
/// bindings (for the shell to seed `rec_fn_bindings` if the
/// statement succeeds), and the resolver's errors. The pre-expander
/// bindings are extracted eagerly because `collect_fn_bindings`
/// only inspects top-level value-bindings, so we don't need the
/// whole pre-expander decl to survive past this point — avoiding
/// a full `CoreDecl` clone.
pub fn resolve_with_session_fns_rec(
    resolved: &Resolved,
    session_fns: &expander::FnEnv,
    rec_session_fns: &expander::FnEnv,
) -> (CoreDecl, expander::FnEnv, Vec<(String, Span)>) {
    let resolver = Resolver::new(&resolved.type_map, resolved.base_line);
    // A checked type that has no name may have been made in this very
    // statement -- a record modifier gives one -- and its conditions were
    // deduced here, so here is where they can be compiled. A later
    // statement that meets the type again could not.
    resolver.register_anon_checks();
    let pre_decl = resolver.resolve_decl(&resolved.decl);
    let mut pre_fn_env = expander::FnEnv::new();
    expander::collect_session_fn_bindings(&pre_decl, &mut pre_fn_env);
    // Run the predicate-inversion pass over the resolved decl (moved
    // by value), accumulating let-bound function definitions as we
    // walk so that `maybe_function` can inline them.
    let decl = expander::expand_decl_with_session_rec(
        pre_decl,
        &resolved.type_map.datatype_map(),
        session_fns,
        rec_session_fns,
    );
    // Any `Expr::Extent` that survived the expander represents an
    // unbounded variable predicate inversion couldn't ground. Surface
    // it as a compile-time error pointing at the original `from p`
    // step's span. Catching it here (rather than emitting a runtime
    // `Code::RaiseIllegalArgument` from the compiler) avoids the
    // dead-code path through code-generation and matches the
    // user-visible shape of other compile errors.
    {
        let mut errors = resolver.errors.borrow_mut();
        check_unbounded_extents(&decl, &mut errors);
    }
    (decl, pre_fn_env, resolver.errors.into_inner())
}

/// Walks `decl` after the expander pass and reports any
/// `Scan(_, Expr::Extent(_, span), _)` reachable from a concrete
/// query as an unbounded-variable compile error.
///
/// Function bodies are NOT recursed into — Extents there may
/// be grounded later by the inliner at a concrete call site
/// (the surrounding parameters become bindings only when the
/// function is applied with real arguments). A user-visible
/// error fires only at the call site, where the post-inline
/// pass flagged the Extent on a real `from`.
/// The message for an extent that could not be ground: the extent's
/// type is the collection, so name the element type, whose values are
/// the ones that cannot be enumerated.
fn unenumerable_message(t: &Rc<Type>) -> String {
    let element = match t.as_ref() {
        Type::List(e) | Type::Bag(e) => e.clone(),
        _ => t.clone(),
    };
    format!("cannot enumerate all values of type '{}'", element)
}

fn check_unbounded_extents(decl: &CoreDecl, errors: &mut Vec<(String, Span)>) {
    fn check_expr(e: &CoreExpr, errors: &mut Vec<(String, Span)>) {
        match e {
            CoreExpr::Apply(_, f, a, _) => {
                check_expr(f, errors);
                check_expr(a, errors);
            }
            CoreExpr::Case(_, subj, arms, _) => {
                check_expr(subj, errors);
                for m in arms {
                    check_expr(&m.expr, errors);
                }
            }
            CoreExpr::Extent(t, span) => {
                // An extent that is not under a scan at all: nothing
                // names it but its type.
                errors.push((unenumerable_message(t), span.clone()));
            }
            CoreExpr::Fn(_, _, _) => {
                // Skip function bodies: their Extents may be
                // grounded by inlining at the call site.
            }
            CoreExpr::Let(_, decls, body) => {
                for d in decls {
                    check_decl(d, errors);
                }
                check_expr(body, errors);
            }
            CoreExpr::Tuple(_, items) | CoreExpr::List(_, items) => {
                for i in items {
                    check_expr(i, errors);
                }
            }
            CoreExpr::Aggregate(_, l, r, _) => {
                check_expr(l, errors);
                check_expr(r, errors);
            }
            CoreExpr::From(_, steps)
            | CoreExpr::Exists(_, steps)
            | CoreExpr::Forall(_, steps) => {
                // A query whose only step is an ungrounded scan has
                // nothing else to blame, so it names the type whose
                // values cannot be enumerated; one of several names
                // the pattern instead. morel-java draws the same
                // distinction.
                let lone = steps.len() == 1;
                for s in steps {
                    check_step(s, lone, errors);
                }
            }
            _ => {}
        }
    }
    fn check_step(s: &CoreStep, lone: bool, errors: &mut Vec<(String, Span)>) {
        match &s.kind {
            CoreStepKind::Scan(pat, src, cond) => {
                if let CoreExpr::Extent(t, span) = src.as_ref() {
                    if lone {
                        errors.push((unenumerable_message(t), span.clone()));
                    } else {
                        let name = match pat.as_ref() {
                            CorePat::Identifier(_, n) => n.clone(),
                            _ => "_".to_string(),
                        };
                        errors.push((
                            format!("pattern '{}' is not grounded", name),
                            span.clone(),
                        ));
                    }
                } else {
                    check_expr(src, errors);
                }
                if let Some(c) = cond {
                    check_expr(c, errors);
                }
            }
            CoreStepKind::Where(c)
            | CoreStepKind::Yield(c)
            | CoreStepKind::Order(c)
            | CoreStepKind::Compute(c)
            | CoreStepKind::Skip(c)
            | CoreStepKind::Take(c) => check_expr(c, errors),
            CoreStepKind::Group(k, agg) => {
                check_expr(k, errors);
                if let Some(a) = agg {
                    check_expr(a, errors);
                }
            }
            CoreStepKind::Except(_, exprs)
            | CoreStepKind::Intersect(_, exprs)
            | CoreStepKind::Union(_, exprs) => {
                for e in exprs {
                    check_expr(e, errors);
                }
            }
            _ => {}
        }
    }
    fn check_decl(d: &CoreDecl, errors: &mut Vec<(String, Span)>) {
        match d {
            CoreDecl::NonRecVal(b) => check_expr(&b.expr, errors),
            CoreDecl::RecVal(binds) => {
                for b in binds {
                    check_expr(&b.expr, errors);
                }
            }
            _ => {}
        }
    }
    check_decl(decl, errors);
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
    /// Span of the receiver of the field selector being resolved, if
    /// any. A field error names the receiver -- the thing that is not a
    /// record -- rather than the whole projection, as morel-java and
    /// morel-go do.
    selector_receiver_span: RefCell<Option<Span>>,
    /// Names of user-defined functions whose first parameter is
    /// (or contains) `self`, so the postfix dispatcher can rewrite
    /// `x.name arg` into a direct application to `name`.
    self_fns: RefCell<HashSet<String>>,
    /// Collection kind (`Some(true)` = bag, `Some(false)` = list) of the
    /// input to the `compute`/`group`/`into` step currently being resolved.
    /// Used to dispatch an overloaded aggregate function (e.g.
    /// `Test.overCount`) to its bag or list variant. `None` elsewhere.
    aggregate_input_is_bag: Cell<Option<bool>>,
    /// Counter for the names of the temporary variables that building a
    /// modified record needs. `$` is not a character a user can write,
    /// so a generated name never captures one the user chose.
    temp_counter: Cell<u32>,
}

/// Builds `F elem`, where `F` is the functor of `map` (`ListMap`, `BagMap`,
/// `OptionMap` or `VectorMap`). Used to re-wrap a field type in the
/// receiver's functor layers when lowering safe navigation `e?.f`.
fn wrap_functor(map: BuiltInFunction, elem: &Rc<Type>) -> Rc<Type> {
    match map {
        BuiltInFunction::ListMap => Rc::new(Type::List(elem.clone())),
        BuiltInFunction::BagMap => Rc::new(Type::Bag(elem.clone())),
        BuiltInFunction::VectorMap => {
            Rc::new(Type::Data("vector".to_string(), vec![elem.clone()]))
        }
        _ => Rc::new(Type::Data("option".to_string(), vec![elem.clone()])),
    }
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
                    t: (*pat_exp.pat.type_()).clone(),
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
                    t: (*pat_exp.pat.type_()).clone(),
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
            t: (*expr_type).clone(),
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
            selector_receiver_span: RefCell::new(None),
            self_fns: RefCell::new(HashSet::new()),
            aggregate_input_is_bag: Cell::new(None),
            temp_counter: Cell::new(0),
        }
    }

    /// Returns a name no user can have written, for a temporary the
    /// building of a modified record introduces.
    fn temp_name(&self) -> String {
        let i = self.temp_counter.get();
        self.temp_counter.set(i + 1);
        format!("$v{}", i)
    }

    /// Converts a record that has modifiers into the `let`s it means:
    /// one per modifier, each binding the fields of the record the
    /// modifier before it produced, and ending in a record built from
    /// those fields.
    ///
    /// [`TypeResolver`] types the record as it is written, and leaves it
    /// to be built here, where the types are settled. Building it
    /// earlier would lose the type of the record being modified.
    fn to_core_modified(
        &self,
        base: &Expr,
        modifiers: &[Modifier],
        span: &Span,
    ) -> CoreExpr {
        // The base, and the argument of each `all` modifier, are
        // evaluated outside the modifiers -- in this environment, which
        // does not have their fields -- and in the order they are
        // written.
        let mut exprs: Vec<&Expr> = vec![base];
        for modifier in modifiers {
            if let Modifier::All(_, _, e) = modifier {
                exprs.push(e);
            }
        }
        self.bind_operands(modifiers, &exprs, 0, &mut Vec::new(), span)
    }

    /// Binds the operands of a modified record, then applies its
    /// modifiers.
    fn bind_operands(
        &self,
        modifiers: &[Modifier],
        exprs: &[&Expr],
        i: usize,
        operands: &mut Vec<CoreExpr>,
        span: &Span,
    ) -> CoreExpr {
        if i == exprs.len() {
            let base = operands[0].clone();
            return self.modify(modifiers, 0, base, operands, span);
        }
        let value = self.resolve_expr(exprs[i]);
        self.let_value(value, span, |id| {
            operands.push(id.clone());
            self.bind_operands(modifiers, exprs, i + 1, operands, span)
        })
    }

    /// Applies the modifiers of a record, from `i` onwards.
    fn modify(
        &self,
        modifiers: &[Modifier],
        i: usize,
        value: CoreExpr,
        operands: &[CoreExpr],
        span: &Span,
    ) -> CoreExpr {
        if i == modifiers.len() {
            return value;
        }
        let modifier = &modifiers[i];
        // Operand 0 is the base; the `all` arguments follow, in the
        // order the modifiers that carry them are written.
        let all = matches!(modifier, Modifier::All(..)).then(|| {
            1 + modifiers[..i]
                .iter()
                .filter(|m| matches!(m, Modifier::All(..)))
                .count()
        });
        self.let_value(value, span, |id| {
            let fields = types::record_fields(&id.type_());
            let names = label_names(&fields);
            let all_names = all.map(|k| {
                label_names(&types::record_fields(&operands[k].type_()))
            });
            // The rules were checked when the record was typed, so
            // applying them again cannot fail.
            let sources =
                record_modifiers::apply(modifier, &names, all_names.as_deref())
                    .expect("checked by TypeResolver");
            // Only an assignment has expressions, and only they can refer
            // to the fields by name.
            let bound: &[String] = if matches!(modifier, Modifier::Assign(..)) {
                &names
            } else {
                &[]
            };
            self.bind_fields(id, bound, 0, span, &|| {
                let record =
                    self.build(&sources, id, all.map(|k| &operands[k]), span);
                self.modify(modifiers, i + 1, record, operands, span)
            })
        })
    }

    /// Binds an expression to a name and applies `body` to it.
    ///
    /// The `let` is what stops the expression being evaluated twice, once
    /// to read its type and once for the result.
    fn let_value<F>(&self, value: CoreExpr, span: &Span, body: F) -> CoreExpr
    where
        F: FnOnce(&CoreExpr) -> CoreExpr,
    {
        if matches!(value, CoreExpr::Identifier(..)) {
            // Already a variable, so reading it twice costs nothing.
            return body(&value);
        }
        let t = value.type_();
        let name = self.temp_name();
        let id = CoreExpr::Identifier(t.clone(), name.clone());
        let body_expr = body(&id);
        self.core_let(CorePat::Identifier(t, name), value, body_expr, span)
    }

    /// Binds each field of a record to its own name, so that the
    /// expressions a modifier assigns can refer to it, and applies
    /// `body` in the environment that results.
    ///
    /// The names shadow the enclosing environment, which is what lets
    /// `{r replace i = j, j = i}` mean what it looks like.
    fn bind_fields(
        &self,
        record: &CoreExpr,
        fields: &[String],
        i: usize,
        span: &Span,
        body: &dyn Fn() -> CoreExpr,
    ) -> CoreExpr {
        if i == fields.len() {
            return body();
        }
        let field = &fields[i];
        let value = self.select(record, field, span);
        let pat = CorePat::Identifier(value.type_(), field.clone());
        let inner = self.bind_fields(record, fields, i + 1, span, body);
        self.core_let(pat, value, inner, span)
    }

    /// Builds the record that a modifier produces.
    ///
    /// Its type is derived from the fields, rather than read from the
    /// type map, because only the last modifier has an entry there, and
    /// because that entry is the type as the user would see it, whereas
    /// Core needs the type erased.
    fn build(
        &self,
        sources: &[(String, Source)],
        record: &CoreExpr,
        all_record: Option<&CoreExpr>,
        span: &Span,
    ) -> CoreExpr {
        let mut args: BTreeMap<Label, CoreExpr> = BTreeMap::new();
        for (label, source) in sources {
            let value = match source {
                Source::Kept(field) => self.select(record, field, span),
                Source::Taken { field, .. } => {
                    self.select(all_record.expect("all"), field, span)
                }
                Source::Assigned { expr, .. } => self.resolve_expr(expr),
            };
            args.insert(Label::from(label.as_str()), value);
        }
        let field_types = args
            .iter()
            .map(|(label, value)| (label.clone(), value.type_()))
            .collect();
        CoreExpr::Tuple(
            Rc::new(types::record_type(field_types)),
            args.into_values().collect(),
        )
    }

    /// Returns an expression that selects a field of a record.
    fn select(&self, record: &CoreExpr, field: &str, span: &Span) -> CoreExpr {
        let record_type = record.type_();
        let slot = record_type
            .lookup_field(field)
            .expect("field of a record whose fields are known");
        let field_type = types::record_fields(&record_type)
            .values()
            .nth(slot)
            .expect("slot")
            .clone();
        let selector_type =
            Rc::new(Type::Fn(record_type.clone(), field_type.clone()));
        CoreExpr::Apply(
            field_type,
            Box::new(CoreExpr::RecordSelector(selector_type, slot)),
            Box::new(record.clone()),
            span.clone(),
        )
    }

    /// Returns `let val <pat> = <value> in <body> end`.
    fn core_let(
        &self,
        pat: CorePat,
        value: CoreExpr,
        body: CoreExpr,
        _span: &Span,
    ) -> CoreExpr {
        let t = pat.type_();
        let decl = CoreDecl::NonRecVal(Box::new(CoreValBind {
            pat,
            t: (*t).clone(),
            expr: value,
            overload_pat: None,
            span: None,
        }));
        CoreExpr::Let(body.type_(), vec![decl], Box::new(body))
    }

    /// Wraps an expression in a check, if the type it is being bound at
    /// constrains anything.
    ///
    /// This is where a value flows into a claim: the binding says the
    /// value is a `nat`, so the condition the type carries must hold of
    /// it. Everywhere else the name has reduced to the type it
    /// abbreviates, so nothing is claimed and nothing need be checked.
    fn with_checks(&self, expr: CoreExpr, pat: &Pat, span: &Span) -> CoreExpr {
        match self.claimed_type(pat, &expr.type_()) {
            Some(claimed) => self.checked(expr, &claimed, span),
            None => expr,
        }
    }

    /// The checked type a pattern claims, or none if it claims nothing.
    ///
    /// A claim is an annotation the user wrote, not a type inference
    /// deduced. The two differ: inference gives the meet, which for a
    /// checked type is the type it abbreviates, so a deduced type has no
    /// condition left to check.
    fn claimed_type(&self, pat: &Pat, erased: &Type) -> Option<Type> {
        match &pat.kind {
            PatKind::Annotated(_, t) => self.claimed_ast_type(t),
            PatKind::As(_, inner) => self.claimed_type(inner, erased),
            // A pattern that destructures claims per component: an
            // annotation on one of them claims that one, and the rest
            // claim nothing. The shape is the value's, not the
            // pattern's, so that a record pattern which does not mention
            // every field still lines up with the value.
            PatKind::Tuple(pats) => {
                let fields = types::record_fields(erased);
                if pats.len() != fields.len() {
                    return None;
                }
                let claims: Vec<Option<Type>> = pats
                    .iter()
                    .zip(fields.values())
                    .map(|(p, t)| self.claimed_type(p, t))
                    .collect();
                if claims.iter().all(Option::is_none) {
                    return None;
                }
                Some(Type::Tuple(
                    claims
                        .into_iter()
                        .zip(fields.values())
                        .map(|(c, t)| {
                            Rc::new(c.unwrap_or_else(|| (**t).clone()))
                        })
                        .collect(),
                ))
            }
            PatKind::Record(pat_fields, _) => {
                let fields = types::record_fields(erased);
                let mut claims: BTreeMap<String, Type> = BTreeMap::new();
                for pat_field in pat_fields {
                    let (label, p) = match pat_field {
                        PatField::Labeled(_, name, p) => (name.clone(), p),
                        PatField::Anonymous(_, p) => (implicit_label(p)?, p),
                    };
                    let t = fields.get(&Label::from(label.as_str()))?;
                    if let Some(c) = self.claimed_type(p, t) {
                        claims.insert(label, c);
                    }
                }
                if claims.is_empty() {
                    return None;
                }
                let mut map = BTreeMap::new();
                for (label, t) in &fields {
                    let claim = claims
                        .remove(&label.to_string())
                        .unwrap_or_else(|| (**t).clone());
                    map.insert(label.clone(), Rc::new(claim));
                }
                Some(types::record_type(map))
            }
            _ => None,
        }
    }

    /// The type a written type names, as written -- keeping the aliases
    /// that say where the conditions are -- or none if it claims
    /// nothing.
    fn claimed_ast_type(&self, ast_type: &AstType) -> Option<Type> {
        let claimed = self.written_type(ast_type)?;
        if !self.has_check(&claimed) {
            return None;
        }
        // A check on a value is made when the value is made, and a
        // function value is not a value its type can be checked
        // against: to check `nat -> nat` every argument it is ever
        // given and every result it ever returns would have to be
        // checked, which means replacing the function with a proxy.
        // Rather than do that silently, or accept the claim and check
        // nothing, the claim is rejected.
        if claims_function(&claimed) {
            self.errors.borrow_mut().push((
                format!("cannot claim a checked function type '{}'", claimed),
                Span::from_pest_span(
                    &ast_type.span.trim_end().to_pest_span(),
                    self.base_line,
                ),
            ));
            return None;
        }
        Some(claimed)
    }

    /// The type a name means, as its declaration wrote it, if it means
    /// anything that carries a condition.
    fn named_type(&self, name: &str) -> Option<Type> {
        let body = self.type_map.type_aliases.get(name)?;
        let claimed = Type::Alias(
            name.to_string(),
            Rc::new(body.clone()),
            vec![],
            self.type_map.checks_of(name),
        );
        self.has_check(&claimed).then_some(claimed)
    }

    /// The type a checked type that has no name means, if the name is
    /// one.
    ///
    /// A named type says what it means through its declaration; this one
    /// has none, so its body is the type of the value that claims it, and
    /// its conditions are the ones its name was derived from.
    fn anon_checked_type(&self, name: &str, value: &CoreExpr) -> Option<Type> {
        if !name.starts_with(ANON_CHECK_PREFIX) {
            return None;
        }
        let checks = self.type_map.checks_of(name);
        if checks.is_empty() {
            return None;
        }
        Some(Type::Alias(name.to_string(), value.type_(), vec![], checks))
    }

    /// A written type, as written: keeping the aliases that say where
    /// the conditions are, so that a claim can be walked.
    ///
    /// Unlike the syntactic conversion, a name that is an alias stays
    /// one; unlike the deduced type, nothing has been expanded or met
    /// with anything.
    fn written_type(&self, ast_type: &AstType) -> Option<Type> {
        match &ast_type.kind {
            TypeKind::Checked(t, checks) => {
                // A condition written where a type is used claims what a
                // declared type's condition claims. The type has no name
                // of its own, so it takes the one its conditions give it.
                //
                // The body may be a type variable standing for whatever
                // inference gives the expression, which is how a condition
                // written on an expression rather than on a type is said.
                // Nothing is claimed of the body -- only the conditions
                // are -- so a variable will do where it is not written.
                let checks = Checks::new(checks.clone());
                let body = self
                    .written_type(t)
                    .unwrap_or(Type::Variable(TypeVariable::new(0)));
                Some(Type::Alias(
                    checks.anon_name(),
                    Rc::new(body),
                    vec![],
                    checks,
                ))
            }
            // `typeof e` names the type `e` was shown to have, conditions
            // and all, so an annotation that writes it claims what that
            // type claims.
            TypeKind::Expression(expr) => self
                .type_map
                .decl_exp_types
                .get(&expr.span.extent())
                .cloned(),
            TypeKind::Id(name) => match self.type_map.type_aliases.get(name) {
                Some(body) => Some(Type::Alias(
                    name.clone(),
                    Rc::new(body.clone()),
                    vec![],
                    self.type_map.checks_of(name),
                )),
                None => ast_type_to_core_type(ast_type),
            },
            TypeKind::Fn(a, b) => Some(Type::Fn(
                Rc::new(self.written_type(a)?),
                Rc::new(self.written_type(b)?),
            )),
            TypeKind::Tuple(types) => {
                let args: Vec<Rc<Type>> = types
                    .iter()
                    .map(|t| self.written_type(t).map(Rc::new))
                    .collect::<Option<_>>()?;
                Some(Type::Tuple(args))
            }
            TypeKind::Record(fields) => {
                let mut map = BTreeMap::new();
                for field in fields {
                    map.insert(
                        Label::from(field.label.name.as_str()),
                        Rc::new(self.written_type(&field.type_)?),
                    );
                }
                Some(types::record_type(map))
            }
            TypeKind::App(args, head) => {
                let TypeKind::Id(name) = &head.kind else {
                    return ast_type_to_core_type(ast_type);
                };
                let flat = AstType::flatten(args);
                let args: Vec<Rc<Type>> = flat
                    .iter()
                    .map(|t| self.written_type(t).map(Rc::new))
                    .collect::<Option<_>>()?;
                Some(match (name.as_str(), args.len()) {
                    ("list", 1) => Type::List(args[0].clone()),
                    ("bag", 1) => Type::Bag(args[0].clone()),
                    _ => Type::Data(name.clone(), args),
                })
            }
            _ => ast_type_to_core_type(ast_type),
        }
    }

    /// Whether a type, or any type within it, carries a condition.
    fn has_check(&self, claimed: &Type) -> bool {
        match claimed {
            Type::Alias(_, body, _, checks) => {
                !checks.is_empty() || self.has_check(body)
            }
            Type::Record(_, fields) => {
                fields.values().any(|t| self.has_check(t))
            }
            Type::Tuple(types) => types.iter().any(|t| self.has_check(t)),
            Type::List(elem) | Type::Bag(elem) => self.has_check(elem),
            // A datatype carries a condition if one of the types it was
            // given does; the walk finds where the constructors put it.
            Type::Data(_, args) => args.iter().any(|t| self.has_check(t)),
            // A function's parameter and result are looked at so that a
            // claim on them can be rejected; `deep_condition` builds no
            // condition for a function, so nothing reaches Core.
            Type::Fn(a, b) => self.has_check(a) || self.has_check(b),
            _ => false,
        }
    }

    /// Returns a condition that holds if `value` satisfies every
    /// condition its type carries, or none if the type carries none.
    ///
    /// A condition on a composite type is the conjunction of the
    /// conditions of its components and its own, in that order: a
    /// type's own condition may assume that its components satisfy
    /// theirs.
    ///
    /// Two types are walked in step. `claimed` is the type as the user
    /// wrote it, which keeps its aliases and so knows where the
    /// conditions are; `erased` is the same type with its aliases
    /// expanded, and is what the expressions being built are typed
    /// with, because an alias must not reach Core.
    ///
    /// `blame` says what the value is of -- `field empno`,
    /// `component 2`, `[_]` -- and is empty at the outermost level,
    /// where the value is the whole. A condition on a component raises
    /// for itself, so that the message names the component and quotes
    /// it; the outermost condition is left bare, for the `$check` that
    /// wraps the whole value to report.
    fn deep_condition(
        &self,
        claimed: &Type,
        erased: &Rc<Type>,
        value: &CoreExpr,
        blame: &str,
        span: &Span,
    ) -> Option<CoreExpr> {
        self.deep_condition_walking(
            claimed,
            erased,
            value,
            blame,
            span,
            &mut Vec::new(),
            true,
        )
    }

    /// As [`Self::deep_condition`], for a condition that asks rather
    /// than claims: a component that fails answers false instead of
    /// raising for itself.
    fn deep_condition_asking(
        &self,
        claimed: &Type,
        erased: &Rc<Type>,
        value: &CoreExpr,
        span: &Span,
    ) -> Option<CoreExpr> {
        self.deep_condition_walking(
            claimed,
            erased,
            value,
            "",
            span,
            &mut Vec::new(),
            false,
        )
    }

    /// As [`Self::deep_condition`], carrying the datatypes whose walk is
    /// in progress.
    ///
    /// A datatype may contain itself, so walking one cannot be an
    /// expansion. morel-java builds a function for each and calls it
    /// where the datatype recurs; morel-rust stops instead, which
    /// claims less and never more.
    fn deep_condition_walking(
        &self,
        claimed: &Type,
        erased: &Rc<Type>,
        value: &CoreExpr,
        blame: &str,
        span: &Span,
        walking: &mut Vec<(String, String)>,
        raising: bool,
    ) -> Option<CoreExpr> {
        match claimed {
            Type::Alias(name, body, _, checks) => {
                let inner = self.deep_condition_walking(
                    body, erased, value, blame, span, walking, raising,
                );
                if checks.is_empty() {
                    return inner;
                }
                // The borrow ends here: compiling the conditions may
                // register them, which borrows again.
                let compiled =
                    self.type_map.check_predicates.borrow().get(name).cloned();
                let predicates = match compiled {
                    Some(predicates) => predicates,
                    // A checked type that has no name was never declared,
                    // so nothing compiled its conditions when a
                    // declaration would have. Compile them here; they are
                    // in hand, on the type itself.
                    //
                    // Unless they were never deduced -- a condition
                    // written inside a type declaration, on a field say,
                    // is not yet -- and then there is nothing to compile
                    // them from, so the condition is dropped.
                    None if name.starts_with(ANON_CHECK_PREFIX)
                        && checks
                            .fns
                            .iter()
                            .all(|f| f.get_type(self.type_map).is_some()) =>
                    {
                        let predicates: Vec<CoreExpr> = checks
                            .fns
                            .iter()
                            .map(|f| self.make_total(self.resolve_expr(f), f))
                            .collect();
                        // Keep them: a later statement that meets this
                        // type again -- through `typeof`, say -- cannot
                        // compile them, because the conditions were
                        // deduced in this one.
                        self.type_map
                            .check_predicates
                            .borrow_mut()
                            .insert(name.clone(), predicates.clone());
                        predicates
                    }
                    None => return None,
                };
                let own = if blame.is_empty() || !raising {
                    and_all(self.conditions(value, &predicates, span))
                } else {
                    self.check_call(
                        value,
                        &type_moniker(claimed),
                        &predicates,
                        BuiltInFunction::ZRequire,
                        Rc::new(Type::Primitive(PrimitiveType::Bool)),
                        blame,
                        span,
                    )
                };
                Some(match inner {
                    None => own,
                    Some(inner) => and_all(vec![inner, own]),
                })
            }
            Type::Record(..) | Type::Tuple(_) => {
                let fields = types::record_fields(claimed);
                let erased_fields = types::record_fields(erased);
                let mut conditions = Vec::new();
                for (i, (label, field_type)) in fields.iter().enumerate() {
                    let erased_field = erased_fields.values().nth(i)?;
                    let field_value =
                        self.select_slot(value, i, erased_field.clone(), span);
                    if let Some(c) = self.deep_condition_walking(
                        field_type,
                        erased_field,
                        &field_value,
                        &append_blame(blame, &field_blame(claimed, label)),
                        span,
                        walking,
                        raising,
                    ) {
                        conditions.push(c);
                    }
                }
                (!conditions.is_empty()).then(|| and_all(conditions))
            }
            Type::List(elem) | Type::Bag(elem) => self.element_condition(
                elem, erased, value, blame, span, walking, raising,
            ),
            // A vector's elements are walked like a collection's.
            Type::Data(name, args) if name == "vector" && args.len() == 1 => {
                self.element_condition(
                    &args[0], erased, value, blame, span, walking, raising,
                )
            }
            Type::Data(name, args) => self.datatype_condition(
                name, args, erased, value, blame, span, walking, raising,
            ),
            _ => None,
        }
    }

    /// A condition that holds if every element of a collection or vector
    /// satisfies the element type's condition.
    #[allow(clippy::too_many_arguments)]
    fn element_condition(
        &self,
        elem: &Rc<Type>,
        erased: &Rc<Type>,
        value: &CoreExpr,
        blame: &str,
        span: &Span,
        walking: &mut Vec<(String, String)>,
        raising: bool,
    ) -> Option<CoreExpr> {
        {
            {
                if !self.has_check(elem) {
                    return None;
                }
                // Every element must satisfy the element type's
                // condition, so the collection is walked.
                let erased_elem = match erased.as_ref() {
                    Type::List(e) | Type::Bag(e) => e.clone(),
                    Type::Data(n, args) if n == "vector" && args.len() == 1 => {
                        args[0].clone()
                    }
                    _ => return None,
                };
                let name = self.temp_name();
                let element =
                    CoreExpr::Identifier(erased_elem.clone(), name.clone());
                let condition = self.deep_condition_walking(
                    elem,
                    &erased_elem,
                    &element,
                    &append_blame(blame, "[_]"),
                    span,
                    walking,
                    raising,
                )?;
                let bool_t = Rc::new(Type::Primitive(PrimitiveType::Bool));
                let predicate = CoreExpr::Fn(
                    Rc::new(Type::Fn(erased_elem.clone(), bool_t.clone())),
                    vec![CoreMatch {
                        pat: CorePat::Identifier(erased_elem.clone(), name),
                        expr: condition,
                    }],
                    span.clone(),
                );
                // A bag is walked by `Bag.all`, a list by `List.all`,
                // a vector by `Vector.all`.
                let all = match erased.as_ref() {
                    Type::Bag(_) => BuiltInFunction::BagAll,
                    Type::Data(n, _) if n == "vector" => {
                        BuiltInFunction::VectorAll
                    }
                    _ => BuiltInFunction::ListAll,
                };
                let all_t = Rc::new(Type::Fn(
                    predicate.type_(),
                    Rc::new(Type::Fn(erased.clone(), bool_t.clone())),
                ));
                Some(CoreExpr::Apply(
                    bool_t.clone(),
                    Box::new(CoreExpr::Apply(
                        Rc::new(Type::Fn(erased.clone(), bool_t)),
                        Box::new(CoreExpr::Literal(all_t, Val::Fn(all))),
                        Box::new(predicate),
                        span.clone(),
                    )),
                    Box::new(value.clone()),
                    span.clone(),
                ))
            }
        }
    }

    /// Returns a condition that holds if every value a datatype's
    /// constructors carry satisfies the conditions its type arguments
    /// carry.
    ///
    /// Without this a condition under a type parameter is claimed and
    /// never checked: `val w: nat option = SOME ~1` printed `nat option`
    /// and held a value that is not one. Records and collections were
    /// already walked; a datatype is the remaining way to reach a type.
    #[allow(clippy::too_many_arguments)]
    fn datatype_condition(
        &self,
        name: &str,
        args: &[Rc<Type>],
        erased: &Rc<Type>,
        value: &CoreExpr,
        blame: &str,
        span: &Span,
        walking: &mut Vec<(String, String)>,
        raising: bool,
    ) -> Option<CoreExpr> {
        let bool_t = Rc::new(Type::Primitive(PrimitiveType::Bool));
        // A datatype met again is called rather than expanded.
        if let Some((_, predicate)) = walking.iter().find(|(n, _)| n == name) {
            let fn_t = Rc::new(Type::Fn(erased.clone(), bool_t.clone()));
            return Some(CoreExpr::Apply(
                bool_t,
                Box::new(CoreExpr::Identifier(fn_t, predicate.clone())),
                Box::new(value.clone()),
                span.clone(),
            ));
        }
        let constructors =
            self.type_map.datatype_constructors.get(name)?.clone();
        let erased_args = match erased.as_ref() {
            Type::Data(_, erased_args) => erased_args.clone(),
            _ => return None,
        };
        // The condition is a function, applied to the value, because a
        // datatype may contain itself. A recursive datatype calls the
        // function being built; one that does not recurse builds it all
        // the same, and the inliner takes it away.
        let predicate_name = self.temp_name();
        let param_name = self.temp_name();
        let param = CoreExpr::Identifier(erased.clone(), param_name.clone());
        let t = erased.clone();
        walking.push((name.to_string(), predicate_name.clone()));
        let mut matches = Vec::new();
        let mut any = false;
        for constructor in &constructors {
            // A constructor that carries nothing has nothing to check.
            let arg_type = self.constructor_arg_type(constructor);
            let arm = match &arg_type {
                None => None,
                Some(arg_type) => {
                    let claimed_arg = instantiate(arg_type, args);
                    let erased_arg =
                        Rc::new(instantiate(arg_type, &erased_args));
                    if self.has_check(&claimed_arg) {
                        let arg_name = self.temp_name();
                        let arg_value = CoreExpr::Identifier(
                            erased_arg.clone(),
                            arg_name.clone(),
                        );
                        self.deep_condition_walking(
                            &claimed_arg,
                            &erased_arg,
                            &arg_value,
                            &append_blame(blame, constructor),
                            span,
                            walking,
                            raising,
                        )
                        .map(|condition| {
                            (
                                CorePat::Identifier(erased_arg, arg_name),
                                condition,
                            )
                        })
                    } else {
                        None
                    }
                }
            };
            let (pat, expr) = match arm {
                Some((arg_pat, condition)) => {
                    any = true;
                    (Some(Box::new(arg_pat)), condition)
                }
                None => (
                    arg_type.map(|arg_type| {
                        Box::new(CorePat::Wildcard(Rc::new(instantiate(
                            &arg_type,
                            &erased_args,
                        ))))
                    }),
                    CoreExpr::Literal(bool_t.clone(), Val::Bool(true)),
                ),
            };
            matches.push(CoreMatch {
                pat: CorePat::Constructor(t.clone(), constructor.clone(), pat),
                expr,
            });
        }
        walking.pop();
        if !any {
            return None;
        }
        let body = CoreExpr::Case(
            bool_t.clone(),
            Box::new(param),
            matches,
            span.clone(),
        );
        let fn_t = Rc::new(Type::Fn(erased.clone(), bool_t.clone()));
        let predicate = CoreExpr::Fn(
            fn_t.clone(),
            vec![CoreMatch {
                pat: CorePat::Identifier(erased.clone(), param_name),
                expr: body,
            }],
            span.clone(),
        );
        let decl = CoreDecl::RecVal(vec![CoreValBind {
            pat: CorePat::Identifier(fn_t.clone(), predicate_name.clone()),
            t: (*fn_t).clone(),
            expr: predicate,
            overload_pat: None,
            span: None,
        }]);
        Some(CoreExpr::Let(
            bool_t.clone(),
            vec![decl],
            Box::new(CoreExpr::Apply(
                bool_t,
                Box::new(CoreExpr::Identifier(fn_t, predicate_name)),
                Box::new(value.clone()),
                span.clone(),
            )),
        ))
    }

    /// The type of a constructor's argument, or none if it carries
    /// nothing.
    ///
    /// A user-declared constructor's is recorded by its declaration; a
    /// built-in one's is read from the type the library gives it.
    fn constructor_arg_type(&self, constructor: &str) -> Option<Type> {
        if let Some(t) = self.type_map.constructor_arg_types.get(constructor) {
            return Some(t.clone());
        }
        LIBRARY.with(|lib| {
            let BuiltIn::Fn(f) = lib.lookup(constructor)? else {
                return None;
            };
            if !f.is_constructor() {
                return None;
            }
            let mut t = lib.fn_type(f).as_ref();
            while let Type::Forall(inner, _) = t {
                t = inner;
            }
            match t {
                Type::Fn(arg, _) => Some((**arg).clone()),
                _ => None,
            }
        })
    }

    /// Returns an expression that selects the `i`th field of a record.
    fn select_slot(
        &self,
        record: &CoreExpr,
        slot: usize,
        field_type: Rc<Type>,
        span: &Span,
    ) -> CoreExpr {
        let selector_type =
            Rc::new(Type::Fn(record.type_(), field_type.clone()));
        CoreExpr::Apply(
            field_type,
            Box::new(CoreExpr::RecordSelector(selector_type, slot)),
            Box::new(record.clone()),
            span.clone(),
        )
    }

    /// Returns an expression that gives the value of `expr` if the
    /// conditions of the type it is claimed at hold of it, and otherwise
    /// raises `Constraint`.
    ///
    /// The `let` is what stops the expression being evaluated twice,
    /// once for the condition and once for the result.
    fn checked(&self, expr: CoreExpr, claimed: &Type, span: &Span) -> CoreExpr {
        self.checked_blamed(expr, claimed, "", span)
    }

    /// As [`Self::checked`], but says what the value is of, for a value
    /// that is a component of something -- the argument of a
    /// constructor, say.
    fn checked_blamed(
        &self,
        expr: CoreExpr,
        claimed: &Type,
        blame: &str,
        span: &Span,
    ) -> CoreExpr {
        self.let_value(expr, span, |id| {
            let erased = id.type_();
            let Some(condition) =
                self.deep_condition(claimed, &erased, id, blame, span)
            else {
                return id.clone();
            };
            self.apply_check(
                condition,
                id,
                &type_moniker(claimed),
                BuiltInFunction::ZCheck,
                erased,
                blame,
                span,
            )
        })
    }

    /// The conjuncts of a type's own conditions, of a value.
    fn conditions(
        &self,
        value: &CoreExpr,
        predicates: &[CoreExpr],
        span: &Span,
    ) -> Vec<CoreExpr> {
        let bool_t = Rc::new(Type::Primitive(PrimitiveType::Bool));
        predicates
            .iter()
            .map(|p| {
                CoreExpr::Apply(
                    bool_t.clone(),
                    Box::new(p.clone()),
                    Box::new(value.clone()),
                    span.clone(),
                )
            })
            .collect()
    }

    /// Applies one of the checking operators to a value and the
    /// conjunction of its type's own conditions.
    fn check_call(
        &self,
        id: &CoreExpr,
        name: &str,
        predicates: &[CoreExpr],
        operator: BuiltInFunction,
        result_t: Rc<Type>,
        blame: &str,
        span: &Span,
    ) -> CoreExpr {
        let condition = and_all(self.conditions(id, predicates, span));
        self.apply_check(condition, id, name, operator, result_t, blame, span)
    }

    /// Applies one of the checking operators to a value and a condition.
    fn apply_check(
        &self,
        condition: CoreExpr,
        id: &CoreExpr,
        name: &str,
        operator: BuiltInFunction,
        result_t: Rc<Type>,
        blame: &str,
        span: &Span,
    ) -> CoreExpr {
        {
            let bool_t = Rc::new(Type::Primitive(PrimitiveType::Bool));
            let string_t = Rc::new(Type::Primitive(PrimitiveType::String));
            let value_t = id.type_();
            // Every clause must hold, so they are conjoined; the
            // branches within one clause are alternatives, and the
            // condition itself decides between them.
            let arg_t = Rc::new(Type::Tuple(vec![
                bool_t,
                value_t.clone(),
                string_t.clone(),
                string_t.clone(),
            ]));
            let arg = CoreExpr::Tuple(
                arg_t.clone(),
                vec![
                    condition,
                    id.clone(),
                    CoreExpr::Literal(
                        string_t.clone(),
                        Val::String(Rc::from(name)),
                    ),
                    CoreExpr::Literal(string_t, Val::String(Rc::from(blame))),
                ],
            );
            let fn_t = Rc::new(Type::Fn(arg_t, result_t.clone()));
            CoreExpr::Apply(
                result_t,
                Box::new(CoreExpr::Literal(fn_t, Val::Fn(operator))),
                Box::new(arg),
                span.clone(),
            )
        }
    }

    /// Makes a condition total, by appending `_ => false` if it does not
    /// already match every value.
    ///
    /// A condition need not be exhaustive: `type z = int check 0 =>
    /// true` says that zero is the only value of the type, and reads
    /// better than spelling out the other case. Without this the
    /// condition would fail to match any other value, rather than
    /// rejecting it.
    ///
    /// The appended branch is not part of the type as it was written,
    /// so it reaches only the compiled condition, never the display.
    fn make_total(&self, predicate: CoreExpr, ast: &Expr) -> CoreExpr {
        let CoreExpr::Fn(t, matches, span) = predicate else {
            return predicate;
        };
        let ExprKind::Fn(ast_matches) = &ast.kind else {
            return CoreExpr::Fn(t, matches, span);
        };
        if pat_coverage::is_exhaustive(ast_matches, self.type_map) {
            return CoreExpr::Fn(t, matches, span);
        }
        let arg_type = matches[0].pat.type_();
        let mut matches = matches;
        matches.push(CoreMatch {
            pat: CorePat::Wildcard(arg_type),
            expr: CoreExpr::Literal(
                Rc::new(Type::Primitive(PrimitiveType::Bool)),
                Val::Bool(false),
            ),
        });
        CoreExpr::Fn(t, matches, span)
    }

    /// Reports an error if a condition refers to anything but the value
    /// it is given and the standard basis.
    ///
    /// That is what lets a checked type be interned like any other type
    /// -- two are the same type when their conditions are textually
    /// equal, which would not follow if a condition could also depend on
    /// an environment -- and it settles what a condition means when the
    /// names it used are re-bound, by making the question not arise.
    ///
    /// Closedness is decided by the binding rather than the name, so
    /// shadowing a basis name does not smuggle an environment in.
    fn check_closed(&self, name: &str, predicate: &CoreExpr, span: &Span) {
        for free in free_names_in(predicate) {
            if self.type_map.user_bindings.contains(&free)
                || library::lookup(&free).is_none()
            {
                self.errors.borrow_mut().push((
                    format!(
                        "condition of checked type '{}' is not closed; \
                         it refers to '{}'",
                        name, free
                    ),
                    span.clone(),
                ));
                return;
            }
        }
    }

    /// Returns `SOME v`.
    fn some(
        &self,
        value: CoreExpr,
        option_t: &Rc<Type>,
        span: &Span,
    ) -> CoreExpr {
        let fn_t = Rc::new(Type::Fn(value.type_(), Rc::clone(option_t)));
        CoreExpr::Apply(
            Rc::clone(option_t),
            Box::new(CoreExpr::Literal(
                fn_t,
                Val::Fn(BuiltInFunction::OptionSome),
            )),
            Box::new(value),
            span.clone(),
        )
    }

    /// Returns an expression that gives `SOME v` if the conditions of
    /// the type hold of `v`, and `NONE` if they do not:
    ///
    /// ```text
    /// let val v = e in if c1 v andalso c2 v then SOME v else NONE end
    /// ```
    ///
    /// `asOpt` asks rather than claims, so a condition that is false is
    /// an answer; but one that raises has no answer, so it raises too.
    fn checked_opt(
        &self,
        expr: CoreExpr,
        claimed: &Type,
        option_t: &Rc<Type>,
        span: &Span,
    ) -> CoreExpr {
        self.let_value(expr, span, |id| {
            let erased = id.type_();
            let condition = self
                .deep_condition(claimed, &erased, id, "", span)
                .expect("the type claims something");
            let attempt = self.apply_check(
                condition,
                id,
                &type_moniker(claimed),
                BuiltInFunction::ZAttempt,
                Rc::new(Type::Primitive(PrimitiveType::Bool)),
                "",
                span,
            );
            let bool_t = Rc::new(Type::Primitive(PrimitiveType::Bool));
            CoreExpr::Case(
                Rc::clone(option_t),
                Box::new(attempt),
                vec![
                    CoreMatch {
                        pat: CorePat::Literal(bool_t.clone(), Val::Bool(true)),
                        expr: self.some(id.clone(), option_t, span),
                    },
                    CoreMatch {
                        pat: CorePat::Literal(bool_t, Val::Bool(false)),
                        expr: CoreExpr::Literal(
                            Rc::clone(option_t),
                            Val::Fn(BuiltInFunction::OptionNone),
                        ),
                    },
                ],
                span.clone(),
            )
        })
    }

    /// The condition of the checked type a scan is over, or none if it
    /// is not over one.
    ///
    /// A scan over a checked type enumerates the values of that type,
    /// so the type's condition belongs in the scan's filter, where the
    /// planner can use it to generate the values rather than generate
    /// and reject them. It does not raise: which values the type has is
    /// the question being asked, not something already claimed of a
    /// value in hand.
    fn scan_type_condition(
        &self,
        pat: &Pat,
        core_pat: &CorePat,
        span: &Span,
    ) -> Option<CoreExpr> {
        let PatKind::Annotated(_, ast_type) = &pat.kind else {
            return None;
        };
        let claimed = self.claimed_ast_type(ast_type)?;
        // The erased type comes from the value, not the pattern: a
        // record pattern reaches Core as a tuple, whose fields are
        // named 1, 2.
        let value = self.row_value(core_pat, &claimed)?;
        let erased = value.type_();
        self.deep_condition_asking(&claimed, &erased, &value, span)
    }

    /// An expression for the row a scan's pattern binds, or none if the
    /// pattern is one this does not know how to reassemble.
    fn row_value(
        &self,
        core_pat: &CorePat,
        claimed: &Type,
    ) -> Option<CoreExpr> {
        match core_pat {
            CorePat::Identifier(t, name) => {
                Some(CoreExpr::Identifier(t.clone(), name.clone()))
            }
            CorePat::Record(_, pat_fields, _) => {
                // A record pattern binds its fields by name.
                let fields = types::record_fields(claimed);
                let mut values = Vec::with_capacity(fields.len());
                for label in fields.keys() {
                    let name = label.to_string();
                    let bound = pat_fields.iter().find_map(|f| match f {
                        CorePatField::Labeled(l, p) if *l == name => {
                            Some(p.as_ref())
                        }
                        _ => None,
                    })?;
                    let CorePat::Identifier(t, bound_name) = bound else {
                        return None;
                    };
                    values.push(CoreExpr::Identifier(
                        t.clone(),
                        bound_name.clone(),
                    ));
                }
                let types_: BTreeMap<Label, Rc<Type>> = fields
                    .keys()
                    .cloned()
                    .zip(values.iter().map(CoreExpr::type_))
                    .collect();
                Some(CoreExpr::Tuple(
                    Rc::new(types::record_type(types_)),
                    values,
                ))
            }
            CorePat::Tuple(_, args) => {
                // A record pattern, `{i, j}`, reaches Core as a tuple of
                // the fields in field order, so the names -- and the
                // types the condition is written against -- come from
                // the type the user wrote, not from the pattern.
                let fields = types::record_fields(claimed);
                if fields.len() != args.len() {
                    return None;
                }
                let mut values = Vec::with_capacity(args.len());
                for arg in args {
                    let CorePat::Identifier(t, name) = arg else {
                        return None;
                    };
                    values.push(CoreExpr::Identifier(t.clone(), name.clone()));
                }
                let types_: BTreeMap<Label, Rc<Type>> = fields
                    .keys()
                    .cloned()
                    .zip(values.iter().map(CoreExpr::type_))
                    .collect();
                Some(CoreExpr::Tuple(
                    Rc::new(types::record_type(types_)),
                    values,
                ))
            }
            _ => None,
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
            DeclKind::FloatingAttr(_) => {
                // Floating attributes carry no runtime semantics; emit a
                // unit no-op binding so the rest of the pipeline can
                // ignore them.
                let unit_type = Rc::new(Type::Primitive(PrimitiveType::Unit));
                CoreDecl::NonRecVal(Box::new(CoreValBind {
                    pat: CorePat::Tuple(unit_type.clone(), vec![]),
                    t: (*unit_type).clone(),
                    expr: CoreExpr::Tuple(unit_type, vec![]),
                    overload_pat: None,
                    span: None,
                }))
            }
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
                let unit_type = Rc::new(Type::Primitive(PrimitiveType::Unit));
                CoreDecl::NonRecVal(Box::new(CoreValBind {
                    pat: CorePat::Tuple(unit_type.clone(), vec![]),
                    t: (*unit_type).clone(),
                    expr: CoreExpr::Tuple(unit_type, vec![]),
                    overload_pat: None,
                    span: None,
                }))
            }
            DeclKind::Type(type_binds) => CoreDecl::Type(
                type_binds
                    .iter()
                    .map(|tb| self.resolve_type_bind(tb, &decl.span))
                    .collect(),
            ),
            DeclKind::Val(rec, _overload, val_binds) => {
                // Uses the new resolve_val_decl method.
                let resolved_val_decl = self.resolve_val_decl(val_binds, *rec);

                // Use the expression's type for the val binding.
                // For query expressions (From), the FromBuilder
                // computes the authoritative collection type
                // (List vs Bag) via the `ordered` flag.
                let to_val_bind = |pe: &PatExpr| {
                    // For query expressions (From) whose type is a
                    // collection (List or Bag), use the expr's type
                    // which has the correct collection kind from
                    // FromBuilder's `ordered` flag.
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
                        _ => (*pat_type).clone(),
                    };
                    CoreValBind {
                        pat: pe.pat.clone().with_type(Rc::new(t.clone())),
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
            ExprKind::Aggregate(a0, a1) => {
                let fn_core = self
                    .aggregate_input_is_bag
                    .get()
                    .and_then(|is_bag| self.dispatch_collection_fn(a0, is_bag))
                    .unwrap_or_else(|| self.resolve_expr(a0));
                // `sum over e` on an empty group has no element to dispatch
                // on at run time, so bind the zero to the static element
                // type here; otherwise a real sum would yield the int zero.
                let fn_core = Self::specialize_sum(
                    fn_core,
                    a1.get_type(self.type_map).as_deref(),
                );
                CoreExpr::Aggregate(
                    t,
                    Box::new(fn_core),
                    Box::new(self.resolve_expr(a1)),
                    span.clone(),
                )
            }
            ExprKind::AndAlso(a0, a1) => {
                self.call2(t, BuiltInFunction::BoolAndAlso, &span, a0, a1)
            }
            ExprKind::Annotated(inner, ann) => {
                // An ascription is a claim, like a binding, so it is
                // checked wherever it appears -- not only where its
                // value is bound.
                let value = self.resolve_expr(inner);
                match self.claimed_ast_type(ann) {
                    Some(claimed) => self.checked(value, &claimed, &span),
                    None => value,
                }
            }
            ExprKind::Append(a0, a1) => {
                self.call2(t, BuiltInFunction::ListAt, &span, a0, a1)
            }
            ExprKind::Apply(func, arg) => {
                // Applying a datatype constructor is a construction
                // site, like a binding: `Box ~1` claims that `~1` is a
                // `nat`, because that is what `Box` was declared to
                // hold.
                if let ExprKind::Identifier(name) = &func.kind
                    && let Some(arg_type) =
                        self.type_map.constructor_arg_types.get(name)
                    && self.has_check(arg_type)
                {
                    let arg_type = arg_type.clone();
                    let core_arg = self.resolve_expr(arg);
                    let blame = format!("argument of {}", name);
                    // The constructor is what claims the type, so it is
                    // what the message blames -- not the application.
                    let fn_span = Span::from_pest_span(
                        &func.span.to_pest_span(),
                        self.base_line,
                    );
                    let checked = self
                        .checked_blamed(core_arg, &arg_type, &blame, &fn_span);
                    return CoreExpr::Apply(
                        t,
                        Box::new(self.resolve_expr(func)),
                        Box::new(checked),
                        span.clone(),
                    );
                }
                // Safe navigation `e?.f`: lower to a projection through the
                // receiver's functor layers.
                if let ExprKind::SafeRecordSelector(name) = &func.kind {
                    return self.resolve_safe_nav(t, name, arg, &span);
                }
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
                // Dispatch `Relational.sum coll` to sum$int/sum$real by the
                // element type, so plans read `Relational.sum$int` as in
                // morel-java. The bare-identifier `sum` is handled by
                // `specialize_sum` in the identifier arm.
                let is_relational_sum = match &func.kind {
                    ExprKind::Apply(sel, recv) => matches!(
                        (&sel.kind, &recv.kind),
                        (
                            ExprKind::RecordSelector(member),
                            ExprKind::Identifier(structure),
                        ) if member == "sum" && structure == "Relational"
                    ),
                    // The global alias `sum` needs the same treatment.
                    ExprKind::Identifier(name) => name == "sum",
                    _ => false,
                };
                if is_relational_sum
                    && let Some(ty) = arg.get_type(self.type_map)
                {
                    let elem = match ty.as_ref() {
                        Type::Bag(e) | Type::List(e) => Some(e.as_ref()),
                        _ => None,
                    };
                    match elem {
                        Some(Type::Primitive(PrimitiveType::Int)) => {
                            return self.call1(
                                t,
                                BuiltInFunction::RelationalSumInt,
                                arg,
                                &span,
                            );
                        }
                        Some(Type::Primitive(PrimitiveType::Real)) => {
                            return self.call1(
                                t,
                                BuiltInFunction::RelationalSumReal,
                                arg,
                                &span,
                            );
                        }
                        _ => {}
                    }
                }
                // Try postfix method-call rewriting. Pattern: outer
                // Apply wraps an
                // inner `Apply(RecordSelector(name), recv)` that
                // couldn't be a field projection on `recv`.
                if let Some(core) = self.try_postfix_call(&t, func, arg, &span)
                {
                    return core;
                }
                // A field error names the receiver, so make the
                // argument's span available while the selector resolves.
                let saved = self.selector_receiver_span.replace(Some(
                    Span::from_pest_span(
                        &arg.span.to_pest_span(),
                        self.base_line,
                    ),
                ));
                let func_core = self.resolve_expr(func);
                *self.selector_receiver_span.borrow_mut() = saved;
                CoreExpr::Apply(
                    t,
                    Box::new(func_core),
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
            ExprKind::Cast(kind, inner, target) => {
                let value = self.resolve_expr(inner);
                let Some(claimed) = self.claimed_ast_type(target) else {
                    // Converting to a type that constrains nothing
                    // claims nothing, so it is erased, as an annotation
                    // is -- except that `asOpt` still has to answer.
                    return match kind {
                        CastKind::As => value,
                        CastKind::AsOpt => self.some(value, &t, &span),
                    };
                };
                match kind {
                    CastKind::As => self.checked(value, &claimed, &span),
                    CastKind::AsOpt => {
                        self.checked_opt(value, &claimed, &t, &span)
                    }
                }
            }
            ExprKind::Check(e, checks) => {
                // A condition written on an expression is a claim, like
                // an ascription, so it is checked where it is written.
                let checks = Checks::new(checks.clone());
                let value = self.resolve_expr(e);
                let claimed = Type::Alias(
                    checks.anon_name(),
                    value.type_(),
                    vec![],
                    checks,
                );
                self.checked(value, &claimed, &span)
            }
            ExprKind::Cons(a0, a1) => {
                self.call2(t, BuiltInFunction::ListCons, &span, a0, a1)
            }
            ExprKind::Current => CoreExpr::Current(t),
            ExprKind::Div(a0, a1) => {
                let f = if self.is_word(a0) {
                    BuiltInFunction::WordDiv
                } else {
                    BuiltInFunction::IntDiv
                };
                self.call2(t, f, &span, a0, a1)
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

                expander::expand_from(
                    builder
                        .build_simplify()
                        .expect("Failed to build EXISTS expression"),
                    &self.type_map.datatype_map(),
                )
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

                let from_expr = expander::expand_from(
                    builder
                        .build_simplify()
                        .expect("Failed to build FORALL expression"),
                    &self.type_map.datatype_map(),
                );

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
                    Type::Primitive(PrimitiveType::Word) => {
                        self.call2(t, BuiltInFunction::WordOpGt, &span, a0, a1)
                    }
                    _ => self.call2(t, BuiltInFunction::GGt, &span, a0, a1),
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
                    Type::Primitive(PrimitiveType::Word) => {
                        self.call2(t, BuiltInFunction::WordOpGe, &span, a0, a1)
                    }
                    Type::Primitive(PrimitiveType::Char) => {
                        self.call2(t, BuiltInFunction::CharGe, &span, a0, a1)
                    }
                    _ => self.call2(t, BuiltInFunction::GGe, &span, a0, a1),
                }
            }
            ExprKind::Identifier(name) => {
                // Check if this identifier refers to a global built-in
                // function. Global constructors like DESC need to be
                // resolved to literals so they can be compiled properly.
                // However, if the identifier is locally bound (e.g.
                // as a function parameter or let binding), the local
                // binding shadows the built-in.
                // A name the user has bound is the user's, whatever it
                // is: `val not = fn b => true` declares a value of their
                // own, and `not` afterwards means that one. Whether a
                // reference is to the basis is decided by the binding,
                // not by the name.
                let is_shadowed = self.type_map.user_bindings.contains(name)
                    || if let Some(local_type) = expr.get_type(self.type_map) {
                        // A local binding of a basis name shadows it too.
                        // This does not see one whose type is the same as
                        // the built-in's, which the binding above does.
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

                let bool_type = Rc::new(Type::Primitive(PrimitiveType::Bool));
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
                    Type::Primitive(PrimitiveType::Word) => {
                        self.call2(t, BuiltInFunction::WordOpLt, &span, a0, a1)
                    }
                    _ => self.call2(t, BuiltInFunction::GLt, &span, a0, a1),
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
                    Type::Primitive(PrimitiveType::Word) => {
                        self.call2(t, BuiltInFunction::WordOpLe, &span, a0, a1)
                    }
                    _ => self.call2(t, BuiltInFunction::GLe, &span, a0, a1),
                }
            }
            ExprKind::Let(decls, body) => {
                // Register any user-defined `fun name self …` before
                // resolving the body, so postfix calls in the body can
                // dispatch to them.
                self.register_self_fns(decls);
                let resolved_decls: Vec<_> =
                    decls.iter().map(|d| self.resolve_decl(d)).collect();
                let mut result = self.resolve_expr(body);
                // Declarations in a `let` are sequential: each is in
                // scope for those that follow it, so
                // `let val x = 1 fun g y = x + y in g 5 end` must give
                // 6. Nest them, one declaration per `Let`, the shape
                // morel-java's `Core.Let` enforces by holding a single
                // declaration.
                for d in resolved_decls.into_iter().rev() {
                    result =
                        CoreExpr::Let(t.clone(), vec![d], Box::new(result));
                }
                result
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
                    Type::Primitive(PrimitiveType::Word) => self.call2(
                        t,
                        BuiltInFunction::WordOpMinus,
                        &span,
                        a0,
                        a1,
                    ),
                    _ => self.call2(t, BuiltInFunction::GMinus, &span, a0, a1),
                }
            }
            ExprKind::Mod(a0, a1) => {
                let f = if self.is_word(a0) {
                    BuiltInFunction::WordMod
                } else {
                    BuiltInFunction::IntMod
                };
                self.call2(t, f, &span, a0, a1)
            }
            ExprKind::Negate(a0) => {
                match a0.get_type(self.type_map).expect("type").as_ref() {
                    Type::Primitive(PrimitiveType::Int) => {
                        self.call1(t, BuiltInFunction::IntNegate, a0, &span)
                    }
                    Type::Primitive(PrimitiveType::Real) => {
                        self.call1(t, BuiltInFunction::RealNegate, a0, &span)
                    }
                    Type::Primitive(PrimitiveType::Word) => {
                        self.call1(t, BuiltInFunction::WordOpNegate, a0, &span)
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
                    _ => self.call2(t, BuiltInFunction::GNe, &span, a0, a1),
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
                    Type::Primitive(PrimitiveType::Word) => self.call2(
                        t,
                        BuiltInFunction::WordOpPlus,
                        &span,
                        a0,
                        a1,
                    ),
                    // Polymorphic / unconstrained type variable: use the
                    // generic dispatcher which resolves at runtime.
                    _ => self.call2(t, BuiltInFunction::GPlus, &span, a0, a1),
                }
            }
            ExprKind::Raise(e) => {
                CoreExpr::Raise(t, Box::new(self.resolve_expr(e)), span.clone())
            }
            ExprKind::Record(with_base, fields, modifiers) => {
                match with_base {
                    Some(base) if !modifiers.is_empty() => {
                        let built =
                            self.to_core_modified(base, modifiers, &span);
                        // A chain that leaves the record's shape alone
                        // gives back the type it was given, and the
                        // type resolver says so by giving the two the
                        // same type. That is the chain claiming it: the
                        // field keeps its declared type, so the value
                        // assigned to it must have it, and the claim is
                        // checked here because nobody else wrote the
                        // type down.
                        let claimed = self
                            .type_map
                            .claiming_records
                            .get(&expr.span.extent())
                            .and_then(|name| {
                                self.named_type(name).or_else(|| {
                                    self.anon_checked_type(name, &built)
                                })
                            });
                        // The deduced type has been met with what was
                        // assigned to each field, so it is the alias's
                        // name that says what was claimed, and the
                        // declaration that says what the name means.
                        match claimed {
                            Some(claimed) => {
                                self.checked(built, &claimed, &span)
                            }
                            None => built,
                        }
                    }
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
                                    let selector_type = Rc::new(Type::Fn(
                                        base_type.clone(),
                                        field_type.clone(),
                                    ));
                                    let selector = CoreExpr::RecordSelector(
                                        selector_type,
                                        slot,
                                    );
                                    CoreExpr::Apply(
                                        field_type.clone(),
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
                    let error_span = self
                        .selector_receiver_span
                        .borrow()
                        .clone()
                        .unwrap_or_else(|| span.clone());
                    self.errors.borrow_mut().push((msg, error_span));
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
                    Type::Primitive(PrimitiveType::Word) => self.call2(
                        t,
                        BuiltInFunction::WordOpTimes,
                        &span,
                        a0,
                        a1,
                    ),
                    _ => self.call2(t, BuiltInFunction::GTimes, &span, a0, a1),
                }
            }
            ExprKind::Tuple(elements) => CoreExpr::Tuple(
                t,
                elements.iter().map(|e| self.resolve_expr(e)).collect(),
            ),
            ExprKind::TypeString(operand) => {
                // Prefer the type as it would be displayed, which keeps an
                // alias; the expanded type would say "int" for a value the
                // shell prints as `foo`.
                let moniker = operand
                    .id
                    .and_then(|id| self.type_map.get_type_with_alias(id))
                    .or_else(|| operand.get_type(self.type_map))
                    .map(|ty| ty.to_string())
                    .unwrap_or_default();
                CoreExpr::Literal(t, Val::String((moniker).into()))
            }
            _ => todo!("Unimplemented expression kind: {:?}", expr.kind),
        }
    }

    /// Returns true if `expr` has type `word`, used to dispatch the
    /// overloaded operators (`+`, `-`, `*`, `div`, `mod`) to their `Word`
    /// variants.
    fn is_word(&self, expr: &Expr) -> bool {
        matches!(
            expr.get_type(self.type_map).as_deref(),
            Some(Type::Primitive(PrimitiveType::Word))
        )
    }

    /// When an aggregate function `a0 over a1` is a qualified structure
    /// member that has both a bag and a list variant (e.g.
    /// `Test.overCount`), choose the variant matching the input
    /// collection's kind, mirroring morel-java's rule "if both list and
    /// bag forms exist, choose the one that matches the input collection
    /// type". Returns `None` (so normal resolution applies) otherwise.
    fn dispatch_collection_fn(
        &self,
        fn_expr: &Expr,
        input_is_bag: bool,
    ) -> Option<CoreExpr> {
        // `fn_expr` must be `Structure.member`, i.e.
        // `Apply(RecordSelector(member), Identifier(structure))`.
        let ExprKind::Apply(func, recv) = &fn_expr.kind else {
            return None;
        };
        let ExprKind::RecordSelector(member) = &func.kind else {
            return None;
        };
        let ExprKind::Identifier(structure) = &recv.kind else {
            return None;
        };
        let (bag_fn, list_fn) =
            library::aggregate_collection_variants(structure, member)?;
        let chosen = if input_is_bag { bag_fn } else { list_fn };
        Some(CoreExpr::Literal(chosen.get_type(), Val::Fn(chosen)))
    }

    /// Replaces a reference to the type-dispatched `Relational.sum` with
    /// the `int` or `real` variant when the element type is known. The
    /// dispatched version reads the element type off the first element,
    /// so an empty collection would always sum to the int zero.
    fn specialize_sum(fn_core: CoreExpr, elem_type: Option<&Type>) -> CoreExpr {
        let CoreExpr::Literal(_, Val::Fn(BuiltInFunction::RelationalSum)) =
            &fn_core
        else {
            return fn_core;
        };
        let f = match elem_type {
            Some(Type::Primitive(PrimitiveType::Int)) => {
                BuiltInFunction::RelationalSumInt
            }
            Some(Type::Primitive(PrimitiveType::Real)) => {
                BuiltInFunction::RelationalSumReal
            }
            _ => return fn_core,
        };
        CoreExpr::Literal(f.get_type(), Val::Fn(f))
    }

    fn call1(
        &self,
        t: Rc<Type>,
        f: BuiltInFunction,
        a0: &Expr,
        span: &Span,
    ) -> CoreExpr {
        let fn_type = f.get_type();
        let fn_literal = CoreExpr::Literal(fn_type.clone(), Val::Fn(f));
        let c0 = self.resolve_expr(a0);
        CoreExpr::Apply(t, Box::new(fn_literal), Box::new(c0), span.clone())
    }

    /// Lowers safe navigation `e?.f` by tunneling through the receiver's
    /// functor layers (option, list, bag, vector) down to the record:
    /// `F1.map (F2.map (... (Fn.map #f))) e`. The field's own type is
    /// preserved, so the result is the field's type wrapped in those same
    /// functor layers.
    fn resolve_safe_nav(
        &self,
        t: Rc<Type>,
        name: &str,
        arg: &Expr,
        span: &Span,
    ) -> CoreExpr {
        let core_arg = self.resolve_expr(arg);

        // Peel the functor layers (outermost first) down to the record.
        let mut maps: Vec<BuiltInFunction> = Vec::new();
        let mut cur = core_arg.type_();
        loop {
            let next = match cur.as_ref() {
                Type::List(elem) => (BuiltInFunction::ListMap, elem.clone()),
                Type::Bag(elem) => (BuiltInFunction::BagMap, elem.clone()),
                Type::Data(n, args) if n == "option" && args.len() == 1 => {
                    (BuiltInFunction::OptionMap, args[0].clone())
                }
                Type::Data(n, args) if n == "vector" && args.len() == 1 => {
                    (BuiltInFunction::VectorMap, args[0].clone())
                }
                _ => break,
            };
            maps.push(next.0);
            cur = next.1;
        }
        let record_t = cur;

        // Build the record selector at the bottom record.
        let slot = record_t.lookup_field(name).unwrap_or_else(|| {
            self.errors.borrow_mut().push((
                format!("no field '{}' in type '{}'", name, record_t),
                span.clone(),
            ));
            0
        });
        let field_t = record_t.field_types().get(slot).map_or_else(
            || Rc::new(Type::Primitive(PrimitiveType::Unit)),
            |ft| Rc::new(ft.clone()),
        );
        let mut fn_expr = CoreExpr::RecordSelector(
            Rc::new(Type::Fn(record_t.clone(), field_t.clone())),
            slot,
        );

        // Wrap "F1.map (F2.map (... (Fn.map #f)))", innermost layer first.
        let mut in_type = record_t;
        let mut out_type = field_t;
        for map in maps.iter().rev() {
            let f_in = wrap_functor(*map, &in_type);
            let f_out = wrap_functor(*map, &out_type);
            let inner_fn = Rc::new(Type::Fn(in_type.clone(), out_type.clone()));
            let outer_fn = Rc::new(Type::Fn(f_in.clone(), f_out.clone()));
            let map_type = Rc::new(Type::Fn(inner_fn, outer_fn.clone()));
            let map_lit = CoreExpr::Literal(map_type, Val::Fn(*map));
            fn_expr = CoreExpr::Apply(
                outer_fn,
                Box::new(map_lit),
                Box::new(fn_expr),
                span.clone(),
            );
            in_type = f_in;
            out_type = f_out;
        }

        CoreExpr::Apply(t, Box::new(fn_expr), Box::new(core_arg), span.clone())
    }

    fn call2(
        &self,
        t: Rc<Type>,
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
    /// to the appropriate built-in.
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
        // first parameter is `self`. The
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
        let t_box = Rc::new(t.clone());
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
    fn effective_type(&self, expr: &Expr) -> Option<Rc<Type>> {
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
        t: Rc<Type>,
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
                    Rc::new(Type::Fn(arg_t.clone(), t.clone()));
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
            PostfixKind::Curried2Rev => {
                // `recv.m a` — build the curried call `m a recv`,
                // i.e. `Apply(Apply(m, a), recv)`. Used when the
                // receiver appears in the second curried position
                // (e.g. `Time.fmt : int -> time -> string`).
                let c_arg = self.resolve_expr(arg);
                let recv_t = c_recv.type_();
                let intermediate_t =
                    Rc::new(Type::Fn(recv_t.clone(), t.clone()));
                let inner = CoreExpr::Apply(
                    intermediate_t,
                    Box::new(fn_literal),
                    Box::new(c_arg),
                    span.clone(),
                );
                CoreExpr::Apply(
                    t,
                    Box::new(inner),
                    Box::new(c_recv),
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
                Val::String((parser::unquote_string(s).unwrap()).into())
            }
            LiteralKind::Unit => Val::Unit,
            LiteralKind::Word(w) => {
                Val::Word(parser::parse_word_literal(w).unwrap())
            }
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
                // The annotation as written wins, even over an alias the
                // deduced type already carries: that one's body has been
                // expanded, so `nats` would be `int list` rather than
                // `nat2 list`. morel-java takes the same route, converting
                // the written annotation in `deduceRealTypes`.
                // `typeof e` names the type `e` was shown to have, so a
                // pattern annotated with one is displayed with that type,
                // alias and all.
                if let TypeKind::Expression(operand) = &ann_type.kind
                    && let Some(t) =
                        self.type_map.decl_exp_types.get(&operand.span.extent())
                    && matches!(t, Type::Alias(..))
                {
                    return resolved.with_type(Rc::new(t.clone()));
                }
                if let TypeKind::Id(name) = &ann_type.kind
                    && let Some(body) = self.type_map.type_aliases.get(name)
                {
                    let alias_type = Rc::new(Type::Alias(
                        name.clone(),
                        Rc::new(body.clone()),
                        vec![],
                        self.type_map.checks_of(name),
                    ));
                    return resolved.with_type(alias_type);
                }
                if matches!(*resolved.type_(), Type::Alias(..)) {
                    // Already wrapped by get_type_with_alias
                    return resolved;
                }
                if let TypeKind::Id(name) = &ann_type.kind
                    && let Some(ann_id) = ann_type.id
                {
                    let var = Var { id: ann_id };
                    if self.type_map.var_alias_map.contains_key(&var) {
                        // The annotation as written, not the deduced type
                        // wrapped in the name: an alias whose body names
                        // another alias keeps it that way, so `nats` is
                        // `nat2 list`, not `int list`. morel-java takes
                        // the same route, converting the written
                        // annotation in `deduceRealTypes`.
                        let inner_type =
                            match self.type_map.type_aliases.get(name) {
                                Some(body) => Rc::new(body.clone()),
                                None => resolved.type_().clone(),
                            };
                        let alias_type = Rc::new(Type::Alias(
                            name.clone(),
                            inner_type,
                            vec![],
                            self.type_map.checks_of(name),
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
                        return Some(Type::List(Rc::new(Type::Alias(
                            name.clone(),
                            elem_type.clone(),
                            vec![],
                            self.type_map.checks_of(name),
                        ))));
                    }
                }
                None
            }
            ExprKind::Annotated(_, ann_type) => {
                // `val x = e : typeof y` annotates the expression, and
                // `typeof` names the type `y` was shown to have.
                if let TypeKind::Expression(operand) = &ann_type.kind
                    && let Some(t) =
                        self.type_map.decl_exp_types.get(&operand.span.extent())
                    && matches!(t, Type::Alias(..))
                {
                    return Some(t.clone());
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
            Rc::new(self.resolve_ast_type(type_annotation))
        } else {
            // Try to get type from the pattern or expression ID.
            if let Some(id) = val_bind.pat.id {
                self.type_map.get_type(id).unwrap_or_else(|| {
                    Rc::new(Type::Primitive(PrimitiveType::Unit))
                })
            } else if let Some(id) = val_bind.expr.id {
                self.type_map.get_type(id).unwrap_or_else(|| {
                    Rc::new(Type::Primitive(PrimitiveType::Unit))
                })
            } else {
                Rc::new(Type::Primitive(PrimitiveType::Unit))
            }
        };

        let span = Some(Span::from_pest_span(
            &val_bind.pat.span.union(&val_bind.expr.span).to_pest_span(),
            self.base_line,
        ));
        CoreValBind {
            pat,
            t: (*type_).clone(),
            expr,
            overload_pat: None,
            span,
        }
    }

    /// Resolves an AST type binding to a core type binding. The
    /// alias's right-hand side is converted to a core type via
    /// the same simple-shape recogniser used by the type-resolver.
    /// Unsupported shapes fall back to `unit`.
    fn resolve_type_bind(
        &self,
        type_bind: &TypeBind,
        decl_span: &AstSpan,
    ) -> CoreTypeBind {
        // Prefer the type resolver's expansion, which resolves names against
        // the aliases in scope before the declaration.
        let core_type = self
            .type_map
            .expanded_type_binds
            .get(&type_bind.name)
            .cloned()
            .or_else(|| ast_type_to_core_type(&type_bind.type_))
            .unwrap_or(Type::Primitive(PrimitiveType::Unit));
        let checks = self.type_map.checks_of(&type_bind.name);
        // A condition is compiled once, here, where it was written and
        // where its nodes have types. Where a check is inserted is
        // usually a later statement, whose type map knows nothing of
        // them.
        if !checks.is_empty() {
            // The declaration is what is at fault when a condition is
            // not closed, so it is what the error blames.
            let span = Span::from_pest_span(
                &decl_span.to(&type_bind.span).trim_end().to_pest_span(),
                self.base_line,
            );
            let predicates = checks
                .fns
                .iter()
                .map(|f| {
                    let predicate = self.make_total(self.resolve_expr(f), f);
                    self.check_closed(&type_bind.name, &predicate, &span);
                    predicate
                })
                .collect();
            self.type_map
                .check_predicates
                .borrow_mut()
                .insert(type_bind.name.clone(), predicates);
        }
        // A condition written inside the declaration -- on a field, on a
        // component, on an element -- belongs to a checked type that has
        // no name of its own, and no declaration of its own to compile it.
        // This is that declaration, so it is compiled here; the
        // conditions are carried from statement to statement compiled,
        // and the type will be met again where nothing can deduce them.
        self.register_nested_checks(&core_type);
        CoreTypeBind {
            type_vars: type_bind.type_vars.clone(),
            name: type_bind.name.clone(),
            type_: core_type,
            checks,
        }
    }

    /// Compiles the conditions of every checked type that has no name
    /// and was made in this statement, so that a later statement which
    /// meets the type again finds them ready.
    fn register_anon_checks(&self) {
        let names: Vec<String> = self
            .type_map
            .type_checks
            .keys()
            .filter(|name| name.starts_with(ANON_CHECK_PREFIX))
            .cloned()
            .collect();
        for name in names {
            let checks = self.type_map.checks_of(&name);
            self.register_checks(&name, &checks);
        }
    }

    /// Compiles the conditions of a checked type that has no name, if
    /// they were deduced in this statement and are not compiled already.
    fn register_checks(&self, name: &str, checks: &Checks) {
        if checks.is_empty()
            || self.type_map.check_predicates.borrow().contains_key(name)
            || !checks
                .fns
                .iter()
                .all(|f| f.get_type(self.type_map).is_some())
        {
            return;
        }
        let predicates = checks
            .fns
            .iter()
            .map(|f| self.make_total(self.resolve_expr(f), f))
            .collect();
        self.type_map
            .check_predicates
            .borrow_mut()
            .insert(name.to_string(), predicates);
    }

    /// Compiles the conditions of every checked type that has no name
    /// within a type, and registers them under the name its conditions
    /// gave it.
    fn register_nested_checks(&self, type_: &Type) {
        match type_ {
            Type::Alias(name, body, args, checks) => {
                if name.starts_with(ANON_CHECK_PREFIX)
                    && !checks.is_empty()
                    && !self
                        .type_map
                        .check_predicates
                        .borrow()
                        .contains_key(name)
                    && checks
                        .fns
                        .iter()
                        .all(|f| f.get_type(self.type_map).is_some())
                {
                    let predicates = checks
                        .fns
                        .iter()
                        .map(|f| self.make_total(self.resolve_expr(f), f))
                        .collect();
                    self.type_map
                        .check_predicates
                        .borrow_mut()
                        .insert(name.clone(), predicates);
                }
                self.register_nested_checks(body);
                args.iter().for_each(|t| self.register_nested_checks(t));
            }
            Type::Record(_, fields) => {
                fields.values().for_each(|t| self.register_nested_checks(t));
            }
            Type::Tuple(types) | Type::Data(_, types) => {
                types.iter().for_each(|t| self.register_nested_checks(t));
            }
            Type::List(t) | Type::Bag(t) | Type::Forall(t, _) => {
                self.register_nested_checks(t);
            }
            Type::Fn(a, b) => {
                self.register_nested_checks(a);
                self.register_nested_checks(b);
            }
            _ => {}
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
                        // `BOX of typeof e` has no syntactic conversion;
                        // the type resolver deduced the expression's type
                        // and left it here.
                        if let TypeKind::Expression(expr) = &t.kind {
                            self.type_map
                                .decl_exp_types
                                .get(&expr.span.extent())
                                .cloned()
                        } else {
                            ast_type_to_core_type_with_vars(t, tvs)
                        }
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
        let pat = self.resolve_pat(&ast_match.pat);
        let expr = self.resolve_expr(&ast_match.expr);
        // Entering a branch whose pattern claims a type is where a value
        // flows into the claim, so that is where the check goes. A
        // branch is what a function's parameter and a `case` have in
        // common, so both are checked here, and a function of several
        // branches is checked in whichever branch claims -- the
        // parameter of the function as a whole claims nothing, because
        // another branch may match instead.
        //
        //   (n: nat) => e
        //
        // becomes
        //
        //   v => let val n = $check (c v, v, "nat", "") in e end
        //
        // rather than checking and discarding, which an optimizer would
        // be entitled to remove: the body reads the name the check
        // binds. It is inside the function, so it travels with the
        // function value and fires however the function is called --
        // including from polymorphic code that knows nothing of the
        // checked type.
        let Some(claimed) = self.claimed_type(&ast_match.pat, &pat.type_())
        else {
            return CoreMatch { pat, expr };
        };
        let t = &pat.type_();
        let span = Span::from_pest_span(
            &ast_match
                .pat
                .span
                .union(&ast_match.expr.span)
                .to_pest_span(),
            self.base_line,
        );
        let raw_name = self.temp_name();
        let raw = CorePat::Identifier(t.clone(), raw_name.clone());
        let value = CoreExpr::Identifier(t.clone(), raw_name);
        let checked = self.checked(value, &claimed, &span);
        // A `case` rather than a `let`, because a body that never reads
        // the name the check binds would leave the binding unused, and
        // an optimizer that reasons about values alone is entitled to
        // drop an unused binding. A scrutinee is evaluated whatever the
        // branch does with it, and raising is a check's only effect.
        CoreMatch {
            pat: raw,
            expr: CoreExpr::Case(
                expr.type_(),
                Box::new(checked),
                vec![CoreMatch { pat, expr }],
                span.clone(),
            ),
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
            let from_result = expander::expand_from(
                builder
                    .build_simplify()
                    .expect("Failed to build From expression"),
                &self.type_map.datatype_map(),
            );

            // Apply the function to the query result. If the function is an
            // overloaded aggregate (e.g. `Test.overCount`), dispatch it to
            // the variant matching the query's collection kind.
            let func = self
                .dispatch_collection_fn(func_expr, !builder.is_ordered())
                .unwrap_or_else(|| self.resolve_expr(func_expr));

            // The application's type is the function's *result* type, not
            // the function's. They differ wherever the type is used: an
            // `into` nested in a `yield` took the function type as the
            // outer collection's element type, so the query evaluated to
            // the function itself.
            let fn_type = func_expr
                .get_type(self.type_map)
                .expect("INTO function must have a type");
            let result_type = match fn_type.as_ref() {
                Type::Fn(_, result) => result.clone(),
                _ => fn_type,
            };

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

        expander::expand_from(
            builder
                .build_simplify()
                .expect("Failed to build From expression"),
            &self.type_map.datatype_map(),
        )
    }

    /// Resolves a step in a query, adding it to a [FromBuilder].
    fn resolve_step(&self, builder: &mut FromBuilder, step: &AstStep) {
        match &step.kind {
            // lint: sort until '#}' where '##AstStepKind::'
            AstStepKind::Compute(expr) => {
                self.aggregate_input_is_bag.set(Some(!builder.is_ordered()));
                let resolved_expr = self.resolve_expr(expr);
                self.aggregate_input_is_bag.set(None);
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
            AstStepKind::Group(binder, key_expr, aggregate_expr) => {
                // Resolve the group key expression.
                let resolved_key = self.resolve_expr(key_expr);

                // Resolve the aggregate expression if present. Its `over`
                // aggregates see the pre-group collection kind.
                self.aggregate_input_is_bag.set(Some(!builder.is_ordered()));
                let resolved_aggregate =
                    aggregate_expr.as_ref().map(|e| self.resolve_expr(e));
                self.aggregate_input_is_bag.set(None);

                // Add the group step to the builder. A binder ("group g =
                // ...") names the whole group row 'g', an atom.
                builder.group(
                    binder.as_deref(),
                    resolved_key,
                    resolved_aggregate,
                );
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
                    Rc::new(bool_type),
                    Box::new(fn_literal),
                    Box::new(resolved_expr),
                    span,
                );
                builder.where_(negated);
            }
            AstStepKind::Scan(join_type, pat, expr, condition) => {
                // Resolve the pattern and expression.
                let resolved_pat = self.resolve_pat(pat);
                let resolved_expr = self.resolve_expr(expr);

                // Resolve the condition if present.
                let resolved_condition =
                    condition.as_ref().map(|c| self.resolve_expr(c));

                // Add the scan step, preserving the join type (inner / left
                // / right / full).
                let span = Span::from_pest_span(
                    &pat.span.to_pest_span(),
                    self.base_line,
                );
                builder.scan_with_join(
                    *join_type,
                    resolved_pat.clone(),
                    resolved_expr,
                    resolved_condition,
                );
                if let Some(condition) =
                    self.scan_type_condition(pat, &resolved_pat, &span)
                {
                    builder.where_(condition);
                }
            }
            AstStepKind::ScanEq(pat, expr) => {
                // `join pat = expr` is a cross join with a singleton list.
                // Desugar to a scan over `[expr]`.
                let resolved_pat = self.resolve_pat(pat);
                let resolved_expr = self.resolve_expr(expr);
                let elem_type = resolved_expr.type_();
                let list_type =
                    Rc::new(Type::List(Rc::new(elem_type.as_ref().clone())));
                let singleton = CoreExpr::List(list_type, vec![resolved_expr]);
                builder.scan_with_condition(resolved_pat, singleton, None);
            }
            AstStepKind::ScanExtent(pat) => {
                // `from p` (or `join p`) with no explicit source: the
                // variable `p` is unbounded. Lower to a scan over an
                // `Extent(t, span)` placeholder; predicate inversion
                // (Phase 1+) replaces the placeholder with a real
                // generator derived from surrounding `where`
                // predicates. Programs that reach code generation
                // containing an Extent are rejected with a "pattern
                // not grounded" error pointing at the captured span.
                //
                // Use the pattern's span, not the step's: Pest's
                // `scan1` rule span can extend past the pattern into
                // the next token (it consumes whitespace while
                // looking ahead for an `=` or `in` it never finds).
                // An unbounded scan yields the distinct values of the
                // variables its pattern binds, in natural order, so its
                // collection is a list. A bounded scan is unaffected:
                // `from i in [1, 2, 3, 2]` still has four elements.
                let resolved_pat = self.resolve_pat(pat);
                let elem_type = resolved_pat.type_();
                let extent_type =
                    Rc::new(Type::List(Rc::new(elem_type.as_ref().clone())));
                let span = Span::from_pest_span(
                    &pat.span.to_pest_span(),
                    self.base_line,
                );
                let extent = CoreExpr::Extent(extent_type, span.clone());
                builder.scan_with_condition(resolved_pat.clone(), extent, None);
                // The type's condition becomes a step of its own rather
                // than part of the scan's condition, which only a join
                // reads.
                if let Some(condition) =
                    self.scan_type_condition(pat, &resolved_pat, &span)
                {
                    builder.where_(condition);
                }
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
                    Type::Fn(_, result) => result.clone(),
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
            AstStepKind::Yield(binder, expr) => {
                let resolved_expr = self.resolve_expr(expr);
                // A binder ("yield r = e") names the whole output row 'r', an
                // atom, instead of scattering the record's fields into scope.
                match binder {
                    Some(name) => {
                        builder.yield_binder(name, resolved_expr);
                    }
                    None => {
                        builder.yield_(resolved_expr);
                    }
                }
            }
            AstStepKind::YieldAll(binder, expr) => {
                // Lower "yieldAll e" to a scan over the collection-valued
                // expression "e" followed by a yield of the freshly-bound
                // element. For example,
                //
                //   from r in orders
                //     yieldAll r.items
                //
                // becomes
                //
                //   from r in orders,
                //       i in r.items
                //     yield i
                //
                // The scan multiplies each input row by the elements of
                // "e" ("r.items"), then the yield drops the input bindings
                // ("r"), keeping only the element ("i").
                let resolved_expr = self.resolve_expr(expr);
                match resolved_expr.type_().as_ref() {
                    Type::List(elem) | Type::Bag(elem) => {
                        let elem_type = elem.clone();
                        // A binder ("yieldAll r in e") names each flattened
                        // element 'r', a real scan variable that combines with
                        // a following 'join'; otherwise use a fresh unique
                        // name so the element is visible only as 'current'.
                        let name = match binder {
                            Some(name) => name.clone(),
                            None => format!(
                                "v_{}",
                                std::ptr::addr_of!(**expr) as usize
                            ),
                        };
                        let pat = CorePat::Identifier(
                            elem_type.clone(),
                            name.clone(),
                        );
                        let id = CoreExpr::Identifier(elem_type, name);
                        builder.scan(pat, resolved_expr);
                        builder.yield_(id);
                    }
                    _ => {
                        // Unreachable in practice: the type resolver's
                        // `constrain_bag_or_list` already rejects a
                        // non-collection `yieldAll` expression with a "no
                        // valid overloads" type error before resolution.
                        // Kept as a defensive fallback that reports a
                        // compile error (rather than panicking) and
                        // recovers by treating it as a plain yield.
                        let span = Span::from_pest_span(
                            &expr.span.to_pest_span(),
                            self.base_line,
                        );
                        self.errors.borrow_mut().push((
                            "yieldAll expression must be a list or bag"
                                .to_string(),
                            span,
                        ));
                        builder.yield_(resolved_expr);
                    }
                }
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
                Val::String((parser::unquote_string(x).unwrap()).into())
            }
            LiteralKind::Unit => Val::Unit,
            LiteralKind::Word(x) => {
                Val::Word(parser::parse_word_literal(x).unwrap())
            }
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
            // If the binding uses an overloaded name at an abstract type, the
            // type resolver left the overload constraint unresolved; record it
            // as a predicate of a qualified type
            // (hydromatic/morel#426).
            if let Some(id) = val_bind.pat.id
                && let Some(qualified) = self.type_map.get_qualified_type(id)
            {
                core_pat = core_pat.with_type(qualified);
            }
            // Check if the expression has an alias annotation that
            // should propagate to the pattern type.
            if let Some(alias_type) =
                self.expr_alias_for_pat(&val_bind.expr, &core_pat)
            {
                core_pat = core_pat.with_type(Rc::new(alias_type));
            }
            let core_expr = self.resolve_expr(&val_bind.expr);
            let span = Some(Span::from_pest_span(
                &val_bind.pat.span.union(&val_bind.expr.span).to_pest_span(),
                self.base_line,
            ));
            // A binding at a checked type is where a value flows into a
            // claim, so the type's condition is checked here.
            let core_expr = self.with_checks(
                core_expr,
                &val_bind.pat,
                span.as_ref().expect("just built"),
            );

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
                t: (*pat.type_()).clone(),
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
            t: (*expr_type).clone(),
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
                        match &*args[0] {
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
            GeneralO, IntDiv, IntGe, IntGt, IntLe, IntLt, IntMinus, IntMod,
            IntPlus, IntTimes, ListAt, ListCons, RealDivide, RealGe, RealGt,
            RealLe, RealLt, RealMinus, RealPlus, RealTimes, StringCaret,
            StringGe, StringGt, StringLe, StringLt,
        };
        match (op_name, arg_type) {
            // Function composition is polymorphic over its operand types.
            ("o", _) => GeneralO,
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
            GDiv, GEq, GGe, GGt, GLe, GLt, GMinus, GMod, GNe, GNegate, GPlus,
            GTimes, ListCons,
        };
        match op_name {
            "~" => GNegate,
            "+" => GPlus,
            "*" => GTimes,
            "-" => GMinus,
            "div" => GDiv,
            "mod" => GMod,
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

/// Returns the result type of a postfix call, given the dispatched
/// built-in and the *concrete* receiver type. We need this because
/// type inference leaves the outer Apply's type variable unresolved
/// (the record-selector action only fires when the receiver is a
/// true record, not a built-in type).
///
/// Computes the answer by parsing the function's declared type
/// signature, unifying the receiver's actual type against the
/// declared receiver position to bind type variables, and applying
/// that substitution to the declared return type. Adding a new
/// dispatchable built-in needs no edit here — the answer comes from
/// the function's strum metadata.
fn postfix_return_type(
    builtin: BuiltInFunction,
    kind: PostfixKind,
    recv_type: &Type,
    arg_type: Option<&Type>,
) -> Rc<Type> {
    let ty = builtin.get_type();
    let stripped = strip_forall(&ty);
    let Type::Fn(arg, ret) = stripped else {
        return Rc::new(recv_type.clone());
    };
    // Locate the declared type of the receiver position and the
    // declared return type, depending on the dispatch kind.
    let (declared_recv, declared_ret): (&Type, &Type) =
        match (kind, arg.as_ref(), ret.as_ref()) {
            (PostfixKind::Tupled2, Type::Tuple(fs), _) if fs.len() == 2 => {
                (&fs[0], ret)
            }
            (PostfixKind::Tupled3, Type::Tuple(fs), _) if fs.len() == 3 => {
                (&fs[0], ret)
            }
            (PostfixKind::Curried2, a, Type::Fn(_, r)) => (a, r),
            (PostfixKind::Curried2Rev, _, Type::Fn(a2, r)) => (a2, r),
            (PostfixKind::Unary, a, _) => (a, ret),
            _ => return Rc::new(recv_type.clone()),
        };
    // Bind type variables by matching declared_recv against the
    // actual receiver type.
    let mut subst: HashMap<usize, Type> = HashMap::new();
    unify_into(declared_recv, peel_type(recv_type), &mut subst);
    let mut out = substitute(declared_ret, &subst);
    // If the result is still a free variable, fall back to the
    // argument's concrete type — this covers `OptionGetOpt` on a
    // polymorphic receiver like `NONE.getOpt(0)`, where the result
    // type variable is determined by the second argument.
    if is_unresolved_type(&out)
        && let Some(at) = arg_type
        && !is_unresolved_type(at)
    {
        out = at.clone();
    }
    Rc::new(out)
}

/// Strips `Type::Forall` wrappers, returning the inner type.
fn strip_forall(t: &Type) -> &Type {
    let mut cur = t;
    while let Type::Forall(inner, _) = cur {
        cur = inner;
    }
    cur
}

/// Walks `declared` and `actual` in parallel, recording bindings of
/// declared type variables to the corresponding actual sub-types.
/// Mismatches in shape are silently ignored (the caller falls back to
/// the unsubstituted declared type).
fn unify_into(
    declared: &Type,
    actual: &Type,
    subst: &mut HashMap<usize, Type>,
) {
    let actual = peel_type(actual);
    match (declared, actual) {
        (Type::Variable(tv), t) => {
            subst.insert(tv.id, t.clone());
        }
        (Type::List(a), Type::List(b)) | (Type::Bag(a), Type::Bag(b)) => {
            unify_into(a, b, subst);
        }
        (Type::Data(n, a), Type::Data(m, b))
            if n == m && a.len() == b.len() =>
        {
            for (a, b) in a.iter().zip(b.iter()) {
                unify_into(a, b, subst);
            }
        }
        (Type::Named(a, n), Type::Named(b, m))
            if n == m && a.len() == b.len() =>
        {
            for (a, b) in a.iter().zip(b.iter()) {
                unify_into(a, b, subst);
            }
        }
        // Cross-spelling: type parser canonicalises some types to
        // `Type::List` / `Type::Bag` and others to `Type::Named`.
        (Type::Bag(a), Type::Named(b, name))
        | (Type::Named(b, name), Type::Bag(a))
            if name == "bag" && b.len() == 1 =>
        {
            unify_into(a, &b[0], subst);
        }
        (Type::List(a), Type::Named(b, name))
        | (Type::Named(b, name), Type::List(a))
            if name == "list" && b.len() == 1 =>
        {
            unify_into(a, &b[0], subst);
        }
        _ => {}
    }
}

/// Replaces every `Type::Variable(id)` in `t` with `subst[id]` (if
/// present), and normalises `Type::Named(_, name)` to
/// `Type::Data(name, _)` for the built-in datatype names that the
/// pretty printer special-cases. Variables not in the substitution
/// are left untouched.
fn substitute(t: &Type, subst: &HashMap<usize, Type>) -> Type {
    match t {
        Type::Variable(tv) => {
            subst.get(&tv.id).cloned().unwrap_or_else(|| t.clone())
        }
        Type::List(inner) => Type::List(Rc::new(substitute(inner, subst))),
        Type::Bag(inner) => Type::Bag(Rc::new(substitute(inner, subst))),
        Type::Fn(a, r) => Type::Fn(
            Rc::new(substitute(a, subst)),
            Rc::new(substitute(r, subst)),
        ),
        Type::Data(n, args) => Type::Data(
            n.clone(),
            args.iter().map(|a| Rc::new(substitute(a, subst))).collect(),
        ),
        Type::Named(args, n) => {
            let new_args: Vec<Rc<Type>> =
                args.iter().map(|a| Rc::new(substitute(a, subst))).collect();
            // The type parser produces `Type::Named([], name)` for
            // every datatype; normalise the ones the pretty printer
            // expects as `Type::Data` so that postfix call results
            // render the same as their prefix counterparts.
            // `list` and `bag` have dedicated `Type` variants; every
            // other built-in named type (entries in `BuiltInDatatype`
            // and `BuiltInEqtype`) lowers to `Type::Data`.
            if n == "bag" && new_args.len() == 1 {
                Type::Bag(new_args.into_iter().next().unwrap())
            } else if n == "list" && new_args.len() == 1 {
                Type::List(new_args.into_iter().next().unwrap())
            } else if library::builtin_type_arity(n.as_str()).is_some() {
                Type::Data(n.clone(), new_args)
            } else {
                Type::Named(new_args, n.clone())
            }
        }
        Type::Tuple(fs) => Type::Tuple(
            fs.iter().map(|a| Rc::new(substitute(a, subst))).collect(),
        ),
        _ => t.clone(),
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
fn match_has_self_first_param(m: &FunMatch) -> bool {
    match m.pats.first() {
        Some(pat) => pat_has_self(pat),
        None => false,
    }
}

/// Returns true if a pattern is `self`, `self : T`, or a record /
/// tuple pattern containing a field named `self`.
fn pat_has_self(pat: &Pat) -> bool {
    match &pat.kind {
        PatKind::Identifier(name) => name == "self",
        PatKind::Annotated(inner, _) => pat_has_self(inner),
        PatKind::Record(fields, _) => fields.iter().any(|f| match f {
            PatField::Labeled(_, name, _) => name == "self",
            PatField::Anonymous(_, _) => false,
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

/// The names of a record's fields, in label order.
fn label_names(fields: &BTreeMap<Label, Rc<Type>>) -> Vec<String> {
    fields.keys().map(Label::to_string).collect()
}

/// How a claimed type is written, for a message.
fn type_moniker(claimed: &Type) -> String {
    match claimed {
        // A checked type that has no name is not named in the message
        // either. Its made-up name would be no use to a reader, and its
        // conditions are already written where the value was claimed.
        Type::Alias(name, _, _, _)
            if name.is_empty() || name.starts_with(ANON_CHECK_PREFIX) =>
        {
            "value".to_string()
        }
        _ => claimed.to_string(),
    }
}

/// The label an anonymous field of a record pattern gives its value:
/// `{x, y}` names its fields `x` and `y`, and `{x: nat}` names its `x`.
fn implicit_label(pat: &Pat) -> Option<String> {
    match &pat.kind {
        PatKind::Identifier(name) => Some(name.clone()),
        PatKind::Annotated(inner, _) => implicit_label(inner),
        PatKind::As(name, _) => Some(name.clone()),
        _ => None,
    }
}

/// What a component of a value is of: `field empno`, `component 2`.
fn field_blame(record: &Type, label: &Label) -> String {
    match record {
        Type::Tuple(_) => format!("component {}", label),
        _ => format!("field {}", label),
    }
}

/// Appends a segment to a blame path.
fn append_blame(blame: &str, segment: &str) -> String {
    if blame.is_empty() {
        return segment.to_string();
    }
    // A path reads as one selection: `field lead.empno`, not
    // `field lead.field empno`.
    match segment.strip_prefix("field ") {
        Some(field) => format!("{}.{}", blame, field),
        None => match segment.strip_prefix("component ") {
            Some(ordinal) => format!("{}.{}", blame, ordinal),
            // An element is written as a subscript, so it joins what it
            // is an element of without a space: `[_][_]`, `emps[_].sal`.
            None if segment.starts_with('[') => {
                format!("{}{}", blame, segment)
            }
            None => format!("{} {}", blame, segment),
        },
    }
}

/// Whether a type claims a condition on a function's parameter or
/// result, at any depth.
///
/// A condition on the function type itself is not this: it is given the
/// function value, and is checked like any other. Where the condition
/// lands is decided by parenthesization, so `int -> int check c => ...`
/// is allowed and `(int check c => ...) -> int` is not.
fn claims_function(claimed: &Type) -> bool {
    match claimed {
        Type::Fn(a, b) => {
            has_condition(a)
                || has_condition(b)
                || claims_function(a)
                || claims_function(b)
        }
        Type::Alias(_, body, _, _) => claims_function(body),
        Type::Record(_, fields) => fields.values().any(|t| claims_function(t)),
        Type::Tuple(types) => types.iter().any(|t| claims_function(t)),
        Type::List(elem) | Type::Bag(elem) => claims_function(elem),
        _ => false,
    }
}

/// Whether a type, or any type within it, carries a condition.
///
/// The free counterpart of [`Resolver::has_check`], for the checks that
/// do not need the type map.
fn has_condition(t: &Type) -> bool {
    match t {
        Type::Alias(_, body, _, checks) => {
            !checks.is_empty() || has_condition(body)
        }
        Type::Record(_, fields) => fields.values().any(|t| has_condition(t)),
        Type::Tuple(types) => types.iter().any(|t| has_condition(t)),
        Type::List(elem) | Type::Bag(elem) => has_condition(elem),
        Type::Data(_, args) => args.iter().any(|t| has_condition(t)),
        Type::Fn(a, b) => has_condition(a) || has_condition(b),
        _ => false,
    }
}
