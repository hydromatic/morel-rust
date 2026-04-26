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

use crate::compile::core::{Decl, Expr, Match, Pat, Step, StepKind, ValBind};
use crate::compile::library::BuiltInFunction;
use crate::compile::types::Type;
use crate::eval::order::Order;
use crate::eval::val::Val;
use im::HashMap;
use std::cmp::Ordering;
use std::collections::BTreeMap;
use std::collections::HashMap as StdHashMap;

/// Can transform any expression, declaration, or pattern in a tree.
/// Combined with [Decl::visit], [Expr::visit], and [Pat::visit], this
/// can reshape a whole tree.
trait Transformer {
    fn transform_decl(&self, env: &Env, decl: &Decl) -> Decl;
    fn transform_expr(&self, env: &Env, expr: &Expr) -> Expr;
    fn transform_pat(&self, env: &Env, pat: &Pat) -> Pat;
    /// How a binding is classified by the analyzer. Defaults to
    /// `MultiUnsafe` for transformers without an analysis attached.
    fn binding_use(&self, _name: &str) -> Use {
        Use::MultiUnsafe
    }
}

// ---------------------------------------------------------------------------
// Analyzer (ported from morel-java's `Analyzer.java`)
// ---------------------------------------------------------------------------

/// Classification of how a binding is used. Drives the inliner's
/// dead-code-elimination and substitution decisions.
///
/// Note: morel-rust's analyzer is name-based rather than identity-based
/// like morel-java's. Nested `let`s that re-use a name will conflate
/// outer and inner bindings; the conservative outcome is `MultiUnsafe`,
/// which causes the inliner to leave the let in place.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum Use {
    /// Reserved for recursive-bindings that participate in a cycle.
    /// Currently morel-rust never produces this.
    LoopBreaker,
    /// Binding is not referenced. The let can be discarded.
    Dead,
    /// Binding occurs exactly once, not inside a lambda. Inlining is
    /// unconditionally safe; it duplicates neither code nor work.
    OnceSafe,
    /// Binding is bound to an atomic expression (literal or identifier).
    /// Inlining is unconditionally safe regardless of use count.
    Atomic,
    /// Binding occurs at most once in each of several distinct case
    /// branches. Inlining may duplicate code but not work.
    MultiSafe,
    /// Binding occurs exactly once, inside a lambda. Reserved.
    OnceUnsafe,
    /// Binding may occur many times, including inside lambdas; do not
    /// inline.
    MultiUnsafe,
}

#[derive(Default)]
struct MutableUse {
    top: bool,
    atomic: bool,
    parallel: bool,
    use_count: u32,
}

impl MutableUse {
    fn fix(&self) -> Use {
        if self.top {
            Use::MultiUnsafe
        } else if self.use_count == 0 {
            Use::Dead
        } else if self.atomic {
            Use::Atomic
        } else if self.use_count == 1 {
            if self.parallel {
                Use::MultiSafe
            } else {
                Use::OnceSafe
            }
        } else {
            Use::MultiUnsafe
        }
    }
}

/// Result of an analysis: the `Use` for each name encountered.
#[derive(Debug)]
pub struct Analysis {
    map: StdHashMap<String, Use>,
}

impl Analysis {
    /// Returns the `Use` of `name`. Defaults to `MultiUnsafe` for names
    /// the analyzer never saw, so the inliner stays conservative.
    pub fn use_of(&self, name: &str) -> Use {
        self.map.get(name).copied().unwrap_or(Use::MultiUnsafe)
    }
}

struct Analyzer {
    map: StdHashMap<String, MutableUse>,
}

impl Analyzer {
    fn new() -> Self {
        Self {
            map: StdHashMap::new(),
        }
    }

    fn entry(&mut self, name: &str) -> &mut MutableUse {
        self.map.entry(name.to_string()).or_default()
    }

    fn ensure_bindings(&mut self, pat: &Pat) {
        pat.for_each_id_pat(&mut |(_, name)| {
            self.entry(name);
        });
    }

    fn visit_decl(&mut self, decl: &Decl) {
        match decl {
            Decl::NonRecVal(vb) => {
                self.ensure_bindings(&vb.pat);
                self.visit_expr(&vb.expr);
                if is_atom(&vb.expr)
                    && let Some(name) = vb.pat.name()
                {
                    self.entry(&name).atomic = true;
                }
            }
            Decl::RecVal(vbs) => {
                for vb in vbs {
                    self.ensure_bindings(&vb.pat);
                }
                for vb in vbs {
                    self.visit_expr(&vb.expr);
                    if is_atom(&vb.expr)
                        && let Some(name) = vb.pat.name()
                    {
                        self.entry(&name).atomic = true;
                    }
                }
            }
            Decl::Type(_) | Decl::Datatype(_) | Decl::Over(_) => {}
        }
    }

    fn visit_expr(&mut self, expr: &Expr) {
        match expr {
            Expr::Identifier(_, name) => {
                self.entry(name).use_count += 1;
            }
            Expr::Literal(_, _)
            | Expr::Current(_)
            | Expr::Ordinal(_)
            | Expr::RecordSelector(_, _) => {}
            Expr::Aggregate(_, a, b) => {
                self.visit_expr(a);
                self.visit_expr(b);
            }
            Expr::Apply(_, f, a, _) => {
                self.visit_expr(f);
                self.visit_expr(a);
            }
            Expr::Tuple(_, args) | Expr::List(_, args) => {
                for arg in args {
                    self.visit_expr(arg);
                }
            }
            Expr::Let(_, decls, body) => {
                for d in decls {
                    self.visit_decl(d);
                }
                self.visit_expr(body);
            }
            Expr::Case(_, scrutinee, matches, _) => {
                self.visit_expr(scrutinee);
                if matches.len() == 1 {
                    self.ensure_bindings(&matches[0].pat);
                    self.visit_expr(&matches[0].expr);
                } else {
                    self.visit_parallel(matches);
                }
            }
            Expr::Fn(_, matches, _) => {
                // Conservatively count uses inside a lambda the same as
                // outside. morel-java's analyzer also does not treat
                // lambdas specially when producing `Use`.
                for m in matches {
                    self.ensure_bindings(&m.pat);
                    self.visit_expr(&m.expr);
                }
            }
            Expr::From(_, steps)
            | Expr::Exists(_, steps)
            | Expr::Forall(_, steps) => {
                for step in steps {
                    self.visit_step(&step.kind);
                }
            }
        }
    }

    fn visit_parallel(&mut self, matches: &[Match]) {
        let mut branch_uses: StdHashMap<String, Vec<MutableUse>> =
            StdHashMap::new();
        for m in matches {
            let mut sub = Analyzer::new();
            sub.ensure_bindings(&m.pat);
            sub.visit_expr(&m.expr);
            for (name, mu) in sub.map {
                branch_uses.entry(name).or_default().push(mu);
            }
        }
        for (name, uses) in branch_uses {
            let max_count: u32 =
                uses.iter().map(|u| u.use_count).max().unwrap_or(0);
            let entry = self.entry(&name);
            if uses.len() > 1 {
                entry.parallel = true;
            }
            entry.use_count += max_count;
        }
    }

    fn visit_step(&mut self, kind: &StepKind) {
        match kind {
            StepKind::Compute(e)
            | StepKind::Order(e)
            | StepKind::Where(e)
            | StepKind::Yield(e)
            | StepKind::Require(e)
            | StepKind::Skip(e)
            | StepKind::Take(e) => self.visit_expr(e),
            StepKind::Group(e, opt) => {
                self.visit_expr(e);
                if let Some(o) = opt {
                    self.visit_expr(o);
                }
            }
            StepKind::Scan(pat, expr, cond) => {
                self.ensure_bindings(pat);
                self.visit_expr(expr);
                if let Some(c) = cond {
                    self.visit_expr(c);
                }
            }
            StepKind::Except(_, exprs)
            | StepKind::Intersect(_, exprs)
            | StepKind::Union(_, exprs) => {
                for e in exprs {
                    self.visit_expr(e);
                }
            }
            StepKind::Distinct | StepKind::Exists | StepKind::Unorder => {}
        }
    }
}

fn is_atom(expr: &Expr) -> bool {
    matches!(expr, Expr::Literal(_, _) | Expr::Identifier(_, _))
}

/// Counts how many times each binding is used. Mirrors
/// [`Analyzer::analyze`](https://github.com/hydromatic/morel/blob/main/src/main/java/net/hydromatic/morel/compile/Analyzer.java).
pub fn analyze(decl: &Decl) -> Analysis {
    let mut analyzer = Analyzer::new();
    // Mark top-level bindings so they aren't dropped.
    if let Decl::NonRecVal(vb) = decl {
        vb.pat.for_each_id_pat(&mut |(_, name)| {
            analyzer.entry(name).top = true;
        });
    }
    analyzer.visit_decl(decl);
    Analysis {
        map: analyzer
            .map
            .into_iter()
            .map(|(k, v)| (k, v.fix()))
            .collect(),
    }
}

/// Tries to convert a constant expression to a runtime value. Returns `None`
/// if the expression is not a recognizable constant, or if its value cannot
/// be matched against patterns (e.g. function values).
fn expr_to_val(expr: &Expr) -> Option<Val> {
    match expr {
        Expr::Literal(_, v) => match v {
            // The `NONE`, `nil`, `LESS`/`EQUAL`/`GREATER` and similar
            // nullary constants live in the environment as `Val::Fn(...)`
            // until compilation lowers them to their runtime forms. Apply
            // the same lowering here so the case-on-constant logic can
            // match them.
            Val::Fn(BuiltInFunction::OptionNone) => Some(Val::Unit),
            Val::Fn(BuiltInFunction::ListNil)
            | Val::Fn(BuiltInFunction::BagNil) => Some(Val::List(Vec::new())),
            Val::Fn(BuiltInFunction::OrderLess) => {
                Some(Val::Order(Order(Ordering::Less)))
            }
            Val::Fn(BuiltInFunction::OrderEqual) => {
                Some(Val::Order(Order(Ordering::Equal)))
            }
            Val::Fn(BuiltInFunction::OrderGreater) => {
                Some(Val::Order(Order(Ordering::Greater)))
            }
            // Other function values, code, and closures cannot be matched
            // against patterns so we conservatively decline.
            Val::Fn(_) | Val::Code(_) | Val::Closure(..) => None,
            _ => Some(v.clone()),
        },
        Expr::Tuple(_, args) => args
            .iter()
            .map(expr_to_val)
            .collect::<Option<Vec<_>>>()
            .map(Val::List),
        Expr::Apply(_, fn_expr, arg, _) => {
            if let Expr::Literal(_, Val::Fn(f)) = fn_expr.as_ref() {
                let v = expr_to_val(arg)?;
                match f {
                    BuiltInFunction::OptionSome => Some(Val::Some(Box::new(v))),
                    BuiltInFunction::EitherInl => Some(Val::Inl(Box::new(v))),
                    BuiltInFunction::EitherInr => Some(Val::Inr(Box::new(v))),
                    _ => None,
                }
            } else {
                None
            }
        }
        _ => None,
    }
}

/// Returns true if `expr` has no side effects and can be safely eliminated
/// when its value is not used. Constant expressions (those for which
/// [`expr_to_val`] succeeds) are pure; we additionally accept identifiers
/// and record selectors.
fn is_pure(expr: &Expr) -> bool {
    if expr_to_val(expr).is_some() {
        return true;
    }
    match expr {
        Expr::Identifier(_, _) | Expr::RecordSelector(_, _) => true,
        Expr::Tuple(_, args) => args.iter().all(is_pure),
        _ => false,
    }
}

fn decl_is_pure(decl: &Decl) -> bool {
    match decl {
        Decl::NonRecVal(vb) => is_pure(&vb.expr),
        Decl::RecVal(_) => false,
        Decl::Type(_) | Decl::Datatype(_) | Decl::Over(_) => true,
    }
}

/// Returns true if the named identifier is referenced anywhere in `expr`.
/// Used for dead-code elimination of unused let bindings. This walks
/// through binding constructs (fn, case, let, from-scan) and stops the
/// search if a sub-binding shadows the name.
fn references_var(expr: &Expr, name: &str) -> bool {
    match expr {
        Expr::Identifier(_, id) => id == name,
        Expr::Literal(_, _)
        | Expr::Current(_)
        | Expr::Ordinal(_)
        | Expr::RecordSelector(_, _) => false,
        Expr::Aggregate(_, a, b) => {
            references_var(a, name) || references_var(b, name)
        }
        Expr::Apply(_, f, a, _) => {
            references_var(f, name) || references_var(a, name)
        }
        Expr::Case(_, scrutinee, matches, _) => {
            if references_var(scrutinee, name) {
                return true;
            }
            matches.iter().any(|m| {
                !pat_binds(&m.pat, name) && references_var(&m.expr, name)
            })
        }
        Expr::Fn(_, matches, _) => matches
            .iter()
            .any(|m| !pat_binds(&m.pat, name) && references_var(&m.expr, name)),
        Expr::Let(_, decls, body) => {
            for d in decls {
                if decl_references_var(d, name) {
                    return true;
                }
                if decl_binds(d, name) {
                    return false;
                }
            }
            references_var(body, name)
        }
        Expr::Tuple(_, args) | Expr::List(_, args) => {
            args.iter().any(|e| references_var(e, name))
        }
        Expr::From(_, steps)
        | Expr::Exists(_, steps)
        | Expr::Forall(_, steps) => {
            for s in steps {
                let (refs, shadows) = step_refs(&s.kind, name);
                if refs {
                    return true;
                }
                if shadows {
                    return false;
                }
            }
            false
        }
    }
}

fn pat_binds(pat: &Pat, name: &str) -> bool {
    let mut found = false;
    pat.for_each_id_pat(&mut |(_, n)| {
        if n == name {
            found = true;
        }
    });
    found
}

/// Returns true if no variable bound by `pat` is referenced in `body`.
fn pat_unused(pat: &Pat, body: &Expr) -> bool {
    let mut names: Vec<String> = Vec::new();
    pat.for_each_id_pat(&mut |(_, n)| names.push(n.to_string()));
    names.iter().all(|n| !references_var(body, n))
}

fn decl_binds(decl: &Decl, name: &str) -> bool {
    let mut found = false;
    decl.for_each_id_pat(|(_, n)| {
        if n == name {
            found = true;
        }
    });
    found
}

fn decl_references_var(decl: &Decl, name: &str) -> bool {
    match decl {
        Decl::NonRecVal(vb) => references_var(&vb.expr, name),
        Decl::RecVal(vbs) => {
            // Check whether any binding pattern shadows `name`. If so, the
            // let-rec scope is closed and references inside don't count.
            let shadows = vbs.iter().any(|vb| pat_binds(&vb.pat, name));
            if shadows {
                false
            } else {
                vbs.iter().any(|vb| references_var(&vb.expr, name))
            }
        }
        Decl::Over(_) | Decl::Type(_) | Decl::Datatype(_) => false,
    }
}

/// Returns `(references, shadows)`: whether `name` is referenced in this
/// step, and whether the step binds `name` (shadowing later steps).
fn step_refs(kind: &StepKind, name: &str) -> (bool, bool) {
    match kind {
        StepKind::Compute(e)
        | StepKind::Order(e)
        | StepKind::Where(e)
        | StepKind::Yield(e)
        | StepKind::Require(e)
        | StepKind::Skip(e)
        | StepKind::Take(e) => (references_var(e, name), false),
        StepKind::Group(e, opt) => {
            let r = references_var(e, name)
                || opt.as_deref().is_some_and(|o| references_var(o, name));
            (r, false)
        }
        StepKind::Scan(pat, expr, cond) => {
            let r = references_var(expr, name)
                || cond.as_deref().is_some_and(|c| references_var(c, name));
            (r, pat_binds(pat, name))
        }
        StepKind::Except(_, exprs)
        | StepKind::Intersect(_, exprs)
        | StepKind::Union(_, exprs) => {
            (exprs.iter().any(|e| references_var(e, name)), false)
        }
        StepKind::Distinct | StepKind::Exists | StepKind::Unorder => {
            (false, false)
        }
    }
}

/// Passes over a tree and inlines constants.
/// Maximum number of analysis-and-inline passes; mirrors morel-java's
/// `inlinePassCount` default.
pub const INLINE_PASS_COUNT: usize = 5;

/// Runs the analyzer and inliner together, iterating up to
/// `INLINE_PASS_COUNT` (5) times until the declaration's `Display` is
/// stable. Mirrors the loop in morel-java's `Compiles.java`.
pub fn inline_decl(env: &Env, decl: &Decl) -> Decl {
    let mut current = decl.clone();
    for _ in 0..INLINE_PASS_COUNT {
        let analysis = analyze(&current);
        let inliner = Inliner {
            analysis: Some(analysis),
        };
        let next = inliner.transform_decl(env, &current);
        if format!("{}", next) == format!("{}", current) {
            return next;
        }
        current = next;
    }
    current
}

struct Inliner {
    analysis: Option<Analysis>,
}

impl Transformer for Inliner {
    fn binding_use(&self, name: &str) -> Use {
        self.analysis
            .as_ref()
            .map_or(Use::MultiUnsafe, |a| a.use_of(name))
    }

    fn transform_decl(&self, env: &Env, decl: &Decl) -> Decl {
        decl.visit(env, self)
    }

    fn transform_expr(&self, env: &Env, expr: &Expr) -> Expr {
        let expr = expr.visit(env, self);
        match &expr {
            // lint: sort until '#}' where '##Expr::'
            Expr::Apply(result_type, f, a, span) => {
                if let Expr::RecordSelector(_fn_type, slot) = f.as_ref()
                    && let Expr::Literal(record_type, v) = a.as_ref()
                    && let Some(field_type) =
                        record_type.field_types().get(*slot)
                {
                    let v2 = v.get_field(*slot).unwrap();
                    return Expr::Literal(
                        Box::new(field_type.clone()),
                        v2.clone(),
                    );
                }
                // Beta-reduction: `(fn pat => body) arg` becomes
                // `let val pat = arg in body end`. Mirrors morel-java's
                // visit(Core.Apply). Only applies when the lambda has a
                // single match arm.
                if let Expr::Fn(_fn_t, matches, _) = f.as_ref()
                    && matches.len() == 1
                {
                    let m = &matches[0];
                    let pat_t = m.pat.type_();
                    let val_bind = ValBind {
                        pat: m.pat.clone(),
                        t: *pat_t,
                        expr: (**a).clone(),
                        overload_pat: None,
                        span: Some(span.clone()),
                    };
                    let body = m.expr.clone();
                    let let_expr = Expr::Let(
                        result_type.clone(),
                        vec![Decl::NonRecVal(Box::new(val_bind))],
                        Box::new(body),
                    );
                    return self.transform_expr(env, &let_expr);
                }
                expr
            }
            Expr::Case(_t, scrutinee, matches, _span) => {
                // Single-arm cases like `case x of y => exp` (which the
                // inliner generates when destructuring patterns) are
                // rewritten to a let so that further inlining can take
                // place. This mirrors morel-java's `getSub`.
                if matches.len() == 1
                    && let Some(val) = expr_to_val(scrutinee)
                {
                    let m = &matches[0];
                    let mut binds: Vec<(Box<Pat>, Val)> = Vec::new();
                    let matched = m.pat.bind_recurse(&val, &mut |p, v| {
                        binds.push((p, v.clone()));
                    });
                    if matched {
                        let mut result = m.expr.clone();
                        for (pat, v) in binds.into_iter().rev() {
                            let pat_t = pat.type_();
                            let lit = Expr::Literal(pat_t.clone(), v.clone());
                            let val_bind = ValBind {
                                pat: *pat,
                                t: *pat_t,
                                expr: lit,
                                overload_pat: None,
                                span: None,
                            };
                            let result_t = result.type_();
                            result = Expr::Let(
                                result_t,
                                vec![Decl::NonRecVal(Box::new(val_bind))],
                                Box::new(result),
                            );
                        }
                        return self.transform_expr(env, &result);
                    }
                }
                // If the scrutinee is a constant expression and there is more
                // than one match arm, find the first arm whose pattern matches
                // and substitute the bound variables. This implements
                // "case x of 1 => one | 2 => two" -> "two" when x = 2.
                if matches.len() > 1
                    && let Some(val) = expr_to_val(scrutinee)
                {
                    for m in matches {
                        let mut binds: Vec<(Box<Pat>, Val)> = Vec::new();
                        let matched = m.pat.bind_recurse(&val, &mut |p, v| {
                            binds.push((p, v.clone()));
                        });
                        if matched {
                            let mut result = m.expr.clone();
                            for (pat, v) in binds.into_iter().rev() {
                                let pat_t = pat.type_();
                                let lit =
                                    Expr::Literal(pat_t.clone(), v.clone());
                                let val_bind = ValBind {
                                    pat: *pat,
                                    t: *pat_t,
                                    expr: lit,
                                    overload_pat: None,
                                    span: None,
                                };
                                let result_t = result.type_();
                                result = Expr::Let(
                                    result_t,
                                    vec![Decl::NonRecVal(Box::new(val_bind))],
                                    Box::new(result),
                                );
                            }
                            return self.transform_expr(env, &result);
                        }
                    }
                }
                expr
            }
            Expr::Identifier(t, id) => {
                // `elements` is a pseudo-variable whose meaning is
                // `from`-step-specific (it refers to the elements of
                // the current group). The compiler binds it as a frame
                // slot, so it must not be substituted by the inliner
                // even if a user has shadowed the name in an outer
                // scope.
                if id == "elements" {
                    return expr;
                }
                // If the name is bound to an expression in the env (a
                // let-bound `ATOMIC` or `ONCE_SAFE` binding), substitute
                // by re-visiting the expression so further inlining can
                // take place. Skip if the bound expression is the same
                // identifier (e.g. `let val i = i in ...` from
                // beta-reducing `(fn i => ...) i`); re-visiting such a
                // binding would loop forever.
                if let Some(e) = env.lookup_expr(id)
                    && !matches!(&e, Expr::Identifier(_, n) if n == id)
                {
                    return self.transform_expr(env, &e);
                }
                // Otherwise, if the name is a constant in the environment
                // (a built-in or atomic literal), replace it with a
                // literal value. We do this for package names: for
                // example, "Sys.set" becomes the record (list) value
                // "Sys"; next, the transformation on "Apply" of the 9th
                // field (because "set" is the 9th field of "Sys" record
                // type) converts that the field into a function literal.
                if let Some(v) = env.lookup_constant(id) {
                    return Expr::Literal(t.clone(), v.clone());
                }
                expr
            }
            Expr::Let(t, decl_list, body) => {
                // The visit() of Expr::Let has already eliminated any
                // declarations whose `Use` is `Dead`, `Atomic`, or
                // `OnceSafe` and rewritten body references. If no decls
                // remain, return the body directly.
                if decl_list.is_empty() {
                    return (**body).clone();
                }
                Expr::Let(t.clone(), decl_list.clone(), body.clone())
            }
            _ => expr,
        }
    }

    fn transform_pat(&self, _v: &Env, pat: &Pat) -> Pat {
        pat.clone() // For now, just return the pattern unchanged
    }
}

impl Pat {
    fn visit(&self, _env: &Env, _x: &dyn Transformer) -> Pat {
        self.clone()
    }
}

impl Expr {
    fn visit(&self, env: &Env, x: &dyn Transformer) -> Expr {
        match &self {
            // lint: sort until '#}' where '##Expr::'
            Expr::Aggregate(t, a0, a1) => Expr::Aggregate(
                t.clone(),
                Box::new(x.transform_expr(env, a0)),
                Box::new(x.transform_expr(env, a1)),
            ),
            Expr::Apply(result_type, f, a, span) => {
                let f2 = x.transform_expr(env, f);
                let a2 = x.transform_expr(env, a);
                match (&f2, &a2) {
                    (Expr::RecordSelector(_, slot), Expr::Literal(_, v)) => {
                        Expr::Literal(
                            result_type.clone(),
                            v.expect_list()[*slot].clone(),
                        )
                    }
                    (..) => Expr::Apply(
                        result_type.clone(),
                        Box::new(f2),
                        Box::new(a2),
                        span.clone(),
                    ),
                }
            }
            Expr::Case(t, expr, matches, span) => {
                let expr2 = Box::new(x.transform_expr(env, expr));
                let mut matches2 = Vec::new();
                for m in matches {
                    let pat = x.transform_pat(env, &m.pat);
                    // Shadow names bound by the case pattern in the
                    // arm's body environment, just like Expr::Fn.
                    let mut body_env = env.clone();
                    pat.for_each_id_pat(&mut |(t, name)| {
                        body_env = body_env.child_none(name, t);
                    });
                    let expr = x.transform_expr(&body_env, &m.expr);
                    matches2.push(Match { pat, expr });
                }
                Expr::Case(t.clone(), expr2, matches2, span.clone())
            }
            Expr::Current(_) => self.clone(),
            Expr::Fn(t, match_list, span) => {
                let mut match_list2 = Vec::new();
                for m in match_list {
                    let pat = x.transform_pat(env, &m.pat);
                    // Shadow every name bound by the pattern so that
                    // inlining does not substitute global constants for
                    // function parameters of the same name. We must
                    // walk the whole pattern tree (e.g. tuple, record,
                    // cons, as patterns) — `pat.name()` only returns
                    // the top-level name and is None for compound
                    // patterns like `(p, v)`.
                    let mut body_env = env.clone();
                    pat.for_each_id_pat(&mut |(t, name)| {
                        body_env = body_env.child_none(name, t);
                    });
                    let expr = x.transform_expr(&body_env, &m.expr);
                    match_list2.push(Match { pat, expr });
                }
                Expr::Fn(t.clone(), match_list2, span.clone())
            }
            Expr::From(t, steps) => {
                let mut step_env = env.clone();
                let mut steps2 = Vec::with_capacity(steps.len());
                for s in steps {
                    let (s2, env2) = Self::visit_step(&step_env, x, s);
                    steps2.push(s2);
                    step_env = env2;
                }
                Expr::From(t.clone(), steps2)
            }
            Expr::Identifier(t, id) => {
                // `elements` is a `from`-step pseudo-variable; the
                // compiler resolves it via a frame slot, so the inliner
                // must leave it as an identifier.
                if id == "elements" {
                    return self.clone();
                }
                if let Some(e) = env.lookup_expr(id)
                    && !matches!(&e, Expr::Identifier(_, n) if n == id)
                {
                    return x.transform_expr(env, &e);
                }
                if let Some(v) = env.lookup_constant(id) {
                    Expr::Literal(t.clone(), v.clone())
                } else {
                    self.clone()
                }
            }
            Expr::Let(t, decl_list, e) => {
                // Each declaration is classified by the analyzer:
                //
                // * Dead: drop entirely.
                // * Atomic / OnceSafe: drop the let, but bind the
                //   expression in the body env so that references in
                //   the body are substituted (and re-visited).
                // * Otherwise: keep the decl, shadow the name in the
                //   body env so outer-scope substitutions don't leak in.
                //
                // Mirrors morel-java's Inliner.visit(Core.Let).
                let mut decl_list2: Vec<Decl> = Vec::new();
                let mut body_env = env.clone();
                for d in decl_list {
                    let d2 = x.transform_decl(env, d);
                    let mut handled = false;
                    if let Decl::NonRecVal(vb) = &d2
                        && let Some(name) = vb.pat.name()
                    {
                        match x.binding_use(&name) {
                            Use::Dead => {
                                handled = true;
                            }
                            Use::Atomic | Use::OnceSafe => {
                                body_env = body_env.child_expr(
                                    name.as_str(),
                                    &vb.t,
                                    &vb.expr,
                                );
                                handled = true;
                            }
                            _ => {}
                        }
                    }
                    if !handled {
                        d.for_each_id_pat(&mut |(t, name): (&Type, &str)| {
                            body_env = body_env.child_none(name, t);
                        });
                        decl_list2.push(d2);
                    }
                }
                let e2 = Box::new(x.transform_expr(&body_env, e));
                if decl_list2.is_empty() {
                    *e2
                } else {
                    Expr::Let(t.clone(), decl_list2, e2)
                }
            }
            Expr::List(t, expr_list) => Expr::List(
                t.clone(),
                Self::visit_list(env, x, expr_list).into_iter().collect(),
            ),
            Expr::Literal(_t, _v) => self.clone(),
            Expr::Ordinal(_) => self.clone(),
            Expr::RecordSelector(_t, _) => self.clone(),
            Expr::Tuple(t, expr_list) => Expr::Tuple(
                t.clone(),
                Self::visit_list(env, x, expr_list).into_iter().collect(),
            ),
            _ => todo!("inline {:}", self),
        }
    }

    fn visit_list(
        env: &Env,
        x: &dyn Transformer,
        expr_list: &[Expr],
    ) -> Vec<Expr> {
        expr_list.iter().map(|e| x.transform_expr(env, e)).collect()
    }

    fn visit_step(env: &Env, x: &dyn Transformer, step: &Step) -> (Step, Env) {
        let (kind, env2) = match &step.kind {
            // lint: sort until '#}' where '##StepKind::'
            StepKind::Compute(expr) => {
                let expr2 = x.transform_expr(env, expr);
                (StepKind::Compute(Box::new(expr2)), env.clone())
            }
            StepKind::Distinct | StepKind::Exists | StepKind::Unorder => {
                (step.kind.clone(), env.clone())
            }
            StepKind::Except(distinct, exprs) => {
                let exprs2 = Self::visit_list(env, x, exprs);
                (StepKind::Except(*distinct, exprs2), env.clone())
            }
            StepKind::Group(expr, opt) => {
                let expr2 = x.transform_expr(env, expr);
                let opt2 =
                    opt.as_ref().map(|o| Box::new(x.transform_expr(env, o)));
                (StepKind::Group(Box::new(expr2), opt2), env.clone())
            }
            StepKind::Intersect(distinct, exprs) => {
                let exprs2 = Self::visit_list(env, x, exprs);
                (StepKind::Intersect(*distinct, exprs2), env.clone())
            }
            StepKind::Order(expr) => {
                let expr2 = x.transform_expr(env, expr);
                (StepKind::Order(Box::new(expr2)), env.clone())
            }
            StepKind::Require(expr) => {
                let expr2 = x.transform_expr(env, expr);
                (StepKind::Require(Box::new(expr2)), env.clone())
            }
            StepKind::Scan(pat, expr, condition) => {
                let pat2 = x.transform_pat(env, pat);
                let expr2 = x.transform_expr(env, expr);
                let condition2 = condition
                    .as_ref()
                    .map(|c| Box::new(x.transform_expr(env, c)));
                // Shadow names bound by the scan pattern so that
                // subsequent steps (e.g. Where, Yield) do not inline
                // outer-scope constants for variables of the same name.
                let mut scan_env = env.clone();
                pat.for_each_id_pat(&mut |(t, name)| {
                    scan_env = scan_env.child_none(name, t);
                });
                (
                    StepKind::Scan(Box::new(pat2), Box::new(expr2), condition2),
                    scan_env,
                )
            }
            StepKind::Skip(expr) => {
                let expr2 = x.transform_expr(env, expr);
                (StepKind::Skip(Box::new(expr2)), env.clone())
            }
            StepKind::Take(expr) => {
                let expr2 = x.transform_expr(env, expr);
                (StepKind::Take(Box::new(expr2)), env.clone())
            }
            StepKind::Union(distinct, exprs) => {
                let exprs2 = Self::visit_list(env, x, exprs);
                (StepKind::Union(*distinct, exprs2), env.clone())
            }
            StepKind::Where(expr) => {
                let expr2 = x.transform_expr(env, expr);
                (StepKind::Where(Box::new(expr2)), env.clone())
            }
            StepKind::Yield(expr) => {
                let expr2 = x.transform_expr(env, expr);
                (StepKind::Yield(Box::new(expr2)), env.clone())
            }
        };
        (
            Step {
                kind,
                env: step.env.clone(),
            },
            env2,
        )
    }
}

impl Decl {
    fn visit(&self, env: &Env, x: &dyn Transformer) -> Decl {
        match &self {
            Decl::NonRecVal(val_bind) => {
                let env2 = if let Some(name) = val_bind.pat.name() {
                    env.child_none(name.as_str(), &val_bind.t)
                } else {
                    env.clone()
                };
                Decl::NonRecVal(Box::new(ValBind {
                    pat: x.transform_pat(env, &val_bind.pat),
                    expr: x.transform_expr(&env2, &val_bind.expr),
                    t: val_bind.t.clone(),
                    overload_pat: val_bind.overload_pat.clone(),
                    span: val_bind.span.clone(),
                }))
            }
            Decl::RecVal(val_binds) => {
                let val_binds2 =
                    val_binds.iter().map(|b| b.visit(env, x)).collect();
                Decl::RecVal(val_binds2)
            }
            // Type and Datatype declarations have no values to inline.
            Decl::Type(_) | Decl::Datatype(_) | Decl::Over(_) => self.clone(),
        }
    }
}

impl ValBind {
    fn visit(&self, env: &Env, x: &dyn Transformer) -> Self {
        let env2 = env.child_none(self.pat.name().unwrap().as_str(), &self.t);
        let pat = x.transform_pat(env, &self.pat);
        let expr = x.transform_expr(&env2, &self.expr);
        ValBind {
            pat,
            t: self.t.clone(),
            expr,
            overload_pat: self.overload_pat.clone(),
            span: self.span.clone(),
        }
    }
}
/// Environment for inlining. Tracks two parallel maps:
///
/// * `map`: scoped `(type, optional value)` for built-in constants and
///   atomic literals (used by `lookup_constant`).
/// * `exprs`: scoped expressions to substitute for `ATOMIC` and
///   `ONCE_SAFE` let-bound variables (used by `lookup_expr`).
#[derive(Clone, Debug)]
pub struct Env {
    map: im::HashMap<String, (Type, Option<Val>)>,
    exprs: im::HashMap<String, Expr>,
}

impl Env {
    /// Returns an empty environment.
    pub(crate) fn empty() -> Self {
        Env {
            map: HashMap::new(),
            exprs: HashMap::new(),
        }
    }

    /// Returns an environment with a given backing map.
    pub fn with(map: HashMap<String, (Type, Option<Val>)>) -> Env {
        Env {
            map,
            exprs: HashMap::new(),
        }
    }

    pub(crate) fn child(&self, name: &str, t: &Type, v: &Val) -> Env {
        let map2 = self
            .map
            .update(name.to_string(), (t.clone(), Some(v.clone())));
        let exprs2 = self.exprs.without(name);
        Env {
            map: map2,
            exprs: exprs2,
        }
    }

    pub(crate) fn child_none(&self, name: &str, t: &Type) -> Env {
        let map2 = self.map.update(name.to_string(), (t.clone(), None));
        let exprs2 = self.exprs.without(name);
        Env {
            map: map2,
            exprs: exprs2,
        }
    }

    /// Binds `name` to a let-bound expression that the inliner should
    /// substitute on every reference. Use this for `ATOMIC` and
    /// `ONCE_SAFE` bindings.
    pub(crate) fn child_expr(&self, name: &str, t: &Type, expr: &Expr) -> Env {
        let map2 = self.map.update(name.to_string(), (t.clone(), None));
        let exprs2 = self.exprs.update(name.to_string(), expr.clone());
        Env {
            map: map2,
            exprs: exprs2,
        }
    }

    pub(crate) fn lookup_expr(&self, s: &str) -> Option<Expr> {
        self.exprs.get(s).cloned()
    }

    pub(crate) fn multi(
        &self,
        map: &BTreeMap<&str, (Type, Option<Val>)>,
    ) -> Env {
        if map.is_empty() {
            return self.clone();
        }

        // Optimization: Use from_iter for batch construction.
        // This is more efficient than chaining updates.
        let new_entries = map.iter().map(|(k, v)| (k.to_string(), v.clone()));
        let map2 = self.map.clone().union(HashMap::from_iter(new_entries));
        let mut exprs2 = self.exprs.clone();
        for k in map.keys() {
            exprs2 = exprs2.without(*k);
        }
        Env {
            map: map2,
            exprs: exprs2,
        }
    }

    pub(crate) fn lookup_constant(&self, s: &str) -> Option<Val> {
        if let Some((_, v)) = self.lookup(s) {
            v
        } else {
            None
        }
    }

    pub(crate) fn lookup(&self, s: &str) -> Option<(Type, Option<Val>)> {
        self.map.get(s).cloned()
    }
}
