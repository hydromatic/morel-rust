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

//! Two-phase predicate-inversion pipeline. Phase 1.
//!
//! `expand_from(from_expr)` analyses `where`-conjuncts to derive a
//! generator for each unbounded pattern (i.e. each Scan over an
//! `Expr::Extent`), then rewrites the `from` so the unbounded
//! source becomes a real collection-scan and the conjuncts that
//! the generator subsumes are dropped from the surrounding `where`.
//!
//! Mirrors morel-java's `compile.Expander`, less the bits that
//! Phase 1 doesn't need (no outer-scope filtering, no recursive
//! function inlining, no case/exists/string-prefix).

use crate::compile::core::{
    Binding, Decl, Expr, Match, Pat, Step, StepEnv, StepKind, ValBind,
};
use crate::compile::fbbt;
use crate::compile::generator::Cache;
use crate::compile::generators::{
    fold_literal_bounds_into_range_scans, has_infinite_range_scan,
    maybe_generator_with_scope, rewrite_infinite_range_scans, split_conjuncts,
};
use crate::compile::library::BuiltInFunction;
use crate::compile::span::Span;
use crate::compile::types::{Label, PrimitiveType, Type};
use crate::eval::val::Val;
use std::collections::{BTreeSet, HashMap, HashSet};
use std::rc::Rc;

/// Map of let-bound function name → (parameter pattern, body
/// expression). Populated as `expand_decl` walks down through
/// nested `Let` expressions so that `maybe_function` can inline a
/// known function's body when it sees a constraint of the form
/// `f arg`.
pub type FnEnv = HashMap<String, (Pat, Expr)>;

/// Map of user-defined datatype name → its constructor names in
/// declaration order. Lets `finite_extent` enumerate values of
/// `Type::Data(name, _)` for constraint-free unbounded patterns
/// (e.g. `from c, d where c <> d` over a `Color`).
pub type DatatypeMap = HashMap<String, Vec<String>>;

/// Convenience wrapper for callers that don't have a function
/// environment available (e.g. the resolver, which calls this
/// before `expand_decl` runs the full tree-walk pass).
pub fn expand_from(expr: Expr, datatypes: &DatatypeMap) -> Expr {
    let env = FnEnv::new();
    expand_from_with(expr, &env, datatypes)
}

/// If `expr` is a `From`, `Exists`, or `Forall` containing one or
/// more Scans over Extents, rewrite it by deriving generators from
/// `where` clauses and using them as the scan sources. Otherwise
/// returns `expr` unchanged.
pub fn expand_from_with(
    expr: Expr,
    env: &FnEnv,
    datatypes: &DatatypeMap,
) -> Expr {
    expand_from_with_scope(expr, env, datatypes, &BTreeSet::new())
}

/// Same as `expand_from_with` but passes a set of names known
/// to be in outer scope (function parameters, let-bound vals)
/// so the leaf strategies can treat them as runtime-stable
/// filters in record-elem constraints.
pub fn expand_from_with_scope(
    expr: Expr,
    env: &FnEnv,
    datatypes: &DatatypeMap,
    outer_scope: &BTreeSet<String>,
) -> Expr {
    let empty_rec = FnEnv::new();
    expand_from_with_scope_rec(expr, env, &empty_rec, datatypes, outer_scope)
}

/// Same as [`expand_from_with_scope`] but additionally accepts
/// a "recursive-fn" environment of pre-expander bodies that
/// Phase 2's `try_invert_recursive_predicates` consults when
/// recognising self-recursive predicates whose original step
/// constraints have been consumed by an earlier expansion. This
/// is kept separate from `env` (which holds post-expander bodies
/// used by `inline_tuple_fn_calls_in_where`) so inlining doesn't
/// accidentally expand a pre-expander recursive body in place.
pub fn expand_from_with_scope_rec(
    expr: Expr,
    env: &FnEnv,
    rec_env: &FnEnv,
    datatypes: &DatatypeMap,
    outer_scope: &BTreeSet<String>,
) -> Expr {
    // Make infinite single-constructor range scans (`from x in [1..]`)
    // finite. First fold a literal `where` bound into the range
    // constructor in place (works for int and char); any remaining
    // infinite int scans (bound deduced by FBBT, not literal) become
    // list-typed Extent scans grounded by the range extractor.
    let prep = |steps: Vec<Step>| {
        if !has_infinite_range_scan(&steps) {
            return steps;
        }
        let steps = fold_literal_bounds_into_range_scans(steps);
        if has_infinite_range_scan(&steps) {
            rewrite_infinite_range_scans(steps)
        } else {
            steps
        }
    };
    match expr {
        Expr::From(t, steps) => {
            let steps = prep(steps);
            if !has_extent_scan(&steps) {
                return Expr::From(t, steps);
            }
            Expr::From(
                t,
                expand_steps_with_scope(
                    steps,
                    env,
                    rec_env,
                    datatypes,
                    outer_scope,
                ),
            )
        }
        Expr::Exists(t, steps) => {
            let steps = prep(steps);
            if !has_extent_scan(&steps) {
                return Expr::Exists(t, steps);
            }
            Expr::Exists(
                t,
                expand_steps_with_scope(
                    steps,
                    env,
                    rec_env,
                    datatypes,
                    outer_scope,
                ),
            )
        }
        Expr::Forall(t, steps) => {
            let steps = prep(steps);
            if !has_extent_scan(&steps) {
                return Expr::Forall(t, steps);
            }
            Expr::Forall(
                t,
                expand_steps_with_scope(
                    steps,
                    env,
                    rec_env,
                    datatypes,
                    outer_scope,
                ),
            )
        }
        _ => expr,
    }
}

/// Tree-walking pass that re-runs `expand_from_with` on every
/// `From`/`Exists`/`Forall` it encounters, with a `FnEnv` populated
/// from enclosing `let val rec ... = fn p => body` bindings. This
/// Entry point used after the resolver finishes, so that
/// `maybe_function` can inline let-bound predicates that the
/// per-query passes inside `resolve_query` couldn't see.
///
/// Seeds the inlining environment with cross-statement function
/// bindings the session has accumulated from earlier `fun` / `val`
/// decls so predicate inversion can inline a function declared in
/// a previous shell statement. `rec_session_fns` carries the
/// pre-expander function bodies for recursive-predicate inversion,
/// while `session_fns` keeps post-expander bodies for use by
/// `inline_tuple_fn_calls_in_where`.
pub fn expand_decl_with_session_rec(
    decl: Decl,
    datatypes: &DatatypeMap,
    session_fns: &FnEnv,
    rec_session_fns: &FnEnv,
) -> Decl {
    walk_decl_rec(decl, session_fns, rec_session_fns, datatypes)
}

/// Walks a Core decl and records any single-arm `fn p => body`
/// value-bindings into `env`. Mirrors `collect_fn_bindings` but
/// is exposed for the shell, which tracks session-level fn
/// definitions for cross-statement predicate inversion.
pub fn collect_session_fn_bindings(decl: &Decl, env: &mut FnEnv) {
    collect_fn_bindings(decl, env);
}

/// Adds every identifier-name bound by `pat` to `out`. Used to
/// extend the "outer scope" set as we walk into a `Fn` body or
/// a `Case` arm.
fn collect_pat_names(pat: &Pat, out: &mut BTreeSet<String>) {
    let mut bs: Vec<Binding> = Vec::new();
    Binding::collect_bindings(pat, &mut bs);
    for b in bs {
        out.insert(b.id.name);
    }
}

/// Adds every identifier-name bound by `decl`'s left-hand
/// patterns to `out`. Used to extend the "outer scope" set as
/// we walk into a `Let` body.
fn collect_decl_pat_names(decl: &Decl, out: &mut BTreeSet<String>) {
    use std::slice::from_ref;
    let binds: &[ValBind] = match decl {
        Decl::NonRecVal(b) => from_ref(b.as_ref()),
        Decl::RecVal(binds) => binds.as_slice(),
        _ => return,
    };
    for b in binds {
        collect_pat_names(&b.pat, out);
    }
}

fn walk_decl_rec(
    decl: Decl,
    env: &FnEnv,
    rec_env: &FnEnv,
    datatypes: &DatatypeMap,
) -> Decl {
    walk_decl_with_scope(decl, env, rec_env, datatypes, &BTreeSet::new())
}

fn walk_decl_with_scope(
    decl: Decl,
    env: &FnEnv,
    rec_env: &FnEnv,
    datatypes: &DatatypeMap,
    outer_scope: &BTreeSet<String>,
) -> Decl {
    match decl {
        Decl::NonRecVal(b) => {
            let mut b2 = (*b).clone();
            b2.expr = walk_expr_with_scope(
                b2.expr,
                env,
                rec_env,
                datatypes,
                outer_scope,
            );
            Decl::NonRecVal(Box::new(b2))
        }
        Decl::RecVal(binds) => {
            let mut new_binds = Vec::with_capacity(binds.len());
            for mut b in binds {
                b.expr = walk_expr_with_scope(
                    b.expr,
                    env,
                    rec_env,
                    datatypes,
                    outer_scope,
                );
                new_binds.push(b);
            }
            Decl::RecVal(new_binds)
        }
        other => other,
    }
}

fn walk_expr_with_scope(
    expr: Expr,
    env: &FnEnv,
    rec_env: &FnEnv,
    datatypes: &DatatypeMap,
    outer_scope: &BTreeSet<String>,
) -> Expr {
    match expr {
        Expr::Let(t, decls, body) => {
            // Extend the environment with single-arg `fn` bindings
            // before recursing into the body. Also extend
            // outer_scope with the let-binding's pat names so
            // record-elem strategies treat them as runtime-stable.
            let mut env2 = env.clone();
            let mut rec_env2 = rec_env.clone();
            let mut scope2 = outer_scope.clone();
            for d in &decls {
                // Pre-expander bodies into both maps. `env2` is the
                // post-expander map for `inline_tuple_fn_calls_in_where`;
                // because Let-bound bodies haven't been walked yet at
                // this point, both maps temporarily hold the same
                // pre-expander bodies. (Phase 2 only fires for
                // self-recursive shapes that don't get inlined.)
                collect_fn_bindings(d, &mut env2);
                collect_fn_bindings(d, &mut rec_env2);
                collect_decl_pat_names(d, &mut scope2);
            }
            let new_decls: Vec<Decl> = decls
                .into_iter()
                .map(|d| {
                    walk_decl_with_scope(
                        d, &env2, &rec_env2, datatypes, &scope2,
                    )
                })
                .collect();
            let new_body = Box::new(walk_expr_with_scope(
                *body, &env2, &rec_env2, datatypes, &scope2,
            ));
            Expr::Let(t, new_decls, new_body)
        }
        Expr::From(_, _) | Expr::Exists(_, _) | Expr::Forall(_, _) => {
            let inner = walk_query_steps(expr, env, rec_env, datatypes);
            expand_from_with_scope_rec(
                inner,
                env,
                rec_env,
                datatypes,
                outer_scope,
            )
        }
        Expr::Apply(t, f, a, span) => {
            // Higher-order predicate inversion: inline a call to a
            // non-recursive let-bound function whose body contains
            // an unresolved `Extent`. After substitution, the body's
            // from is walked normally and its inversion has access
            // to the concrete arg (e.g. `enumerate isClerk` becomes
            // `from r where isClerk r`, whose `isClerk r` grounds
            // `r` via the body's `elem` clause).
            //
            // Self-recursive functions are skipped — inlining them
            // would loop forever, and the dedicated iterate-inversion
            // path handles their self-call shapes.
            if let Expr::Identifier(_, fn_name) = f.as_ref()
                && let Some((param_pat, body)) = env.get(fn_name)
                && let Pat::Identifier(_, param_name) = param_pat
                && body_has_extent(body)
                && !contains_self_call(body, fn_name)
            {
                use crate::compile::replacer::substitute;
                let mut subst: HashMap<String, Expr> = HashMap::new();
                subst.insert(param_name.clone(), (*a).clone());
                let inlined = substitute(body, &subst);
                return walk_expr_with_scope(
                    inlined,
                    env,
                    rec_env,
                    datatypes,
                    outer_scope,
                );
            }
            Expr::Apply(
                t,
                Box::new(walk_expr_with_scope(
                    *f,
                    env,
                    rec_env,
                    datatypes,
                    outer_scope,
                )),
                Box::new(walk_expr_with_scope(
                    *a,
                    env,
                    rec_env,
                    datatypes,
                    outer_scope,
                )),
                span,
            )
        }
        Expr::Case(t, subject, arms, span) => Expr::Case(
            t,
            Box::new(walk_expr_with_scope(
                *subject,
                env,
                rec_env,
                datatypes,
                outer_scope,
            )),
            arms.into_iter()
                .map(|m| {
                    let mut scope2 = outer_scope.clone();
                    collect_pat_names(&m.pat, &mut scope2);
                    Match {
                        pat: m.pat,
                        expr: walk_expr_with_scope(
                            m.expr, env, rec_env, datatypes, &scope2,
                        ),
                    }
                })
                .collect(),
            span,
        ),
        Expr::Fn(t, arms, span) => Expr::Fn(
            t,
            arms.into_iter()
                .map(|m| {
                    let mut scope2 = outer_scope.clone();
                    collect_pat_names(&m.pat, &mut scope2);
                    Match {
                        pat: m.pat,
                        expr: walk_expr_with_scope(
                            m.expr, env, rec_env, datatypes, &scope2,
                        ),
                    }
                })
                .collect(),
            span,
        ),
        Expr::Tuple(t, items) => Expr::Tuple(
            t,
            items
                .into_iter()
                .map(|e| {
                    walk_expr_with_scope(
                        e,
                        env,
                        rec_env,
                        datatypes,
                        outer_scope,
                    )
                })
                .collect(),
        ),
        Expr::List(t, items) => Expr::List(
            t,
            items
                .into_iter()
                .map(|e| {
                    walk_expr_with_scope(
                        e,
                        env,
                        rec_env,
                        datatypes,
                        outer_scope,
                    )
                })
                .collect(),
        ),
        Expr::Aggregate(t, e1, e2) => Expr::Aggregate(
            t,
            Box::new(walk_expr_with_scope(
                *e1,
                env,
                rec_env,
                datatypes,
                outer_scope,
            )),
            Box::new(walk_expr_with_scope(
                *e2,
                env,
                rec_env,
                datatypes,
                outer_scope,
            )),
        ),
        other => other,
    }
}

/// Walk inside a `From`/`Exists`/`Forall`'s steps so that
/// expressions embedded in `Where`, `Yield`, and other step kinds
/// get the same treatment. The query's outer wrapper is recreated.
fn walk_query_steps(
    expr: Expr,
    env: &FnEnv,
    rec_env: &FnEnv,
    datatypes: &DatatypeMap,
) -> Expr {
    let (kind, t, steps) = match expr {
        Expr::From(t, s) => ('f', t, s),
        Expr::Exists(t, s) => ('e', t, s),
        Expr::Forall(t, s) => ('a', t, s),
        other => return other,
    };
    let outer_scope = BTreeSet::new();
    let new_steps: Vec<Step> = steps
        .into_iter()
        .map(|s| {
            let new_kind = match s.kind {
                StepKind::Scan(p, source, cond) => StepKind::Scan(
                    p,
                    Box::new(walk_expr_with_scope(
                        *source,
                        env,
                        rec_env,
                        datatypes,
                        &outer_scope,
                    )),
                    cond.map(|c| {
                        Box::new(walk_expr_with_scope(
                            *c,
                            env,
                            rec_env,
                            datatypes,
                            &outer_scope,
                        ))
                    }),
                ),
                StepKind::Where(c) => {
                    StepKind::Where(Box::new(walk_expr_with_scope(
                        *c,
                        env,
                        rec_env,
                        datatypes,
                        &outer_scope,
                    )))
                }
                StepKind::Yield(e) => {
                    StepKind::Yield(Box::new(walk_expr_with_scope(
                        *e,
                        env,
                        rec_env,
                        datatypes,
                        &outer_scope,
                    )))
                }
                StepKind::Order(e) => {
                    StepKind::Order(Box::new(walk_expr_with_scope(
                        *e,
                        env,
                        rec_env,
                        datatypes,
                        &outer_scope,
                    )))
                }
                StepKind::Compute(e) => {
                    StepKind::Compute(Box::new(walk_expr_with_scope(
                        *e,
                        env,
                        rec_env,
                        datatypes,
                        &outer_scope,
                    )))
                }
                StepKind::Group(k, a) => StepKind::Group(
                    Box::new(walk_expr_with_scope(
                        *k,
                        env,
                        rec_env,
                        datatypes,
                        &outer_scope,
                    )),
                    a.map(|e| {
                        Box::new(walk_expr_with_scope(
                            *e,
                            env,
                            rec_env,
                            datatypes,
                            &outer_scope,
                        ))
                    }),
                ),
                other => other,
            };
            Step::new(new_kind, s.env)
        })
        .collect();
    match kind {
        'f' => Expr::From(t, new_steps),
        'e' => Expr::Exists(t, new_steps),
        _ => Expr::Forall(t, new_steps),
    }
}

/// Inspects a `Decl` and, for every value-binding whose RHS is a
/// single-arm `fn p => body`, records the binding in `env`. We
/// cap at one parameter for now — multi-clause functions and
/// curried definitions can be added in a later phase.
fn collect_fn_bindings(decl: &Decl, env: &mut FnEnv) {
    use std::slice::from_ref;
    let binds: &[ValBind] = match decl {
        Decl::NonRecVal(b) => from_ref(b.as_ref()),
        Decl::RecVal(binds) => binds.as_slice(),
        _ => return,
    };
    for b in binds {
        if let Pat::Identifier(_, name) = &b.pat
            && let Expr::Fn(_, arms, _) = &b.expr
            && arms.len() == 1
            && let Match { pat, expr } = &arms[0]
        {
            env.insert(name.clone(), (pat.clone(), expr.clone()));
        }
    }
}

fn has_extent_scan(steps: &[Step]) -> bool {
    steps.iter().any(|s| {
        matches!(&s.kind,
            StepKind::Scan(_, source, _)
                if matches!(source.as_ref(), Expr::Extent(_, _)))
    })
}

/// Pre-pass: rewrite each `where (x, y, …) elem coll` whose left-
/// hand tuple is exactly the names of some unbounded patterns in
/// this from. The matched ScanExtents are merged into a single
/// `Scan(Tuple([x, y, …]), coll)` step (mirroring the user-typed
/// `from (x, y, …) in coll`), and the original `elem` conjunct
/// is dropped from the surrounding `Where`.
///
/// The merged scan is placed at the position of the *last* of the
/// matched ScanExtents, so later steps that reference any of the
/// destructured names see them as bound.
/// Inlines simple function calls in Where conjuncts when the
/// function has a tuple-pattern parameter. This lets
/// `decompose_tuple_elems` see e.g. `(n, d) elem coll` even
/// when the user wrote `f (n, d)` for a let-bound
/// `fun f (n, d) = (n, d) elem coll`.
fn inline_tuple_fn_calls_in_where(
    steps: Vec<Step>,
    fn_env: &FnEnv,
) -> Vec<Step> {
    use crate::compile::generators::split_conjuncts;
    use crate::compile::replacer::substitute;
    if fn_env.is_empty() {
        return steps;
    }
    let try_inline = |c: &Expr| -> Expr {
        let Expr::Apply(_, f, arg, _) = c else {
            return c.clone();
        };
        let Expr::Identifier(_, fn_name) = f.as_ref() else {
            return c.clone();
        };
        let Some((param_pat, body)) = fn_env.get(fn_name) else {
            return c.clone();
        };
        let mut subst_map: HashMap<String, Expr> = HashMap::new();
        match param_pat {
            // `fun f x = body` — substitute the whole arg.
            Pat::Identifier(_, n) => {
                subst_map.insert(n.clone(), (**arg).clone());
            }
            // `fun f (a, b) = body` — destructure a literal tuple
            // arg into its components.
            Pat::Tuple(_, sub_pats) => {
                let Expr::Tuple(_, arg_elems) = arg.as_ref() else {
                    return c.clone();
                };
                if sub_pats.len() != arg_elems.len() {
                    return c.clone();
                }
                for (sp, ae) in sub_pats.iter().zip(arg_elems.iter()) {
                    if let Pat::Identifier(_, n) = sp {
                        subst_map.insert(n.clone(), ae.clone());
                    } else {
                        return c.clone();
                    }
                }
            }
            _ => return c.clone(),
        }
        // Phase 4: if `body` is self-recursive (e.g. bounded path,
        // arity-3 with arithmetic constraint that Phase 0z's iterate
        // builder couldn't recognise), strip the recursive disjuncts
        // of any top-level `orelse`. The remaining non-recursive
        // base lets the surrounding pipeline ground the goal pattern
        // when the recursive case adds nothing under the program's
        // depth bound. Mirrors morel-java's `removeRecursiveBranches`
        // fallback in `Generators.maybeFunction`. When there's no
        // top-level `orelse` to peel (e.g. the cousin2 shape:
        // `base andalso not (...)`), fall back to inlining the
        // body unchanged — the pipeline's later passes will surface
        // the appropriate "pattern not grounded" error.
        let body_to_inline = if contains_self_call(body, fn_name)
            && let Some(stripped) = remove_recursive_branches(body, fn_name)
        {
            stripped
        } else {
            body.clone()
        };
        substitute(&body_to_inline, &subst_map)
    };
    steps
        .into_iter()
        .map(|s| match s.kind {
            StepKind::Where(cond) => {
                let conjuncts: Vec<Expr> = split_conjuncts(&cond)
                    .into_iter()
                    .map(|c| try_inline(&c))
                    .collect();
                let new_cond = if conjuncts.is_empty() {
                    *cond
                } else {
                    let mut iter = conjuncts.into_iter();
                    let first = iter.next().unwrap();
                    iter.fold(first, |a, b| and_all(vec![a, b]))
                };
                Step::new(StepKind::Where(Box::new(new_cond)), s.env)
            }
            other => Step::new(other, s.env),
        })
        .collect()
}

/// Phase 0z: detects a self-recursive transitive-closure
/// predicate `f p` in this query's `where` and rewrites the
/// corresponding `Scan(p, Extent(_), None)` source into a
/// `Relational.iterate` call computing the fixed point. Drops
/// the consumed conjunct from the surrounding `Where`.
///
/// Phase 1 only handles the binary case
///
/// ```sml
/// fun f (x, y) =
///   base (x, y) orelse
///   (exists z where f (x, z) andalso step (z, y))
/// ```
///
/// where `base` and `step` are let-bound predicates on
/// `int * int`-like tuple parameters whose body has the
/// `pat elem coll` shape — currently only a record-`elem`
/// (`{x, y} elem coll`) is recognised; other base shapes return
/// `None` and let the existing pipeline produce its
/// "pattern not grounded" error.
fn try_invert_recursive_predicates(
    steps: Vec<Step>,
    fn_env: &FnEnv,
    rec_fn_env: &FnEnv,
    datatypes: &DatatypeMap,
) -> Vec<Step> {
    if fn_env.is_empty() && rec_fn_env.is_empty() {
        return steps;
    }
    use crate::compile::generators::split_conjuncts;
    // Outer scope: anything introduced by an earlier scan in this
    // from. Used by Phase 2's recursive `expand_from_with_scope`
    // call so its sub-pipeline treats those names as runtime-stable.
    let outer_scope: BTreeSet<String> = {
        let mut s = BTreeSet::new();
        for st in &steps {
            if let StepKind::Scan(p, _, _) = &st.kind {
                let mut bs: Vec<Binding> = Vec::new();
                Binding::collect_bindings(p, &mut bs);
                for b in bs {
                    s.insert(b.id.name);
                }
            }
        }
        s
    };
    // Find the first Where conjunct that matches.
    for (where_idx, s) in steps.iter().enumerate() {
        let StepKind::Where(cond) = &s.kind else {
            continue;
        };
        let conjuncts = split_conjuncts(cond);
        for (cj_idx, cj) in conjuncts.iter().enumerate() {
            let Expr::Apply(_, f, arg, _) = cj else {
                continue;
            };
            let Expr::Identifier(_, fn_name) = f.as_ref() else {
                continue;
            };
            // Recognise three call shapes:
            //   (a) `f p` — single identifier arg matching one
            //       extent-scan pattern;
            //   (b) `f (v, v, ..., v)` — Phase 5: a tuple of
            //       identifiers with EVERY position equal to the
            //       same name `v`, matching a single extent-scan
            //       on `v`. After Phase 0z fires, the scan source
            //       is replaced with a wrapper that filters the
            //       iterate's bag for diagonal tuples and yields
            //       the single column. Used by `odd_path (v0, v0)`
            //       when querying for `v0` such that an odd cycle
            //       passes through `v0`.
            //   (c) `f (x, y, …)` — distinct identifiers, each
            //       matching its own extent-scan. The iterate's bag
            //       of tuples is consumed by a single Scan with a
            //       Tuple-pat (x, y, …) that destructures each
            //       element back into the original variables; the
            //       per-variable scans are dropped.
            enum ArgShape<'a> {
                Single(&'a Type, &'a str),
                Diagonal(&'a Type, &'a str, usize),
                DistinctTuple(&'a Type, Vec<(&'a str, &'a Type)>),
            }
            let arg_shape: ArgShape = match arg.as_ref() {
                Expr::Identifier(t, n) => {
                    ArgShape::Single(t.as_ref(), n.as_str())
                }
                Expr::Tuple(tt, items) => {
                    let id_components: Option<Vec<(&str, &Type)>> = items
                        .iter()
                        .map(|e| match e {
                            Expr::Identifier(t, n) => {
                                Some((n.as_str(), t.as_ref()))
                            }
                            _ => None,
                        })
                        .collect();
                    let Some(components) = id_components else {
                        continue;
                    };
                    if components.is_empty() {
                        continue;
                    }
                    let first_name = components[0].0;
                    let all_same =
                        components.iter().all(|(n, _)| *n == first_name);
                    if all_same {
                        ArgShape::Diagonal(
                            components[0].1,
                            first_name,
                            components.len(),
                        )
                    } else {
                        let mut sorted = components.clone();
                        sorted.sort_by_key(|(n, _)| *n);
                        sorted.dedup_by_key(|(n, _)| *n);
                        if sorted.len() != components.len() {
                            // Mix of repeats and distinct names — not
                            // currently supported.
                            continue;
                        }
                        ArgShape::DistinctTuple(tt.as_ref(), components)
                    }
                }
                _ => continue,
            };
            // Find matching extent-scan(s).
            let (arg_t, arg_name, diagonal_arity, scan_indices): (
                &Type,
                &str,
                usize,
                Vec<usize>,
            ) = match &arg_shape {
                ArgShape::Single(t, n) | ArgShape::Diagonal(t, n, _) => {
                    let arity = match arg_shape {
                        ArgShape::Diagonal(_, _, a) => a,
                        _ => 1,
                    };
                    let scan_idx = steps.iter().position(|st| {
                        matches!(&st.kind,
                            StepKind::Scan(p, src, None)
                                if matches!(src.as_ref(), Expr::Extent(_, _))
                                && matches!(p.as_ref(),
                                    Pat::Identifier(_, nn) if nn == n))
                    });
                    let Some(scan_idx) = scan_idx else {
                        continue;
                    };
                    (*t, *n, arity, vec![scan_idx])
                }
                ArgShape::DistinctTuple(tt, components) => {
                    let mut scans: Vec<usize> =
                        Vec::with_capacity(components.len());
                    let mut all_found = true;
                    for (n, _) in components {
                        let Some(idx) = steps.iter().position(|st| {
                            matches!(&st.kind,
                                StepKind::Scan(p, src, None)
                                    if matches!(src.as_ref(), Expr::Extent(_, _))
                                    && matches!(p.as_ref(),
                                        Pat::Identifier(_, nn) if nn == n))
                        }) else {
                            all_found = false;
                            break;
                        };
                        scans.push(idx);
                    }
                    if !all_found {
                        continue;
                    }
                    (*tt, components[0].0, 0, scans)
                }
            };
            let _ = arg_name;
            let scan_idx = scan_indices[0];
            // Capture owned tuple-args info before the borrow on
            // `arg_shape` ends (needed by the DistinctTuple rewrite).
            let distinct_tuple: Option<(Type, Vec<(String, Type)>)> =
                match &arg_shape {
                    ArgShape::DistinctTuple(tt, components) => Some((
                        (*tt).clone(),
                        components
                            .iter()
                            .map(|(n, t)| ((*n).to_string(), (*t).clone()))
                            .collect(),
                    )),
                    _ => None,
                };
            // Phase 3: skip non-stratified predicates (those with
            // a self-call inside `not(...)`). Inverting them would
            // either compute the wrong fixed point or diverge.
            // Falling through lets the existing pipeline produce
            // its "pattern not grounded" error instead of an
            // infinite loop. The pre-expander body is the right
            // one to inspect: post-expander shapes may have
            // already absorbed conjuncts into sub-froms.
            let body_for_strat = rec_fn_env
                .get(fn_name)
                .map(|(_, b)| b)
                .or_else(|| fn_env.get(fn_name).map(|(_, b)| b));
            if let Some(body) = body_for_strat
                && contains_self_call_under_negation(body, fn_name)
            {
                continue;
            }
            // Try Phase 2 first (the more general algorithm). It
            // handles ≥2 intermediate vars and arbitrary tuple-of-
            // identifiers recursive-call args; rec_fn_env supplies
            // pre-expander bodies so the original step predicates
            // are still visible. Falls back to Phase 1.
            let iterate_expr = build_iterate_for_recursive_v2(
                fn_name,
                rec_fn_env,
                fn_env,
                datatypes,
                &outer_scope,
            )
            .or_else(|| build_iterate_for_recursive(fn_name, arg_t, fn_env));
            let Some(iterate_expr) = iterate_expr else {
                continue;
            };
            // DistinctTuple: each iterate element is a tuple
            // (x, y, …) destructured by a single Scan whose pat
            // binds all the original sibling names.
            if let Some((tuple_type, components)) = distinct_tuple {
                return rewrite_steps_for_iterate_tuple(
                    steps,
                    where_idx,
                    cj_idx,
                    &scan_indices,
                    &components,
                    &tuple_type,
                    iterate_expr,
                );
            }
            // Phase 5: wrap the iterate with a diagonal-projection
            // `from` when the call site is `f (v, v, ..., v)` with
            // arity > 1, so the scan source's element type matches
            // the single-column pattern `v`.
            let final_source = if diagonal_arity > 1 {
                match wrap_diagonal_projection(
                    iterate_expr,
                    arg_t,
                    diagonal_arity,
                ) {
                    Some(w) => w,
                    None => continue,
                }
            } else {
                iterate_expr
            };
            // Rewrite: replace the scan source, drop the conjunct.
            return rewrite_steps_for_iterate(
                steps,
                where_idx,
                cj_idx,
                scan_idx,
                final_source,
            );
        }
    }
    steps
}

/// Phase 2 of recursive predicate inversion. Generalises
/// [`build_iterate_for_recursive`] to handle bodies whose
/// inductive case introduces ≥2 intermediate variables and whose
/// recursive call's arguments are an arbitrary tuple of
/// identifiers (param names or intermediate-var names). For
/// example,
///
/// ```sml
/// fun cousin (x, y) = sib (x, y)
///   orelse (exists xp, yp where par (x, xp)
///                       andalso par (y, yp)
///                       andalso cousin (xp, yp));
/// ```
///
/// Returns `Some(iterate_expr)` if the body matches; `None`
/// otherwise — in which case the caller falls back to Phase 1.
///
/// The body is read from `rec_fn_env` (pre-expander, with the
/// original step predicates still as conjuncts of the inner
/// `where`). The seed and update-fn body are synthesised as
/// un-expanded `from` expressions and then handed to
/// [`expand_from_with_scope`] so the existing inversion
/// pipeline produces real Scans for them.
fn build_iterate_for_recursive_v2(
    fn_name: &str,
    rec_fn_env: &FnEnv,
    fn_env: &FnEnv,
    datatypes: &DatatypeMap,
    outer_scope: &BTreeSet<String>,
) -> Option<Expr> {
    use crate::compile::generators::split_conjuncts;
    use crate::compile::type_env::Id;
    let (param_pat_orig, body_orig) = rec_fn_env.get(fn_name)?;
    let (param_pat_owned, body_owned) =
        normalize_tuple_id_param(param_pat_orig, body_orig);
    let param_pat = &param_pat_owned;
    let body = &body_owned;
    // Param must be a tuple of identifier sub-patterns. Phase 2's
    // synthesised seed/update bodies place each param in its own
    // Scan, so we need the names and types up-front.
    let Pat::Tuple(_, sub_pats) = param_pat else {
        return None;
    };
    if sub_pats.len() < 2 {
        // 0/1-param Phase 5; binary closure handled by Phase 1.
        return None;
    }
    let mut params: Vec<(String, Rc<Type>)> = Vec::new();
    for sp in sub_pats {
        match sp {
            Pat::Identifier(t, n) => params.push((n.clone(), t.clone())),
            _ => return None,
        }
    }
    // Body must be `base orelse recursive`. The recursive case is
    // `from <intermediate vars> where <step preds> andalso
    // f(<args>)` ending in an Exists step.
    let (base_case, recursive_case) = match_top_orelse(body)?;
    let inner_steps = match recursive_case {
        Expr::From(_, st) | Expr::Exists(_, st) => st,
        _ => return None,
    };
    if !matches!(inner_steps.last().map(|s| &s.kind), Some(StepKind::Exists)) {
        return None;
    }
    // Collect intermediate vars from leading Scan(_, Extent(_), None)
    // steps. They must be plain identifier patterns.
    let mut intermediates: Vec<(String, Rc<Type>)> = Vec::new();
    let mut where_cond: Option<&Expr> = None;
    for step in inner_steps {
        match &step.kind {
            StepKind::Scan(p, src, None)
                if matches!(src.as_ref(), Expr::Extent(_, _)) =>
            {
                match p.as_ref() {
                    Pat::Identifier(t, n) => {
                        intermediates.push((n.clone(), t.clone()))
                    }
                    _ => return None,
                }
            }
            StepKind::Where(c) => {
                if where_cond.is_some() {
                    return None;
                }
                where_cond = Some(c);
            }
            StepKind::Exists => {}
            // Anything else (yield, scan-over-non-Extent, etc.)
            // breaks Phase 2's recognition window.
            _ => return None,
        }
    }
    if intermediates.is_empty() {
        return None;
    }
    let where_cond = where_cond?;
    // Decompose the inner where into the recursive call and the
    // step predicates.
    let conjuncts = split_conjuncts(where_cond);
    let mut rec_args: Option<&Expr> = None;
    let mut step_preds: Vec<Expr> = Vec::new();
    for c in &conjuncts {
        if let Some(arg) = match_call_to(c, fn_name) {
            if rec_args.is_some() {
                return None;
            }
            rec_args = Some(arg);
        } else {
            step_preds.push(c.clone());
        }
    }
    let rec_args = rec_args?;
    if step_preds.is_empty() {
        return None;
    }
    // Recursive call's args must be a tuple of identifiers, each
    // resolving to either a param name or an intermediate-var
    // name. (Phase 2 doesn't synthesise bindings for fresh names
    // introduced by the recursive call.)
    let Expr::Tuple(_, rc_items) = rec_args else {
        return None;
    };
    if rc_items.len() != params.len() {
        return None;
    }
    let mut rec_arg_names: Vec<(String, Rc<Type>)> = Vec::new();
    let known: BTreeSet<&str> = params
        .iter()
        .chain(intermediates.iter())
        .map(|(n, _)| n.as_str())
        .collect();
    for it in rc_items {
        let Expr::Identifier(t, n) = it else {
            return None;
        };
        if !known.contains(n.as_str()) {
            return None;
        }
        rec_arg_names.push((n.clone(), t.clone()));
    }
    // Result tuple type is (param_t1, ..., param_tN).
    let elem_t = Type::Tuple(
        params.iter().map(|(_, t)| Rc::new((**t).clone())).collect(),
    );
    let coll_t = Type::Bag(Rc::new(elem_t.clone()));
    let elem_t_box = Rc::new(elem_t.clone());
    // Helper: build a step env containing the given bindings.
    let mk_env = |bs: Vec<Binding>| StepEnv::new(bs, false, false);
    let bs_for = |names: &[(String, Rc<Type>)]| -> Vec<Binding> {
        names
            .iter()
            .map(|(n, t)| Binding::new(Id::new(n, 0), t.clone()))
            .collect()
    };
    // ----- Seed: `from p1, p2, ... where base yield (p1,p2,...)` -----
    let mut seed_steps: Vec<Step> = Vec::new();
    let mut bound: Vec<(String, Rc<Type>)> = Vec::new();
    for (n, t) in &params {
        bound.push((n.clone(), t.clone()));
        seed_steps.push(Step::new(
            StepKind::Scan(
                Box::new(Pat::Identifier(t.clone(), n.clone())),
                Box::new(Expr::Extent(t.clone(), Span::new(""))),
                None,
            ),
            mk_env(bs_for(&bound)),
        ));
    }
    seed_steps.push(Step::new(
        StepKind::Where(Box::new(base_case.clone())),
        mk_env(bs_for(&bound)),
    ));
    let yield_tuple = Expr::Tuple(
        elem_t_box.clone(),
        params
            .iter()
            .map(|(n, t)| Expr::Identifier(t.clone(), n.clone()))
            .collect(),
    );
    let yield_env = StepEnv::new(
        vec![Binding::new(Id::new("current", 0), elem_t_box.clone())],
        true,
        false,
    );
    seed_steps.push(Step::new(
        StepKind::Yield(Box::new(yield_tuple.clone())),
        yield_env.clone(),
    ));
    let seed_from = Expr::From(Rc::new(coll_t.clone()), seed_steps);
    let seed_expanded = expand_from_with_scope_rec(
        seed_from,
        fn_env,
        rec_fn_env,
        datatypes,
        outer_scope,
    );
    // If the seed still contains an Extent scan, we couldn't
    // ground something; bail out and let Phase 1 try.
    if from_has_extent(&seed_expanded) {
        return None;
    }
    // ----- Update fn body -----
    // Build:
    //   from p1, p2, ..., (rc_arg1, rc_arg2, ...) in newF
    //     where step_preds yield (p1, ..., pN)
    // The first N scans are over Extents (will be inverted by
    // expand_from_with_scope using the step predicates). The
    // rec-args scan is concrete (newF). When rc_args mention any
    // params or intermediates, we still emit param scans first;
    // because rec_args names duplicate names already bound in the
    // param scans, we use FRESH names for the rec-args scan and
    // add an equality where-clause to bind them — actually no:
    // the rec_args identifiers are the **canonical** names from
    // the inner exists, so `rec_arg_names` may include both param
    // names and intermediate-var names. To avoid clashes with the
    // param scans we destructure into fresh names and equate.
    let new_name = "__tc_new";
    let new_id =
        Expr::Identifier(Rc::new(coll_t.clone()), new_name.to_string());
    // Build fresh-name destructuring pattern for the newF scan.
    // For each rc_arg, use a fresh name `__tc_v{i}`.
    let mut fresh_pats: Vec<Pat> = Vec::new();
    let mut fresh_eqs: Vec<Expr> = Vec::new();
    for (i, (orig_name, orig_t)) in rec_arg_names.iter().enumerate() {
        let fresh = format!("__tc_v{}", i);
        fresh_pats.push(Pat::Identifier(orig_t.clone(), fresh.clone()));
        // Equality: orig_name = fresh_name. The orig_name comes
        // from `params` or `intermediates`, both of which we'll
        // bind via Extent scans (and step_preds invert them).
        let eq_op = match orig_t.as_ref() {
            Type::Primitive(PrimitiveType::Int) => BuiltInFunction::IntEq,
            Type::Primitive(PrimitiveType::String) => BuiltInFunction::StringEq,
            Type::Primitive(PrimitiveType::Char) => BuiltInFunction::CharEq,
            Type::Primitive(PrimitiveType::Bool) => BuiltInFunction::BoolEq,
            _ => BuiltInFunction::GEq,
        };
        let pair_t = Rc::new(Type::Tuple(vec![
            Rc::new((**orig_t).clone()),
            Rc::new((**orig_t).clone()),
        ]));
        let fn_t = Rc::new(Type::Fn(
            pair_t.clone(),
            Rc::new(Type::Primitive(PrimitiveType::Bool)),
        ));
        let eq_lit = Expr::Literal(fn_t, Val::Fn(eq_op));
        let lhs = Expr::Identifier(orig_t.clone(), orig_name.clone());
        let rhs = Expr::Identifier(orig_t.clone(), fresh);
        let arg = Expr::Tuple(pair_t, vec![lhs, rhs]);
        fresh_eqs.push(Expr::Apply(
            Rc::new(Type::Primitive(PrimitiveType::Bool)),
            Box::new(eq_lit),
            Box::new(arg),
            Span::new(""),
        ));
    }
    let rec_args_t = Type::Tuple(
        rec_arg_names
            .iter()
            .map(|(_, t)| Rc::new((**t).clone()))
            .collect(),
    );
    let rec_args_pat = Pat::Tuple(Rc::new(rec_args_t.clone()), fresh_pats);
    // Build update-body steps.
    let mut update_steps: Vec<Step> = Vec::new();
    let mut bound2: Vec<(String, Rc<Type>)> = Vec::new();
    for (n, t) in &params {
        bound2.push((n.clone(), t.clone()));
        update_steps.push(Step::new(
            StepKind::Scan(
                Box::new(Pat::Identifier(t.clone(), n.clone())),
                Box::new(Expr::Extent(t.clone(), Span::new(""))),
                None,
            ),
            mk_env(bs_for(&bound2)),
        ));
    }
    for (n, t) in &intermediates {
        bound2.push((n.clone(), t.clone()));
        update_steps.push(Step::new(
            StepKind::Scan(
                Box::new(Pat::Identifier(t.clone(), n.clone())),
                Box::new(Expr::Extent(t.clone(), Span::new(""))),
                None,
            ),
            mk_env(bs_for(&bound2)),
        ));
    }
    // Add the newF scan with fresh names.
    for (i, (_, t)) in rec_arg_names.iter().enumerate() {
        let fresh = format!("__tc_v{}", i);
        bound2.push((fresh, t.clone()));
    }
    update_steps.push(Step::new(
        StepKind::Scan(Box::new(rec_args_pat), Box::new(new_id.clone()), None),
        mk_env(bs_for(&bound2)),
    ));
    // Where: step_preds andalso fresh equalities.
    let mut all_conjuncts = step_preds.clone();
    all_conjuncts.extend(fresh_eqs);
    let combined_where = and_all(all_conjuncts);
    update_steps.push(Step::new(
        StepKind::Where(Box::new(combined_where)),
        mk_env(bs_for(&bound2)),
    ));
    update_steps.push(Step::new(
        StepKind::Yield(Box::new(yield_tuple.clone())),
        yield_env,
    ));
    let update_body = Expr::From(Rc::new(coll_t.clone()), update_steps);
    // Recursively expand the update body so step_preds invert
    // the param/intermediate Extent scans.
    let mut update_outer_scope: BTreeSet<String> = outer_scope.clone();
    update_outer_scope.insert(new_name.to_string());
    let update_body_expanded = expand_from_with_scope_rec(
        update_body,
        fn_env,
        rec_fn_env,
        datatypes,
        &update_outer_scope,
    );
    if from_has_extent(&update_body_expanded) {
        return None;
    }
    // Wrap update body in `fn (allF, newF) => ...`.
    let all_name = "__tc_all";
    let coll_t_box = Rc::new(coll_t.clone());
    let pair_pat = Pat::Tuple(
        Rc::new(Type::Tuple(vec![
            Rc::new(coll_t.clone()),
            Rc::new(coll_t.clone()),
        ])),
        vec![
            Pat::Identifier(coll_t_box.clone(), all_name.to_string()),
            Pat::Identifier(coll_t_box.clone(), new_name.to_string()),
        ],
    );
    let fn_t = Rc::new(Type::Fn(
        Rc::new(Type::Tuple(vec![
            Rc::new(coll_t.clone()),
            Rc::new(coll_t.clone()),
        ])),
        Rc::new(coll_t.clone()),
    ));
    let update_fn = Expr::Fn(
        fn_t.clone(),
        vec![Match {
            pat: pair_pat,
            expr: update_body_expanded,
        }],
        Span::new(""),
    );
    // Build `Relational.iterate seed updateFn`.
    let iter_t = Rc::new(Type::Fn(
        Rc::new(coll_t.clone()),
        Rc::new(Type::Fn(
            Rc::new(fn_t.as_ref().clone()),
            Rc::new(coll_t.clone()),
        )),
    ));
    let iter_lit =
        Expr::Literal(iter_t, Val::Fn(BuiltInFunction::RelationalIterate));
    let after_seed_t = Rc::new(Type::Fn(
        Rc::new(fn_t.as_ref().clone()),
        Rc::new(coll_t.clone()),
    ));
    let with_seed = Expr::Apply(
        after_seed_t,
        Box::new(iter_lit),
        Box::new(seed_expanded),
        Span::new(""),
    );
    Some(Expr::Apply(
        Rc::new(coll_t.clone()),
        Box::new(with_seed),
        Box::new(update_fn),
        Span::new(""),
    ))
}

/// Returns true if `expr` is a `From` whose steps still contain a
/// `Scan(_, Extent(_), _)` — i.e. predicate inversion didn't
/// successfully ground every unbounded pattern.
fn from_has_extent(expr: &Expr) -> bool {
    let Expr::From(_, steps) = expr else {
        return false;
    };
    steps.iter().any(|s| {
        matches!(&s.kind,
            StepKind::Scan(_, src, _)
                if matches!(src.as_ref(), Expr::Extent(_, _)))
    })
}

/// Returns true if `expr` contains an `Extent` placeholder anywhere
/// in its tree. Used to identify let-bound function bodies that
/// can't compile on their own (because they reference unbounded
/// domain variables) and need to be inlined at call sites for
/// predicate inversion to ground the variables.
fn body_has_extent(expr: &Expr) -> bool {
    match expr {
        Expr::Extent(_, _) => true,
        Expr::Aggregate(_, e1, e2) => {
            body_has_extent(e1) || body_has_extent(e2)
        }
        Expr::Apply(_, f, a, _) => body_has_extent(f) || body_has_extent(a),
        Expr::Case(_, subj, arms, _) => {
            body_has_extent(subj)
                || arms.iter().any(|m| body_has_extent(&m.expr))
        }
        Expr::Exists(_, steps)
        | Expr::Forall(_, steps)
        | Expr::From(_, steps) => steps.iter().any(step_has_extent),
        Expr::Fn(_, arms, _) => arms.iter().any(|m| body_has_extent(&m.expr)),
        Expr::Let(_, _, body) => body_has_extent(body),
        Expr::List(_, items) | Expr::Tuple(_, items) => {
            items.iter().any(body_has_extent)
        }
        Expr::Raise(_, e, _) => body_has_extent(e),
        Expr::Current(_)
        | Expr::Identifier(_, _)
        | Expr::Literal(_, _)
        | Expr::Ordinal(_)
        | Expr::RecordSelector(_, _) => false,
    }
}

fn step_has_extent(s: &Step) -> bool {
    match &s.kind {
        StepKind::Compute(e)
        | StepKind::Order(e)
        | StepKind::Skip(e)
        | StepKind::Take(e)
        | StepKind::Where(e)
        | StepKind::Yield(e) => body_has_extent(e),
        StepKind::Group(k, agg) => {
            body_has_extent(k) || agg.as_deref().is_some_and(body_has_extent)
        }
        StepKind::Scan(_, src, cond) => {
            matches!(src.as_ref(), Expr::Extent(_, _))
                || body_has_extent(src)
                || cond.as_deref().is_some_and(body_has_extent)
        }
        StepKind::Except(_, exprs)
        | StepKind::Intersect(_, exprs)
        | StepKind::Union(_, exprs) => exprs.iter().any(body_has_extent),
        StepKind::Distinct | StepKind::Exists | StepKind::Unorder => false,
    }
}

/// Returns `Some(iterate_expr)` if `fn_env[fn_name]` matches the
/// Phase 1 transitive-closure shape, or `None` otherwise.
fn build_iterate_for_recursive(
    fn_name: &str,
    arg_type: &Type,
    fn_env: &FnEnv,
) -> Option<Expr> {
    let (param_pat_orig, body_orig) = fn_env.get(fn_name)?;
    let (param_pat_owned, body_owned) =
        normalize_tuple_id_param(param_pat_orig, body_orig);
    let param_pat = &param_pat_owned;
    let body = &body_owned;
    // Param must be `(x, y)` — a binary tuple of identifier subpats.
    let Pat::Tuple(_, sub_pats) = param_pat else {
        return None;
    };
    if sub_pats.len() != 2 {
        return None;
    }
    let (x_name, x_t) = match &sub_pats[0] {
        Pat::Identifier(t, n) => (n.clone(), t.clone()),
        _ => return None,
    };
    let (_y_name, y_t) = match &sub_pats[1] {
        Pat::Identifier(t, n) => (n.clone(), t.clone()),
        _ => return None,
    };
    // Body must be `Apply(BoolOrElse, Tuple([base, step]))`.
    let (base_case, recursive_case) = match_top_orelse(body)?;
    // Recursive case: `From(_, [Scan(z, _, None), ..., Where(c),
    // ..., Exists])`. Phase 1 accepts both the un-expanded shape
    // (`Scan(z, Extent(_), None)` with a 2-conjunct where) and the
    // post-expander shape (`Scan(z, sub_from, None)` produced by
    // inverting the step predicate, leaving only the self-call).
    let inner_steps = match recursive_case {
        Expr::From(_, st) | Expr::Exists(_, st) => st,
        _ => return None,
    };
    if !matches!(inner_steps.last().map(|s| &s.kind), Some(StepKind::Exists)) {
        return None;
    }
    let StepKind::Scan(z_pat, _z_src, None) = &inner_steps[0].kind else {
        return None;
    };
    let (z_name, z_t) = match z_pat.as_ref() {
        Pat::Identifier(t, n) => (n.clone(), t.clone()),
        _ => return None,
    };
    let where_step = inner_steps
        .iter()
        .find(|s| matches!(s.kind, StepKind::Where(_)))?;
    let StepKind::Where(inner_cond) = &where_step.kind else {
        return None;
    };
    use crate::compile::generators::split_conjuncts;
    let inner_conjuncts = split_conjuncts(inner_cond);
    let mut rec_call_args: Option<&Expr> = None;
    let mut other_count = 0;
    for c in &inner_conjuncts {
        if let Some(arg) = match_call_to(c, fn_name) {
            if rec_call_args.is_some() {
                return None; // multiple self-calls
            }
            rec_call_args = Some(arg);
        } else {
            other_count += 1;
        }
    }
    let rec_call = rec_call_args?;
    // Phase 1: zero other conjuncts (post-expansion; step
    // predicate already inverted) or exactly one (un-expanded).
    if other_count > 1 {
        return None;
    }
    // rec_call args must be `(Var(x_name), Var(z_name))`.
    let Expr::Tuple(_, rc_args) = rec_call else {
        return None;
    };
    if rc_args.len() != 2 {
        return None;
    }
    if !matches!(&rc_args[0], Expr::Identifier(_, n) if n == &x_name) {
        return None;
    }
    if !matches!(&rc_args[1], Expr::Identifier(_, n) if n == &z_name) {
        return None;
    }
    // Extract the seed expression from the base case. Phase 1
    // recognises `Apply(Var("edge"), Tuple([Var(x), Var(y)]))`
    // where edge's body is `Apply(BoolElem, Tuple([rec_or_tuple,
    // coll]))`. Returns `coll`. The rec_or_tuple may contain
    // computed fields.
    let Expr::Apply(_, base_f, _base_arg, _) = base_case else {
        return None;
    };
    let Expr::Identifier(_, base_name) = base_f.as_ref() else {
        return None;
    };
    let (base_param_pat, base_body) = fn_env.get(base_name)?;
    let (seed_expr, base_lhs_record_field_order) =
        extract_seed_from_elem_body(base_body, base_param_pat)?;
    // Build the iterate expression. Element type T is (x_t, y_t).
    let _ = arg_type; // kept for future Phase 2 use
    Some(build_iterate_ast(
        x_t.as_ref(),
        y_t.as_ref(),
        z_t.as_ref(),
        seed_expr,
        base_lhs_record_field_order,
    ))
}

/// If `body` is `Apply(BoolOrElse, Tuple([a, b]))`, returns
/// `Some((a, b))`.
/// If `pat` is a single-identifier param with tuple type (e.g.
/// `fun path p = …` where `p : 'a * 'b`), rewrite the pair into the
/// equivalent tuple-pattern form (`fun path (p__1, p__2) = …`),
/// substituting `#i p` projections in the body with the matching
/// component identifier and replacing whole-`p` references with the
/// reconstructed tuple. Returns `(pat, body)` unchanged when no
/// rewrite applies. Lets the recursive-iterate phases that require
/// tuple-shaped params (Phase 1 and Phase 2) accept programs
/// written in the projection style.
fn normalize_tuple_id_param(pat: &Pat, body: &Expr) -> (Pat, Expr) {
    let Pat::Identifier(t, name) = pat else {
        return (pat.clone(), body.clone());
    };
    let Type::Tuple(elem_types) = t.as_ref() else {
        return (pat.clone(), body.clone());
    };
    if elem_types.is_empty() {
        return (pat.clone(), body.clone());
    }
    let comp_names: Vec<String> = (0..elem_types.len())
        .map(|i| format!("{}__{}", name, i + 1))
        .collect();
    let comp_pats: Vec<Pat> = elem_types
        .iter()
        .zip(comp_names.iter())
        .map(|(et, cn)| Pat::Identifier((*et).clone(), cn.clone()))
        .collect();
    let comp_idents: Vec<Expr> = elem_types
        .iter()
        .zip(comp_names.iter())
        .map(|(et, cn)| Expr::Identifier((*et).clone(), cn.clone()))
        .collect();
    let new_pat = Pat::Tuple(t.clone(), comp_pats);
    let tuple_replacement = Expr::Tuple(t.clone(), comp_idents);

    use crate::compile::replacer::substitute;
    let mut map = HashMap::new();
    map.insert(name.clone(), tuple_replacement);
    let body_subst = substitute(body, &map);
    let body_simplified = simplify_tuple_projections(&body_subst);
    (new_pat, body_simplified)
}

/// Recursively folds `Apply(RecordSelector(_, slot), Tuple(args))`
/// into `args[slot]`. Used after substituting a tuple expression for
/// a single-id tuple-typed param so projections like `#1 p` collapse
/// to the component variable.
fn simplify_tuple_projections(expr: &Expr) -> Expr {
    match expr {
        Expr::Aggregate(t, e1, e2) => Expr::Aggregate(
            t.clone(),
            Box::new(simplify_tuple_projections(e1)),
            Box::new(simplify_tuple_projections(e2)),
        ),
        Expr::Apply(t, f, a, span) => {
            let f2 = simplify_tuple_projections(f);
            let a2 = simplify_tuple_projections(a);
            if let Expr::RecordSelector(_, slot) = &f2
                && let Expr::Tuple(_, items) = &a2
                && *slot < items.len()
            {
                items[*slot].clone()
            } else {
                Expr::Apply(t.clone(), Box::new(f2), Box::new(a2), span.clone())
            }
        }
        Expr::Case(t, subj, arms, span) => Expr::Case(
            t.clone(),
            Box::new(simplify_tuple_projections(subj)),
            arms.iter()
                .map(|m| Match {
                    pat: m.pat.clone(),
                    expr: simplify_tuple_projections(&m.expr),
                })
                .collect(),
            span.clone(),
        ),
        Expr::Exists(t, steps) => {
            Expr::Exists(t.clone(), simplify_tuple_projections_in_steps(steps))
        }
        Expr::Fn(t, arms, span) => Expr::Fn(
            t.clone(),
            arms.iter()
                .map(|m| Match {
                    pat: m.pat.clone(),
                    expr: simplify_tuple_projections(&m.expr),
                })
                .collect(),
            span.clone(),
        ),
        Expr::Forall(t, steps) => {
            Expr::Forall(t.clone(), simplify_tuple_projections_in_steps(steps))
        }
        Expr::From(t, steps) => {
            Expr::From(t.clone(), simplify_tuple_projections_in_steps(steps))
        }
        Expr::Let(t, decls, body) => Expr::Let(
            t.clone(),
            decls.clone(),
            Box::new(simplify_tuple_projections(body)),
        ),
        Expr::List(t, items) => Expr::List(
            t.clone(),
            items.iter().map(simplify_tuple_projections).collect(),
        ),
        Expr::Tuple(t, items) => Expr::Tuple(
            t.clone(),
            items.iter().map(simplify_tuple_projections).collect(),
        ),
        Expr::Raise(t, e, span) => Expr::Raise(
            t.clone(),
            Box::new(simplify_tuple_projections(e)),
            span.clone(),
        ),
        Expr::Current(_)
        | Expr::Extent(_, _)
        | Expr::Identifier(_, _)
        | Expr::Literal(_, _)
        | Expr::Ordinal(_)
        | Expr::RecordSelector(_, _) => expr.clone(),
    }
}

fn simplify_tuple_projections_in_steps(steps: &[Step]) -> Vec<Step> {
    steps
        .iter()
        .map(|s| {
            let kind = match &s.kind {
                StepKind::Compute(e) => {
                    StepKind::Compute(Box::new(simplify_tuple_projections(e)))
                }
                StepKind::Distinct => StepKind::Distinct,
                StepKind::Except(d, exprs) => StepKind::Except(
                    *d,
                    exprs.iter().map(simplify_tuple_projections).collect(),
                ),
                StepKind::Exists => StepKind::Exists,
                StepKind::Group(k, agg) => StepKind::Group(
                    Box::new(simplify_tuple_projections(k)),
                    agg.as_deref()
                        .map(|e| Box::new(simplify_tuple_projections(e))),
                ),
                StepKind::Intersect(d, exprs) => StepKind::Intersect(
                    *d,
                    exprs.iter().map(simplify_tuple_projections).collect(),
                ),
                StepKind::Order(e) => {
                    StepKind::Order(Box::new(simplify_tuple_projections(e)))
                }
                StepKind::Scan(p, src, cond) => StepKind::Scan(
                    p.clone(),
                    Box::new(simplify_tuple_projections(src)),
                    cond.as_deref()
                        .map(|c| Box::new(simplify_tuple_projections(c))),
                ),
                StepKind::Skip(e) => {
                    StepKind::Skip(Box::new(simplify_tuple_projections(e)))
                }
                StepKind::Take(e) => {
                    StepKind::Take(Box::new(simplify_tuple_projections(e)))
                }
                StepKind::Union(d, exprs) => StepKind::Union(
                    *d,
                    exprs.iter().map(simplify_tuple_projections).collect(),
                ),
                StepKind::Unorder => StepKind::Unorder,
                StepKind::Where(e) => {
                    StepKind::Where(Box::new(simplify_tuple_projections(e)))
                }
                StepKind::Yield(e) => {
                    StepKind::Yield(Box::new(simplify_tuple_projections(e)))
                }
            };
            Step::new(kind, s.env.clone())
        })
        .collect()
}

fn match_top_orelse(body: &Expr) -> Option<(&Expr, &Expr)> {
    let Expr::Apply(_, f, arg, _) = body else {
        return None;
    };
    let Expr::Literal(_, Val::Fn(BuiltInFunction::BoolOrElse)) = f.as_ref()
    else {
        return None;
    };
    let Expr::Tuple(_, items) = arg.as_ref() else {
        return None;
    };
    if items.len() != 2 {
        return None;
    }
    Some((&items[0], &items[1]))
}

/// If `e` is `Apply(Var(name), arg)`, returns `Some(arg)`.
fn match_call_to<'a>(e: &'a Expr, name: &str) -> Option<&'a Expr> {
    let Expr::Apply(_, f, arg, _) = e else {
        return None;
    };
    let Expr::Identifier(_, n) = f.as_ref() else {
        return None;
    };
    if n != name {
        return None;
    }
    Some(arg)
}

/// Returns true if `body` contains an `Apply(Var(name), _)`
/// anywhere — i.e. a call to the named function.
fn contains_self_call(body: &Expr, name: &str) -> bool {
    fn walk(e: &Expr, name: &str) -> bool {
        if let Expr::Apply(_, f, _, _) = e
            && let Expr::Identifier(_, n) = f.as_ref()
            && n == name
        {
            return true;
        }
        match e {
            Expr::Apply(_, f, a, _) => walk(f, name) || walk(a, name),
            Expr::Tuple(_, items) | Expr::List(_, items) => {
                items.iter().any(|i| walk(i, name))
            }
            Expr::Case(_, subj, arms, _) => {
                walk(subj, name) || arms.iter().any(|m| walk(&m.expr, name))
            }
            Expr::Fn(_, arms, _) => arms.iter().any(|m| walk(&m.expr, name)),
            Expr::Let(_, _, body) => walk(body, name),
            Expr::From(_, steps)
            | Expr::Exists(_, steps)
            | Expr::Forall(_, steps) => steps.iter().any(|s| match &s.kind {
                StepKind::Scan(_, src, cond) => {
                    walk(src, name)
                        || cond.as_ref().is_some_and(|c| walk(c, name))
                }
                StepKind::Where(c)
                | StepKind::Yield(c)
                | StepKind::Order(c)
                | StepKind::Compute(c)
                | StepKind::Skip(c)
                | StepKind::Take(c) => walk(c, name),
                StepKind::Group(k, agg) => {
                    walk(k, name) || agg.as_ref().is_some_and(|a| walk(a, name))
                }
                _ => false,
            }),
            Expr::Aggregate(_, l, r) => walk(l, name) || walk(r, name),
            _ => false,
        }
    }
    walk(body, name)
}

/// Phase 4: if `body` has top-level `Bool.orelse` decomposed into
/// disjuncts, returns the orelse over the disjuncts that DON'T
/// contain a self-call to `name`. Returns `None` when every
/// disjunct is recursive or the body has no top-level `orelse`.
/// Used to fall back to base-case-only inversion when neither
/// Phase 1's nor Phase 2's iterate builder matches the body
/// shape (e.g. bounded recursion with arithmetic constraints).
fn remove_recursive_branches(body: &Expr, name: &str) -> Option<Expr> {
    use crate::compile::generators::split_orelse;
    let disjuncts = split_orelse(body);
    if disjuncts.len() < 2 {
        return None; // No top-level orelse to peel.
    }
    let kept: Vec<Expr> = disjuncts
        .into_iter()
        .filter(|d| !contains_self_call(d, name))
        .collect();
    if kept.is_empty() {
        return None;
    }
    let mut iter = kept.into_iter();
    let first = iter.next().unwrap();
    Some(iter.fold(first, |a, b| {
        let bool_t = Rc::new(Type::Primitive(PrimitiveType::Bool));
        let pair_t = Rc::new(Type::Tuple(vec![
            Rc::new((*bool_t).clone()),
            Rc::new((*bool_t).clone()),
        ]));
        let fn_t = Rc::new(Type::Fn(pair_t.clone(), bool_t.clone()));
        let fn_lit = Expr::Literal(fn_t, Val::Fn(BuiltInFunction::BoolOrElse));
        Expr::Apply(
            bool_t,
            Box::new(fn_lit),
            Box::new(Expr::Tuple(pair_t, vec![a, b])),
            Span::new(""),
        )
    }))
}

/// Phase 3: returns true if `body` contains a call to `name`
/// inside any subexpression headed by `Bool.not` (or whose
/// surrounding `from` ends in an `Exists` step that is itself
/// negated upstream). Such a binding is non-stratified — naively
/// inverting it would compute the wrong fixed point or diverge.
/// The check is a conservative: it walks the AST tracking a
/// "negation depth" parity and reports any self-call seen at
/// odd parity.
fn contains_self_call_under_negation(body: &Expr, name: &str) -> bool {
    fn walk(e: &Expr, name: &str, neg: bool) -> bool {
        match e {
            Expr::Apply(_, f, arg, _) => {
                // `Bool.not`-headed call flips the negation parity for
                // the argument.
                let arg_neg = if matches!(
                    f.as_ref(),
                    Expr::Literal(_, Val::Fn(BuiltInFunction::BoolNot))
                ) {
                    !neg
                } else {
                    neg
                };
                if neg
                    && let Expr::Identifier(_, n) = f.as_ref()
                    && n == name
                {
                    return true;
                }
                walk(f, name, neg) || walk(arg, name, arg_neg)
            }
            Expr::Tuple(_, items) | Expr::List(_, items) => {
                items.iter().any(|i| walk(i, name, neg))
            }
            Expr::Case(_, subj, arms, _) => {
                walk(subj, name, neg)
                    || arms.iter().any(|m| walk(&m.expr, name, neg))
            }
            Expr::Fn(_, arms, _) => {
                arms.iter().any(|m| walk(&m.expr, name, neg))
            }
            Expr::Let(_, _, body) => walk(body, name, neg),
            Expr::From(_, steps)
            | Expr::Exists(_, steps)
            | Expr::Forall(_, steps) => steps.iter().any(|s| match &s.kind {
                StepKind::Scan(_, src, cond) => {
                    walk(src, name, neg)
                        || cond.as_ref().is_some_and(|c| walk(c, name, neg))
                }
                StepKind::Where(c)
                | StepKind::Yield(c)
                | StepKind::Order(c)
                | StepKind::Compute(c)
                | StepKind::Skip(c)
                | StepKind::Take(c) => walk(c, name, neg),
                StepKind::Group(k, agg) => {
                    walk(k, name, neg)
                        || agg.as_ref().is_some_and(|a| walk(a, name, neg))
                }
                _ => false,
            }),
            Expr::Aggregate(_, l, r) => {
                walk(l, name, neg) || walk(r, name, neg)
            }
            _ => false,
        }
    }
    walk(body, name, false)
}

/// Recognises a body of the form `pat_or_tuple elem coll` and
/// returns the collection plus, when the LHS is a record, the
/// label order so we can map record fields back to tuple slots.
fn extract_seed_from_elem_body(
    body: &Expr,
    _param_pat: &Pat,
) -> Option<(Expr, Option<Vec<String>>)> {
    let Expr::Apply(_, f, arg, _) = body else {
        return None;
    };
    let Expr::Literal(_, Val::Fn(BuiltInFunction::ListElem)) = f.as_ref()
    else {
        return None;
    };
    let Expr::Tuple(_, items) = arg.as_ref() else {
        return None;
    };
    if items.len() != 2 {
        return None;
    }
    let lhs = &items[0];
    let coll = &items[1];
    // LHS is either a tuple `(x, y)` or a record `{x, y}`. Either
    // way, the arg-type tells us the field order.
    let elem_t = lhs.type_();
    let label_order = match elem_t.as_ref() {
        Type::Record(_, fields) => {
            let mut ord = Vec::new();
            for lbl in fields.keys() {
                if let Label::String(s) = lbl {
                    ord.push(s.clone());
                } else {
                    return None;
                }
            }
            Some(ord)
        }
        Type::Tuple(_) => None,
        _ => return None,
    };
    Some((coll.clone(), label_order))
}

/// Builds the `Relational.iterate seed updateFn` AST. The element
/// type of the result is `(x_t, y_t)` (a 2-tuple). If
/// `seed_label_order` is `Some(labels)`, the seed collection's
/// elements are records and we wrap with a projection
/// `from r in seed yield (r.<labels[0]>, r.<labels[1]>)` to
/// convert them to tuples.
fn build_iterate_ast(
    x_t: &Type,
    y_t: &Type,
    _z_t: &Type,
    seed_expr: Expr,
    seed_label_order: Option<Vec<String>>,
) -> Expr {
    use crate::compile::type_env::Id;
    // Result element type: (x_t, y_t).
    let elem_t = Type::Tuple(vec![Rc::new(x_t.clone()), Rc::new(y_t.clone())]);
    let bool_t = Type::Primitive(PrimitiveType::Bool);
    // Result collection type: Bag(elem_t). (We don't preserve list
    // ordering in Phase 1; iterate's runtime uses Val::List as its
    // representation regardless.)
    let coll_t = Type::Bag(Rc::new(elem_t.clone()));
    // Convert seed from records to tuples if needed.
    let typed_seed: Expr = match seed_label_order {
        None => {
            // Seed is already collection of tuples — just unify the
            // type to Bag(elem_t) if it was List(elem_t).
            seed_expr
        }
        Some(labels) => {
            // Wrap as `from r in seed yield (r.label0, r.label1)`.
            let r_name = "__tc_r";
            // Determine seed's element type.
            let seed_t = seed_expr.type_();
            let seed_elem_t = match seed_t.as_ref() {
                Type::List(t) | Type::Bag(t) => (**t).clone(),
                _ => return Expr::List(Rc::new(coll_t), Vec::new()),
            };
            let r_pat =
                Pat::Identifier(Rc::new(seed_elem_t.clone()), r_name.into());
            let r_id =
                Expr::Identifier(Rc::new(seed_elem_t.clone()), r_name.into());
            let mut tuple_items: Vec<Expr> = Vec::new();
            for (i, lbl) in labels.iter().enumerate() {
                let field_t = match &seed_elem_t {
                    Type::Record(_, fs) => {
                        let key = Label::String(lbl.clone());
                        match fs.get(&key) {
                            Some(t) => t.clone(),
                            None => {
                                return Expr::List(Rc::new(coll_t), Vec::new());
                            }
                        }
                    }
                    _ => return Expr::List(Rc::new(coll_t), Vec::new()),
                };
                let sel_t = Rc::new(Type::Fn(
                    Rc::new(seed_elem_t.clone()),
                    field_t.clone(),
                ));
                let sel = Expr::RecordSelector(sel_t, i);
                tuple_items.push(Expr::Apply(
                    field_t.clone(),
                    Box::new(sel),
                    Box::new(r_id.clone()),
                    Span::new(""),
                ));
            }
            let tuple_expr = Expr::Tuple(Rc::new(elem_t.clone()), tuple_items);
            let r_binding =
                Binding::new(Id::new(r_name, 0), Rc::new(seed_elem_t.clone()));
            let scan_env =
                StepEnv::new(vec![r_binding.clone()], true, seed_t.is_list());
            let yield_env = StepEnv::new(
                vec![Binding::new(
                    Id::new("current", 0),
                    Rc::new(elem_t.clone()),
                )],
                true,
                seed_t.is_list(),
            );
            let inner_steps = vec![
                Step::new(
                    StepKind::Scan(
                        Box::new(r_pat),
                        Box::new(seed_expr.clone()),
                        None,
                    ),
                    scan_env,
                ),
                Step::new(StepKind::Yield(Box::new(tuple_expr)), yield_env),
            ];
            let inner_t = if seed_t.is_list() {
                Type::List(Rc::new(elem_t.clone()))
            } else {
                Type::Bag(Rc::new(elem_t.clone()))
            };
            Expr::From(Rc::new(inner_t), inner_steps)
        }
    };
    // Build the update fn: `fn (allP, newP) =>
    //   from (px, pz) in newP, (sz, sy) in seed_tuples
    //   where pz = sz yield (px, sy)`.
    let all_name = "__tc_all";
    let new_name = "__tc_new";
    let px_name = "__tc_px";
    let pz_name = "__tc_pz";
    let sz_name = "__tc_sz";
    let sy_name = "__tc_sy";
    let coll_t_box = Rc::new(coll_t.clone());
    let all_pat = Pat::Identifier(coll_t_box.clone(), all_name.to_string());
    let new_pat = Pat::Identifier(coll_t_box.clone(), new_name.to_string());
    let pair_pat = Pat::Tuple(
        Rc::new(Type::Tuple(vec![
            Rc::new(coll_t.clone()),
            Rc::new(coll_t.clone()),
        ])),
        vec![all_pat, new_pat.clone()],
    );
    let new_id = Expr::Identifier(coll_t_box.clone(), new_name.into());
    // (px, pz) in newP
    let prev_pat = Pat::Tuple(
        Rc::new(elem_t.clone()),
        vec![
            Pat::Identifier(Rc::new(x_t.clone()), px_name.into()),
            Pat::Identifier(Rc::new(y_t.clone()), pz_name.into()),
        ],
    );
    // (sz, sy) in typed_seed
    let step_pat = Pat::Tuple(
        Rc::new(elem_t.clone()),
        vec![
            Pat::Identifier(Rc::new(x_t.clone()), sz_name.into()),
            Pat::Identifier(Rc::new(y_t.clone()), sy_name.into()),
        ],
    );
    // Where pz = sz
    let pair_int_t = Rc::new(Type::Tuple(vec![
        Rc::new(y_t.clone()),
        Rc::new(x_t.clone()),
    ]));
    let eq_op = match y_t {
        Type::Primitive(PrimitiveType::Int) => BuiltInFunction::IntEq,
        Type::Primitive(PrimitiveType::String) => BuiltInFunction::StringEq,
        Type::Primitive(PrimitiveType::Char) => BuiltInFunction::CharEq,
        Type::Primitive(PrimitiveType::Bool) => BuiltInFunction::BoolEq,
        _ => BuiltInFunction::GEq,
    };
    let eq_fn_t =
        Rc::new(Type::Fn(pair_int_t.clone(), Rc::new(bool_t.clone())));
    let eq_lit = Expr::Literal(eq_fn_t, Val::Fn(eq_op));
    let pz_id = Expr::Identifier(Rc::new(y_t.clone()), pz_name.into());
    let sz_id = Expr::Identifier(Rc::new(x_t.clone()), sz_name.into());
    let eq_arg = Expr::Tuple(pair_int_t, vec![pz_id, sz_id]);
    let where_cond = Expr::Apply(
        Rc::new(bool_t.clone()),
        Box::new(eq_lit),
        Box::new(eq_arg),
        Span::new(""),
    );
    // Yield (px, sy)
    let px_id = Expr::Identifier(Rc::new(x_t.clone()), px_name.into());
    let sy_id = Expr::Identifier(Rc::new(y_t.clone()), sy_name.into());
    let yield_tuple = Expr::Tuple(Rc::new(elem_t.clone()), vec![px_id, sy_id]);
    // Build inner from steps with their environments.
    let scan1_bindings = vec![
        Binding::new(Id::new(px_name, 0), Rc::new(x_t.clone())),
        Binding::new(Id::new(pz_name, 0), Rc::new(y_t.clone())),
    ];
    let scan1_env = StepEnv::new(scan1_bindings.clone(), false, false);
    let scan2_bindings = {
        let mut b = scan1_bindings.clone();
        b.push(Binding::new(Id::new(sz_name, 0), Rc::new(x_t.clone())));
        b.push(Binding::new(Id::new(sy_name, 0), Rc::new(y_t.clone())));
        b
    };
    let scan2_env = StepEnv::new(scan2_bindings.clone(), false, false);
    let where_env = scan2_env.clone();
    let yield_env = StepEnv::new(
        vec![Binding::new(Id::new("current", 0), Rc::new(elem_t.clone()))],
        true,
        false,
    );
    let inner_steps = vec![
        Step::new(
            StepKind::Scan(Box::new(prev_pat), Box::new(new_id), None),
            scan1_env,
        ),
        Step::new(
            StepKind::Scan(
                Box::new(step_pat),
                Box::new(typed_seed.clone()),
                None,
            ),
            scan2_env,
        ),
        Step::new(StepKind::Where(Box::new(where_cond)), where_env),
        Step::new(StepKind::Yield(Box::new(yield_tuple)), yield_env),
    ];
    let inner_from = Expr::From(Rc::new(coll_t.clone()), inner_steps);
    let update_fn_t = Rc::new(Type::Fn(
        Rc::new(Type::Tuple(vec![
            Rc::new(coll_t.clone()),
            Rc::new(coll_t.clone()),
        ])),
        Rc::new(coll_t.clone()),
    ));
    let update_fn = Expr::Fn(
        update_fn_t.clone(),
        vec![Match {
            pat: pair_pat,
            expr: inner_from,
        }],
        Span::new(""),
    );
    // Build `Relational.iterate seed updateFn`.
    let iter_t = Rc::new(Type::Fn(
        Rc::new(coll_t.clone()),
        Rc::new(Type::Fn(
            Rc::new(update_fn_t.as_ref().clone()),
            Rc::new(coll_t.clone()),
        )),
    ));
    let iter_lit =
        Expr::Literal(iter_t, Val::Fn(BuiltInFunction::RelationalIterate));
    let after_seed_t = Rc::new(Type::Fn(
        Rc::new(update_fn_t.as_ref().clone()),
        Rc::new(coll_t.clone()),
    ));
    let with_seed = Expr::Apply(
        after_seed_t,
        Box::new(iter_lit),
        Box::new(typed_seed),
        Span::new(""),
    );
    Expr::Apply(
        Rc::new(coll_t.clone()),
        Box::new(with_seed),
        Box::new(update_fn),
        Span::new(""),
    )
}

/// Phase 5: wraps an iterate expression that produces a bag of
/// `arity`-tuples in a `from (a, b, ...) in iterate where a = b
/// andalso a = c andalso ... yield a` projection so the resulting
/// scan source has element type `t` (matching a single-column
/// pattern `v` in the outer query). Returns `None` if `arity < 2`
/// or `iterate_expr` does not have a `Bag(Tuple(...))` type.
fn wrap_diagonal_projection(
    iterate_expr: Expr,
    elem_t: &Type,
    arity: usize,
) -> Option<Expr> {
    use crate::compile::type_env::Id;
    if arity < 2 {
        return None;
    }
    // The iterate's type is Bag(Tuple([elem_t; arity])).
    let tuple_t = {
        let rc = Rc::new(elem_t.clone());
        Type::Tuple((0..arity).map(|_| rc.clone()).collect())
    };
    let bag_t = Rc::new(Type::Bag(Rc::new(elem_t.clone())));
    // Fresh names for the tuple components.
    let names: Vec<String> =
        (0..arity).map(|i| format!("__dg_{}", i)).collect();
    let scan_pat = Pat::Tuple(
        Rc::new(tuple_t.clone()),
        names
            .iter()
            .map(|n| Pat::Identifier(Rc::new(elem_t.clone()), n.clone()))
            .collect(),
    );
    let bool_t = Type::Primitive(PrimitiveType::Bool);
    let pair_t =
        Type::Tuple(vec![Rc::new(elem_t.clone()), Rc::new(elem_t.clone())]);
    let eq_op = match elem_t {
        Type::Primitive(PrimitiveType::Int) => BuiltInFunction::IntEq,
        Type::Primitive(PrimitiveType::String) => BuiltInFunction::StringEq,
        Type::Primitive(PrimitiveType::Char) => BuiltInFunction::CharEq,
        Type::Primitive(PrimitiveType::Bool) => BuiltInFunction::BoolEq,
        _ => BuiltInFunction::GEq,
    };
    let eq_fn_t =
        Rc::new(Type::Fn(Rc::new(pair_t.clone()), Rc::new(bool_t.clone())));
    // Build conjuncts: __dg_0 = __dg_1 andalso __dg_0 = __dg_2 ...
    let mk_eq = |a: &str, b: &str| -> Expr {
        let lhs = Expr::Identifier(Rc::new(elem_t.clone()), a.to_string());
        let rhs = Expr::Identifier(Rc::new(elem_t.clone()), b.to_string());
        let arg = Expr::Tuple(Rc::new(pair_t.clone()), vec![lhs, rhs]);
        Expr::Apply(
            Rc::new(bool_t.clone()),
            Box::new(Expr::Literal(eq_fn_t.clone(), Val::Fn(eq_op))),
            Box::new(arg),
            Span::new(""),
        )
    };
    let mut eqs: Vec<Expr> = Vec::new();
    for i in 1..arity {
        eqs.push(mk_eq(&names[0], &names[i]));
    }
    let where_cond = and_all(eqs);
    let yield_id = Expr::Identifier(Rc::new(elem_t.clone()), names[0].clone());
    let scan_bindings: Vec<Binding> = names
        .iter()
        .map(|n| Binding::new(Id::new(n, 0), Rc::new(elem_t.clone())))
        .collect();
    let scan_env = StepEnv::new(scan_bindings.clone(), false, false);
    let yield_env = StepEnv::new(
        vec![Binding::new(Id::new("current", 0), Rc::new(elem_t.clone()))],
        true,
        false,
    );
    let inner_steps = vec![
        Step::new(
            StepKind::Scan(Box::new(scan_pat), Box::new(iterate_expr), None),
            scan_env.clone(),
        ),
        Step::new(StepKind::Where(Box::new(where_cond)), scan_env),
        Step::new(StepKind::Yield(Box::new(yield_id)), yield_env),
    ];
    Some(Expr::From(bag_t, inner_steps))
}

/// Replaces the source of `steps[scan_idx]` with `iterate_expr`
/// and drops the conjunct at `cj_idx` from the Where at
/// `where_idx`. If the Where becomes empty, the step is removed.
fn rewrite_steps_for_iterate(
    steps: Vec<Step>,
    where_idx: usize,
    cj_idx: usize,
    scan_idx: usize,
    iterate_expr: Expr,
) -> Vec<Step> {
    use crate::compile::generators::split_conjuncts;
    let mut out: Vec<Step> = Vec::with_capacity(steps.len());
    let mut iterate_opt = Some(iterate_expr);
    for (i, st) in steps.into_iter().enumerate() {
        if i == scan_idx {
            let StepKind::Scan(pat, _src, cond) = st.kind else {
                out.push(st);
                continue;
            };
            let iter = iterate_opt.take().expect("scan_idx visited once");
            out.push(Step::new(
                StepKind::Scan(pat, Box::new(iter), cond),
                st.env,
            ));
        } else if i == where_idx {
            let StepKind::Where(cond) = st.kind else {
                out.push(st);
                continue;
            };
            let conjuncts = split_conjuncts(&cond);
            let kept: Vec<Expr> = conjuncts
                .into_iter()
                .enumerate()
                .filter(|(j, _)| *j != cj_idx)
                .map(|(_, c)| c)
                .collect();
            if kept.is_empty() {
                continue; // drop the Where step
            }
            let mut iter = kept.into_iter();
            let first = iter.next().unwrap();
            let new_cond = iter.fold(first, |a, b| and_all(vec![a, b]));
            out.push(Step::new(StepKind::Where(Box::new(new_cond)), st.env));
        } else {
            out.push(st);
        }
    }
    out
}

/// Like [`rewrite_steps_for_iterate`], but for the case where the
/// recursive call's argument is a tuple of *distinct* unbounded
/// variables (`f (x, y, …)`). Replaces the first matched scan with
/// a tuple-pattern scan that destructures each iterate element back
/// into the original variables, drops the remaining matched scans,
/// and removes the consumed conjunct from the surrounding `where`.
/// An implicit `distinct` is appended after the tuple-pat scan to
/// dedup the join-projected results — the recursive case typically
/// has intermediate variables (e.g. `z` in `path (x, z) andalso edge
/// (z, y)`) that are projected away.
fn rewrite_steps_for_iterate_tuple(
    steps: Vec<Step>,
    where_idx: usize,
    cj_idx: usize,
    scan_indices: &[usize],
    components: &[(String, Type)],
    tuple_type: &Type,
    iterate_expr: Expr,
) -> Vec<Step> {
    use crate::compile::generators::split_conjuncts;
    let primary = scan_indices[0];
    let drop_set: HashSet<usize> = scan_indices[1..].iter().copied().collect();
    // Use the env of the LAST sibling scan as the tuple-pat scan's
    // env — that's the one that has bindings for *all* the
    // components. Reusing the primary's env would only carry the
    // first component (x), losing y, …, in subsequent steps.
    let last_scan_idx = *scan_indices.iter().max().unwrap();
    let merged_env = steps[last_scan_idx].env.clone();
    let mut out: Vec<Step> = Vec::with_capacity(steps.len());
    let mut iterate_opt = Some(iterate_expr);
    for (i, st) in steps.into_iter().enumerate() {
        if i == primary {
            let StepKind::Scan(_, _, cond) = st.kind else {
                out.push(st);
                continue;
            };
            // Tuple-pat (x, y, …) destructures each iterate element
            // into its sibling bindings.
            let sub_pats: Vec<Pat> = components
                .iter()
                .map(|(n, t)| Pat::Identifier(Rc::new(t.clone()), n.clone()))
                .collect();
            let new_pat = Pat::Tuple(Rc::new(tuple_type.clone()), sub_pats);
            let iter = iterate_opt.take().expect("primary visited once");
            out.push(Step::new(
                StepKind::Scan(Box::new(new_pat), Box::new(iter), cond),
                merged_env.clone(),
            ));
            // Implicit distinct — same step env, since the binding
            // shape is unchanged.
            out.push(Step::new(StepKind::Distinct, merged_env.clone()));
        } else if drop_set.contains(&i) {
            // Drop sibling scans; their bindings were unioned into
            // the primary scan's tuple-pat above.
            continue;
        } else if i == where_idx {
            let StepKind::Where(cond) = st.kind else {
                out.push(st);
                continue;
            };
            let conjuncts = split_conjuncts(&cond);
            let kept: Vec<Expr> = conjuncts
                .into_iter()
                .enumerate()
                .filter(|(j, _)| *j != cj_idx)
                .map(|(_, c)| c)
                .collect();
            if kept.is_empty() {
                continue;
            }
            let mut iter = kept.into_iter();
            let first = iter.next().unwrap();
            let new_cond = iter.fold(first, |a, b| and_all(vec![a, b]));
            out.push(Step::new(StepKind::Where(Box::new(new_cond)), st.env));
        } else {
            out.push(st);
        }
    }
    out
}

/// Destructures `Scan(Identifier(Tuple(...), name), Extent(_),
/// None)` into a tuple-pattern scan when `name` is referenced via
/// a function call whose parameter is a tuple. Lets
/// `inline_tuple_fn_calls_in_where` handle `f p` (where `p` has
/// tuple type) by exposing the tuple components as bindings.
///
/// Adds an explicit `Yield` of the tuple to preserve the
/// original tuple-typed result; without this, the implicit
/// from-yield (a record over all bindings) would change the
/// result type.
fn destructure_tuple_extents_for_fn_calls(
    steps: Vec<Step>,
    fn_env: &FnEnv,
) -> Vec<Step> {
    use crate::compile::generators::split_conjuncts;
    use crate::compile::replacer::substitute;
    if fn_env.is_empty() {
        return steps;
    }
    // Find tuple-typed scan-extent bindings.
    let mut targets: Vec<(usize, String, Vec<Rc<Type>>, Span)> = Vec::new();
    for (i, s) in steps.iter().enumerate() {
        let StepKind::Scan(p, source, cond) = &s.kind else {
            continue;
        };
        if cond.is_some() {
            continue;
        }
        let Expr::Extent(_, span) = source.as_ref() else {
            continue;
        };
        let Pat::Identifier(t, name) = p.as_ref() else {
            continue;
        };
        let Type::Tuple(elems) = t.as_ref() else {
            continue;
        };
        targets.push((i, name.clone(), elems.clone(), span.clone()));
    }
    if targets.is_empty() {
        return steps;
    }
    // Keep only targets that are referenced as `f var` for a
    // tuple-param `f` somewhere in subsequent Where conjuncts.
    let needs_destructure = |name: &str| -> bool {
        for s in &steps {
            let StepKind::Where(cond) = &s.kind else {
                continue;
            };
            for c in split_conjuncts(cond) {
                if where_has_tuple_fn_call_on(&c, name, fn_env) {
                    return true;
                }
            }
        }
        false
    };
    let targets: Vec<_> = targets
        .into_iter()
        .filter(|(_, name, _, _)| needs_destructure(name))
        .collect();
    if targets.is_empty() {
        return steps;
    }
    // For each target, build the substitution and per-component
    // ScanExtent steps. Per-component extents (rather than a
    // tuple-pat over the original Extent) let
    // `decompose_tuple_elems` invert each elem-conjunct
    // independently against the corresponding component extent.
    use crate::compile::type_env::Id;
    let mut subst_map: HashMap<String, Expr> = HashMap::new();
    // For each destructured target name, the new bindings that
    // replace the original `p` binding in subsequent step envs.
    let mut binding_subst: HashMap<String, Vec<Binding>> = HashMap::new();
    let mut replacement_kinds: HashMap<usize, Vec<StepKind>> = HashMap::new();
    let mut tuple_yields: Vec<Expr> = Vec::new();
    for (idx, name, elems, span) in &targets {
        let mut new_kinds: Vec<StepKind> = Vec::with_capacity(elems.len());
        let mut new_bindings: Vec<Binding> = Vec::with_capacity(elems.len());
        for (i, t) in elems.iter().enumerate() {
            let fresh_name = format!("{}__{}", name, i + 1);
            let pat = Pat::Identifier((*t).clone(), fresh_name.clone());
            // Carry the original `from p` span onto each
            // destructured component's Extent so a downstream
            // "pattern not grounded" error points at the user's
            // source location, not an empty span.
            let source = Expr::Extent((*t).clone(), span.clone());
            new_kinds.push(StepKind::Scan(
                Box::new(pat),
                Box::new(source),
                None,
            ));
            new_bindings
                .push(Binding::new(Id::new(&fresh_name, 0), (*t).clone()));
        }
        let tuple_t = Rc::new(Type::Tuple(elems.clone()));
        let tuple_expr_items: Vec<Expr> = elems
            .iter()
            .enumerate()
            .map(|(i, t)| {
                Expr::Identifier((*t).clone(), format!("{}__{}", name, i + 1))
            })
            .collect();
        let tuple_expr = Expr::Tuple(tuple_t, tuple_expr_items);
        subst_map.insert(name.clone(), tuple_expr.clone());
        binding_subst.insert(name.clone(), new_bindings);
        replacement_kinds.insert(*idx, new_kinds);
        tuple_yields.push(tuple_expr);
        let _ = idx;
    }
    // Replace `p` binding with `p__1, p__2, ...` in a StepEnv.
    let rewrite_env = |env: &StepEnv| -> StepEnv {
        let mut new_bs: Vec<Binding> = Vec::new();
        for b in &env.bindings {
            if let Some(repl) = binding_subst.get(&b.id.name) {
                new_bs.extend(repl.iter().cloned());
            } else {
                new_bs.push(b.clone());
            }
        }
        // `atom` is true only when there's exactly one binding;
        // destructuring breaks that invariant, so clear it.
        let atom = env.atom && new_bs.len() == 1;
        StepEnv::new(new_bs, atom, env.ordered)
    };
    // Walk steps applying replacements + substitutions. As we go,
    // accumulate bindings introduced by the (replacement) scans so
    // subsequent steps see a consistent, post-destructure StepEnv.
    let mut out: Vec<Step> = Vec::with_capacity(steps.len());
    let had_yield = steps.iter().any(|s| matches!(s.kind, StepKind::Yield(_)));
    let outer_is_exists =
        matches!(steps.last().map(|s| &s.kind), Some(StepKind::Exists));
    let mut acc_bindings: Vec<Binding> = Vec::new();
    let last_orig_ordered = steps.last().is_none_or(|s| s.env.ordered);
    for (i, step) in steps.into_iter().enumerate() {
        if let Some(repl_kinds) = replacement_kinds.remove(&i) {
            // Find the destructured name's replacement bindings.
            let target = targets.iter().find(|(j, _, _, _)| *j == i).unwrap();
            let new_bs = binding_subst.get(&target.1).unwrap();
            // Drop the original `p` binding from acc_bindings (in
            // case it was already introduced by an earlier scan;
            // here it's the binding this step introduces).
            acc_bindings.retain(|b| b.id.name != target.1);
            // Each replacement Scan adds one component binding.
            for (kind, b) in repl_kinds.into_iter().zip(new_bs.iter()) {
                acc_bindings.push(b.clone());
                out.push(Step::new(
                    kind,
                    StepEnv::new(acc_bindings.clone(), false, step.env.ordered),
                ));
            }
            continue;
        }
        let new_kind = match step.kind {
            StepKind::Where(cond) => {
                StepKind::Where(Box::new(substitute(&cond, &subst_map)))
            }
            StepKind::Yield(e) => {
                StepKind::Yield(Box::new(substitute(&e, &subst_map)))
            }
            StepKind::Order(e) => {
                StepKind::Order(Box::new(substitute(&e, &subst_map)))
            }
            StepKind::Group(k, agg) => StepKind::Group(
                Box::new(substitute(&k, &subst_map)),
                agg.map(|a| Box::new(substitute(&a, &subst_map))),
            ),
            StepKind::Compute(e) => {
                StepKind::Compute(Box::new(substitute(&e, &subst_map)))
            }
            other => other,
        };
        out.push(Step::new(new_kind, rewrite_env(&step.env)));
    }
    // Add an explicit Yield + Distinct of the destructured tuple
    // if the original had no yield and isn't an exists/forall —
    // preserves the original tuple result type and dedups
    // duplicates introduced by inner-exists lifting.
    if !had_yield && !outer_is_exists && tuple_yields.len() == 1 {
        let yield_expr = tuple_yields.into_iter().next().unwrap();
        // After Yield, the from carries a single `current` binding
        // of the yielded tuple type (atom = true).
        let yield_t = yield_expr.type_();
        let yield_env = StepEnv::new(
            vec![Binding::new(Id::new("current", 0), yield_t.clone())],
            true,
            last_orig_ordered,
        );
        out.push(Step::new(
            StepKind::Yield(Box::new(yield_expr)),
            yield_env.clone(),
        ));
        out.push(Step::new(StepKind::Distinct, yield_env));
    }
    out
}

/// True if `expr` contains an application of a function in
/// `fn_env` (with a tuple parameter pattern) directly to the
/// identifier `name`.
fn where_has_tuple_fn_call_on(expr: &Expr, name: &str, fn_env: &FnEnv) -> bool {
    if let Expr::Apply(_, f, arg, _) = expr
        && let Expr::Identifier(_, fn_name) = f.as_ref()
        && let Some((Pat::Tuple(_, _), _)) = fn_env.get(fn_name)
        && let Expr::Identifier(_, n) = arg.as_ref()
        && n == name
    {
        return true;
    }
    // Walk children. Only care about Apply / nested boolean
    // ops; doing a generic walk is fine but wasteful, so just
    // check the cases that show up in Where conjuncts.
    match expr {
        Expr::Apply(_, f, a, _) => {
            where_has_tuple_fn_call_on(f, name, fn_env)
                || where_has_tuple_fn_call_on(a, name, fn_env)
        }
        Expr::Tuple(_, items) => items
            .iter()
            .any(|e| where_has_tuple_fn_call_on(e, name, fn_env)),
        _ => false,
    }
}

/// Detects an inner Scan that was specialized into a "point"
/// generator referencing only outer-scope names (e.g.
/// `Scan(y, [x])` where `x` is bound outside this exists). Such
/// scans can't be promoted as-is — when lifted into the parent,
/// they execute before the outer name is grounded.
///
/// Returns `Some((scan_extent, equality_where))` to convert the
/// scan back to a `ScanExtent` + equality `Where`. The post-lift
/// generator pipeline can then re-merge these with the outer
/// scope's grounding scans. Returns `None` if the scan doesn't
/// match this shape (it'll be promoted unchanged).
fn unground_outer_point_scan(
    pat: &Pat,
    source: &Expr,
    cond: Option<&Expr>,
    inner_bound: &HashSet<String>,
) -> Option<(StepKind, Expr)> {
    if cond.is_some() {
        return None;
    }
    let Pat::Identifier(pat_t, pat_name) = pat else {
        return None;
    };
    let Expr::List(_, items) = source else {
        return None;
    };
    if items.len() != 1 {
        return None;
    }
    let item = &items[0];
    use crate::compile::free_finder::free_names_in;
    let item_free = free_names_in(item);
    if item_free.is_empty() || item_free.iter().any(|n| inner_bound.contains(n))
    {
        return None;
    }
    let extent = Expr::Extent(pat_t.clone(), Span::new(""));
    let extent_step =
        StepKind::Scan(Box::new(pat.clone()), Box::new(extent), None);
    let bool_t = Rc::new(Type::Primitive(PrimitiveType::Bool));
    let pair_t = Rc::new(Type::Tuple(vec![
        Rc::new((**pat_t).clone()),
        Rc::new((**pat_t).clone()),
    ]));
    let eq_op = match pat_t.as_ref() {
        Type::Primitive(PrimitiveType::Int) => BuiltInFunction::IntEq,
        Type::Primitive(PrimitiveType::Real) => BuiltInFunction::RealEq,
        Type::Primitive(PrimitiveType::String) => BuiltInFunction::StringEq,
        Type::Primitive(PrimitiveType::Char) => BuiltInFunction::CharEq,
        Type::Primitive(PrimitiveType::Bool) => BuiltInFunction::BoolEq,
        _ => BuiltInFunction::GEq,
    };
    let fn_t = Rc::new(Type::Fn(pair_t.clone(), bool_t.clone()));
    let fn_lit = Expr::Literal(fn_t, Val::Fn(eq_op));
    let arg = Expr::Tuple(
        pair_t,
        vec![
            Expr::Identifier(pat_t.clone(), pat_name.clone()),
            item.clone(),
        ],
    );
    let eq =
        Expr::Apply(bool_t, Box::new(fn_lit), Box::new(arg), Span::new(""));
    Some((extent_step, eq))
}

/// Lifts the inner Scans and Where conjuncts of any Where
/// conjunct that is itself a nested `exists`-like expression
/// into the outer steps. Equivalence:
///
///   exists x where (exists y where P(x, y))
///     ≡ exists x, y where P(x, y)
///
///   from x where (exists y where P(x, y))
///     ≡ from x, y where P(x, y) yield x distinct
///
/// The lift lets later passes (`decompose_tuple_elems`, the
/// per-pattern generator pipeline) see the inner constraints
/// alongside the outer scans, so e.g. `(x, y) elem coll` can be
/// merged into a single Scan(Tuple([x, y]), coll) that grounds
/// both x and y.
///
/// For `from` outers we synthesise a `yield (...)` over the
/// original outer-bound names plus a `distinct` to preserve the
/// original cardinality (one row per outer-bound combination,
/// not per inner-iteration).
fn lift_nested_exists_in_where(steps: Vec<Step>) -> Vec<Step> {
    use crate::compile::generators::split_conjuncts;

    // First pass: find conjuncts that are inner exists, collect
    // their scans + conjuncts, and remember which to drop.
    let mut new_inner_scans: Vec<Step> = Vec::new();
    let mut new_inner_conjuncts: Vec<Expr> = Vec::new();
    let mut where_drops: HashMap<usize, HashSet<usize>> = HashMap::new();
    for (wi, step) in steps.iter().enumerate() {
        let StepKind::Where(cond) = &step.kind else {
            continue;
        };
        let conjuncts = split_conjuncts(cond);
        for (ci, c) in conjuncts.iter().enumerate() {
            // Match both `Expr::Exists` and `Expr::From` whose
            // last step is `Exists` — the resolver represents
            // a parenthesised `(exists ... where ...)` as the
            // latter, where the trailing Exists turns a bag
            // into a bool.
            let inner_steps = match c {
                Expr::Exists(_, s) => s,
                Expr::From(_, s)
                    if matches!(
                        s.last().map(|s| &s.kind),
                        Some(StepKind::Exists)
                    ) =>
                {
                    s
                }
                _ => continue,
            };
            if !matches!(
                inner_steps.last().map(|s| &s.kind),
                Some(StepKind::Exists)
            ) {
                continue;
            }
            // Names bound by inner scans (everything we promote
            // is from this scope). A Scan whose source references
            // names *outside* this set was effectively a "point"
            // generator that depends on outer state — when lifted
            // out, it would be evaluated before its outer
            // dependency is grounded. Such scans are converted
            // back to `ScanExtent` + equality `Where`, letting the
            // post-lift generator pipeline re-merge them in the
            // correct order.
            let mut inner_bound: HashSet<String> = HashSet::new();
            for s in &inner_steps[..inner_steps.len() - 1] {
                if let StepKind::Scan(p, _, _) = &s.kind {
                    let mut bs: Vec<Binding> = Vec::new();
                    Binding::collect_bindings(p, &mut bs);
                    for b in bs {
                        inner_bound.insert(b.id.name);
                    }
                }
            }

            // Promote inner Scans (including ScanExtents) and
            // Where conjuncts. Skip yields/groups/orders — those
            // wouldn't show up in a plain exists query but we
            // ignore them defensively.
            let mut ok = true;
            let mut promoted_scans: Vec<Step> = Vec::new();
            let mut promoted_conjuncts: Vec<Expr> = Vec::new();
            for s in &inner_steps[..inner_steps.len() - 1] {
                match &s.kind {
                    StepKind::Scan(p, source, cond) => {
                        if let Some((scan, eq)) = unground_outer_point_scan(
                            p,
                            source,
                            cond.as_deref(),
                            &inner_bound,
                        ) {
                            promoted_scans.push(Step::new(scan, s.env.clone()));
                            promoted_conjuncts.push(eq);
                        } else {
                            promoted_scans.push(s.clone());
                        }
                    }
                    StepKind::Where(ic) => {
                        promoted_conjuncts.extend(split_conjuncts(ic));
                    }
                    _ => {
                        ok = false;
                        break;
                    }
                }
            }
            if !ok {
                continue;
            }
            new_inner_scans.extend(promoted_scans);
            new_inner_conjuncts.extend(promoted_conjuncts);
            where_drops.entry(wi).or_default().insert(ci);
        }
    }

    if new_inner_scans.is_empty() && new_inner_conjuncts.is_empty() {
        return steps;
    }

    let outer_is_exists =
        matches!(steps.last().map(|s| &s.kind), Some(StepKind::Exists));

    // For `from` outers, capture the bindings emitted by the
    // outer's pre-lift Scans so we can yield only those, then
    // distinct to preserve cardinality.
    let outer_bindings: Vec<Binding> = if outer_is_exists {
        Vec::new()
    } else {
        let mut bs: Vec<Binding> = Vec::new();
        for s in &steps {
            if let StepKind::Scan(p, _, _) = &s.kind {
                Binding::collect_bindings(p, &mut bs);
            }
        }
        bs
    };

    // Pick a step env that represents the post-lift scope. For
    // exists/forall the trailing-step env is fine; for `from` we
    // just reuse the last step's env as a starting point.
    let trailing_env = steps.last().unwrap().env.clone();

    // Last position of a Where that had a conjunct lifted. For
    // from-outers, we splice lifted scans + synth yield + distinct
    // *immediately after* that Where, so user-supplied trailing
    // steps (yield, distinct, order, …) operate on the post-lift
    // {outer-bindings-only} record stream.
    let last_lift_where_pos: Option<usize> = where_drops.keys().copied().max();

    // Skip the synthetic yield+distinct if the outer steps
    // already supply a Yield (e.g. `destructure_tuple_extents`
    // added one to preserve the original tuple result type).
    let already_has_yield =
        steps.iter().any(|s| matches!(s.kind, StepKind::Yield(_)));

    // Build the synthetic yield + distinct (for from-outer only).
    let build_yield_distinct = |new_inner_scans: &mut Vec<Step>,
                                new_inner_conjuncts: &mut Vec<Expr>|
     -> Vec<Step> {
        let mut buf: Vec<Step> = Vec::new();
        buf.append(new_inner_scans);
        if !new_inner_conjuncts.is_empty() {
            let cond = and_all(std::mem::take(new_inner_conjuncts));
            buf.push(Step::new(
                StepKind::Where(Box::new(cond)),
                trailing_env.clone(),
            ));
        }
        if !outer_bindings.is_empty() && !already_has_yield {
            let yield_expr = if outer_bindings.len() == 1 {
                Expr::Identifier(
                    outer_bindings[0].type_.clone(),
                    outer_bindings[0].id.name.clone(),
                )
            } else {
                use std::collections::BTreeMap;
                let fields: BTreeMap<Label, Rc<Type>> = outer_bindings
                    .iter()
                    .map(|b| {
                        (Label::String(b.id.name.clone()), b.type_.clone())
                    })
                    .collect();
                let rec_t = Rc::new(Type::Record(false, fields));
                let mut sorted = outer_bindings.clone();
                sorted.sort_by(|a, b| a.id.name.cmp(&b.id.name));
                let items: Vec<Expr> = sorted
                    .iter()
                    .map(|b| {
                        Expr::Identifier(b.type_.clone(), b.id.name.clone())
                    })
                    .collect();
                Expr::Tuple(rec_t, items)
            };
            buf.push(Step::new(
                StepKind::Yield(Box::new(yield_expr)),
                trailing_env.clone(),
            ));
            buf.push(Step::new(StepKind::Distinct, trailing_env.clone()));
        }
        buf
    };

    // Rebuild.
    let mut out: Vec<Step> = Vec::with_capacity(steps.len());
    let mut inserted_lifted = false;
    let n_steps = steps.len();
    for (i, step) in steps.into_iter().enumerate() {
        // Drop matched conjuncts from the Where that contained them.
        if let Some(drops) = where_drops.get(&i)
            && let StepKind::Where(cond) = &step.kind
        {
            let conjuncts = split_conjuncts(cond);
            let kept: Vec<Expr> = conjuncts
                .into_iter()
                .enumerate()
                .filter(|(ci, _)| !drops.contains(ci))
                .map(|(_, c)| c)
                .collect();
            if !kept.is_empty() {
                out.push(Step::new(
                    StepKind::Where(Box::new(and_all(kept))),
                    step.env.clone(),
                ));
            }
            // For from-outer, splice lifted block right here (the
            // last Where to lose a conjunct gets the splice; any
            // earlier ones are absorbed into the same
            // `new_inner_*` accumulators).
            if !outer_is_exists
                && !inserted_lifted
                && Some(i) == last_lift_where_pos
            {
                let block = build_yield_distinct(
                    &mut new_inner_scans,
                    &mut new_inner_conjuncts,
                );
                out.extend(block);
                inserted_lifted = true;
            }
            continue;
        }
        // For exists/forall, insert lifted steps just before the
        // trailing Exists.
        if outer_is_exists
            && matches!(step.kind, StepKind::Exists)
            && !inserted_lifted
        {
            for s in new_inner_scans.drain(..) {
                out.push(s);
            }
            if !new_inner_conjuncts.is_empty() {
                let cond = and_all(std::mem::take(&mut new_inner_conjuncts));
                out.push(Step::new(
                    StepKind::Where(Box::new(cond)),
                    trailing_env.clone(),
                ));
            }
            inserted_lifted = true;
        }
        out.push(step);
    }
    let _ = n_steps; // (kept in case we need bounds checks later)

    // Fallback: if we never spliced (e.g. the lifted Where had
    // no `kept` conjuncts, so it was suppressed), append at the
    // end. Preserves the original behaviour for the common case.
    if !outer_is_exists && !inserted_lifted {
        let block = build_yield_distinct(
            &mut new_inner_scans,
            &mut new_inner_conjuncts,
        );
        out.extend(block);
    }
    out
}

/// Beta-reduces single-arm `case (e1, …, en) of (a1, …, an) =>
/// body` to `body[ai := ei]` in Where conjuncts. Lets
/// `decompose_tuple_elems` see e.g. `(y, x) elem coll` even when
/// the user wrote `case (y, x) of (a, b) => (a, b) elem coll`.
fn inline_tuple_case_in_where(steps: Vec<Step>) -> Vec<Step> {
    use crate::compile::generators::split_conjuncts;
    use crate::compile::replacer::substitute;
    let try_inline = |c: &Expr| -> Expr {
        let Expr::Case(_, subject, arms, _) = c else {
            return c.clone();
        };
        if arms.len() != 1 {
            return c.clone();
        }
        let arm = &arms[0];
        let Pat::Tuple(_, sub_pats) = &arm.pat else {
            return c.clone();
        };
        let Expr::Tuple(_, arg_elems) = subject.as_ref() else {
            return c.clone();
        };
        if sub_pats.len() != arg_elems.len() {
            return c.clone();
        }
        let mut subst_map: HashMap<String, Expr> = HashMap::new();
        for (sp, ae) in sub_pats.iter().zip(arg_elems.iter()) {
            if let Pat::Identifier(_, n) = sp {
                subst_map.insert(n.clone(), ae.clone());
            } else {
                return c.clone();
            }
        }
        substitute(&arm.expr, &subst_map)
    };
    steps
        .into_iter()
        .map(|s| match s.kind {
            StepKind::Where(cond) => {
                let conjuncts: Vec<Expr> = split_conjuncts(&cond)
                    .into_iter()
                    .map(|c| try_inline(&c))
                    .collect();
                let new_cond = if conjuncts.is_empty() {
                    *cond
                } else {
                    let mut iter = conjuncts.into_iter();
                    let first = iter.next().unwrap();
                    iter.fold(first, |a, b| and_all(vec![a, b]))
                };
                Step::new(StepKind::Where(Box::new(new_cond)), s.env)
            }
            other => Step::new(other, s.env),
        })
        .collect()
}

/// Drops `ScanExtent` steps whose pattern name doesn't appear in
/// any of the from's other steps (whose result is `bool` —
/// `exists` / `forall` — so unconstrained, unread bindings have
/// no effect on the answer). Only the leaf-pattern case (a
/// single `Pat::Identifier`) is pruned; compound patterns might
/// have non-identifier sub-patterns we don't analyse here.
fn prune_unused_scan_extents(steps: Vec<Step>) -> Vec<Step> {
    use crate::compile::free_finder::free_names_in;
    // Collect names referenced by every non-(self-)scan step.
    let mut referenced: HashSet<String> = HashSet::new();
    for (i, s) in steps.iter().enumerate() {
        match &s.kind {
            StepKind::Scan(p, source, cond) => {
                // A scan's source/condition can reference earlier
                // patterns; we count those references. The pattern
                // bound by *this* scan is excluded below — we want
                // self-references not to count.
                let bound_here: HashSet<String> = {
                    let mut bs: Vec<Binding> = Vec::new();
                    Binding::collect_bindings(p, &mut bs);
                    bs.into_iter().map(|b| b.id.name).collect()
                };
                let _ = i;
                for n in free_names_in(source).into_iter() {
                    if !bound_here.contains(&n) {
                        referenced.insert(n);
                    }
                }
                if let Some(c) = cond {
                    for n in free_names_in(c).into_iter() {
                        if !bound_here.contains(&n) {
                            referenced.insert(n);
                        }
                    }
                }
            }
            StepKind::Where(c) => {
                for n in free_names_in(c) {
                    referenced.insert(n);
                }
            }
            StepKind::Yield(e) | StepKind::Order(e) | StepKind::Compute(e) => {
                for n in free_names_in(e) {
                    referenced.insert(n);
                }
            }
            StepKind::Group(k, a) => {
                for n in free_names_in(k) {
                    referenced.insert(n);
                }
                if let Some(agg) = a {
                    for n in free_names_in(agg) {
                        referenced.insert(n);
                    }
                }
            }
            _ => {}
        }
    }

    // Drop any `ScanExtent(name)` whose `name` is unreferenced.
    steps
        .into_iter()
        .filter(|s| match &s.kind {
            StepKind::Scan(p, source, _)
                if matches!(source.as_ref(), Expr::Extent(_, _)) =>
            {
                if let Pat::Identifier(_, n) = p.as_ref() {
                    referenced.contains(n)
                } else {
                    true
                }
            }
            _ => true,
        })
        .collect()
}

/// Reorders steps so every `Where`'s free names are bound by
/// an earlier `Scan`. `decompose_tuple_elems` may drop an
/// extent Scan and insert the merged Scan further down the
/// list, leaving a `Where` step that referenced the dropped
/// name out of order. This pass walks left-to-right, holds
/// back any `Where` whose names aren't yet bound, and emits
/// it once a later `Scan` supplies the missing binding.
///
/// `Distinct`, `Order`, `Take`, `Skip` are "binding-preserving"
/// (don't change which names are in scope) — held Wheres can
/// pass through them and still be emitted later. `Yield` and
/// `Group` re-project bindings, so any held Where must be
/// emitted before them (best-effort; an unbound Where is left
/// in its original position to surface as a runtime error).
fn reorder_wheres_after_scans(steps: Vec<Step>) -> Vec<Step> {
    use crate::compile::free_finder::free_names_in;

    let mut bound: HashSet<String> = HashSet::new();
    let mut held: Vec<(Box<Expr>, StepEnv)> = Vec::new();
    let mut out: Vec<Step> = Vec::with_capacity(steps.len());

    fn try_release(
        bound: &HashSet<String>,
        held: &mut Vec<(Box<Expr>, StepEnv)>,
        out: &mut Vec<Step>,
    ) {
        let mut i = 0;
        while i < held.len() {
            let free = free_names_in(&held[i].0);
            if free.iter().all(|n| bound.contains(n)) {
                let (cond, env) = held.remove(i);
                out.push(Step::new(StepKind::Where(cond), env));
            } else {
                i += 1;
            }
        }
    }

    for step in steps {
        match step.kind {
            StepKind::Scan(p, source, cond) => {
                let mut bs: Vec<Binding> = Vec::new();
                Binding::collect_bindings(&p, &mut bs);
                for b in bs {
                    bound.insert(b.id.name);
                }
                out.push(Step::new(StepKind::Scan(p, source, cond), step.env));
                try_release(&bound, &mut held, &mut out);
            }
            StepKind::Where(cond) => {
                let free = free_names_in(&cond);
                if free.iter().all(|n| bound.contains(n)) {
                    out.push(Step::new(StepKind::Where(cond), step.env));
                } else {
                    held.push((cond, step.env));
                }
            }
            StepKind::Distinct
            | StepKind::Order(_)
            | StepKind::Take(_)
            | StepKind::Skip(_) => {
                // Binding-preserving — held Wheres can wait past
                // these and still be released by a later Scan.
                out.push(Step::new(step.kind, step.env));
            }
            other => {
                // Yield / Group / Compute / Exists / etc. change
                // or terminate the binding scope. Flush any
                // still-held Wheres before emitting this step.
                for (cond, env) in held.drain(..) {
                    out.push(Step::new(StepKind::Where(cond), env));
                }
                out.push(Step::new(other, step.env));
            }
        }
    }
    for (cond, env) in held {
        out.push(Step::new(StepKind::Where(cond), env));
    }
    out
}

/// Iteratively merges tuple-elem conjuncts until a fixed point.
/// Each pass turns a `Scan(name, Extent)` matched in a tuple-
/// elem into a regular Scan that binds `name` from the elem
/// collection. After the merge, that name is "already bound"
/// in subsequent passes, so e.g. `(y, z) elem coll` whose `y`
/// was just merged becomes matchable in pass 2 as an
/// already-bound + extent pair.
fn decompose_tuple_elems(steps: Vec<Step>) -> Vec<Step> {
    let mut current = steps;
    loop {
        let before = step_signature(&current);
        let after = decompose_tuple_elems_once(current);
        let after_sig = step_signature(&after);
        current = after;
        if before == after_sig {
            return current;
        }
    }
}

/// Coarse fingerprint of the step list used to detect fixed
/// point in the iterative decompose. Captures step kinds and
/// the names introduced by each Scan; ignores expression
/// equality.
fn step_signature(steps: &[Step]) -> Vec<String> {
    steps
        .iter()
        .map(|s| match &s.kind {
            StepKind::Scan(p, _, _) => {
                let mut bs: Vec<Binding> = Vec::new();
                Binding::collect_bindings(p, &mut bs);
                let names: Vec<String> =
                    bs.into_iter().map(|b| b.id.name).collect();
                format!("Scan({})", names.join(","))
            }
            StepKind::Where(_) => "Where".into(),
            StepKind::Yield(_) => "Yield".into(),
            StepKind::Order(_) => "Order".into(),
            StepKind::Group(_, _) => "Group".into(),
            StepKind::Compute(_) => "Compute".into(),
            StepKind::Distinct => "Distinct".into(),
            StepKind::Exists => "Exists".into(),
            other => format!("{:?}", other),
        })
        .collect()
}

fn decompose_tuple_elems_once(steps: Vec<Step>) -> Vec<Step> {
    use HashSet;

    // Gather all ScanExtent positions and the names they bind.
    let mut extent_index: HashMap<String, usize> = HashMap::new();
    // Names bound by *any* prior scan in this from (regular or
    // unbounded), with their step position. Tuple-LHS components
    // that are bound here can be matched via a fresh-named
    // scan-binding plus an equality filter, even though they
    // don't have their own ScanExtent.
    let mut already_bound: HashMap<String, usize> = HashMap::new();
    for (i, step) in steps.iter().enumerate() {
        if let StepKind::Scan(p, source, _) = &step.kind {
            if matches!(source.as_ref(), Expr::Extent(_, _))
                && let Pat::Identifier(_, n) = p.as_ref()
            {
                extent_index.insert(n.clone(), i);
            } else {
                let mut bs: Vec<Binding> = Vec::new();
                Binding::collect_bindings(p, &mut bs);
                for b in bs {
                    already_bound.insert(b.id.name, i);
                }
            }
        }
    }
    if extent_index.is_empty() {
        return steps;
    }
    // Counter for synthesising fresh names for already-bound
    // tuple components.
    let mut fresh_counter: usize = 0;

    // For each where-step, decompose its conjuncts and identify
    // which ones are tuple-elem candidates we can merge.
    //
    // (positions_to_drop, replacement_at_position, conjunct_index_to_drop)
    let mut drop_positions: HashSet<usize> = HashSet::new();
    let mut replacement_at: HashMap<usize, Step> = HashMap::new();
    // Steps to insert immediately *after* a given position (used
    // when the merged Scan's last reference is an already-bound
    // name, so the existing Scan must be kept).
    let mut insert_after: HashMap<usize, Step> = HashMap::new();
    // Per Where step: which conjunct indices to drop.
    let mut where_drops: HashMap<usize, HashSet<usize>> = HashMap::new();

    for (wi, step) in steps.iter().enumerate() {
        let StepKind::Where(cond) = &step.kind else {
            continue;
        };
        let conjuncts = split_conjuncts(cond);
        for (ci, c) in conjuncts.iter().enumerate() {
            // Look for `Apply(ListElem, Tuple(_, [tuple_lhs, coll]))`
            // where `tuple_lhs` is a Tuple of Identifiers, all of
            // which are ScanExtent-bound and not yet claimed.
            let Expr::Apply(_, f, arg, _) = c else {
                continue;
            };
            let Expr::Literal(_, Val::Fn(BuiltInFunction::ListElem)) =
                f.as_ref()
            else {
                continue;
            };
            let Expr::Tuple(_, args) = arg.as_ref() else {
                continue;
            };
            if args.len() != 2 {
                continue;
            }
            let Expr::Tuple(_tuple_t, ids) = &args[0] else {
                continue;
            };
            let coll = &args[1];

            // Each component must be either:
            //   * an Identifier naming a not-yet-claimed ScanExtent
            //     (becomes a Pat::Identifier in the merged scan), or
            //   * a Literal (becomes a Pat::Literal — narrows the
            //     scan to records whose field equals that constant).
            // Anything else (a free expression, a non-extent
            // identifier, etc.) makes us skip this conjunct and let
            // the per-pattern generator pipeline handle it.
            let mut named_pats: Vec<Pat> = Vec::with_capacity(ids.len());
            // Positions of ScanExtents we'll drop and replace; the
            // merged Scan sits at the *last* of these.
            let mut extent_positions: Vec<usize> =
                Vec::with_capacity(ids.len());
            // Positions that constrain *where* the merged Scan can
            // be inserted: extent positions (above) plus positions
            // of already-bound names referenced as tuple components.
            // The merged Scan is placed at max(reference_positions)
            // so all referenced bindings are in scope.
            let mut reference_positions: Vec<usize> =
                Vec::with_capacity(ids.len());
            let mut bound_names: Vec<String> = Vec::new();
            // Equality filters to apply after the merged Scan,
            // matching synthesised binding-names for already-
            // bound tuple components against the original
            // identifiers.
            let mut post_filters: Vec<(String, Rc<Type>, Expr)> = Vec::new();
            let mut ok = true;
            for id in ids {
                match id {
                    Expr::Identifier(t, n) => {
                        if let Some(pos) = extent_index.get(n) {
                            if drop_positions.contains(pos)
                                || replacement_at.contains_key(pos)
                                || bound_names.contains(n)
                            {
                                ok = false;
                                break;
                            }
                            named_pats
                                .push(Pat::Identifier(t.clone(), n.clone()));
                            extent_positions.push(*pos);
                            reference_positions.push(*pos);
                            bound_names.push(n.clone());
                        } else if let Some(pos) = already_bound.get(n) {
                            // Already-bound name: scan position
                            // gets a fresh binding-name we'll
                            // compare against the original.
                            let fresh = format!("__decomp${}", fresh_counter);
                            fresh_counter += 1;
                            named_pats.push(Pat::Identifier(
                                t.clone(),
                                fresh.clone(),
                            ));
                            post_filters.push((fresh, t.clone(), id.clone()));
                            reference_positions.push(*pos);
                        } else {
                            ok = false;
                            break;
                        }
                    }
                    Expr::Literal(t, v) => {
                        named_pats.push(Pat::Literal(t.clone(), v.clone()));
                    }
                    _ => {
                        ok = false;
                        break;
                    }
                }
            }
            // Need at least one identifier to merge — otherwise this
            // is a constant `elem` that doesn't bind anything.
            if !ok || extent_positions.is_empty() {
                continue;
            }

            // Build the merged Scan. Element type = first named
            // pat's tuple type (i.e. the tuple type from the LHS).
            let tuple_t = match &args[0] {
                Expr::Tuple(t, _) => t.clone(),
                _ => continue,
            };
            let tuple_pat = Pat::Tuple(tuple_t.clone(), named_pats);
            // Build a Scan condition that compares each fresh-
            // bound component to its original (already-bound)
            // identifier. The condition lives on the Scan, so it
            // runs once per element, filtering early.
            let cond = if post_filters.is_empty() {
                None
            } else {
                let bool_t = Rc::new(Type::Primitive(PrimitiveType::Bool));
                let mut conjuncts: Vec<Expr> = Vec::new();
                for (fresh, t, orig) in &post_filters {
                    let pair_t = Rc::new(Type::Tuple(vec![
                        Rc::new((**t).clone()),
                        Rc::new((**t).clone()),
                    ]));
                    let fn_t =
                        Rc::new(Type::Fn(pair_t.clone(), bool_t.clone()));
                    let eq_op = match t.as_ref() {
                        Type::Primitive(PrimitiveType::Int) => {
                            BuiltInFunction::IntEq
                        }
                        Type::Primitive(PrimitiveType::Real) => {
                            BuiltInFunction::RealEq
                        }
                        Type::Primitive(PrimitiveType::String) => {
                            BuiltInFunction::StringEq
                        }
                        Type::Primitive(PrimitiveType::Char) => {
                            BuiltInFunction::CharEq
                        }
                        Type::Primitive(PrimitiveType::Bool) => {
                            BuiltInFunction::BoolEq
                        }
                        _ => BuiltInFunction::GEq,
                    };
                    let fn_lit = Expr::Literal(fn_t, Val::Fn(eq_op));
                    let arg = Expr::Tuple(
                        pair_t,
                        vec![
                            Expr::Identifier(t.clone(), fresh.clone()),
                            orig.clone(),
                        ],
                    );
                    conjuncts.push(Expr::Apply(
                        bool_t.clone(),
                        Box::new(fn_lit),
                        Box::new(arg),
                        Span::new(""),
                    ));
                }
                Some(Box::new(and_all(conjuncts)))
            };
            let scan = Step::new(
                StepKind::Scan(
                    Box::new(tuple_pat),
                    Box::new(coll.clone()),
                    cond,
                ),
                step.env.clone(),
            );

            // Place the scan at the position of the *last*
            // referenced binding (extent or already-bound) so
            // every dependency is in scope.
            let last_pos = *reference_positions.iter().max().unwrap();
            let last_is_extent = extent_positions.contains(&last_pos);
            for p in &extent_positions {
                if *p != last_pos {
                    drop_positions.insert(*p);
                }
            }
            if last_is_extent {
                if replacement_at.contains_key(&last_pos) {
                    // Two merges want the same slot; bail.
                    continue;
                }
                replacement_at.insert(last_pos, scan);
            } else {
                if insert_after.contains_key(&last_pos) {
                    continue;
                }
                insert_after.insert(last_pos, scan);
            }

            // Mark the conjunct for removal from this Where.
            where_drops.entry(wi).or_default().insert(ci);
        }
    }

    if drop_positions.is_empty()
        && replacement_at.is_empty()
        && insert_after.is_empty()
    {
        return steps;
    }

    // Rebuild the step list applying the replacements.
    let mut out: Vec<Step> = Vec::with_capacity(steps.len());
    for (i, step) in steps.into_iter().enumerate() {
        if drop_positions.contains(&i) {
            continue;
        }
        if let Some(repl) = replacement_at.remove(&i) {
            out.push(repl);
            if let Some(after) = insert_after.remove(&i) {
                out.push(after);
            }
            continue;
        }
        // For Where steps, drop matched conjuncts.
        if let Some(drops) = where_drops.get(&i)
            && let StepKind::Where(cond) = &step.kind
        {
            let conjuncts = split_conjuncts(cond);
            let kept: Vec<Expr> = conjuncts
                .into_iter()
                .enumerate()
                .filter(|(ci, _)| !drops.contains(ci))
                .map(|(_, c)| c)
                .collect();
            if kept.is_empty() {
                // Whole where becomes vacuous; drop it.
                if let Some(after) = insert_after.remove(&i) {
                    out.push(after);
                }
                continue;
            }
            let new_cond = and_all(kept);
            out.push(Step::new(StepKind::Where(Box::new(new_cond)), step.env));
            if let Some(after) = insert_after.remove(&i) {
                out.push(after);
            }
            continue;
        }
        out.push(step);
        if let Some(after) = insert_after.remove(&i) {
            out.push(after);
        }
    }
    out
}

#[allow(clippy::too_many_arguments)]
fn expand_steps_with_scope(
    steps: Vec<Step>,
    env: &FnEnv,
    rec_env: &FnEnv,
    datatypes: &DatatypeMap,
    outer_scope: &BTreeSet<String>,
) -> Vec<Step> {
    // Phase 0 (pre-pass): merge tuple-pattern `elem` conjuncts
    // with the corresponding ScanExtents. A `where (x, y) elem
    // coll` constraint, combined with `ScanExtent(x)` and
    // `ScanExtent(y)`, becomes a single `Scan(Tuple([x, y]), coll)`
    // — equivalent to writing `from (x, y) in coll`. Without this
    // step the per-pattern generators couldn't preserve the
    // tuple's correlation between `x` and `y`.
    // Phase 0a: inline let-bound function calls in `where`
    // conjuncts whose body would, after substitution, be a
    // tuple-elem constraint (e.g. `fun f (n, d) = (n, d) elem
    // coll`). The per-pattern function-inlining strategy in
    // `maybe_function` only lets us derive a generator for one
    // pattern at a time; for tuple-elem we want
    // `decompose_tuple_elems` to merge ScanExtents for *all*
    // tuple components into one Scan, so the inlining has to
    // happen at the from-level pre-pass.
    // Inline first — turning `isHappy p` into the inlined exists
    // body — so that `lift_nested_exists_in_where` can see the
    // newly-revealed inner exists conjunct.
    // Phase 0a': destructure tuple-typed scan extents that are
    // referenced via a function call whose parameter is a tuple.
    // Lets `inline_tuple_fn_calls_in_where` handle `f p` for
    // `fun f (x, y) = ...`.
    // Phase 0z: detect a self-recursive `f p` constraint of the
    // transitive-closure shape and rewrite the corresponding
    // ScanExtent's source into a `Relational.iterate` call. Runs
    // before `destructure_tuple_extents_for_fn_calls` so the
    // ScanExtent still holds the original tuple-typed pattern and
    // the `f p` conjunct is still un-inlined.
    let steps = try_invert_recursive_predicates(steps, env, rec_env, datatypes);
    let steps = destructure_tuple_extents_for_fn_calls(steps, env);
    let steps = inline_tuple_fn_calls_in_where(steps, env);
    let steps = lift_nested_exists_in_where(steps);
    // Inline again, now that lift has surfaced the inner exists's
    // conjuncts at the outer Where level.
    let steps = inline_tuple_fn_calls_in_where(steps, env);
    let steps = inline_tuple_case_in_where(steps);
    let steps = decompose_tuple_elems(steps);
    let steps = reorder_wheres_after_scans(steps);

    // Phase 0b: prune fully-unused ScanExtents from `exists` /
    // `forall` queries. `exists w, x, y where (x, 2) elem coll`
    // depends only on x; w and y don't gate the answer, so
    // morel-java drops them. We only do this for exists/forall
    // (last step is StepKind::Exists) — for a regular `from` the
    // iteration count of an unconstrained var would matter.
    let steps =
        if matches!(steps.last().map(|s| &s.kind), Some(StepKind::Exists)) {
            prune_unused_scan_extents(steps)
        } else {
            steps
        };

    // Phase A: derive generators by scanning where-clauses.
    let mut cache = Cache::new();
    derive_generators(&steps, &mut cache, env, datatypes, outer_scope);

    // Phase B: collect every Scan-over-Extent's (pat, env) pair in
    // the order they appear in `steps`, then topologically sort by
    // generator dependencies. A scan whose generator references
    // another unbounded pattern must come after that pattern's
    // scan. Without this, e.g.
    //   `from dno, name, v where v elem scott.depts
    //                       where dno = v.deptno`
    // would emit `Scan(dno, [v.deptno])` before `v` is bound.
    let extent_scans: Vec<(Pat, StepEnv)> = steps
        .iter()
        .filter_map(|s| match &s.kind {
            StepKind::Scan(p, source, _)
                if matches!(source.as_ref(), Expr::Extent(_, _)) =>
            {
                Some(((**p).clone(), s.env.clone()))
            }
            _ => None,
        })
        .collect();
    let ordered_scans = topo_order(&extent_scans, &cache);

    // Phase C: rebuild the steps. Replace each Scan-over-Extent
    // with its generator's expression, but defer emission until
    // the generator's free patterns are bound by earlier scans
    // (regular `from x in coll` or already-emitted unbounded
    // scans). Decompose every Where into conjuncts and drop
    // those whose text appears in a sealed generator's
    // provenance. Other steps pass through.
    // Names introduced by *this* from's scans (regular and
    // unbounded). Used to decide whether a generator's free-pat
    // dependency must be emitted before it; names from outer
    // scopes (let-bound vals, function parameters, …) are always
    // in scope and don't gate scan ordering.
    let from_names: HashSet<String> = {
        let mut s = HashSet::new();
        for st in &steps {
            if let StepKind::Scan(p, _, _) = &st.kind {
                let mut bs: Vec<Binding> = Vec::new();
                Binding::collect_bindings(p, &mut bs);
                for b in bs {
                    s.insert(b.id.name);
                }
            }
        }
        s
    };

    let provenance: Vec<Expr> =
        cache.sealed_provenance().into_iter().cloned().collect();
    let mut out = Vec::with_capacity(steps.len());
    let mut scan_idx = 0;
    let mut bound_names: HashSet<String> = HashSet::new();
    // Bindings ordered as scans are emitted; used to rebuild the
    // step env when we reorder ScanExtents past regular Scans.
    let mut bound_bindings: Vec<Binding> = Vec::new();
    // ScanExtents waiting on their free-pat dependencies. Each
    // entry is (next_pat, next_env, original_cond, original_span).
    // The span comes from the source `Expr::Extent(_, span)` so that
    // a still-deferred-after-flush emission produces a "pattern not
    // grounded" error pointing at the user's `from p`.
    let mut deferred: Vec<(Pat, StepEnv, Option<Box<Expr>>, Span)> = Vec::new();

    let try_flush =
        |bound_names: &mut HashSet<String>,
         bound_bindings: &mut Vec<Binding>,
         deferred: &mut Vec<(Pat, StepEnv, Option<Box<Expr>>, Span)>,
         out: &mut Vec<Step>| {
            let mut progress = true;
            while progress {
                progress = false;
                let mut still: Vec<(Pat, StepEnv, Option<Box<Expr>>, Span)> =
                    Vec::new();
                for (next_pat, orig_env, cond, orig_span) in deferred.drain(..)
                {
                    let Pat::Identifier(_, n) = &next_pat else {
                        still.push((next_pat, orig_env, cond, orig_span));
                        continue;
                    };
                    let name = n.clone();
                    let ready = match cache.best(&name) {
                        Some(g) => g.free_pats.iter().all(|fp| {
                            // Outer-scope names are always in scope;
                            // only require from-step names to be
                            // bound by an earlier emitted scan.
                            !from_names.contains(fp.as_str())
                                || bound_names.contains(fp.as_str())
                        }),
                        None => true,
                    };
                    if !ready {
                        still.push((next_pat, orig_env, cond, orig_span));
                        continue;
                    }
                    // Add the new pattern's bindings.
                    let mut bs: Vec<Binding> = Vec::new();
                    Binding::collect_bindings(&next_pat, &mut bs);
                    for b in bs {
                        if !bound_names.contains(&b.id.name) {
                            bound_names.insert(b.id.name.clone());
                            bound_bindings.push(b);
                        }
                    }
                    let new_atom = bound_bindings.len() == 1;
                    let new_env = StepEnv::new(
                        bound_bindings.clone(),
                        new_atom,
                        orig_env.ordered,
                    );
                    if let Some(generator) = cache.best(&name) {
                        let merged_cond = match (
                            cond.map(|c| *c),
                            generator.extra_filter.clone(),
                        ) {
                            (None, None) => None,
                            (Some(c), None) | (None, Some(c)) => {
                                Some(Box::new(c))
                            }
                            (Some(c), Some(f)) => {
                                Some(Box::new(and_all(vec![c, f])))
                            }
                        };
                        let unique = generator.unique;
                        out.push(Step::new(
                            StepKind::Scan(
                                Box::new(next_pat),
                                Box::new(generator.exp.clone()),
                                merged_cond,
                            ),
                            new_env.clone(),
                        ));
                        // A non-unique generator (e.g. point-orelse-
                        // range) may produce the same value via more
                        // than one branch. Strip duplicates so the
                        // result has set semantics.
                        if !unique {
                            out.push(Step::new(StepKind::Distinct, new_env));
                        }
                    } else {
                        let extent =
                            Expr::Extent(next_pat.type_(), orig_span.clone());
                        out.push(Step::new(
                            StepKind::Scan(
                                Box::new(next_pat),
                                Box::new(extent),
                                cond,
                            ),
                            new_env,
                        ));
                    }
                    progress = true;
                }
                *deferred = still;
            }
        };

    for step in steps {
        match step.kind {
            StepKind::Scan(pat, source, cond)
                if matches!(source.as_ref(), Expr::Extent(_, _)) =>
            {
                let extent_span = match source.as_ref() {
                    Expr::Extent(_, s) => s.clone(),
                    _ => Span::new(""),
                };
                if !matches!(pat.as_ref(), Pat::Identifier(_, _))
                    || scan_idx >= ordered_scans.len()
                {
                    out.push(Step::new(
                        StepKind::Scan(pat, source, cond),
                        step.env,
                    ));
                    continue;
                }
                let (next_pat, next_env) = ordered_scans[scan_idx].clone();
                scan_idx += 1;
                deferred.push((next_pat, next_env, cond, extent_span));
                try_flush(
                    &mut bound_names,
                    &mut bound_bindings,
                    &mut deferred,
                    &mut out,
                );
            }
            StepKind::Scan(pat, source, cond) => {
                // Regular Scan: emit, then try to flush deferred.
                let mut bs: Vec<Binding> = Vec::new();
                Binding::collect_bindings(&pat, &mut bs);
                for b in bs {
                    // Synthetic `__decomp$N` names introduced by
                    // `decompose_tuple_elems` exist only to bind a
                    // tuple component to a fresh slot for the
                    // post-filter; they're not user-visible
                    // scope, so we keep them out of the step env's
                    // bindings list (which drives the implicit
                    // yield's projection).
                    if b.id.name.starts_with("__decomp$") {
                        continue;
                    }
                    if !bound_names.contains(&b.id.name) {
                        bound_names.insert(b.id.name.clone());
                        bound_bindings.push(b);
                    }
                }
                let new_atom = bound_bindings.len() == 1;
                let new_env = StepEnv::new(
                    bound_bindings.clone(),
                    new_atom,
                    step.env.ordered,
                );
                out.push(Step::new(StepKind::Scan(pat, source, cond), new_env));
                try_flush(
                    &mut bound_names,
                    &mut bound_bindings,
                    &mut deferred,
                    &mut out,
                );
            }
            StepKind::Where(condition) => {
                try_flush(
                    &mut bound_names,
                    &mut bound_bindings,
                    &mut deferred,
                    &mut out,
                );
                let conjuncts = split_conjuncts(&condition);
                let kept: Vec<Expr> = conjuncts
                    .into_iter()
                    .filter(|c| !provenance_contains(&provenance, c))
                    .collect();
                if kept.is_empty() {
                    continue;
                }
                let new_cond = and_all(kept);
                out.push(Step::new(
                    StepKind::Where(Box::new(new_cond)),
                    step.env,
                ));
            }
            other => {
                try_flush(
                    &mut bound_names,
                    &mut bound_bindings,
                    &mut deferred,
                    &mut out,
                );
                out.push(Step::new(other, step.env));
            }
        }
    }
    // Emit any still-deferred scans best-effort; they'll surface
    // as "pattern X is not grounded" at compile time, pointing at
    // the original `from p` step's span.
    for (next_pat, next_env, cond, orig_span) in deferred {
        let extent = Expr::Extent(next_pat.type_(), orig_span);
        out.push(Step::new(
            StepKind::Scan(Box::new(next_pat), Box::new(extent), cond),
            next_env,
        ));
    }
    out
}

/// Topologically sorts the unbounded scans by generator
/// dependency: a scan whose generator references pattern `q` is
/// emitted *after* `q`'s own scan. Cycles fall back to the original
/// order for the cycle members.
fn topo_order(
    extent_scans: &[(Pat, StepEnv)],
    cache: &Cache,
) -> Vec<(Pat, StepEnv)> {
    use HashSet;
    let names: Vec<String> = extent_scans
        .iter()
        .filter_map(|(p, _)| match p {
            Pat::Identifier(_, n) => Some(n.clone()),
            _ => None,
        })
        .collect();
    let unbounded: HashSet<&str> = names.iter().map(String::as_str).collect();
    let mut emitted: HashSet<String> = HashSet::new();
    let mut order: Vec<(Pat, StepEnv)> = Vec::with_capacity(extent_scans.len());
    let mut remaining: Vec<(Pat, StepEnv)> = extent_scans.to_vec();
    let mut last_size = remaining.len() + 1;
    while !remaining.is_empty() && remaining.len() < last_size {
        last_size = remaining.len();
        let mut still: Vec<(Pat, StepEnv)> = Vec::new();
        for (p, e) in remaining.drain(..) {
            let Pat::Identifier(_, ref n) = p else {
                order.push((p, e));
                continue;
            };
            let n = n.clone();
            // The scan is ready if every free pattern of its
            // generator is either NOT an unbounded scan in this
            // from (i.e. outer-scope or a bounded scan) or has
            // already been emitted.
            let ready = match cache.best(&n) {
                Some(g) => g.free_pats.iter().all(|fp| {
                    !unbounded.contains(fp.as_str())
                        || emitted.contains(fp.as_str())
                }),
                None => true,
            };
            if ready {
                emitted.insert(n);
                order.push((p, e));
            } else {
                still.push((p, e));
            }
        }
        remaining = still;
    }
    // Anything left is part of a cycle (or has missing deps);
    // append it in original order so we at least preserve the
    // surface arrangement.
    for entry in remaining {
        order.push(entry);
    }
    order
}

fn derive_generators(
    steps: &[Step],
    cache: &mut Cache,
    env: &FnEnv,
    datatypes: &DatatypeMap,
    outer_scope: &BTreeSet<String>,
) {
    // Collect all Where conjuncts visible in this from. The morel-java
    // Expander does this in step order, but for Phase 1 (leaf-only,
    // no dependencies between generators) the order doesn't matter.
    let mut all_constraints: Vec<Expr> = Vec::new();
    for step in steps {
        if let StepKind::Where(cond) = &step.kind {
            all_constraints.extend(split_conjuncts(cond));
        }
    }

    // Collect names of every unbounded sibling so we can break
    // equality-constraint cycles (`y2 = y` with both unbounded).
    let unbounded_pats: Vec<(String, Rc<Type>)> = steps
        .iter()
        .filter_map(|s| match &s.kind {
            StepKind::Scan(p, source, _)
                if matches!(source.as_ref(), Expr::Extent(_, _)) =>
            {
                if let Pat::Identifier(t, n) = p.as_ref() {
                    Some((n.clone(), t.clone()))
                } else {
                    None
                }
            }
            _ => None,
        })
        .collect();
    let unbounded_siblings: BTreeSet<String> =
        unbounded_pats.iter().map(|(n, _)| n.clone()).collect();

    // Feasibility-based bound tightening: deduce constant bounds for the
    // unbounded patterns (from `abs`, cross-variable, and multiplication
    // constraints) and prepend them so the range extractor below grounds
    // patterns it otherwise couldn't. Prepending makes a deduced constant
    // bound win over a same-side cross-variable bound (which would create
    // a cyclic generator dependency).
    let deduced = fbbt::strengthen(&unbounded_pats, &all_constraints);
    if !deduced.is_empty() {
        let mut combined = deduced;
        combined.extend(all_constraints);
        all_constraints = combined;
    }

    // For every Scan-over-Extent, attempt to synthesise a generator.
    // Use a copy of the constraints so each pattern sees the full set.
    for step in steps {
        if let StepKind::Scan(pat, source, _) = &step.kind
            && matches!(source.as_ref(), Expr::Extent(_, _))
            && let Pat::Identifier(t, name) = pat.as_ref()
        {
            // The current `from` is a bag if any Scan source is a
            // bag, otherwise a list. For Phase 1 we're conservative:
            // unbounded extents default to bag, matching the type
            // resolver's `deduce_scan_extent_step_type`.
            let ordered = matches!(source.as_ref(), Expr::Extent(t, _)
                if matches!(t.as_ref(), Type::List(_)));
            maybe_generator_with_scope(
                cache,
                pat,
                name,
                t,
                ordered,
                &all_constraints,
                env,
                datatypes,
                outer_scope,
                &unbounded_siblings,
            );
        }
    }
}

fn provenance_contains(provenance: &[Expr], conjunct: &Expr) -> bool {
    provenance.iter().any(|p| expr_eq(p, conjunct))
}

/// Structural equality between two Core expressions, ignoring spans.
/// Adequate for matching `where` conjuncts against generator
/// provenance — no alpha-renaming is needed because both sides come
/// from the same surface query.
pub(crate) fn expr_eq(a: &Expr, b: &Expr) -> bool {
    match (a, b) {
        (Expr::Literal(t1, v1), Expr::Literal(t2, v2)) => t1 == t2 && v1 == v2,
        (Expr::Identifier(t1, n1), Expr::Identifier(t2, n2)) => {
            t1 == t2 && n1 == n2
        }
        (Expr::RecordSelector(t1, s1), Expr::RecordSelector(t2, s2)) => {
            t1 == t2 && s1 == s2
        }
        (Expr::Apply(_, f1, a1, _), Expr::Apply(_, f2, a2, _)) => {
            expr_eq(f1, f2) && expr_eq(a1, a2)
        }
        (Expr::Tuple(_, xs), Expr::Tuple(_, ys))
        | (Expr::List(_, xs), Expr::List(_, ys)) => {
            xs.len() == ys.len()
                && xs.iter().zip(ys.iter()).all(|(x, y)| expr_eq(x, y))
        }
        (Expr::Extent(t1, _), Expr::Extent(t2, _)) => t1 == t2,
        _ => false,
    }
}

pub(crate) fn and_all(conjuncts: Vec<Expr>) -> Expr {
    let mut iter = conjuncts.into_iter();
    let first = iter.next().expect("at least one conjunct");
    iter.fold(first, |lhs, rhs| {
        let bool_t = Rc::new(Type::Primitive(PrimitiveType::Bool));
        let pair_t = Rc::new(Type::Tuple(vec![
            Rc::new((*bool_t).clone()),
            Rc::new((*bool_t).clone()),
        ]));
        let fn_t = Rc::new(Type::Fn(pair_t.clone(), bool_t.clone()));
        let fn_expr =
            Expr::Literal(fn_t, Val::Fn(BuiltInFunction::BoolAndAlso));
        let arg = Expr::Tuple(pair_t, vec![lhs, rhs]);
        Expr::Apply(bool_t, Box::new(fn_expr), Box::new(arg), Span::new(""))
    })
}
