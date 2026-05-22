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

//! Capture-aware substitution of free identifiers in a Core
//! expression.
//!
//! Used by the predicate-inversion pipeline (hydromatic/morel#217)
//! to inline function bodies and rewrite case-arm conditions.
//! Mirrors morel-java's `compile.Replacer`.
//!
//! The current implementation is the minimum needed for Phase 1+
//! of the port: it walks `Expr`, `Step`, and `Match` nodes,
//! substituting `Expr::Identifier(_, name)` whenever `name` is in
//! the supplied map *and* is not shadowed by an enclosing
//! pattern binding.

use crate::compile::core::{Expr, Match, Pat, PatField, Step, StepKind};
use std::collections::HashMap;

/// Substitutes every free occurrence of `name` (for `(name, expr) ∈
/// map`) with `expr`. Bound occurrences (introduced by patterns in
/// `fn`, `case`, query `Scan`, etc.) are not substituted.
pub fn substitute(expr: &Expr, map: &HashMap<String, Expr>) -> Expr {
    let mut shadow: Vec<String> = Vec::new();
    visit_expr(expr, map, &mut shadow)
}

fn visit_expr(
    expr: &Expr,
    map: &HashMap<String, Expr>,
    shadow: &mut Vec<String>,
) -> Expr {
    match expr {
        // lint: sort until '#}' where '##Expr::'
        Expr::Aggregate(t, e1, e2) => Expr::Aggregate(
            t.clone(),
            Box::new(visit_expr(e1, map, shadow)),
            Box::new(visit_expr(e2, map, shadow)),
        ),
        Expr::Apply(t, f, a, span) => Expr::Apply(
            t.clone(),
            Box::new(visit_expr(f, map, shadow)),
            Box::new(visit_expr(a, map, shadow)),
            span.clone(),
        ),
        Expr::Case(t, subject, arms, span) => Expr::Case(
            t.clone(),
            Box::new(visit_expr(subject, map, shadow)),
            arms.iter().map(|a| visit_match(a, map, shadow)).collect(),
            span.clone(),
        ),
        Expr::Current(t) => Expr::Current(t.clone()),
        Expr::Exists(t, steps) => {
            Expr::Exists(t.clone(), visit_steps(steps, map, shadow))
        }
        Expr::Extent(t, span) => Expr::Extent(t.clone(), span.clone()),
        Expr::Fn(t, arms, span) => Expr::Fn(
            t.clone(),
            arms.iter().map(|a| visit_match(a, map, shadow)).collect(),
            span.clone(),
        ),
        Expr::Forall(t, steps) => {
            Expr::Forall(t.clone(), visit_steps(steps, map, shadow))
        }
        Expr::From(t, steps) => {
            Expr::From(t.clone(), visit_steps(steps, map, shadow))
        }
        Expr::Identifier(t, name) => {
            if !shadow.contains(name)
                && let Some(replacement) = map.get(name)
            {
                replacement.clone()
            } else {
                Expr::Identifier(t.clone(), name.clone())
            }
        }
        Expr::Let(t, decls, body) => {
            // For Phase 0 we don't model decl-introduced bindings;
            // recurse into the body without shadowing. Phase 3+
            // (function inlining) will refine this when it actually
            // needs to substitute through `let`s.
            Expr::Let(
                t.clone(),
                decls.clone(),
                Box::new(visit_expr(body, map, shadow)),
            )
        }
        Expr::List(t, items) => Expr::List(
            t.clone(),
            items.iter().map(|e| visit_expr(e, map, shadow)).collect(),
        ),
        Expr::Literal(t, val) => Expr::Literal(t.clone(), val.clone()),
        Expr::Ordinal(t) => Expr::Ordinal(t.clone()),
        Expr::Raise(t, e, span) => Expr::Raise(
            t.clone(),
            Box::new(visit_expr(e, map, shadow)),
            span.clone(),
        ),
        Expr::RecordSelector(t, slot) => Expr::RecordSelector(t.clone(), *slot),
        Expr::Tuple(t, items) => Expr::Tuple(
            t.clone(),
            items.iter().map(|e| visit_expr(e, map, shadow)).collect(),
        ),
    }
}

fn visit_match(
    m: &Match,
    map: &HashMap<String, Expr>,
    shadow: &mut Vec<String>,
) -> Match {
    let saved_len = shadow.len();
    collect_pat_bindings(&m.pat, shadow);
    let result = Match {
        pat: m.pat.clone(),
        expr: visit_expr(&m.expr, map, shadow),
    };
    shadow.truncate(saved_len);
    result
}

fn visit_steps(
    steps: &[Step],
    map: &HashMap<String, Expr>,
    shadow: &mut Vec<String>,
) -> Vec<Step> {
    let saved_len = shadow.len();
    let mut out = Vec::with_capacity(steps.len());
    for step in steps {
        out.push(visit_step(step, map, shadow));
    }
    shadow.truncate(saved_len);
    out
}

fn visit_step(
    step: &Step,
    map: &HashMap<String, Expr>,
    shadow: &mut Vec<String>,
) -> Step {
    let kind = match &step.kind {
        // lint: sort until '#}' where '##StepKind::'
        StepKind::Compute(e) => {
            StepKind::Compute(Box::new(visit_expr(e, map, shadow)))
        }
        StepKind::Distinct => StepKind::Distinct,
        StepKind::Except(d, exprs) => StepKind::Except(
            *d,
            exprs.iter().map(|e| visit_expr(e, map, shadow)).collect(),
        ),
        StepKind::Exists => StepKind::Exists,
        StepKind::Group(key, agg) => StepKind::Group(
            Box::new(visit_expr(key, map, shadow)),
            agg.as_deref().map(|e| Box::new(visit_expr(e, map, shadow))),
        ),
        StepKind::Intersect(d, exprs) => StepKind::Intersect(
            *d,
            exprs.iter().map(|e| visit_expr(e, map, shadow)).collect(),
        ),
        StepKind::Order(e) => {
            StepKind::Order(Box::new(visit_expr(e, map, shadow)))
        }
        StepKind::Require(e) => {
            StepKind::Require(Box::new(visit_expr(e, map, shadow)))
        }
        StepKind::Scan(pat, source, cond) => {
            // Substitute in the source first (it doesn't see the
            // pattern's bindings), then bring the pattern's names into
            // scope before walking the optional join condition. The
            // bindings stay live for subsequent sibling steps; the
            // outer `visit_steps` truncates at the end.
            let new_source = Box::new(visit_expr(source, map, shadow));
            collect_pat_bindings(pat, shadow);
            let new_cond = cond
                .as_deref()
                .map(|c| Box::new(visit_expr(c, map, shadow)));
            StepKind::Scan(pat.clone(), new_source, new_cond)
        }
        StepKind::Skip(e) => {
            StepKind::Skip(Box::new(visit_expr(e, map, shadow)))
        }
        StepKind::Take(e) => {
            StepKind::Take(Box::new(visit_expr(e, map, shadow)))
        }
        StepKind::Union(d, exprs) => StepKind::Union(
            *d,
            exprs.iter().map(|e| visit_expr(e, map, shadow)).collect(),
        ),
        StepKind::Unorder => StepKind::Unorder,
        StepKind::Where(e) => {
            StepKind::Where(Box::new(visit_expr(e, map, shadow)))
        }
        StepKind::Yield(e) => {
            StepKind::Yield(Box::new(visit_expr(e, map, shadow)))
        }
    };
    Step::new(kind, step.env.clone())
}

fn collect_pat_bindings(pat: &Pat, bound: &mut Vec<String>) {
    match pat {
        // lint: sort until '#}' where '##Pat::'
        Pat::As(_, name, inner) => {
            bound.push(name.clone());
            collect_pat_bindings(inner, bound);
        }
        Pat::Cons(_, head, tail) => {
            collect_pat_bindings(head, bound);
            collect_pat_bindings(tail, bound);
        }
        Pat::Constructor(_, _, None)
        | Pat::Literal(_, _)
        | Pat::Wildcard(_) => {}
        Pat::Constructor(_, _, Some(inner)) => {
            collect_pat_bindings(inner, bound)
        }
        Pat::Identifier(_, name) => bound.push(name.clone()),
        Pat::List(_, pats) | Pat::Tuple(_, pats) => {
            for p in pats {
                collect_pat_bindings(p, bound);
            }
        }
        Pat::Record(_, fields, _) => {
            for f in fields {
                match f {
                    PatField::Labeled(_, p) | PatField::Anonymous(p) => {
                        collect_pat_bindings(p, bound);
                    }
                    PatField::Ellipsis => {}
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::compile::span::Span;
    use crate::compile::types::{PrimitiveType, Type};
    use crate::eval::val::Val;
    use std::rc::Rc;

    fn t_int() -> Rc<Type> {
        Rc::new(Type::Primitive(PrimitiveType::Int))
    }

    fn id(name: &str) -> Expr {
        Expr::Identifier(t_int(), name.to_string())
    }

    fn lit_int(n: i32) -> Expr {
        Expr::Literal(t_int(), Val::Int(n))
    }

    #[test]
    fn substitutes_a_free_identifier() {
        let mut map = HashMap::new();
        map.insert("x".to_string(), lit_int(7));
        let e = Expr::Tuple(t_int(), vec![id("x"), id("y")]);
        let r = substitute(&e, &map);
        match &r {
            Expr::Tuple(_, items) => {
                assert!(matches!(items[0], Expr::Literal(_, Val::Int(7))));
                assert!(
                    matches!(&items[1], Expr::Identifier(_, n) if n == "y")
                );
            }
            _ => panic!("expected tuple, got {:?}", r),
        }
    }

    #[test]
    fn does_not_substitute_shadowed_identifier() {
        let mut map = HashMap::new();
        map.insert("x".to_string(), lit_int(7));
        // fn x => x  — the inner `x` is bound by the pattern, not free.
        let pat = Pat::Identifier(t_int(), "x".to_string());
        let arm = Match { pat, expr: id("x") };
        let e = Expr::Fn(t_int(), vec![arm], Span::new(""));
        let r = substitute(&e, &map);
        match &r {
            Expr::Fn(_, arms, _) => match &arms[0].expr {
                Expr::Identifier(_, n) => assert_eq!(n, "x"),
                other => panic!("expected identifier, got {:?}", other),
            },
            _ => panic!("expected Fn, got {:?}", r),
        }
    }
}
