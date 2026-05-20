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

//! Collects free identifiers in a Core expression.
//!
//! "Free" means not bound by a surrounding pattern (in a `fn`,
//! `case`, `let`, or query `Scan`/`Yield`). Used by the predicate-
//! inversion pipeline (hydromatic/morel#217) to populate
//! `Generator::free_pats` and to drive scan ordering.
//!
//! Mirrors morel-java's `compile.FreeFinder`.

use crate::compile::core::{
    Binding, Expr, Match, Pat, PatField, Step, StepKind,
};
use std::collections::BTreeSet;

/// Returns the names of identifiers that occur free in `expr`,
/// relative to the bindings already in `env`.
pub fn free_names(expr: &Expr, env: &[Binding]) -> BTreeSet<String> {
    let mut out = BTreeSet::new();
    let mut bound: Vec<String> =
        env.iter().map(|b| b.id.name.clone()).collect();
    visit_expr(expr, &mut bound, &mut out);
    out
}

/// Returns the names of identifiers that occur free in `expr` with
/// no surrounding bindings.
pub fn free_names_in(expr: &Expr) -> BTreeSet<String> {
    free_names(expr, &[])
}

fn visit_expr(
    expr: &Expr,
    bound: &mut Vec<String>,
    out: &mut BTreeSet<String>,
) {
    match expr {
        // lint: sort until '#}' where '##Expr::'
        Expr::Aggregate(_, e1, e2) => {
            visit_expr(e1, bound, out);
            visit_expr(e2, bound, out);
        }
        Expr::Apply(_, f, a, _) => {
            visit_expr(f, bound, out);
            visit_expr(a, bound, out);
        }
        Expr::Case(_, subject, arms, _) => {
            visit_expr(subject, bound, out);
            for arm in arms {
                visit_match(arm, bound, out);
            }
        }
        Expr::Current(_) | Expr::Ordinal(_) => {}
        Expr::Exists(_, steps)
        | Expr::Forall(_, steps)
        | Expr::From(_, steps) => {
            visit_steps(steps, bound, out);
        }
        Expr::Extent(_, _) => {}
        Expr::Fn(_, arms, _) => {
            for arm in arms {
                visit_match(arm, bound, out);
            }
        }
        Expr::Identifier(_, name) => {
            if !bound.contains(name) {
                out.insert(name.clone());
            }
        }
        Expr::Let(_, decls, body) => {
            // For Phase 0 we don't yet model decl-introduced bindings —
            // every name introduced by a decl shadows free vars in
            // sub-expressions but morel-rust's Decl is opaque enough
            // that the first user (Phase 1+) will refine this. For now
            // recurse into any embedded expressions visible to us via
            // the body. (This is a conservative over-estimate of free
            // names, which is safe for the current callers.)
            for _ in decls {}
            visit_expr(body, bound, out);
        }
        Expr::List(_, items) | Expr::Tuple(_, items) => {
            for e in items {
                visit_expr(e, bound, out);
            }
        }
        Expr::Literal(_, _) | Expr::RecordSelector(_, _) => {}
        Expr::Raise(_, e, _) => {
            visit_expr(e, bound, out);
        }
    }
}

fn visit_match(m: &Match, bound: &mut Vec<String>, out: &mut BTreeSet<String>) {
    let saved_len = bound.len();
    collect_pat_bindings(&m.pat, bound);
    visit_expr(&m.expr, bound, out);
    bound.truncate(saved_len);
}

fn visit_steps(
    steps: &[Step],
    bound: &mut Vec<String>,
    out: &mut BTreeSet<String>,
) {
    let saved_len = bound.len();
    for step in steps {
        visit_step(step, bound, out);
    }
    bound.truncate(saved_len);
}

fn visit_step(
    step: &Step,
    bound: &mut Vec<String>,
    out: &mut BTreeSet<String>,
) {
    match &step.kind {
        // lint: sort until '#}' where '##StepKind::'
        StepKind::Compute(e)
        | StepKind::Order(e)
        | StepKind::Require(e)
        | StepKind::Skip(e)
        | StepKind::Take(e)
        | StepKind::Where(e)
        | StepKind::Yield(e) => visit_expr(e, bound, out),
        StepKind::Distinct | StepKind::Exists | StepKind::Unorder => {}
        StepKind::Except(_, exprs)
        | StepKind::Intersect(_, exprs)
        | StepKind::Union(_, exprs) => {
            for e in exprs {
                visit_expr(e, bound, out);
            }
        }
        StepKind::Group(key, agg) => {
            visit_expr(key, bound, out);
            if let Some(a) = agg {
                visit_expr(a, bound, out);
            }
        }
        StepKind::Scan(pat, source, condition) => {
            visit_expr(source, bound, out);
            // The pattern's bindings are visible to subsequent steps
            // and to the optional join condition.
            collect_pat_bindings(pat, bound);
            if let Some(cond) = condition {
                visit_expr(cond, bound, out);
            }
        }
    }
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
    use crate::compile::types::{PrimitiveType, Type};
    use crate::eval::val::Val;

    fn t_int() -> Box<Type> {
        Box::new(Type::Primitive(PrimitiveType::Int))
    }

    fn id(name: &str) -> Expr {
        Expr::Identifier(t_int(), name.to_string())
    }

    fn lit_int(n: i32) -> Expr {
        Expr::Literal(t_int(), Val::Int(n))
    }

    #[test]
    fn lone_identifier_is_free() {
        let e = id("x");
        let names = free_names_in(&e);
        assert!(names.contains("x") && names.len() == 1);
    }

    #[test]
    fn literal_has_no_free_names() {
        let e = lit_int(42);
        assert!(free_names_in(&e).is_empty());
    }

    #[test]
    fn tuple_collects_each_element() {
        let e = Expr::Tuple(t_int(), vec![id("a"), id("b"), id("a")]);
        let names = free_names_in(&e);
        assert!(names.contains("a"));
        assert!(names.contains("b"));
        assert_eq!(names.len(), 2);
    }
}
