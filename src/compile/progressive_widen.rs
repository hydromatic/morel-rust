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

//! Post-resolution widening pass for progressive `Sys.file` records.
//!
//! Mirrors morel-java's `Resolver.toCore` widening. Where the unifier-
//! action path in [`crate::compile::type_resolver`] handles direct
//! file references (and val bindings that name a `Val::File`
//! directly), this pass reaches Files through record literals, tuple
//! destructuring, and let-bindings — any value path the unifier-time
//! [`crate::eval::file::TypedValue`] map does not cover.
//!
//! Strategy: walk the core decl. At each `Apply(_,
//! RecordSelector(_, slot), arg, _)` whose `arg.type_()` is a
//! progressive record, run `value_of(arg)`. If that yields
//! `Val::File(f)`, call `f.discover_field(name)` to widen the file,
//! then refine the recorded types on the Apply, the selector, and
//! the arg.

use crate::compile::core::{Decl, Expr, Match, Step, StepKind};
use crate::compile::types::Type;
use crate::eval::file::{File, FileState, TypedValue, file_as_val};
use crate::eval::val::Val;
use std::collections::HashMap;
use std::rc::Rc;

/// Walks `decl` in place, widening any progressive-record field
/// selector whose receiver value resolves to a `Val::File`. `env`
/// is the runtime binding map from the shell (previous statements'
/// val bindings); `file_root` is the session's root `File`.
pub fn widen(
    decl: &mut Decl,
    env: &HashMap<String, Val>,
    file_root: &Rc<File>,
) {
    match decl {
        Decl::NonRecVal(b) => walk_expr(&mut b.expr, env, file_root),
        Decl::RecVal(binds) => {
            for b in binds {
                walk_expr(&mut b.expr, env, file_root);
            }
        }
        Decl::Over(_) | Decl::Type(_) | Decl::Datatype(_) => {}
    }
}

fn walk_expr(e: &mut Expr, env: &HashMap<String, Val>, file_root: &Rc<File>) {
    match e {
        Expr::Apply(apply_ty, fx, arg, _) => {
            walk_expr(fx, env, file_root);
            walk_expr(arg, env, file_root);

            // Only progressive-record receivers are interesting.
            let is_progressive =
                matches!(arg.type_().as_ref(), Type::Record(true, _));
            if !is_progressive {
                return;
            }
            // Must be a RecordSelector application.
            let Expr::RecordSelector(sel_ty, slot) = fx.as_mut() else {
                return;
            };
            let slot = *slot;

            // Look up the field name in the current (stale) arg type
            // and use the value-walk to find the underlying File.
            let Some(field_name) =
                arg.type_().field_name(slot).map(ToString::to_string)
            else {
                return;
            };
            let Some(Val::File(f)) = value_of(arg, env, file_root) else {
                return;
            };

            // Widen the file. May be a no-op if already wide enough.
            f.discover_field(&field_name);

            // Pull the new (post-widen) types out of the File.
            let widened_arg_ty = f.type_();
            let widened_field_ty = match widened_arg_ty.as_ref() {
                Type::Record(_, fields) => fields.values().nth(slot).cloned(),
                _ => None,
            };
            let Some(widened_field_ty) = widened_field_ty else {
                return;
            };

            // Refine in place: arg, the selector's function type,
            // and the Apply's result type.
            set_expr_type(arg.as_mut(), widened_arg_ty.clone());
            *sel_ty =
                Rc::new(Type::Fn(widened_arg_ty, widened_field_ty.clone()));
            *apply_ty = widened_field_ty;
        }
        Expr::Aggregate(_, l, r) => {
            walk_expr(l, env, file_root);
            walk_expr(r, env, file_root);
        }
        Expr::Case(_, scrut, arms, _) => {
            walk_expr(scrut, env, file_root);
            walk_matches(arms, env, file_root);
        }
        Expr::Fn(_, arms, _) => {
            walk_matches(arms, env, file_root);
        }
        Expr::Let(_, decls, body) => {
            for d in decls {
                widen(d, env, file_root);
            }
            walk_expr(body, env, file_root);
        }
        Expr::List(_, elems) | Expr::Tuple(_, elems) => {
            for x in elems {
                walk_expr(x, env, file_root);
            }
        }
        Expr::From(_, steps)
        | Expr::Exists(_, steps)
        | Expr::Forall(_, steps) => {
            for s in steps {
                walk_step(s, env, file_root);
            }
        }
        Expr::Raise(_, inner, _) => {
            walk_expr(inner, env, file_root);
        }
        Expr::Current(_)
        | Expr::Extent(_, _)
        | Expr::Identifier(_, _)
        | Expr::Literal(_, _)
        | Expr::Ordinal(_)
        | Expr::RecordSelector(_, _) => {}
    }
}

fn walk_matches(
    matches: &mut [Match],
    env: &HashMap<String, Val>,
    file_root: &Rc<File>,
) {
    for m in matches {
        walk_expr(&mut m.expr, env, file_root);
    }
}

fn walk_step(
    step: &mut Step,
    env: &HashMap<String, Val>,
    file_root: &Rc<File>,
) {
    match &mut step.kind {
        StepKind::Compute(e)
        | StepKind::Order(e)
        | StepKind::Skip(e)
        | StepKind::Take(e)
        | StepKind::Where(e)
        | StepKind::Yield(e) => walk_expr(e, env, file_root),
        StepKind::Group(key, agg) => {
            walk_expr(key, env, file_root);
            if let Some(a) = agg {
                walk_expr(a, env, file_root);
            }
        }
        StepKind::Scan(_pat, src, cond) => {
            walk_expr(src, env, file_root);
            if let Some(c) = cond {
                walk_expr(c, env, file_root);
            }
        }
        StepKind::Except(_, exprs)
        | StepKind::Intersect(_, exprs)
        | StepKind::Union(_, exprs) => {
            for e in exprs {
                walk_expr(e, env, file_root);
            }
        }
        StepKind::Distinct | StepKind::Exists | StepKind::Unorder => {}
    }
}

/// Walks `expr` as a value-producing tree, projecting through
/// `Val::File` directories and `Val::List` record values. Returns
/// `None` for anything that isn't an identifier-rooted record-
/// selector chain — that covers everything the resolver-time
/// `TypedValue` map already handles.
fn value_of(
    expr: &Expr,
    env: &HashMap<String, Val>,
    file_root: &Rc<File>,
) -> Option<Val> {
    match expr {
        Expr::Identifier(_, name) => {
            if name == "file" {
                file_root.expand();
                Some(Val::File(Rc::clone(file_root)))
            } else {
                env.get(name).cloned()
            }
        }
        Expr::Apply(_, fx, arg, _) => {
            if let Expr::RecordSelector(_, slot) = fx.as_ref() {
                let inner = value_of(arg, env, file_root)?;
                project(&inner, *slot)
            } else {
                None
            }
        }
        _ => None,
    }
}

/// Projects slot `slot` of `v`. `Val::File` directories yield a
/// child file (as a `Val::File` for sub-directories or a
/// `Val::List` of records for data files); `Val::List`-encoded
/// record values just index. Anything else gives `None`.
fn project(v: &Val, slot: usize) -> Option<Val> {
    match v {
        Val::File(f) => {
            f.expand();
            let child = match &*f.state.borrow() {
                FileState::Directory { entries } => {
                    entries.values().nth(slot).cloned()
                }
                _ => None,
            };
            child.map(|c| file_as_val(&c))
        }
        Val::List(items) => items.get(slot).cloned(),
        _ => None,
    }
}

fn set_expr_type(e: &mut Expr, t: Rc<Type>) {
    match e {
        // lint: sort until '#}' where '##Expr::'
        Expr::Aggregate(et, _, _) => *et = t,
        Expr::Apply(et, _, _, _) => *et = t,
        Expr::Case(et, _, _, _) => *et = t,
        Expr::Current(et) => *et = t,
        Expr::Exists(et, _) => *et = t,
        Expr::Extent(et, _) => *et = t,
        Expr::Fn(et, _, _) => *et = t,
        Expr::Forall(et, _) => *et = t,
        Expr::From(et, _) => *et = t,
        Expr::Identifier(et, _) => *et = t,
        Expr::Let(et, _, _) => *et = t,
        Expr::List(et, _) => *et = t,
        Expr::Literal(et, _) => *et = t,
        Expr::Ordinal(et) => *et = t,
        Expr::Raise(et, _, _) => *et = t,
        Expr::RecordSelector(et, _) => *et = t,
        Expr::Tuple(et, _) => *et = t,
    }
}
