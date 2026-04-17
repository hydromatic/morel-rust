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

use crate::compile::core::{Decl, Expr, Match, Pat, PatField, Step, StepKind};
use crate::compile::type_env::Binding;
use crate::compile::types::{Label, Type};
use crate::eval::frame::FrameDef;
use crate::eval::val::Val;
use crate::shell::main::Environment;
use std::collections::HashSet;

/// Collects definitions of, and references to, variables.
///
/// This is used during compilation:
///
/// * A function's stack frame must have one slot for each variable defined in
///   the function.
/// * If a function refers to variables that it does not define, these variables
///   must go into a closure.
/// * If a function is declared as recursive but does not reference itself, it
///   can safely be downgraded to a non-recursive function.
///
/// TODO:
/// * Don't include variables defined in functions.
/// * Use this collector to figure out whether functions declared recursive can
///   safely be made non-recursive.
/// * Add IDs to bindings, so variables with the same name correctly shadow each
///   other.
#[derive(Debug)]
pub struct VarCollector<'a> {
    rec_fns: &'a Environment,
    defs: Vec<Binding>,
    refs: Vec<Binding>,
}

impl<'a> VarCollector<'a> {
    /// Creates a new empty variable collector.
    pub fn new(rec_fns: &'a Environment) -> Self {
        VarCollector {
            rec_fns,
            defs: Vec::new(),
            refs: Vec::new(),
        }
    }

    /// Adds a definition of a variable to the collector.
    /// Variables are defined by patterns ([Pat]).
    pub fn add_def(&mut self, binding: Binding) {
        self.defs.push(binding);
    }

    /// Adds a reference to a variable to the collector.
    /// Variables are defined by patterns ([Pat]).
    pub fn add_ref(&mut self, binding: Binding) {
        self.refs.push(binding);
    }

    /// Returns the bindings of all variables defined.
    pub fn local_vars(&self) -> Vec<Binding> {
        // Make the collection unique, retaining order.
        let mut seen = HashSet::new();
        let mut result = Vec::new();

        for binding in &self.defs {
            if seen.insert(binding.id.name.clone()) {
                result.push(binding.clone());
            }
        }

        result
    }

    /// Returns the bindings of all variables that are referred to but not
    /// defined. These are the variables that must be captured and "bound" by
    /// the closure. If there are no such variables, a closure is not required.
    pub fn bound_vars(&self) -> Vec<Binding> {
        // Make a collection of references, skipping variables that are
        // defined, eliminating duplicates, and preserving order.
        let defined_vars: HashSet<String> =
            self.defs.iter().map(|b| b.id.name.clone()).collect();

        let mut seen_refs = HashSet::new();
        let mut result = Vec::new();

        for binding in &self.refs {
            let name = &binding.id.name;
            // Include this binding if not defined locally, not a recursive
            // function (a `Val::Code` in the env, typically a `Code::Link`
            // for a `fun` / `val rec`), and not already seen. Other env
            // entries — outer-scope `val` bindings holding plain data —
            // are NOT filtered: an inner function parameter that happens
            // to share a name with such an outer binding still needs to
            // be captured into the closure's frame, otherwise the
            // shadowing parameter would be invisible to the body.
            let env_recursive_fn =
                matches!(self.rec_fns.get(name), Some(Val::Code(_)));
            if !defined_vars.contains(name)
                && !env_recursive_fn
                && seen_refs.insert(name.clone())
            {
                result.push(binding.clone());
            }
        }

        result
    }

    /// Creates a frame definition from the bindings of this collector.
    pub fn into_frame_def(self) -> FrameDef {
        FrameDef::new(&self.bound_vars(), &self.local_vars())
    }
}

impl Pat {
    pub(crate) fn collect_vars(&self, collector: &mut VarCollector) {
        match self {
            // lint: sort until '#}' where '##Pat::'
            Pat::As(_, name, pat) => {
                collector.add_def(Binding::of_name(name));
                pat.collect_vars(collector);
            }
            Pat::Cons(_, head, tail) => {
                head.collect_vars(collector);
                tail.collect_vars(collector);
            }
            Pat::Constructor(_, _name, pat) => {
                pat.iter().for_each(|p| p.collect_vars(collector));
            }
            Pat::Identifier(_, name) => {
                collector.add_def(Binding::of_name(name));
            }
            Pat::List(_, pats) | Pat::Tuple(_, pats) => {
                pats.iter().for_each(|p| p.collect_vars(collector));
            }
            Pat::Literal(_, _) => {
                // no variables
            }
            Pat::Record(_, pat_fields, _) => {
                for field in pat_fields {
                    match field {
                        PatField::Labeled(_, p) | PatField::Anonymous(p) => {
                            p.collect_vars(collector);
                        }
                        PatField::Ellipsis => {}
                    }
                }
            }
            Pat::Wildcard(_) => {
                // no variables
            }
        }
    }
}

impl Match {
    pub(crate) fn collect_vars(&self, collector: &mut VarCollector) {
        self.pat.collect_vars(collector);
        self.expr.collect_vars(collector);
    }
}

impl Decl {
    pub(crate) fn collect_vars(&self, collector: &mut VarCollector) {
        match self {
            Decl::NonRecVal(val_bind) => {
                val_bind.pat.collect_vars(collector);
                val_bind.expr.collect_vars(collector);
            }
            Decl::RecVal(val_binds) => {
                for val_bind in val_binds {
                    val_bind.pat.collect_vars(collector);
                    val_bind.expr.collect_vars(collector);
                }
            }
            _ => {
                // no expressions in other declarations, therefore no variables
            }
        }
    }
}

impl Expr {
    pub(crate) fn collect_vars(&self, collector: &mut VarCollector) {
        match self {
            // lint: sort until '#}' where '##Expr::'
            Expr::Aggregate(_, f, _e) => {
                // `f over e`: f is applied to 'elements'. Collect vars from f,
                // and ensure 'elements' has a frame slot.
                f.collect_vars(collector);
                let has_elements =
                    collector.defs.iter().any(|b| b.id.name == "elements");
                if !has_elements {
                    collector.add_def(Binding::of_name("elements"));
                }
            }
            Expr::Apply(_, f, a, _) => {
                f.collect_vars(collector);
                a.collect_vars(collector);
            }
            Expr::Case(_, expr, matches, _) => {
                expr.collect_vars(collector);
                matches.iter().for_each(|m| m.collect_vars(collector));
            }
            Expr::Current(_) => {
                // 'current' refers to the primary element already in the
                // frame; no additional frame slot is needed.
            }
            Expr::Fn(_, match_list, _) => {
                // Propagate the inner fn's *free* variables (variables
                // it references but does not itself define) into the
                // outer collector, so the outer fn captures them and
                // can pass them through to the inner fn's closure.
                //
                // Without this, multi-clause `fun` declarations like
                //   fun strTimes s 0 l = l
                //     | strTimes s i l = strTimes ("a"^s) (i-1) (s::l)
                // are silently miscompiled. They desugar (in
                // type_resolver) to a chain of curried fns wrapping a
                // case expression:
                //   fn v0 => fn v1 => fn v2 =>
                //     case (v0, v1, v2) of ...
                // Each desugared fn defines exactly one of v0, v1, v2.
                // The innermost fn references all three in the case
                // body, so it correctly puts v0 and v1 in its
                // bound_vars. But to read v0 from the middle fn's
                // frame at runtime, the middle fn must itself have
                // captured v0 from the outermost fn — and so on. If
                // we treat `Expr::Fn` as opaque here, the middle fn
                // never learns that it needs to capture v0, and the
                // innermost fn's CreateClosure reads from a slot that
                // does not exist.
                let mut inner = VarCollector::new(collector.rec_fns);
                for m in match_list {
                    m.collect_vars(&mut inner);
                }
                let inner_defs: HashSet<String> =
                    inner.defs.iter().map(|b| b.id.name.clone()).collect();
                for r in inner.refs {
                    if !inner_defs.contains(&r.id.name) {
                        collector.add_ref(r);
                    }
                }
            }
            Expr::From(_, steps) => {
                steps.iter().for_each(|s| s.collect_vars(collector));
            }
            Expr::Identifier(_, name) => {
                collector.add_ref(Binding::of_name(name));
            }
            Expr::Let(_, decls, expr) => {
                decls.iter().for_each(|d| d.collect_vars(collector));
                expr.collect_vars(collector);
            }
            Expr::List(_, exprs) | Expr::Tuple(_, exprs) => {
                exprs.iter().for_each(|e| e.collect_vars(collector));
            }
            Expr::Literal(_, _) => {
                // no variables
            }
            Expr::Ordinal(_) => {
                // 'ordinal' needs a dedicated frame slot so the OrdinalRowSink
                // can write to it before each row is processed.
                collector.add_def(Binding::of_name("ordinal"));
            }
            Expr::RecordSelector(_, _) => {
                // no variables
            }
            _ => todo!("collect_vars {:?}", self),
        }
    }
}

impl Step {
    pub(crate) fn collect_vars(&self, collector: &mut VarCollector) {
        match &self.kind {
            // lint: sort until '#}' where '##StepKind::'
            StepKind::Compute(expr) => {
                // Traverse the compute expression for variable refs.
                expr.collect_vars(collector);
                // If "elements" was referenced, ensure it has a frame slot.
                let has_elements_def =
                    collector.defs.iter().any(|b| b.id.name == "elements");
                let has_elements_ref =
                    collector.refs.iter().any(|b| b.id.name == "elements");
                if has_elements_ref && !has_elements_def {
                    collector.add_def(Binding::of_name("elements"));
                }
            }
            StepKind::Except(_, exprs)
            | StepKind::Intersect(_, exprs)
            | StepKind::Union(_, exprs) => {
                for expr in exprs {
                    expr.collect_vars(collector);
                }
            }
            StepKind::Group(_, None) => {
                // Add group key field names as frame slot defs so that
                // the collection code can read them.
                for binding in &self.env.bindings {
                    collector.add_def(Binding::of_name(&binding.id.name));
                }
            }
            StepKind::Group(_, Some(aggregate_expr)) => {
                // Add all output binding names (key + aggregate)
                // as frame slot defs. The step env bindings were
                // set up by FromBuilder with the correct names.
                for binding in &self.env.bindings {
                    if !collector
                        .defs
                        .iter()
                        .any(|b| b.id.name == binding.id.name)
                    {
                        collector.add_def(Binding::of_name(&binding.id.name));
                    }
                }

                // Traverse aggregate expression for variable refs.
                aggregate_expr.collect_vars(collector);

                // If "elements" was referenced but not already
                // defined as an output field, add it as a frame
                // slot for the rows variable.
                let has_elements_def =
                    collector.defs.iter().any(|b| b.id.name == "elements");
                let has_elements_ref =
                    collector.refs.iter().any(|b| b.id.name == "elements");
                if has_elements_ref && !has_elements_def {
                    collector.add_def(Binding::of_name("elements"));
                }
            }
            StepKind::Order(expr) => {
                expr.collect_vars(collector);
            }
            StepKind::Scan(pat, expr, condition) => {
                expr.collect_vars(collector);
                pat.collect_vars(collector);
                if let Some(cond) = condition {
                    cond.collect_vars(collector);
                }
            }
            StepKind::Where(expr) => {
                expr.collect_vars(collector);
            }
            StepKind::Yield(expr) => {
                // If yielding a record, add field names as defs so that
                // subsequent steps can reference them as frame variables
                // (e.g., 'yield {x = e.deptno} where x > 10').
                if let Type::Record(_, fields) = expr.type_().as_ref() {
                    for label in fields.keys() {
                        if let Label::String(name) = label {
                            collector.add_def(Binding::of_name(name));
                        }
                    }
                }
                expr.collect_vars(collector);
            }
            _ => {
                // For other step kinds, do nothing for now
            }
        }
    }
}
