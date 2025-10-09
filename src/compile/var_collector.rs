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

use crate::compile::core::{Decl, Expr, Match, Pat};
use crate::compile::type_env::Binding;
use crate::eval::frame::FrameDef;
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
            // function, and not already seen.
            if !defined_vars.contains(name)
                && self.rec_fns.get(name).is_none()
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
            Pat::Wildcard(_) => {
                // no variables
            }
            _ => todo!("collect_vars {:?}", self),
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
    pub(crate) fn collect_vars_top(&self, collector: &mut VarCollector) {
        match self {
            Expr::Fn(_, matches) => {
                // We only traverse into 'fn' if it is the whole expression.
                matches.iter().for_each(|m| m.collect_vars(collector));
            }
            _ => {
                self.collect_vars(collector);
            }
        }
    }

    pub(crate) fn collect_vars(&self, collector: &mut VarCollector) {
        match self {
            // lint: sort until '#}' where '##Expr::'
            Expr::Apply(_, f, a) => {
                f.collect_vars(collector);
                a.collect_vars(collector);
            }
            Expr::Case(_, expr, matches) => {
                expr.collect_vars(collector);
                matches.iter().for_each(|m| m.collect_vars(collector));
            }
            Expr::Fn(_, matches) => {
                // do not traverse into a function
                if false {
                    matches.iter().for_each(|m| m.collect_vars(collector));
                }
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
            Expr::RecordSelector(_, _) => {
                // no variables
            }
            _ => todo!("collect_vars {:?}", self),
        }
    }
}
