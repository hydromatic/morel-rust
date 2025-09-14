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

use crate::compile::core::{Decl, Expr, Pat, ValBind};
use crate::compile::types::Type;
use crate::eval::code::Impl;
use crate::eval::val::Val;
use std::collections::BTreeMap;

/// Can transform any expression, declaration or pattern in a tree.
/// Combined with [Decl::visit], [Expr::visit], and [Pat::visit], this
/// can reshape a whole tree.
trait Transformer {
    fn transform_decl(&self, env: &Env, decl: Box<Decl>) -> Box<Decl>;
    fn transform_expr(&self, env: &Env, expr: Box<Expr>) -> Box<Expr>;
    fn transform_pat(&self, env: &Env, pat: Box<Pat>) -> Box<Pat>;
}

/// Passes over a tree and inlines constants.
pub fn inline_decl(env: &Env, decl: &Decl) -> Box<Decl> {
    let inliner = Inliner {};
    inliner.transform_decl(env, Box::new(decl.clone()))
}

struct Inliner {}

impl Transformer for Inliner {
    fn transform_decl(&self, env: &Env, decl: Box<Decl>) -> Box<Decl> {
        decl.visit(env, self)
    }

    fn transform_expr(&self, env: &Env, expr0: Box<Expr>) -> Box<Expr> {
        let expr = expr0.visit(env, self);
        match expr.as_ref() {
            // lint: sort until '#}' where '##Expr::'
            Expr::Apply(_result_type, f, a) => {
                if let Expr::RecordSelector(_fn_type, slot) = f.as_ref()
                    && let Expr::Literal(record_type, v) = a.as_ref()
                    && let Some(field_type) =
                        record_type.field_types().get(*slot)
                {
                    let v2 = v.get_field(*slot).unwrap();
                    return Box::new(Expr::Literal(
                        Box::new(field_type.clone()),
                        v2.clone(),
                    ));
                }
                expr
            }
            Expr::Identifier(t, id) => {
                // If the name is a constant in the environment, replace it with
                // a literal value. We do this for package names: for example,
                // "Sys.set" becomes the record (list) value "Sys"; next, the
                // transformation on "Apply" of the 9th field (because "set" is
                // the 9th field of "Sys" record type) converts that the field
                // into a function literal.
                if let Some(v) = env.lookup_constant(id) {
                    return Box::new(Expr::Literal(t.clone(), v.clone()));
                }
                expr
            }
            _ => expr,
        }
    }

    fn transform_pat(&self, _v: &Env, pat: Box<Pat>) -> Box<Pat> {
        pat // For now, just return the pattern unchanged
    }
}

impl Pat {
    fn visit(&self, _env: &Env, _x: &dyn Transformer) -> Box<Pat> {
        Box::new(self.clone())
    }
}

impl Expr {
    fn visit(&self, env: &Env, x: &dyn Transformer) -> Box<Expr> {
        Box::new(match &self {
            // lint: sort until '#}' where '##Expr::'
            Expr::Apply(result_type, f, a) => {
                let f2 = x.transform_expr(env, f.clone());
                let a2 = x.transform_expr(env, a.clone());
                Expr::Apply(result_type.clone(), f2, a2)
            }
            Expr::Identifier(t, id) => {
                if let Some(v) = env.lookup_constant(id) {
                    Expr::Literal(t.clone(), v.clone())
                } else {
                    self.clone()
                }
            }
            Expr::List(t, expr_list) => {
                Expr::List(t.clone(), Self::visit_list(env, x, expr_list))
            }
            Expr::Literal(_t, _v) => self.clone(),
            Expr::Tuple(t, expr_list) => {
                Expr::Tuple(t.clone(), Self::visit_list(env, x, expr_list))
            }
            _ => todo!("inline {:}", self),
        })
    }

    #[allow(clippy::vec_box)]
    fn visit_list(
        env: &Env,
        x: &dyn Transformer,
        expr_list: &[Box<Expr>],
    ) -> Vec<Box<Expr>> {
        expr_list
            .iter()
            .map(|e| x.transform_expr(env, e.clone()))
            .collect()
    }
}

impl Decl {
    fn visit(&self, env: &Env, x: &dyn Transformer) -> Box<Decl> {
        match &self {
            Decl::NonRecVal(val_bind) => {
                let env2 = env.child_none(
                    val_bind.pat.name().unwrap().as_str(),
                    val_bind.t.clone(),
                );
                Box::new(Decl::NonRecVal(Box::new(ValBind {
                    pat: x.transform_pat(env, val_bind.pat.clone()),
                    expr: x.transform_expr(&env2, val_bind.expr.clone()),
                    t: val_bind.t.clone(),
                    overload_pat: val_bind.overload_pat.clone(),
                })))
            }
            _ => todo!("inline {:}", self),
        }
    }
}

/// Environment for inlining.
pub enum Env<'a> {
    Root,
    Child(&'a Env<'a>, String, Box<Type>, Option<Val>),
    Multi(&'a Env<'a>, &'a BTreeMap<&'a str, Binding>),
}

impl<'a> Env<'a> {
    pub(crate) fn child(&self, name: &str, t: Box<Type>, v: &Val) -> Env<'_> {
        Env::Child(self, name.to_string(), t, Some(v.clone()))
    }

    pub(crate) fn child_none(&self, name: &str, t: Box<Type>) -> Env<'_> {
        Env::Child(self, name.to_string(), t, None)
    }

    pub(crate) fn multi(&self, map: &'a BTreeMap<&str, Binding>) -> Env<'_> {
        Env::Multi(self, map)
    }

    pub(crate) fn lookup_constant(&self, s: &str) -> Option<Val> {
        match self {
            Env::Root => None,
            Env::Child(parent, name, _, v) => {
                if name == s && v.is_some() {
                    v.clone()
                } else {
                    parent.lookup_constant(s)
                }
            }
            Env::Multi(parent, map) => {
                if let Some(binding) = map.get(s) {
                    Some(binding.to_val())
                } else {
                    parent.lookup_constant(s)
                }
            }
        }
    }
}

pub enum Binding {
    Single(Impl),
    List(Vec<Binding>),
}

impl Binding {
    pub(crate) fn to_val(&self) -> Val {
        match self {
            Binding::Single(impl_) => Val::Impl(*impl_),
            Binding::List(list) => {
                Val::List(list.iter().map(Binding::to_val).collect())
            }
        }
    }
}
