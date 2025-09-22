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

use crate::compile::core::{Decl, Expr, Match, Pat, ValBind};
use crate::compile::types::Type;
use crate::eval::val::Val;
use im::HashMap;
use std::collections::BTreeMap;

/// Can transform any expression, declaration, or pattern in a tree.
/// Combined with [Decl::visit], [Expr::visit], and [Pat::visit], this
/// can reshape a whole tree.
trait Transformer {
    fn transform_decl(&self, env: &Env, decl: &Decl) -> Decl;
    fn transform_expr(&self, env: &Env, expr: &Expr) -> Expr;
    fn transform_pat(&self, env: &Env, pat: &Pat) -> Pat;
}

/// Passes over a tree and inlines constants.
pub fn inline_decl(env: &Env, decl: &Decl) -> Decl {
    let inliner = Inliner {};
    inliner.transform_decl(env, decl)
}

struct Inliner {}

impl Transformer for Inliner {
    fn transform_decl(&self, env: &Env, decl: &Decl) -> Decl {
        decl.visit(env, self)
    }

    fn transform_expr(&self, env: &Env, expr: &Expr) -> Expr {
        let expr = expr.visit(env, self);
        match &expr {
            // lint: sort until '#}' where '##Expr::'
            Expr::Apply(_result_type, f, a) => {
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
                    return Expr::Literal(t.clone(), v.clone());
                }
                expr
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
            Expr::Apply(result_type, f, a) => {
                let f2 = Box::new(x.transform_expr(env, f));
                let a2 = Box::new(x.transform_expr(env, a));
                Expr::Apply(result_type.clone(), f2, a2)
            }
            Expr::Case(t, expr, matches) => {
                let expr2 = Box::new(x.transform_expr(env, expr));
                let mut matches2 = Vec::new();
                for m in matches {
                    let pat = x.transform_pat(env, &m.pat);
                    let expr = x.transform_expr(env, &m.expr);
                    matches2.push(Match { pat, expr });
                }
                Expr::Case(t.clone(), expr2, matches2)
            }
            Expr::Fn(t, match_list) => {
                let mut match_list2 = Vec::new();
                for m in match_list {
                    let pat = x.transform_pat(env, &m.pat);
                    let expr = x.transform_expr(env, &m.expr);
                    match_list2.push(Match { pat, expr });
                }
                Expr::Fn(t.clone(), match_list2)
            }
            Expr::Identifier(t, id) => {
                if let Some(v) = env.lookup_constant(id) {
                    Expr::Literal(t.clone(), v.clone())
                } else {
                    self.clone()
                }
            }
            Expr::Let(t, decl_list, e) => {
                let mut decl_list2 = Vec::new();
                for d in decl_list {
                    let d2 = x.transform_decl(env, d);
                    decl_list2.push(d2);
                }
                let e2 = Box::new(x.transform_expr(env, e));
                Expr::Let(t.clone(), decl_list2, e2)
            }
            Expr::List(t, expr_list) => Expr::List(
                t.clone(),
                Self::visit_list(env, x, expr_list).into_iter().collect(),
            ),
            Expr::Literal(_t, _v) => self.clone(),
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
}

impl Decl {
    fn visit(&self, env: &Env, x: &dyn Transformer) -> Decl {
        match &self {
            Decl::NonRecVal(val_bind) => {
                let env2 = env.child_none(
                    val_bind.pat.name().unwrap().as_str(),
                    &val_bind.t,
                );
                Decl::NonRecVal(Box::new(ValBind {
                    pat: x.transform_pat(env, &val_bind.pat),
                    expr: x.transform_expr(&env2, &val_bind.expr),
                    t: val_bind.t.clone(),
                    overload_pat: val_bind.overload_pat.clone(),
                }))
            }
            Decl::RecVal(val_binds) => {
                let val_binds2 =
                    val_binds.iter().map(|b| b.visit(env, x)).collect();
                Decl::RecVal(val_binds2)
            }
            _ => todo!("inline {:}", self),
        }
    }
}

impl ValBind {
    fn visit(&self, env: &Env, x: &dyn Transformer) -> Self {
        let env2 = env.child_none(self.pat.name().unwrap().as_str(), &self.t);
        let pat = x.transform_pat(env, &self.pat);
        let expr = x.transform_expr(&env2, &self.expr);
        ValBind::of(&pat, &self.t, &expr)
    }
}
/// Environment for inlining.
#[derive(Debug, Clone)]
pub struct Env {
    map: im::HashMap<String, (Type, Option<Val>)>,
}

impl Env {
    /// Returns an empty environment.
    pub(crate) fn empty() -> Self {
        Env {
            map: HashMap::new(),
        }
    }

    /// Returns an environment with a given backing map.
    pub fn with(map: HashMap<String, (Type, Option<Val>)>) -> Env {
        Env { map }
    }

    pub(crate) fn child(&self, name: &str, t: &Type, v: &Val) -> Env {
        let map2 = self
            .map
            .update(name.to_string(), (t.clone(), Some(v.clone())));
        Self::with(map2)
    }

    pub(crate) fn child_none(&self, name: &str, t: &Type) -> Env {
        let map2 = self.map.update(name.to_string(), (t.clone(), None));
        Self::with(map2)
    }

    pub(crate) fn multi(
        &self,
        map: &BTreeMap<&str, (Type, Option<Val>)>,
    ) -> Env {
        let mut map2 = self.map.clone();
        for entry in map {
            map2 = map2.update(entry.0.to_string(), entry.1.clone());
        }
        Self::with(map2)
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
