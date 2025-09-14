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

use crate::compile::core::{
    DatatypeBind as CoreDatatypeBind, Decl as CoreDecl, Expr as CoreExpr,
    Pat as CorePat, TypeBind as CoreTypeBind, ValBind as CoreValBind,
};
use crate::compile::type_resolver::{Resolved, TypeMap, Typed};
use crate::compile::types::{PrimitiveType, Type};
use crate::eval::val::Val;
use crate::syntax::ast::{
    DatatypeBind, Decl, DeclKind, Expr, ExprKind, Literal, LiteralKind, Pat,
    PatKind, Type as AstType, TypeBind, ValBind,
};
use crate::syntax::parser;

/// Converts an AST to a Core tree.
pub fn resolve(resolved: &Resolved) -> Box<crate::compile::core::Decl> {
    let resolver = Resolver::new(&resolved.type_map);
    resolver.resolve_decl(&resolved.decl)
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
}

/// Helper struct representing a pattern-expression pair with position info.
#[derive(Debug, Clone)]
struct PatExp {
    pat: Box<CorePat>,
    expr: Box<CoreExpr>,
}

/// Resolved value declaration that mirrors the Java ResolvedValDecl.
#[derive(Debug, Clone)]
struct ResolvedValDecl {
    rec: bool,
    composite: bool,
    pat_exps: Vec<PatExp>,
    pat: Box<CorePat>,
    expr: Box<CoreExpr>,
}

impl ResolvedValDecl {
    /// Converts this resolved declaration to a let expression.
    /// This is the Rust translation of the Java toExp method.
    fn to_exp(&self, result_expr: Box<CoreExpr>) -> Box<CoreExpr> {
        if self.rec {
            // Recursive case: create RecVal with all bindings.
            let val_binds: Vec<CoreValBind> = self
                .pat_exps
                .iter()
                .map(|pat_exp| CoreValBind {
                    pat: pat_exp.pat.clone(),
                    t: pat_exp.pat.type_(),
                    expr: pat_exp.expr.clone(),
                    overload_pat: None,
                })
                .collect();

            let decl = CoreDecl::RecVal(val_binds);
            return Box::new(CoreExpr::Let(
                result_expr.type_(),
                vec![decl],
                result_expr,
            ));
        } else if !self.composite && self.pat_exps.len() == 1 {
            // Simple non-recursive case: single identifier pattern.
            let pat_exp = &self.pat_exps[0];
            if let CorePat::Identifier(_, _) = pat_exp.pat.as_ref() {
                let val_bind = CoreValBind {
                    pat: pat_exp.pat.clone(),
                    t: pat_exp.pat.type_(),
                    expr: pat_exp.expr.clone(),
                    overload_pat: None,
                };

                let decl = CoreDecl::NonRecVal(Box::new(val_bind));
                return Box::new(CoreExpr::Let(
                    result_expr.type_(),
                    vec![decl],
                    result_expr,
                ));
            }
        }

        // Complex pattern case: allocate intermediate variable.
        // Generate a unique name for the intermediate variable.
        let temp_name =
            format!("temp_var_{}", std::ptr::addr_of!(self) as usize);
        let expr_type = self.expr.type_();

        // Create intermediate identifier pattern.
        let temp_pat =
            Box::new(CorePat::Identifier(expr_type.clone(), temp_name.clone()));

        // Create the intermediate binding.
        let temp_val_bind = CoreValBind {
            pat: temp_pat.clone(),
            t: expr_type.clone(),
            expr: self.expr.clone(),
            overload_pat: None,
        };

        // Create identifier expression for the temp variable.
        let temp_id = Box::new(CoreExpr::Identifier(expr_type, temp_name));

        // Create the case expression to match the complex pattern.
        let match_ = crate::compile::core::Match {
            pat: self.pat.clone(),
            expr: result_expr,
        };

        let case_expr =
            Box::new(CoreExpr::Case(self.pat.type_(), temp_id, vec![match_]));

        // Create the let expression.
        let decl = CoreDecl::NonRecVal(Box::new(temp_val_bind));
        Box::new(CoreExpr::Let(case_expr.type_(), vec![decl], case_expr))
    }
}

impl<'a> Resolver<'a> {
    /// Creates a new resolver with the given type map.
    pub fn new(type_map: &'a TypeMap) -> Self {
        Self { type_map }
    }

    /// Resolves an AST declaration to a core declaration.
    pub(crate) fn resolve_decl(&self, decl: &Decl) -> Box<CoreDecl> {
        Box::new(match &decl.kind {
            DeclKind::Val(rec, _overload, val_binds) => {
                // Uses the new resolve_val_decl method.
                let resolved_val_decl = self.resolve_val_decl(val_binds, *rec);

                if resolved_val_decl.rec {
                    CoreDecl::RecVal(
                        resolved_val_decl
                            .pat_exps
                            .iter()
                            .map(|pe| CoreValBind {
                                pat: pe.pat.clone(),
                                t: pe.pat.type_(),
                                expr: pe.expr.clone(),
                                overload_pat: None,
                            })
                            .collect(),
                    )
                } else if resolved_val_decl.pat_exps.len() == 1 {
                    let pe = &resolved_val_decl.pat_exps[0];
                    CoreDecl::NonRecVal(Box::new(CoreValBind {
                        pat: pe.pat.clone(),
                        t: pe.pat.type_(),
                        expr: pe.expr.clone(),
                        overload_pat: None,
                    }))
                } else {
                    // Multiple non-recursive bindings - convert to RecVal.
                    CoreDecl::RecVal(
                        resolved_val_decl
                            .pat_exps
                            .iter()
                            .map(|pe| CoreValBind {
                                pat: pe.pat.clone(),
                                t: pe.pat.type_(),
                                expr: pe.expr.clone(),
                                overload_pat: None,
                            })
                            .collect(),
                    )
                }
            }
            DeclKind::Over(name) => CoreDecl::Over(name.clone()),
            DeclKind::Type(type_binds) => CoreDecl::Type(
                type_binds
                    .iter()
                    .map(|tb| self.resolve_type_bind(tb))
                    .collect(),
            ),
            DeclKind::Datatype(datatype_binds) => CoreDecl::Datatype(
                datatype_binds
                    .iter()
                    .map(|db| self.resolve_datatype_bind(db))
                    .collect(),
            ),
            DeclKind::Fun(_) => {
                unreachable!("Should have been desugared already")
            }
        })
    }

    /// Resolves an AST expression to a core expression.
    pub fn resolve_expr(&self, expr: &Expr) -> Box<CoreExpr> {
        let t = expr.get_type(self.type_map).unwrap();
        Box::new(match &expr.kind {
            ExprKind::Literal(l) => {
                CoreExpr::Literal(t, self.resolve_literal(l))
            }
            ExprKind::Identifier(name) => CoreExpr::Identifier(t, name.clone()),
            ExprKind::RecordSelector(name) => {
                let slot = t.lookup_field(name).unwrap();
                CoreExpr::RecordSelector(t, slot)
            }
            ExprKind::Current => CoreExpr::Current(t),
            ExprKind::Ordinal => CoreExpr::Ordinal(t),
            ExprKind::Plus(lhs, rhs) => CoreExpr::Plus(
                t,
                self.resolve_expr(lhs),
                self.resolve_expr(rhs),
            ),
            ExprKind::Apply(func, arg) => CoreExpr::Apply(
                t,
                self.resolve_expr(func),
                self.resolve_expr(arg),
            ),
            ExprKind::If(cond, then_expr, else_expr) => CoreExpr::If(
                t,
                self.resolve_expr(cond),
                self.resolve_expr(then_expr),
                self.resolve_expr(else_expr),
            ),
            ExprKind::Case(expr, matches) => CoreExpr::Case(
                t,
                self.resolve_expr(expr),
                matches.iter().map(|m| self.resolve_match(m)).collect(),
            ),
            ExprKind::Let(decls, body) => CoreExpr::Let(
                t,
                decls.iter().map(|d| *self.resolve_decl(d)).collect(),
                self.resolve_expr(body),
            ),
            ExprKind::Fn(matches) => CoreExpr::Fn(
                t,
                matches.iter().map(|m| self.resolve_match(m)).collect(),
            ),
            ExprKind::Tuple(elements) => CoreExpr::Tuple(
                t,
                elements.iter().map(|e| self.resolve_expr(e)).collect(),
            ),
            ExprKind::List(elements) => CoreExpr::List(
                t,
                elements.iter().map(|e| self.resolve_expr(e)).collect(),
            ),
            ExprKind::Record(_, fields) => CoreExpr::Tuple(
                t,
                fields
                    .iter()
                    .map(|f| self.resolve_expr(f.expr.as_ref()))
                    .collect(),
            ),
            ExprKind::Aggregate(left, right) => CoreExpr::Aggregate(
                t,
                self.resolve_expr(left),
                self.resolve_expr(right),
            ),
            ExprKind::From(steps) => CoreExpr::From(
                t,
                steps.iter().map(|s| self.resolve_step(s)).collect(),
            ),
            ExprKind::Exists(steps) => CoreExpr::Exists(
                t,
                steps.iter().map(|s| self.resolve_step(s)).collect(),
            ),
            ExprKind::Forall(steps) => CoreExpr::Forall(
                t,
                steps.iter().map(|s| self.resolve_step(s)).collect(),
            ),
            ExprKind::Annotated(expr, _) => *self.resolve_expr(expr),
            _ => todo!("Unimplemented expression kind: {:?}", expr.kind),
        })
    }

    /// Resolves an AST literal to a core value.
    fn resolve_literal(&self, literal: &Literal) -> Val {
        match &literal.kind {
            LiteralKind::Bool(b) => Val::Bool(*b),
            LiteralKind::Char(c) => {
                Val::Char(parser::unquote_char_literal(c).unwrap())
            }
            LiteralKind::Int(i) => {
                Val::Int(i.replace("~", "-").parse().unwrap())
            }
            LiteralKind::Real(r) => {
                Val::Real(r.replace("~", "-").parse().unwrap())
            }
            LiteralKind::String(s) => {
                Val::String(parser::unquote_string(s).unwrap())
            }
            LiteralKind::Unit => Val::Unit,
            LiteralKind::Fn(f) => Val::Fn(*f),
        }
    }

    /// Resolves an AST pattern to a core pattern.
    fn resolve_pat(&self, pat: &Pat) -> Box<CorePat> {
        let t = pat.get_type(self.type_map).unwrap();

        Box::new(match &pat.kind {
            PatKind::Wildcard => CorePat::Wildcard(t),
            PatKind::Identifier(name) => CorePat::Identifier(t, name.clone()),
            PatKind::As(name, sub_pat) => {
                CorePat::As(t, name.clone(), self.resolve_pat(sub_pat))
            }
            PatKind::Constructor(name, opt_pat) => CorePat::Constructor(
                t,
                name.clone(),
                opt_pat.as_ref().map(|p| self.resolve_pat(p)),
            ),
            PatKind::Literal(literal) => {
                CorePat::Literal(t, self.resolve_literal(literal))
            }
            PatKind::Tuple(pats) => CorePat::Tuple(
                t,
                pats.iter().map(|p| *self.resolve_pat(p)).collect(),
            ),
            PatKind::List(pats) => CorePat::List(
                t,
                pats.iter().map(|p| *self.resolve_pat(p)).collect(),
            ),
            PatKind::Record(fields, has_ellipsis) => CorePat::Record(
                t,
                fields.iter().map(|f| self.resolve_pat_field(f)).collect(),
                *has_ellipsis,
            ),
            PatKind::Cons(head, tail) => {
                CorePat::Cons(t, self.resolve_pat(head), self.resolve_pat(tail))
            }
            PatKind::Annotated(pat, _) => {
                // For annotated patterns, just resolve the inner pattern
                // since core patterns have embedded types.
                *self.resolve_pat(pat)
            }
        })
    }

    /// Resolves an AST pattern field to a core pattern field.
    fn resolve_pat_field(
        &self,
        _field: &crate::syntax::ast::PatField,
    ) -> crate::compile::core::PatField {
        todo!("Implement pat field resolution")
    }

    /// Resolves an AST value binding to a core value binding.
    fn resolve_val_bind(&self, val_bind: &ValBind) -> CoreValBind {
        let pat = self.resolve_pat(&val_bind.pat);
        let expr = self.resolve_expr(&val_bind.expr);
        // Get type from type annotation if present, otherwise from type map.
        let type_ = if let Some(type_annotation) = &val_bind.type_annotation {
            Box::new(self.resolve_ast_type(type_annotation))
        } else {
            // Try to get type from the pattern or expression ID.
            if let Some(id) = val_bind.pat.id {
                self.type_map.get_type(id).unwrap_or_else(|| {
                    Box::new(Type::Primitive(PrimitiveType::Unit))
                })
            } else if let Some(id) = val_bind.expr.id {
                self.type_map.get_type(id).unwrap_or_else(|| {
                    Box::new(Type::Primitive(PrimitiveType::Unit))
                })
            } else {
                Box::new(Type::Primitive(PrimitiveType::Unit))
            }
        };

        CoreValBind {
            pat,
            t: type_,
            expr,
            overload_pat: None,
        }
    }

    /// Resolves an AST type binding to a core type binding.
    fn resolve_type_bind(&self, _type_bind: &TypeBind) -> CoreTypeBind {
        todo!("Implement type bind resolution")
    }

    /// Resolves an AST datatype binding to a core datatype binding.
    fn resolve_datatype_bind(
        &self,
        _datatype_bind: &DatatypeBind,
    ) -> CoreDatatypeBind {
        todo!("Implement datatype bind resolution")
    }

    /// Resolves an AST type to a core type.
    fn resolve_ast_type(&self, _ast_type: &AstType) -> Type {
        // For now, just returns a basic type. This would need proper
        // implementation to convert AST type to core type based on the
        // type resolver.
        Type::Primitive(PrimitiveType::Unit)
    }

    /// Resolves an AST match to a core match.
    fn resolve_match(
        &self,
        ast_match: &crate::syntax::ast::Match,
    ) -> crate::compile::core::Match {
        crate::compile::core::Match {
            pat: self.resolve_pat(&ast_match.pat),
            expr: self.resolve_expr(&ast_match.expr),
        }
    }

    /// Resolves an AST step to a core step.
    fn resolve_step(
        &self,
        _step: &crate::syntax::ast::Step,
    ) -> crate::compile::core::Step {
        // For now, just returns a placeholder step.
        // This would need proper implementation based on step kinds.
        crate::compile::core::Step {
            kind: crate::compile::core::StepKind::From,
        }
    }

    /// Converts an AST literal to a core value.
    fn literal_val(literal: &Literal) -> Val {
        match &literal.kind {
            LiteralKind::Fn(_fn_literal) => {
                todo!("Implement Fn literal conversion")
            }
            LiteralKind::Bool(x) => Val::Bool(*x),
            LiteralKind::Char(x) => {
                Val::Char(parser::unquote_char_literal(x).unwrap())
            }
            LiteralKind::Int(x) => {
                Val::Int(x.replace("~", "-").parse().unwrap())
            }
            LiteralKind::Real(x) => {
                Val::Real(x.replace("~", "-").parse().unwrap())
            }
            LiteralKind::String(x) => {
                Val::String(parser::unquote_string(x).unwrap())
            }
            LiteralKind::Unit => Val::Unit,
        }
    }

    /// Resolves a value declaration, mirroring the Java resolveValDecl method.
    fn resolve_val_decl(
        &self,
        val_binds: &[ValBind],
        rec: bool,
    ) -> ResolvedValDecl {
        let composite = val_binds.len() > 1;

        // Flatten patterns and expressions.
        let mut pat_exps = Vec::new();

        for val_bind in val_binds {
            let core_pat = self.resolve_pat(&val_bind.pat);
            let core_expr = self.resolve_expr(&val_bind.expr);

            pat_exps.push(PatExp {
                pat: core_pat,
                expr: core_expr,
            });
        }

        // TODO: Convert recursive to non-recursive if the bound variable is not
        // referenced in its definition.

        // Transform composite patterns.
        let (pat, expr) = if composite {
            // Create tuple pattern and expression.
            let pats: Vec<CorePat> =
                pat_exps.iter().map(|pe| *pe.pat.clone()).collect();
            let exprs: Vec<Box<CoreExpr>> =
                pat_exps.iter().map(|pe| pe.expr.clone()).collect();

            // Create tuple type based on the constituent types.
            let tuple_types: Vec<Type> =
                pats.iter().map(|p| *p.type_().clone()).collect();
            let tuple_type = Box::new(Type::Tuple(tuple_types));

            let tuple_pat = Box::new(CorePat::Tuple(tuple_type.clone(), pats));
            let tuple_expr = Box::new(CoreExpr::Tuple(tuple_type, exprs));

            (tuple_pat, tuple_expr)
        } else {
            let pat_exp = &pat_exps[0];
            (pat_exp.pat.clone(), pat_exp.expr.clone())
        };

        ResolvedValDecl {
            rec,
            composite,
            pat_exps,
            pat,
            expr,
        }
    }

    /// Creates a let expression from a resolved value declaration.
    /// This is the main entry point for the Java toExp equivalent.
    pub fn val_decl_to_let_expr(
        &self,
        val_binds: &[ValBind],
        is_rec: bool,
        result_expr: Box<CoreExpr>,
    ) -> Box<CoreExpr> {
        let resolved_val_decl = self.resolve_val_decl(val_binds, is_rec);
        resolved_val_decl.to_exp(result_expr)
    }

    /// Handles complex patterns by creating intermediate variables.
    /// This mirrors the complex pattern handling in the Java code.
    pub fn handle_complex_pattern(
        &self,
        pat: &CorePat,
        expr: &CoreExpr,
        result_expr: Box<CoreExpr>,
    ) -> Box<CoreExpr> {
        // Check if this is a simple identifier pattern.
        if let CorePat::Identifier(_, _) = pat {
            // Simple case - create direct let binding.
            let val_bind = CoreValBind {
                pat: Box::new(pat.clone()),
                t: pat.type_(),
                expr: Box::new(expr.clone()),
                overload_pat: None,
            };

            let decl = CoreDecl::NonRecVal(Box::new(val_bind));
            return Box::new(CoreExpr::Let(
                result_expr.type_(),
                vec![decl],
                result_expr,
            ));
        }

        // Complex pattern case - allocate intermediate variable.
        let temp_name = format!("temp_{}", std::ptr::addr_of!(pat) as usize);
        let expr_type = expr.type_();

        // Create intermediate identifier pattern.
        let temp_pat =
            Box::new(CorePat::Identifier(expr_type.clone(), temp_name.clone()));

        // Create intermediate binding.
        let temp_val_bind = CoreValBind {
            pat: temp_pat.clone(),
            t: expr_type.clone(),
            expr: Box::new(expr.clone()),
            overload_pat: None,
        };

        // Create identifier expression for temp variable.
        let temp_id = Box::new(CoreExpr::Identifier(expr_type, temp_name));

        // Create case expression to match the complex pattern.
        let match_ = crate::compile::core::Match {
            pat: Box::new(pat.clone()),
            expr: result_expr,
        };

        let case_expr =
            Box::new(CoreExpr::Case(pat.type_(), temp_id, vec![match_]));

        // Create the let expression.
        let decl = CoreDecl::NonRecVal(Box::new(temp_val_bind));
        Box::new(CoreExpr::Let(case_expr.type_(), vec![decl], case_expr))
    }
}
