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
    Match as CoreMatch, Pat as CorePat, PatField as CorePatField,
    TypeBind as CoreTypeBind, ValBind as CoreValBind,
};
use crate::compile::from_builder::FromBuilder;
use crate::compile::inliner::Env;
use crate::compile::library;
use crate::compile::library::{BuiltIn, BuiltInFunction};
use crate::compile::type_resolver::{Resolved, TypeMap, Typed};
use crate::compile::types::{PrimitiveType, Type};
use crate::eval::code::Span;
use crate::eval::val::Val;
use crate::syntax::ast::{
    DatatypeBind, Decl, DeclKind, Expr, ExprKind, Literal, LiteralKind, Match,
    Pat, PatField, PatKind, Step as AstStep, StepKind as AstStepKind,
    Type as AstType, TypeBind, ValBind,
};
use crate::syntax::parser;
use std::collections::{HashSet, VecDeque};

/// Converts an AST to a Core tree.
pub fn resolve(resolved: &Resolved) -> CoreDecl {
    let resolver = Resolver::new(&resolved.type_map, resolved.base_line);
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
    base_line: usize,
}

/// Helper struct representing a pattern-expression pair with position info.
#[derive(Clone, Debug)]
struct PatExpr {
    pat: CorePat,
    expr: CoreExpr,
}

/// Resolved value declaration that mirrors the Java ResolvedValDecl.
#[derive(Clone, Debug)]
struct ResolvedValDecl {
    rec: bool,
    composite: bool,
    pat_exps: Vec<PatExpr>,
    pat: CorePat,
    expr: CoreExpr,
}

impl ResolvedValDecl {
    /// Converts this resolved declaration to a let expression.
    /// This is the Rust translation of the Java toExp method.
    fn to_exp(&self, result_expr: &CoreExpr) -> CoreExpr {
        if self.rec {
            // Recursive case: create RecVal with all bindings.
            let val_binds: Vec<CoreValBind> = self
                .pat_exps
                .iter()
                .map(|pat_exp| CoreValBind {
                    pat: pat_exp.pat.clone(),
                    t: *pat_exp.pat.type_(),
                    expr: pat_exp.expr.clone(),
                    overload_pat: None,
                })
                .collect();

            let decl = CoreDecl::RecVal(val_binds);
            return CoreExpr::Let(
                result_expr.type_(),
                vec![decl],
                Box::new(result_expr.clone()),
            );
        } else if !self.composite && self.pat_exps.len() == 1 {
            // Simple non-recursive case: single identifier pattern.
            let pat_exp = &self.pat_exps[0];
            if let CorePat::Identifier(_, _) = pat_exp.pat {
                let val_bind = CoreValBind {
                    pat: pat_exp.pat.clone(),
                    t: *pat_exp.pat.type_(),
                    expr: pat_exp.expr.clone(),
                    overload_pat: None,
                };

                let decl = CoreDecl::NonRecVal(Box::new(val_bind));
                return CoreExpr::Let(
                    result_expr.type_(),
                    vec![decl],
                    Box::new(result_expr.clone()),
                );
            }
        }

        // Complex pattern case: allocate intermediate variable.
        // Generate a unique name for the intermediate variable.
        let temp_name =
            format!("temp_var_{}", std::ptr::addr_of!(self) as usize);
        let expr_type = self.expr.type_();

        // Create intermediate identifier pattern.
        let temp_pat =
            CorePat::Identifier(expr_type.clone(), temp_name.clone());

        // Create the intermediate binding.
        let temp_val_bind = CoreValBind {
            pat: temp_pat.clone(),
            t: *expr_type.clone(),
            expr: self.expr.clone(),
            overload_pat: None,
        };

        // Create an identifier expression for the temp variable.
        let temp_id = Box::new(CoreExpr::Identifier(expr_type, temp_name));

        // Create the case expression to match the complex pattern.
        let match_ = CoreMatch {
            pat: self.pat.clone(),
            expr: result_expr.clone(),
        };

        let case_expr =
            Box::new(CoreExpr::Case(self.pat.type_(), temp_id, vec![match_]));

        // Create the let expression.
        let decl = CoreDecl::NonRecVal(Box::new(temp_val_bind));
        CoreExpr::Let(case_expr.type_(), vec![decl], case_expr)
    }
}

impl<'a> Resolver<'a> {
    /// Creates a new resolver with the given type map.
    pub fn new(type_map: &'a TypeMap, base_line: usize) -> Self {
        Self {
            type_map,
            base_line,
        }
    }

    /// Returns the type map for this resolver.
    pub fn type_map(&self) -> &TypeMap {
        self.type_map
    }

    /// Resolves an AST declaration to a core declaration.
    pub(crate) fn resolve_decl(&self, decl: &Decl) -> CoreDecl {
        match &decl.kind {
            // lint: sort until '#}' where '##DeclKind::'
            DeclKind::Datatype(datatype_binds) => CoreDecl::Datatype(
                datatype_binds
                    .iter()
                    .map(|db| self.resolve_datatype_bind(db))
                    .collect(),
            ),
            DeclKind::Fun(_) => {
                unreachable!("Should have been desugared already")
            }
            DeclKind::Over(name) => CoreDecl::Over(name.clone()),
            DeclKind::Signature(_) => {
                // Signatures are not yet implemented in the core language.
                // For now, we treat them as no-ops by creating a unit
                // binding.
                // TODO: Implement signature resolution once structures are
                // added.
                let unit_type = Box::new(Type::Primitive(PrimitiveType::Unit));
                CoreDecl::NonRecVal(Box::new(CoreValBind {
                    pat: CorePat::Tuple(unit_type.clone(), vec![]),
                    t: *unit_type.clone(),
                    expr: CoreExpr::Tuple(unit_type, vec![]),
                    overload_pat: None,
                }))
            }
            DeclKind::Type(type_binds) => CoreDecl::Type(
                type_binds
                    .iter()
                    .map(|tb| self.resolve_type_bind(tb))
                    .collect(),
            ),
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
                                t: *pe.pat.type_(),
                                expr: pe.expr.clone(),
                                overload_pat: None,
                            })
                            .collect(),
                    )
                } else if resolved_val_decl.pat_exps.len() == 1 {
                    let pe = &resolved_val_decl.pat_exps[0];
                    CoreDecl::NonRecVal(Box::new(CoreValBind {
                        pat: pe.pat.clone(),
                        t: *pe.pat.type_(),
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
                                t: *pe.pat.type_(),
                                expr: pe.expr.clone(),
                                overload_pat: None,
                            })
                            .collect(),
                    )
                }
            }
        }
    }

    /// Resolves an AST expression to a core expression.
    pub fn resolve_expr(&self, expr: &Expr) -> CoreExpr {
        let t = expr.get_type(self.type_map).unwrap();
        let span =
            Span::from_pest_span(&expr.span.to_pest_span(), self.base_line);
        match &expr.kind {
            // lint: sort until '#}' where '##ExprKind::'
            ExprKind::Aggregate(a0, a1) => CoreExpr::Aggregate(
                t,
                Box::new(self.resolve_expr(a0)),
                Box::new(self.resolve_expr(a1)),
            ),
            ExprKind::AndAlso(a0, a1) => {
                self.call2(t, BuiltInFunction::BoolAndAlso, &span, a0, a1)
            }
            ExprKind::Annotated(expr, _) => self.resolve_expr(expr),
            ExprKind::Append(a0, a1) => {
                self.call2(t, BuiltInFunction::ListAt, &span, a0, a1)
            }
            ExprKind::Apply(func, arg) => CoreExpr::Apply(
                t,
                Box::new(self.resolve_expr(func)),
                Box::new(self.resolve_expr(arg)),
                Span::from_pest_span(&expr.span.to_pest_span(), self.base_line),
            ),
            ExprKind::Caret(a0, a1) => {
                self.call2(t, BuiltInFunction::StringCaret, &span, a0, a1)
            }
            ExprKind::Case(expr, matches) => CoreExpr::Case(
                t,
                Box::new(self.resolve_expr(expr)),
                matches.iter().map(|m| self.resolve_match(m)).collect(),
            ),
            ExprKind::Cons(a0, a1) => {
                self.call2(t, BuiltInFunction::ListCons, &span, a0, a1)
            }
            ExprKind::Current => CoreExpr::Current(t),
            ExprKind::Div(a0, a1) => {
                self.call2(t, BuiltInFunction::IntDiv, &span, a0, a1)
            }
            ExprKind::Divide(a0, a1) => {
                self.call2(t, BuiltInFunction::RealDivide, &span, a0, a1)
            }
            ExprKind::Equal(a0, a1) => {
                match a0.get_type(self.type_map).expect("type").as_ref() {
                    Type::Primitive(PrimitiveType::Int) => {
                        self.call2(t, BuiltInFunction::IntEq, &span, a0, a1)
                    }
                    Type::Primitive(PrimitiveType::Real) => {
                        self.call2(t, BuiltInFunction::RealEq, &span, a0, a1)
                    }
                    Type::Primitive(PrimitiveType::String) => {
                        self.call2(t, BuiltInFunction::StringEq, &span, a0, a1)
                    }
                    Type::Primitive(PrimitiveType::Char) => {
                        self.call2(t, BuiltInFunction::CharEq, &span, a0, a1)
                    }
                    Type::Primitive(PrimitiveType::Bool) => {
                        self.call2(t, BuiltInFunction::BoolEq, &span, a0, a1)
                    }
                    _ => self.call2(t, BuiltInFunction::GEq, &span, a0, a1),
                }
            }
            ExprKind::Exists(steps) => {
                // Translate "exists ..." as "Relational.nonEmpty (from ...)".
                let from_expr = self.resolve_query(steps);
                let fn_type = BuiltInFunction::RelationalNonEmpty.get_type();
                let fn_literal = CoreExpr::Literal(
                    fn_type.clone(),
                    Val::Fn(BuiltInFunction::RelationalNonEmpty),
                );
                CoreExpr::Apply(
                    t,
                    Box::new(fn_literal),
                    Box::new(from_expr),
                    span,
                )
            }
            ExprKind::Fn(matches) => CoreExpr::Fn(
                t,
                matches.iter().map(|m| self.resolve_match(m)).collect(),
            ),
            ExprKind::Forall(steps) => {
                // Translate "forall ... require e" as
                // "Relational.empty (from ... where not e)".
                // Note: The "require e" step is handled in resolve_step
                // and translated to "where not e".
                let from_expr = self.resolve_query(steps);
                let fn_type = BuiltInFunction::RelationalEmpty.get_type();
                let fn_literal = CoreExpr::Literal(
                    fn_type.clone(),
                    Val::Fn(BuiltInFunction::RelationalEmpty),
                );
                CoreExpr::Apply(
                    t,
                    Box::new(fn_literal),
                    Box::new(from_expr),
                    span,
                )
            }
            ExprKind::From(steps) => self.resolve_query(steps),
            ExprKind::GreaterThan(a0, a1) => {
                match a0.get_type(self.type_map).expect("type").as_ref() {
                    Type::Primitive(PrimitiveType::Int) => {
                        self.call2(t, BuiltInFunction::IntGt, &span, a0, a1)
                    }
                    Type::Primitive(PrimitiveType::Real) => {
                        self.call2(t, BuiltInFunction::RealGt, &span, a0, a1)
                    }
                    Type::Primitive(PrimitiveType::String) => {
                        self.call2(t, BuiltInFunction::StringGt, &span, a0, a1)
                    }
                    Type::Primitive(PrimitiveType::Char) => {
                        self.call2(t, BuiltInFunction::CharGt, &span, a0, a1)
                    }
                    _ => todo!("resolve {:?}", a0),
                }
            }
            ExprKind::GreaterThanOrEqual(a0, a1) => {
                match a0.get_type(self.type_map).expect("type").as_ref() {
                    Type::Primitive(PrimitiveType::Int) => {
                        self.call2(t, BuiltInFunction::IntGe, &span, a0, a1)
                    }
                    Type::Primitive(PrimitiveType::Real) => {
                        self.call2(t, BuiltInFunction::RealGe, &span, a0, a1)
                    }
                    Type::Primitive(PrimitiveType::String) => {
                        self.call2(t, BuiltInFunction::StringGe, &span, a0, a1)
                    }
                    Type::Primitive(PrimitiveType::Char) => {
                        self.call2(t, BuiltInFunction::CharGe, &span, a0, a1)
                    }
                    _ => todo!("resolve {:?}", a0),
                }
            }
            ExprKind::Identifier(name) => {
                // Check if this identifier refers to a global built-in
                // function. Global constructors like DESC need to be
                // resolved to literals so they can be compiled properly.
                if let Some(built_in) = library::lookup(name) {
                    match built_in {
                        BuiltIn::Fn(f) => {
                            // Convert the global function/constructor to
                            // a literal.
                            CoreExpr::Literal(t, Val::Fn(f))
                        }
                        BuiltIn::Record(_) => {
                            // Records stay as identifiers.
                            CoreExpr::Identifier(t, name.clone())
                        }
                    }
                } else {
                    // This is a regular identifier (local variable).
                    CoreExpr::Identifier(t, name.clone())
                }
            }
            ExprKind::If(cond, then_expr, else_expr) => {
                // Convert 'if cond then e1 else e2'
                // to 'case cond of true => e1 | _ => e2'.
                let cond_core = self.resolve_expr(cond);
                let then_core = self.resolve_expr(then_expr);
                let else_core = self.resolve_expr(else_expr);

                let bool_type = Box::new(Type::Primitive(PrimitiveType::Bool));
                let true_match = CoreMatch {
                    pat: CorePat::Literal(bool_type.clone(), Val::Bool(true)),
                    expr: then_core,
                };
                let false_match = CoreMatch {
                    pat: CorePat::Wildcard(bool_type.clone()),
                    expr: else_core,
                };

                CoreExpr::Case(
                    t,
                    Box::new(cond_core),
                    vec![true_match, false_match],
                )
            }
            ExprKind::Implies(a0, a1) => {
                self.call2(t, BuiltInFunction::BoolImplies, &span, a0, a1)
            }
            ExprKind::LessThan(a0, a1) => {
                match a0.get_type(self.type_map).expect("type").as_ref() {
                    Type::Primitive(PrimitiveType::Int) => {
                        self.call2(t, BuiltInFunction::IntLt, &span, a0, a1)
                    }
                    Type::Primitive(PrimitiveType::Real) => {
                        self.call2(t, BuiltInFunction::RealLt, &span, a0, a1)
                    }
                    Type::Primitive(PrimitiveType::String) => {
                        self.call2(t, BuiltInFunction::StringLt, &span, a0, a1)
                    }
                    Type::Primitive(PrimitiveType::Char) => {
                        self.call2(t, BuiltInFunction::CharLt, &span, a0, a1)
                    }
                    _ => todo!("resolve {:?}", a0),
                }
            }
            ExprKind::LessThanOrEqual(a0, a1) => {
                match a0.get_type(self.type_map).expect("type").as_ref() {
                    Type::Primitive(PrimitiveType::Int) => {
                        self.call2(t, BuiltInFunction::IntLe, &span, a0, a1)
                    }
                    Type::Primitive(PrimitiveType::Real) => {
                        self.call2(t, BuiltInFunction::RealLe, &span, a0, a1)
                    }
                    Type::Primitive(PrimitiveType::String) => {
                        self.call2(t, BuiltInFunction::StringLe, &span, a0, a1)
                    }
                    Type::Primitive(PrimitiveType::Char) => {
                        self.call2(t, BuiltInFunction::CharLe, &span, a0, a1)
                    }
                    _ => todo!("resolve {:?}", a0),
                }
            }
            ExprKind::Let(decls, body) => {
                let resolved_decls =
                    decls.iter().map(|d| self.resolve_decl(d)).collect();
                CoreExpr::Let(
                    t,
                    resolved_decls,
                    Box::new(self.resolve_expr(body)),
                )
            }
            ExprKind::List(elements) => CoreExpr::List(
                t,
                elements.iter().map(|e| self.resolve_expr(e)).collect(),
            ),
            ExprKind::Literal(l) => {
                CoreExpr::Literal(t, self.resolve_literal(l))
            }
            ExprKind::Minus(a0, a1) => {
                match a0.get_type(self.type_map).expect("type").as_ref() {
                    Type::Primitive(PrimitiveType::Int) => {
                        self.call2(t, BuiltInFunction::IntMinus, &span, a0, a1)
                    }
                    Type::Primitive(PrimitiveType::Real) => {
                        self.call2(t, BuiltInFunction::RealMinus, &span, a0, a1)
                    }
                    _ => todo!("resolve {:?}", a0),
                }
            }
            ExprKind::Mod(a0, a1) => {
                self.call2(t, BuiltInFunction::IntMod, &span, a0, a1)
            }
            ExprKind::Negate(a0) => {
                match a0.get_type(self.type_map).expect("type").as_ref() {
                    Type::Primitive(PrimitiveType::Int) => {
                        self.call1(t, BuiltInFunction::IntNegate, a0, &span)
                    }
                    Type::Primitive(PrimitiveType::Real) => {
                        self.call1(t, BuiltInFunction::RealNegate, a0, &span)
                    }
                    _ => todo!("resolve {:?}", a0),
                }
            }
            ExprKind::NotEqual(a0, a1) => {
                match a0.get_type(self.type_map).expect("type").as_ref() {
                    Type::Primitive(PrimitiveType::Int) => {
                        self.call2(t, BuiltInFunction::IntNe, &span, a0, a1)
                    }
                    Type::Primitive(PrimitiveType::Real) => {
                        self.call2(t, BuiltInFunction::RealNe, &span, a0, a1)
                    }
                    Type::Primitive(PrimitiveType::String) => {
                        self.call2(t, BuiltInFunction::StringNe, &span, a0, a1)
                    }
                    Type::Primitive(PrimitiveType::Char) => {
                        self.call2(t, BuiltInFunction::CharNe, &span, a0, a1)
                    }
                    Type::Primitive(PrimitiveType::Bool) => {
                        self.call2(t, BuiltInFunction::BoolNe, &span, a0, a1)
                    }
                    _ => todo!("resolve {:?}", a0),
                }
            }
            ExprKind::OpSection(name) => {
                // Convert 'op <operator>' to a function literal
                // The type tells us which specific built-in to use
                self.op_section_to_literal(&t, name)
            }
            ExprKind::OrElse(a0, a1) => {
                self.call2(t, BuiltInFunction::BoolOrElse, &span, a0, a1)
            }
            ExprKind::Ordinal => CoreExpr::Ordinal(t),
            ExprKind::Plus(a0, a1) => {
                match a0.get_type(self.type_map).expect("type").as_ref() {
                    Type::Primitive(PrimitiveType::Int) => {
                        self.call2(t, BuiltInFunction::IntPlus, &span, a0, a1)
                    }
                    Type::Primitive(PrimitiveType::Real) => {
                        self.call2(t, BuiltInFunction::RealPlus, &span, a0, a1)
                    }
                    _ => todo!("resolve {:?}", a0),
                }
            }
            ExprKind::Record(_, fields) => {
                let resolved_fields =
                    fields.iter().map(|f| self.resolve_expr(&f.expr)).collect();
                CoreExpr::Tuple(t, resolved_fields)
            }
            ExprKind::RecordSelector(name) => {
                let (param_type, _) = t.expect_fn();
                let slot = param_type.lookup_field(name).unwrap();
                CoreExpr::RecordSelector(t, slot)
            }
            ExprKind::Times(a0, a1) => {
                let a0_type = a0.get_type(self.type_map).expect("type");
                match a0_type.as_ref() {
                    Type::Primitive(PrimitiveType::Int) => {
                        self.call2(t, BuiltInFunction::IntTimes, &span, a0, a1)
                    }
                    Type::Primitive(PrimitiveType::Real) => {
                        self.call2(t, BuiltInFunction::RealTimes, &span, a0, a1)
                    }
                    _ => todo!("resolve {:?}", a0),
                }
            }
            ExprKind::Tuple(elements) => CoreExpr::Tuple(
                t,
                elements.iter().map(|e| self.resolve_expr(e)).collect(),
            ),
            _ => todo!("Unimplemented expression kind: {:?}", expr.kind),
        }
    }

    fn call1(
        &self,
        t: Box<Type>,
        f: BuiltInFunction,
        a0: &Expr,
        span: &Span,
    ) -> CoreExpr {
        let fn_type = f.get_type();
        let fn_literal = CoreExpr::Literal(fn_type.clone(), Val::Fn(f));
        let c0 = self.resolve_expr(a0);
        CoreExpr::Apply(t, Box::new(fn_literal), Box::new(c0), span.clone())
    }

    fn call2(
        &self,
        t: Box<Type>,
        f: BuiltInFunction,
        span: &Span,
        a0: &Expr,
        a1: &Expr,
    ) -> CoreExpr {
        let fn_type = f.get_type();
        let fn_literal = CoreExpr::Literal(fn_type.clone(), Val::Fn(f));
        let c0 = self.resolve_expr(a0);
        let c1 = self.resolve_expr(a1);
        let arg = CoreExpr::new_tuple(&[c0, c1]);
        CoreExpr::Apply(t, Box::new(fn_literal), Box::new(arg), span.clone())
    }

    /// Resolves an AST literal to a core value.
    fn resolve_literal(&self, literal: &Literal) -> Val {
        match &literal.kind {
            // lint: sort until '#}' where '##LiteralKind::'
            LiteralKind::Bool(b) => Val::Bool(*b),
            LiteralKind::Char(c) => {
                Val::Char(parser::unquote_char_literal(c).unwrap())
            }
            LiteralKind::Fn(f) => Val::Fn(*f),
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
        }
    }

    /// Resolves an AST pattern to a core pattern.
    fn resolve_pat(&self, pat: &Pat) -> CorePat {
        let t = pat.get_type(self.type_map).unwrap();

        match &pat.kind {
            // lint: sort until '#}' where '##PatKind::'
            PatKind::Annotated(pat, _) => {
                // For annotated patterns, just resolve the inner pattern
                // since core patterns have embedded types.
                self.resolve_pat(pat)
            }
            PatKind::As(name, sub_pat) => CorePat::As(
                t,
                name.clone(),
                Box::new(self.resolve_pat(sub_pat)),
            ),
            PatKind::Cons(head, tail) => CorePat::Cons(
                t,
                Box::new(self.resolve_pat(head)),
                Box::new(self.resolve_pat(tail)),
            ),
            PatKind::Constructor(name, opt_pat) => {
                let resolved_pat =
                    opt_pat.as_ref().map(|p| Box::new(self.resolve_pat(p)));
                CorePat::Constructor(t, name.clone(), resolved_pat)
            }
            PatKind::Identifier(name) => CorePat::Identifier(t, name.clone()),
            PatKind::List(pats) => {
                let resolved_pats =
                    pats.iter().map(|p| self.resolve_pat(p)).collect();
                CorePat::List(t, resolved_pats)
            }
            PatKind::Literal(literal) => {
                CorePat::Literal(t, self.resolve_literal(literal))
            }
            PatKind::Record(fields, has_ellipsis) => {
                let resolved_fields =
                    fields.iter().map(|f| self.resolve_pat_field(f)).collect();
                CorePat::Record(t, resolved_fields, *has_ellipsis)
            }
            PatKind::Tuple(pats) => {
                let resolved_pats = pats.iter().map(|p| self.resolve_pat(p));
                CorePat::Tuple(t, resolved_pats.collect())
            }
            PatKind::Wildcard => CorePat::Wildcard(t),
        }
    }

    /// Resolves an AST pattern field to a core pattern field.
    fn resolve_pat_field(&self, _field: &PatField) -> CorePatField {
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
            t: *type_,
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
        // For now, just returns a basic type. This would need a proper
        // implementation to convert AST type to core type based on the
        // type resolver.
        Type::Primitive(PrimitiveType::Unit)
    }

    /// Resolves an AST match to a core match.
    fn resolve_match(&self, ast_match: &Match) -> CoreMatch {
        CoreMatch {
            pat: self.resolve_pat(&ast_match.pat),
            expr: self.resolve_expr(&ast_match.expr),
        }
    }

    /// Resolves a From query using FromBuilder for optimization.
    /// This is analogous to the Java FromResolver inner class.
    fn resolve_query(&self, steps: &[AstStep]) -> CoreExpr {
        // Check if the last step is Into.
        // If so, we need to apply the function to the query result.
        if let Some(last_step) = steps.last()
            && let AstStepKind::Into(func_expr) = &last_step.kind
        {
            // Process all steps except the last (Into).
            let mut builder = FromBuilder::new();
            for step in &steps[..steps.len() - 1] {
                self.resolve_step(&mut builder, step);
            }
            let from_result = builder
                .build_simplify()
                .expect("Failed to build From expression");

            // Apply the function to the query result.
            let func = self.resolve_expr(func_expr);

            // Get the result type from the type_map for the
            // function application.
            let result_type = func_expr
                .get_type(self.type_map)
                .expect("INTO function must have a type");

            // Apply the function: f(from_result).
            let span = Span::from_pest_span(
                &last_step.span.to_pest_span(),
                self.base_line,
            );
            return CoreExpr::Apply(
                result_type,
                Box::new(func),
                Box::new(from_result),
                span,
            );
        }

        // Normal query processing (no INTO).
        let mut builder = FromBuilder::new();

        for step in steps {
            self.resolve_step(&mut builder, step);
        }

        builder
            .build_simplify()
            .expect("Failed to build From expression")
    }

    /// Resolves a step in a query, adding it to a [FromBuilder].
    fn resolve_step(&self, builder: &mut FromBuilder, step: &AstStep) {
        match &step.kind {
            // lint: sort until '#}' where '##AstStepKind::'
            AstStepKind::Distinct => {
                builder.distinct();
            }
            AstStepKind::Except(distinct, exprs) => {
                let resolved_exprs: Vec<_> =
                    exprs.iter().map(|e| self.resolve_expr(e)).collect();
                builder.except(*distinct, resolved_exprs);
            }
            AstStepKind::Group(key_expr, aggregate_expr) => {
                // Resolve the group key expression.
                let resolved_key = self.resolve_expr(key_expr);

                // Resolve the aggregate expression if present.
                let resolved_aggregate =
                    aggregate_expr.as_ref().map(|e| self.resolve_expr(e));

                // Add the group step to the builder.
                builder.group(resolved_key, resolved_aggregate);
            }
            AstStepKind::Intersect(distinct, exprs) => {
                let resolved_exprs: Vec<_> =
                    exprs.iter().map(|e| self.resolve_expr(e)).collect();
                builder.intersect(*distinct, resolved_exprs);
            }
            AstStepKind::Into(_) => {
                // INTO is handled at the query level in resolve_query,
                // not as a step. This should not be reached during normal
                // processing.
                panic!(
                    "INTO step should be handled in resolve_query, \
                     not resolve_step"
                )
            }
            AstStepKind::Order(expr) => {
                let resolved_expr = self.resolve_expr(expr);
                builder.order(resolved_expr);
            }
            AstStepKind::Require(expr) => {
                // Translate "require e" as "where not e".
                // This is used in forall queries.
                let resolved_expr = self.resolve_expr(expr);
                let bool_type = Type::Primitive(PrimitiveType::Bool);
                let fn_type = BuiltInFunction::BoolNot.get_type();
                let fn_literal = CoreExpr::Literal(
                    fn_type.clone(),
                    Val::Fn(BuiltInFunction::BoolNot),
                );
                let span = Span::from_pest_span(
                    &step.span.to_pest_span(),
                    self.base_line,
                );
                let negated = CoreExpr::Apply(
                    Box::new(bool_type),
                    Box::new(fn_literal),
                    Box::new(resolved_expr),
                    span,
                );
                builder.where_(negated);
            }
            AstStepKind::Scan(pat, expr, condition) => {
                // Resolve the pattern and expression.
                let resolved_pat = self.resolve_pat(pat);
                let resolved_expr = self.resolve_expr(expr);

                // Resolve the condition if present.
                let resolved_condition =
                    condition.as_ref().map(|c| self.resolve_expr(c));

                // Add the scan step to the builder.
                builder.scan_with_condition(
                    resolved_pat,
                    resolved_expr,
                    resolved_condition,
                );
            }
            AstStepKind::Skip(expr) => {
                let resolved_expr = self.resolve_expr(expr);
                builder.skip(resolved_expr);
            }
            AstStepKind::Take(expr) => {
                let resolved_expr = self.resolve_expr(expr);
                builder.take(resolved_expr);
            }
            AstStepKind::Union(distinct, exprs) => {
                let resolved_exprs: Vec<_> =
                    exprs.iter().map(|e| self.resolve_expr(e)).collect();
                builder.union(*distinct, resolved_exprs);
            }
            AstStepKind::Unorder => {
                builder.unorder();
            }
            AstStepKind::Where(expr) => {
                let resolved_expr = self.resolve_expr(expr);
                builder.where_(resolved_expr);
            }
            AstStepKind::Yield(expr) => {
                let resolved_expr = self.resolve_expr(expr);
                builder.yield_(resolved_expr);
            }
            _ => {
                // For now, fall back to the old resolve_step for unsupported
                // step types.
                todo!("resolve_from_step: {:?}", step.kind)
            }
        }
    }

    /// Converts an AST literal to a core value.
    fn literal_val(literal: &Literal) -> Val {
        match &literal.kind {
            // lint: sort until '#}' where '##LiteralKind::'
            LiteralKind::Bool(x) => Val::Bool(*x),
            LiteralKind::Char(x) => {
                Val::Char(parser::unquote_char_literal(x).unwrap())
            }
            LiteralKind::Fn(_fn_literal) => {
                todo!("Implement Fn literal conversion")
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
        mut rec: bool,
    ) -> ResolvedValDecl {
        let composite = val_binds.len() > 1;

        // Flatten patterns and expressions.
        let mut pat_exps = Vec::new();

        for val_bind in val_binds {
            let core_pat = self.resolve_pat(&val_bind.pat);
            let core_expr = self.resolve_expr(&val_bind.expr);

            pat_exps.push(PatExpr {
                pat: core_pat,
                expr: core_expr,
            });
        }

        // Convert recursive to non-recursive if the bound variable is not
        // referenced in its definition. For example,
        //   val rec inc = fn i => i + 1
        // can be converted to
        //   val inc = fn i => i + 1
        // because "i + 1" does not reference "inc".
        rec = rec && !references(&pat_exps);

        // Transform "let val v1 = E1 and v2 = E2 in E end"
        // to "let val v = (v1, v2) in case v of (E1, E2) => E end"
        let (_pat0, _exp) = if composite {
            let pats: Vec<CorePat> =
                pat_exps.iter().map(|x| x.pat.clone()).collect();
            let exps: Vec<CoreExpr> =
                pat_exps.iter().map(|x| x.expr.clone()).collect();
            let exp = CoreExpr::new_tuple(&exps);
            let pat0 = CorePat::Tuple(exp.type_().clone(), pats);
            (pat0, exp)
        } else {
            let pat_exp = &pat_exps[0];
            (pat_exp.pat.clone(), pat_exp.expr.clone())
        };

        // Transform composite patterns.
        let (ref pat, expr) = if composite {
            // Create tuple pattern and expression.
            let pats: Vec<CorePat> =
                pat_exps.iter().map(|pe| pe.pat.clone()).collect();
            let exprs: Vec<CoreExpr> =
                pat_exps.iter().map(|pe| pe.expr.clone()).collect();

            // Create a tuple type based on the constituent types.
            let tuple_expr = CoreExpr::new_tuple(&exprs);
            let tuple_pat = CorePat::Tuple(tuple_expr.type_().clone(), pats);

            (tuple_pat, tuple_expr)
        } else {
            let pat_exp = &pat_exps[0];
            (pat_exp.pat.clone(), pat_exp.expr.clone())
        };

        ResolvedValDecl {
            rec,
            composite,
            pat_exps,
            pat: pat.clone(),
            expr,
        }
    }

    /// Creates a let expression from a resolved value declaration.
    /// This is the main entry point for the Java toExp equivalent.
    pub fn val_decl_to_let_expr(
        &self,
        val_binds: &[ValBind],
        is_rec: bool,
        result_expr: &CoreExpr,
    ) -> CoreExpr {
        let resolved_val_decl = self.resolve_val_decl(val_binds, is_rec);
        resolved_val_decl.to_exp(result_expr)
    }

    /// Handles complex patterns by creating intermediate variables.
    /// This mirrors the complex pattern handling in the Java code.
    pub fn handle_complex_pattern(
        &self,
        pat: &CorePat,
        expr: &CoreExpr,
        result_expr: &CoreExpr,
    ) -> CoreExpr {
        // Check if this is a simple identifier pattern.
        if let CorePat::Identifier(_, _) = pat {
            // Simple case - create direct let binding.
            let val_bind = CoreValBind {
                pat: pat.clone(),
                t: *pat.type_(),
                expr: expr.clone(),
                overload_pat: None,
            };

            let decl = CoreDecl::NonRecVal(Box::new(val_bind));
            return CoreExpr::Let(
                result_expr.type_(),
                vec![decl],
                Box::new(result_expr.clone()),
            );
        }

        // Complex pattern case - allocate intermediate variable.
        let temp_name = format!("temp_{}", std::ptr::addr_of!(pat) as usize);
        let expr_type = expr.type_();

        // Create intermediate identifier pattern.
        let temp_pat =
            CorePat::Identifier(expr_type.clone(), temp_name.clone());

        // Create intermediate binding.
        let temp_val_bind = CoreValBind {
            pat: temp_pat.clone(),
            t: *expr_type.clone(),
            expr: expr.clone(),
            overload_pat: None,
        };

        // Create identifier expression for temp variable.
        let temp_id = Box::new(CoreExpr::Identifier(expr_type, temp_name));

        // Create a case expression to match the complex pattern.
        let match_ = CoreMatch {
            pat: pat.clone(),
            expr: result_expr.clone(),
        };

        let case_expr =
            Box::new(CoreExpr::Case(pat.type_(), temp_id, vec![match_]));

        // Create the let expression.
        let decl = CoreDecl::NonRecVal(Box::new(temp_val_bind));
        CoreExpr::Let(case_expr.type_(), vec![decl], case_expr)
    }

    /// Converts an operator section to a function literal.
    /// After type resolution, we know the concrete type, so we can
    /// directly map to the specific built-in function.
    fn op_section_to_literal(&self, fn_type: &Type, op_name: &str) -> CoreExpr {
        match fn_type {
            Type::Multi(_types) => {
                // Overloaded function - create GNegate, GPlus, etc.
                let builtin = self.multi_op_to_builtin(op_name);
                let fn_val = Val::Fn(builtin);
                let fn_lit_type = builtin.get_type();
                CoreExpr::Literal(fn_lit_type, fn_val)
            }
            Type::Forall(_inner_type, _param_count) => {
                // Polymorphic function
                let builtin = self.multi_op_to_builtin(op_name);
                let fn_val = Val::Fn(builtin);
                let fn_lit_type = builtin.get_type();
                CoreExpr::Literal(fn_lit_type, fn_val)
            }
            Type::Fn(param_type, _result_type) => {
                let builtin = match param_type.as_ref() {
                    Type::Variable(_) => {
                        // Type variable means it's polymorphic
                        self.multi_op_to_builtin(op_name)
                    }
                    Type::Tuple(args) if args.len() == 2 => {
                        // Binary operator
                        match &args[0] {
                            Type::Variable(_) => {
                                self.multi_op_to_builtin(op_name)
                            }
                            _ => self.binary_op_to_builtin(op_name, &args[0]),
                        }
                    }
                    _ => {
                        // Unary operator
                        self.unary_op_to_builtin(op_name, param_type)
                    }
                };
                let fn_val = Val::Fn(builtin);
                let fn_lit_type = builtin.get_type();
                CoreExpr::Literal(fn_lit_type, fn_val)
            }
            _ => todo!("OpSection with non-function type: {:?}", fn_type),
        }
    }

    /// Maps a binary operator and type to the corresponding built-in
    /// function.
    fn binary_op_to_builtin(
        &self,
        op_name: &str,
        arg_type: &Type,
    ) -> BuiltInFunction {
        use BuiltInFunction::{
            IntDiv, IntGe, IntGt, IntLe, IntLt, IntMinus, IntMod, IntPlus,
            IntTimes, ListAt, ListCons, RealDivide, RealGe, RealGt, RealLe,
            RealLt, RealMinus, RealPlus, RealTimes, StringCaret, StringGe,
            StringGt, StringLe, StringLt,
        };
        match (op_name, arg_type) {
            // Integer operators
            ("+", Type::Primitive(PrimitiveType::Int)) => IntPlus,
            ("-", Type::Primitive(PrimitiveType::Int)) => IntMinus,
            ("*", Type::Primitive(PrimitiveType::Int)) => IntTimes,
            ("div", Type::Primitive(PrimitiveType::Int)) => IntDiv,
            ("mod", Type::Primitive(PrimitiveType::Int)) => IntMod,
            ("<", Type::Primitive(PrimitiveType::Int)) => IntLt,
            ("<=", Type::Primitive(PrimitiveType::Int)) => IntLe,
            (">", Type::Primitive(PrimitiveType::Int)) => IntGt,
            (">=", Type::Primitive(PrimitiveType::Int)) => IntGe,

            // Real operators
            ("+", Type::Primitive(PrimitiveType::Real)) => RealPlus,
            ("-", Type::Primitive(PrimitiveType::Real)) => RealMinus,
            ("*", Type::Primitive(PrimitiveType::Real)) => RealTimes,
            ("/", Type::Primitive(PrimitiveType::Real)) => RealDivide,
            ("<", Type::Primitive(PrimitiveType::Real)) => RealLt,
            ("<=", Type::Primitive(PrimitiveType::Real)) => RealLe,
            (">", Type::Primitive(PrimitiveType::Real)) => RealGt,
            (">=", Type::Primitive(PrimitiveType::Real)) => RealGe,

            // String operators
            ("^", Type::Primitive(PrimitiveType::String)) => StringCaret,
            ("<", Type::Primitive(PrimitiveType::String)) => StringLt,
            ("<=", Type::Primitive(PrimitiveType::String)) => StringLe,
            (">", Type::Primitive(PrimitiveType::String)) => StringGt,
            (">=", Type::Primitive(PrimitiveType::String)) => StringGe,

            // List operators - these work on any list type
            ("::", Type::List(_)) => ListCons,
            ("@", Type::List(_)) => ListAt,

            _ => todo!(
                "binary operator '{}' with type {:?} not supported",
                op_name,
                arg_type
            ),
        }
    }

    /// Maps a unary operator and type to the corresponding built-in
    /// function.
    fn unary_op_to_builtin(
        &self,
        op_name: &str,
        arg_type: &Type,
    ) -> BuiltInFunction {
        use BuiltInFunction::{BoolNot, IntNegate, RealNegate};
        match (op_name, arg_type) {
            ("~", Type::Primitive(PrimitiveType::Int)) => IntNegate,
            ("~", Type::Primitive(PrimitiveType::Real)) => RealNegate,
            ("not", Type::Primitive(PrimitiveType::Bool)) => BoolNot,
            _ => todo!(
                "unary operator '{}' with type {:?} not supported",
                op_name,
                arg_type
            ),
        }
    }

    /// Maps an overloaded operator to its general (polymorphic) built-in
    /// function.
    fn multi_op_to_builtin(&self, op_name: &str) -> BuiltInFunction {
        use BuiltInFunction::{
            GEq, GGe, GGt, GLe, GLt, GMinus, GNe, GNegate, GPlus, GTimes,
        };
        match op_name {
            "~" => GNegate,
            "+" => GPlus,
            "*" => GTimes,
            "-" => GMinus,
            "<" => GLt,
            "<=" => GLe,
            ">" => GGt,
            ">=" => GGe,
            "=" => GEq,
            "<>" => GNe,
            _ => todo!("overloaded operator '{}' not supported", op_name),
        }
    }
}

/// Returns whether any of the expressions in `exps` references any of
/// the variables defined in `pats`.
///
/// This method is used to decide whether it is safe to convert a recursive
/// declaration into a non-recursive one.
fn references(pat_exprs: &[PatExpr]) -> bool {
    let finder = ReferenceFinder::new(&Env::empty(), VecDeque::new());

    // Collect references from expressions
    for _pat_expr in pat_exprs {
        // TODO: Implement expression visitor pattern for collecting references
        // For now, we'll assume no references are found
    }

    // Collect definitions from patterns
    let mut def_set = HashSet::new();
    for pat_exp in pat_exprs {
        pat_exp
            .pat
            .for_each_id_pat(&mut |(_, name): (&Type, &str)| {
                def_set.insert(name.to_string());
            });
    }

    finder.ref_set.intersection(&def_set).count() > 0
}

struct ReferenceFinder {
    ref_set: HashSet<String>,
}

impl ReferenceFinder {
    fn new(_env: &Env, _from_stack: VecDeque<()>) -> Self {
        ReferenceFinder {
            ref_set: HashSet::new(),
        }
    }
}
