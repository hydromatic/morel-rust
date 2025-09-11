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

#![allow(clippy::ptr_arg)]
#![allow(clippy::needless_lifetimes)]
#![allow(clippy::needless_borrow)]
#![allow(clippy::collapsible_if)]

use crate::compile::type_env::{EmptyTypeEnv, TypeEnv, TypeSchemeResolver};
use crate::compile::types;
use crate::compile::types::Label;
use crate::compile::types::{PrimitiveType, Subst, Type, TypeVariable};
use crate::compile::unifier::{NullTracer, Op, Sequence, Term, Unifier, Var};
use crate::syntax::ast::{
    Decl, DeclKind, Expr, ExprKind, FunBind, LabeledExpr, LiteralKind, Match,
    MorelNode, Pat, PatField, PatKind, Span, Statement, StatementKind,
    Type as AstType, TypeField, TypeKind, TypeScheme, ValBind,
};
use std::cell::OnceCell;
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::fmt::{Debug, Display, Formatter};
use std::iter::zip;
use std::rc::Rc;
use types::ordinal_names;

/// A field of this name indicates that a record type is progressive.
pub const PROGRESSIVE_LABEL: &str = "z$dummy";

/// Result of type resolution containing the resolved AST and type information.
#[derive(Debug, Clone)]
pub struct Resolved {
    pub decl: Decl,
    pub type_map: TypeMap,
    pub bindings: Vec<TypeBinding>,
}

/// Maps AST nodes to their resolved types.
#[derive(Debug, Clone)]
pub struct TypeMap {
    // Maps from AST node ID to unifier variable.
    pub node_var_map: HashMap<i32, Rc<Var>>,
    // Maps from unifier variables to terms.
    pub var_term_map: HashMap<Rc<Var>, Term>,
}

impl TypeMap {
    pub fn new(node_var_map: &HashMap<i32, Rc<Var>>) -> Self {
        Self {
            node_var_map: node_var_map.clone(),
            var_term_map: HashMap::new(),
        }
    }

    /// Gets the type for an AST node.
    pub fn get_type(&self, id: i32) -> Option<Box<Type>> {
        if let Some(var) = self.node_var_map.get(&id)
            && let Some(term) = self.var_term_map.get(var)
        {
            let mut c = TermToTypeConverter {
                type_map: self,
                var_map: BTreeMap::new(),
            };
            return Some(c.term_type(term));
        }
        None
    }

    /// Ensures that a type is closed.
    pub fn ensure_closed(&self, _type_: Type) -> Type {
        todo!()
    }
}

pub trait Typed {
    fn get_type(&self, type_map: &TypeMap) -> Option<Box<Type>>;
}

impl Typed for Expr {
    fn get_type(&self, type_map: &TypeMap) -> Option<Box<Type>> {
        type_map.get_type(self.id?)
    }
}

impl Typed for ValBind {
    fn get_type(&self, type_map: &TypeMap) -> Option<Box<Type>> {
        self.expr.get_type(type_map)
    }
}

impl Typed for Pat {
    fn get_type(&self, type_map: &TypeMap) -> Option<Box<Type>> {
        type_map.get_type(self.id?)
    }
}

struct TermToTypeConverter<'a> {
    type_map: &'a TypeMap,
    var_map: BTreeMap<i32, Box<Type>>,
}

impl<'a> TermToTypeConverter<'a> {
    /// Converts a term to a type.
    fn term_type(&mut self, term: &Term) -> Box<Type> {
        match term {
            Term::Sequence(sequence) => match sequence.op.name.as_str() {
                "bool" | "char" | "int" | "real" | "string" | "unit" => {
                    let primitive_type =
                        PrimitiveType::parse_name(&sequence.op.name).unwrap();
                    Box::new(Type::Primitive(primitive_type))
                }
                "fn" => {
                    assert_eq!(sequence.terms.len(), 2);
                    let param_type = self.term_type(&sequence.terms[0]);
                    let result_type = self.term_type(&sequence.terms[1]);
                    Box::new(Type::Fn(param_type, result_type))
                }
                "list" => {
                    assert_eq!(sequence.terms.len(), 1);
                    let type_ = self.term_type(&sequence.terms[0]);
                    Box::new(Type::List(type_))
                }
                "option" => {
                    assert_eq!(sequence.terms.len(), 1);
                    let args = vec![*self.term_type(&sequence.terms[0])];
                    Box::new(Type::Named(args, sequence.op.name.clone()))
                }
                "tuple" => {
                    let types = sequence
                        .terms
                        .iter()
                        .map(|t| *(self.term_type(t)))
                        .collect();
                    Box::new(Type::Tuple(types))
                }
                s if s.starts_with("record") => {
                    let labels = TypeResolver::field_list(sequence).unwrap();
                    let mut fields = BTreeMap::<Label, Type>::new();
                    for (label, term) in zip(labels, sequence.terms.iter()) {
                        fields
                            .insert(Label::from(label), *self.term_type(term));
                    }
                    Box::new(Type::Record(false, fields))
                }
                _ => todo!("{:?}", term),
            },
            Term::Variable(v) => {
                if let Some(term) = self.type_map.var_term_map.get(v) {
                    self.term_type(term)
                } else {
                    let id = self.var_map.len();
                    self.var_map
                        .entry(v.id)
                        .or_insert_with(|| {
                            Box::new(Type::Variable(TypeVariable { id }))
                        })
                        .clone()
                }
            }
        }
    }
}

impl Display for TypeMap {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "node-vars {:?} var-terms {:?}",
            self.node_var_map, self.var_term_map
        )
    }
}

/// Binding of a name to a type.
#[derive(Debug, Clone)]
pub struct TypeBinding {
    pub name: String,
    pub resolved_type: Type,
    pub kind: BindingKind,
}

/// Kind of binding (value, type constructor, etc.).
#[derive(Debug, Clone, PartialEq)]
pub enum BindingKind {
    Val,
    Type,
    Constructor,
}

/// Main type resolver that deduces types for ML expressions.
#[allow(dead_code)]
pub struct TypeResolver {
    warnings: Vec<Warning>,

    /// Mapping from node ids (patterns and expressions) to the unifier variable
    /// that holds the node's type.
    node_var_map: HashMap<i32, Rc<Var>>,

    /// List of (variable, term) pairs where the term is equivalent to the
    /// variable. Will be the input to the unifier.
    terms: Vec<(Rc<Var>, Term)>,
    unifier: Unifier,
    next_id: i32,

    /// Cached operators for common type-constructors.
    list_op: Rc<Op>,
    bag_op: Rc<Op>,
    tuple_op: Rc<Op>,
    arg_op: Rc<Op>,
    overload_op: Rc<Op>,
    record_op: Rc<Op>,
    fn_op: Rc<Op>,
}

impl Default for TypeResolver {
    fn default() -> Self {
        Self::new()
    }
}

#[allow(dead_code)]
impl TypeResolver {
    /// Creates a new type resolver.
    pub fn new() -> Self {
        let mut unifier = Unifier::new(true);
        let list_op = unifier.op("list", Some(1));
        let bag_op = unifier.op("bag", Some(1));
        let tuple_op = unifier.op("tuple", None);
        let arg_op = unifier.op("$arg", None);
        let overload_op = unifier.op("overload", None);
        let record_op = unifier.op("record", None);
        let fn_op = unifier.op("fn", Some(2));
        Self {
            warnings: Vec::new(),
            node_var_map: HashMap::new(),
            terms: Vec::new(),
            next_id: 0,
            unifier,
            list_op,
            bag_op,
            tuple_op,
            arg_op,
            overload_op,
            record_op,
            fn_op,
        }
    }

    /// Allocates a unique ID for AST nodes.
    fn next_id(&mut self) -> i32 {
        self.next_id += 1;
        self.next_id - 1
    }

    /// Deduces a statement's type.
    ///
    /// A statement is represented by an AST node and may be an expression
    /// or a declaration.
    pub fn deduce_type(
        &mut self,
        env: &dyn TypeEnv,
        statement: &Statement,
    ) -> Resolved {
        self.terms.clear();

        let decl = ensure_decl(statement);
        let mut term_map = Vec::new();
        let decl2 = self.deduce_decl_type(env, &decl, &mut term_map);

        // Create term pairs for unification
        let term_pairs: Vec<(Term, Term)> = self
            .terms
            .iter()
            .map(|(var, term)| (term.clone(), Term::Variable(var.clone())))
            .collect();

        let substitution =
            match self.unifier.unify(term_pairs.as_ref(), &NullTracer) {
                Ok(x) => x,
                Err(x) => {
                    panic!("Unification failed: {}", x)
                }
            };

        // Create a map with the results of unification.
        let mut type_map = TypeMap::new(&self.node_var_map);
        for (v, term) in substitution.substitutions {
            type_map.var_term_map.insert(v, term);
        }

        Resolved {
            decl: decl2,
            type_map,
            bindings: Vec::new(), // TODO: populate bindings
        }
    }

    /// Deduces a declaration's type.
    fn deduce_decl_type(
        &mut self,
        env: &dyn TypeEnv,
        decl: &Decl,
        term_map: &mut Vec<(String, Term)>,
    ) -> Decl {
        match &decl.kind {
            DeclKind::Val(rec, inst, val_binds) => {
                let kind = &self.deduce_val_decl_type(
                    env, *rec, *inst, val_binds, term_map,
                );
                Decl {
                    kind: kind.clone(),
                    span: decl.span.clone(),
                    id: Some(self.next_id()),
                }
            }
            DeclKind::Fun(fun_binds) => {
                let val_decl = self.convert_fun_to_val(env, fun_binds);
                self.deduce_decl_type(env, &val_decl, term_map)
            }
            _ => todo!("{:?}", decl.kind),
        }
    }

    /// Converts a function declaration to a value declaration. In other words,
    /// `fun` is syntactic sugar, and this is the de-sugaring machine.
    ///
    /// For example, `fun inc x = x + 1` becomes `val rec inc = fn x => x + 1`.
    ///
    /// If there are multiple arguments, there is one `fn` for each
    /// argument: `fun sum x y = x + y` becomes `val rec sum = fn x =>
    /// fn y => x + y`.
    ///
    /// If there are multiple clauses, we generate `case`:
    ///
    /// ```sml
    /// fun gcd a 0 = a | gcd a b = gcd b (a mod b)
    /// ```
    ///
    /// becomes
    ///
    /// ```sml
    /// val rec gcd = fn x => fn y =>
    /// case (x, y) of
    ///     (a, 0) => a
    ///   | (a, b) = gcd b (a mod b)
    /// ```
    fn convert_fun_to_val(
        &mut self,
        env: &dyn TypeEnv,
        fun_binds: &[FunBind],
    ) -> Box<Decl> {
        let val_bind_list: Vec<ValBind> = fun_binds
            .iter()
            .map(|fun_bind| self.convert_fun_bind_to_val_bind(env, fun_bind))
            .collect();

        let x = DeclKind::Val(true, false, val_bind_list);
        let span = Span::sum(fun_binds, |b| b.span.clone());
        Box::new(x.spanned(&span.unwrap()))
    }

    fn convert_fun_bind_to_val_bind(
        &mut self,
        _env: &dyn TypeEnv,
        fun_bind: &FunBind,
    ) -> ValBind {
        let vars: Vec<Pat>;
        let mut expr: Box<Expr>;
        let mut type_annotation: Option<Box<AstType>> = None;
        let span = fun_bind.span.clone();

        if fun_bind.matches.len() == 1 {
            let fun_match = &fun_bind.matches[0];
            expr = fun_match.expr.clone();
            vars = fun_match.pats.clone();
            type_annotation = fun_match.type_.clone();
        } else {
            let var_names: Vec<String> = (0..fun_bind.matches[0].pats.len())
                .map(|index| format!("v{}", index))
                .collect();

            vars = var_names
                .iter()
                .map(|v| PatKind::Identifier(v.clone()).spanned(&span))
                .collect();

            let mut match_list = Vec::new();
            let mut prev_return_type: Option<Box<AstType>> = None;

            for fun_match in &fun_bind.matches {
                match_list.push(Match {
                    pat: Box::new(self.pat_tuple(&span, &fun_match.pats)),
                    expr: fun_match.expr.clone(),
                });

                if fun_match.type_.is_some() {
                    if let (Some(prev_type), Some(curr_type)) =
                        (&prev_return_type, &fun_match.type_)
                        && prev_type.kind != curr_type.kind
                    {
                        let combined_span =
                            prev_type.span.union(&fun_match.span);
                        self.warnings.push(Warning {
                            span: combined_span.clone(),
                            message: W_INCONSISTENT_PARAMETERS.to_string(),
                        });
                    }
                    prev_return_type = Some(fun_match.type_.clone().unwrap());
                }
            }

            let x =
                ExprKind::Case(self.id_tuple(&span, &var_names), match_list);
            expr = Box::new(x.spanned(&span));
        }

        for var in vars.iter().rev() {
            let pat = Box::new(var.clone());
            let kind = ExprKind::Fn(vec![Match { pat, expr }]);
            expr = Box::new(kind.spanned(&span));
        }

        ValBind {
            pat: Box::new(
                PatKind::Identifier(fun_bind.name.clone()).spanned(&span),
            ),
            type_annotation,
            expr,
            overload_pat: None,
        }
    }

    fn all_the_same<T: PartialEq>(list: &[T]) -> bool {
        list.iter().all(|x| list.iter().all(|y| x == y))
    }

    /// Converts a list of variable names to a variable or tuple.
    ///
    /// For example, `["x"]` becomes `x` (an `Id`), and `["x", "y"]`
    /// becomes `(x, y)` (a `Tuple` of `Id`s).
    fn id_tuple(&self, span: &Span, vars: &[String]) -> Box<Expr> {
        let id_list: Vec<Box<Expr>> = vars
            .iter()
            .map(|v| {
                Box::new(ExprKind::Identifier(v.to_string()).spanned(span))
            })
            .collect();

        if id_list.len() == 1 {
            id_list.into_iter().next().unwrap()
        } else {
            Box::new(ExprKind::Tuple(id_list).spanned(span))
        }
    }

    /// Converts a list of patterns to a singleton pattern or tuple pattern.
    fn pat_tuple(&self, span: &Span, pat_list: &[Pat]) -> Pat {
        if pat_list.is_empty() {
            PatKind::Literal(LiteralKind::Unit.spanned(span)).spanned(span)
        } else if pat_list.len() == 1 {
            pat_list.first().unwrap().clone()
        } else {
            PatKind::Tuple(
                pat_list.iter().map(|p| Box::new(p.clone())).collect(),
            )
            .spanned(&Span::sum(pat_list, |p| p.span.clone()).unwrap())
        }
    }

    fn deduce_val_decl_type(
        &mut self,
        env: &dyn TypeEnv,
        rec: bool,
        inst: bool,
        val_binds: &[ValBind],
        term_map: &mut Vec<(String, Term)>,
    ) -> DeclKind {
        let mut env_holder = env.builder();
        let mut map0 = Vec::new();

        // First pass: create variables for each binding
        for b in val_binds {
            map0.push((b, OnceCell::new()));
        }

        // Second pass: if recursive, bind identifiers to their types
        for (val_bind, v_pat_supplier) in &map0 {
            if rec {
                if let PatKind::Identifier(name) = &val_bind.pat.kind {
                    let var =
                        v_pat_supplier.get_or_init(|| self.variable()).clone();
                    env_holder.push(name.clone(), Term::Variable(var));
                }
            }
        }

        let env2 = env_holder.build();
        let mut val_binds2 = Vec::new();

        // Third pass: deduce types for each binding
        for (val_bind, v_supplier) in map0 {
            let var = v_supplier.get_or_init(|| self.variable()).clone();
            let val_bind2 =
                self.deduce_val_bind_type(&*env2, &val_bind, term_map, &var);
            val_binds2.push(val_bind2);
        }

        DeclKind::Val(rec, inst, val_binds2)
    }

    /// Converts a type AST node to a type term.
    fn deduce_type_type(
        &mut self,
        env: &dyn TypeEnv,
        type_: &AstType,
        v: &Rc<Var>,
    ) -> Box<AstType> {
        let mut converter = TypeToTermConverter {
            type_resolver: self,
            env,
            type_variables: BTreeMap::new(),
        };
        converter.type_term(type_, &Subst::Empty, v)
    }

    fn deduce_type_scheme(
        &mut self,
        env: &dyn TypeEnv,
        type_scheme: &TypeScheme,
        v: &Rc<Var>,
    ) -> Box<AstType> {
        let mut type_variables = BTreeMap::new();
        for i in 0..type_scheme.var_count {
            let type_variable = Box::new(TypeVariable::new(i));
            type_variables.insert(type_variable.name(), type_variable);
        }
        let mut converter = TypeToTermConverter {
            type_resolver: self,
            env,
            type_variables,
        };
        converter.type_scheme_term(type_scheme, v)
    }

    /// Deduces an expression's type.
    /// Associates the type with variable `v` and returns the modified
    /// expression.
    fn deduce_expr_type<'a>(
        &mut self,
        env: &dyn TypeEnv,
        expr: &Expr,
        v: &'a Rc<Var>,
    ) -> Box<Expr> {
        match &expr.kind {
            ExprKind::Literal(lit) => {
                let resolved_type = Self::literal_type(&lit.kind);
                self.primitive_term(&resolved_type, v);
                self.reg_expr(&expr.kind, &expr.span, expr.id, v)
            }
            ExprKind::Identifier(name) => {
                let term = env.get(name, self).unwrap_or_else(|| {
                    todo!("identifier '{}' not found", name)
                });
                self.equiv(&term, v);
                self.reg_expr(&expr.kind, &expr.span, expr.id, v)
            }
            ExprKind::List(expr_list) => {
                let v_element = self.variable();
                if expr_list.is_empty() {
                    // Don't link v0 to anything. It becomes a type variable.
                } else {
                    self.deduce_expr_type(
                        env,
                        expr_list.first().unwrap(),
                        &v_element,
                    );
                    for expr in expr_list.iter().skip(1) {
                        let v2 = self.variable();
                        self.deduce_expr_type(env, expr, &v2);
                        self.equiv(&Term::Variable(v2), &v_element.clone());
                    }
                }
                self.list_term(Term::Variable(v_element), v);
                self.reg_expr(&expr.kind, &expr.span, expr.id, v)
            }
            ExprKind::Record(with_expr, labeled_expr_list) => {
                // First, create a copy of expressions and their labels,
                // sorted into the order that they will appear in the record
                // type.
                let mut label_expr_map: BTreeMap<Label, LabeledExpr> =
                    BTreeMap::new();
                for labeled_expr in labeled_expr_list {
                    let label = if let Some(label_name) = &labeled_expr.label {
                        Label::from(&label_name.name)
                    } else {
                        // Field has no label, so generate a temporary name.
                        // FIXME The temporary name might overlap with later
                        // explicit labels, and certain types of expressions
                        // have an implicit label.
                        let ordinal = label_expr_map.len() + 1;
                        Label::Ordinal(ordinal)
                    };
                    label_expr_map.insert(label, labeled_expr.clone());
                }

                // Second, duplicate the record expression and its labels.
                let mut label_terms: BTreeMap<Label, Term> = BTreeMap::new();
                let mut labeled_expr_list2 = Vec::new();
                for (label, labeled_expr) in &label_expr_map {
                    let v2 = self.variable();
                    let e2 =
                        self.deduce_expr_type(env, &labeled_expr.expr, &v2);
                    labeled_expr_list2.push(LabeledExpr {
                        expr: e2,
                        ..labeled_expr.clone()
                    });
                    label_terms.insert(label.clone(), Term::Variable(v2));
                }
                self.record_term(&label_terms, v);
                let x = ExprKind::Record(with_expr.clone(), labeled_expr_list2);
                self.reg_expr(&x, &expr.span, expr.id, v)
            }
            ExprKind::Tuple(expr_list) => {
                let mut terms = Vec::new();
                let mut expr_list2 = Vec::new();
                for e in expr_list {
                    let v2 = self.variable();
                    let e2 = self.deduce_expr_type(env, e, &v2);
                    expr_list2.push(e2);
                    terms.push(Term::Variable(v2));
                }
                self.tuple_term(&terms, v);
                self.reg_expr(
                    &ExprKind::Tuple(expr_list2),
                    &expr.span,
                    expr.id,
                    v,
                )
            }
            ExprKind::Fn(matches) => {
                let mut matches2 = Vec::new();
                let v_param = self.variable();
                let v_result = self.variable();
                for match_ in matches {
                    matches2.push(
                        self.deduce_match_type(
                            env, match_, &v_param, &v_result,
                        ),
                    );
                }
                self.fn_term(&v_param, &v_result, v);
                let fn2 = &ExprKind::Fn(matches2);
                self.reg_expr(fn2, &expr.span, expr.id, v)
            }
            ExprKind::Apply(left, right) => {
                let (left2, right2) =
                    self.deduce_apply_type(env, &left, &right, v);
                let apply2 = ExprKind::Apply(left2, right2);
                self.reg_expr(&apply2, &expr.span, expr.id, v)
            }
            ExprKind::Let(decl_list, expr) => {
                let mut term_map = Vec::new();
                let mut decl_list2 = Vec::new();
                for decl in decl_list {
                    let decl2 = self.deduce_decl_type(env, decl, &mut term_map);
                    decl_list2.push(decl2);
                }
                let env2 = env.bind_all(term_map.as_ref());
                let expr2 = self.deduce_expr_type(&*env2, expr, v);
                let x = ExprKind::Let(decl_list2, expr2);
                self.reg_expr(&x, &expr.span, expr.id, v)
            }
            ExprKind::If(a0, a1, a2) => {
                let (a02, a12, a22) =
                    self.deduce_call3_type(env, "op if", a0, a1, a2, v);
                let x = ExprKind::If(a02, a12, a22);
                self.reg_expr(&x, &expr.span, expr.id, v)
            }
            ExprKind::Case(e, match_list) => {
                let v_e = self.unifier.variable();
                let e2 = self.deduce_expr_type(env, e, &v_e);
                let mut label_names = BTreeSet::new();

                if let Some(sequence) = self.variable_to_sequence(&v_e)
                    && let Some(field_list) = Self::field_list(&sequence)
                {
                    label_names.extend(field_list);
                }

                let match_list2 = self.deduce_match_list_type(
                    env,
                    &match_list,
                    &mut label_names,
                    &v_e,
                    v,
                );

                let x = ExprKind::Case(e2, match_list2);
                self.reg_expr(&x, &expr.span, expr.id, v)
            }
            ExprKind::AndAlso(left, right) => {
                let (left2, right2) =
                    self.deduce_call2_type(env, "op andalso", left, right, v);
                let x = ExprKind::AndAlso(left2, right2);
                self.reg_expr(&x, &expr.span, expr.id, v)
            }
            ExprKind::OrElse(left, right) => {
                let (left2, right2) =
                    self.deduce_call2_type(env, "op orelse", left, right, v);
                let x = ExprKind::OrElse(left2, right2);
                self.reg_expr(&x, &expr.span, expr.id, v)
            }
            ExprKind::Implies(left, right) => {
                let (left2, right2) =
                    self.deduce_call2_type(env, "op implies", left, right, v);
                let x = ExprKind::Implies(left2, right2);
                self.reg_expr(&x, &expr.span, expr.id, v)
            }
            ExprKind::LessThan(left, right) => {
                let (left2, right2) =
                    self.deduce_call2_type(env, "op <", left, right, v);
                let x = ExprKind::LessThan(left2, right2);
                self.reg_expr(&x, &expr.span, expr.id, v)
            }
            ExprKind::GreaterThan(left, right) => {
                let (left2, right2) =
                    self.deduce_call2_type(env, "op >", left, right, v);
                let x = ExprKind::GreaterThan(left2, right2);
                self.reg_expr(&x, &expr.span, expr.id, v)
            }
            ExprKind::LessThanOrEqual(left, right) => {
                let (left2, right2) =
                    self.deduce_call2_type(env, "op <=", left, right, v);
                let x = ExprKind::LessThanOrEqual(left2, right2);
                self.reg_expr(&x, &expr.span, expr.id, v)
            }
            ExprKind::GreaterThanOrEqual(left, right) => {
                let (left2, right2) =
                    self.deduce_call2_type(env, "op >=", left, right, v);
                let x = ExprKind::GreaterThanOrEqual(left2, right2);
                self.reg_expr(&x, &expr.span, expr.id, v)
            }
            ExprKind::Equal(left, right) => {
                let (left2, right2) =
                    self.deduce_call2_type(env, "op =", left, right, v);
                let x = ExprKind::Equal(left2, right2);
                self.reg_expr(&x, &expr.span, expr.id, v)
            }
            ExprKind::NotEqual(left, right) => {
                let (left2, right2) =
                    self.deduce_call2_type(env, "op <>", left, right, v);
                let x = ExprKind::NotEqual(left2, right2);
                self.reg_expr(&x, &expr.span, expr.id, v)
            }
            ExprKind::Plus(left, right) => {
                let (left2, right2) =
                    self.deduce_call2_type(env, "op +", left, right, v);
                let x = ExprKind::Plus(left2, right2);
                self.reg_expr(&x, &expr.span, expr.id, v)
            }
            ExprKind::Minus(left, right) => {
                let (left2, right2) =
                    self.deduce_call2_type(env, "op -", left, right, v);
                let x = ExprKind::Minus(left2, right2);
                self.reg_expr(&x, &expr.span, expr.id, v)
            }
            ExprKind::Times(left, right) => {
                let (left2, right2) =
                    self.deduce_call2_type(env, "op *", left, right, v);
                let x = ExprKind::Times(left2, right2);
                self.reg_expr(&x, &expr.span, expr.id, v)
            }
            ExprKind::Divide(left, right) => {
                let (left2, right2) =
                    self.deduce_call2_type(env, "op /", left, right, v);
                let x = ExprKind::Divide(left2, right2);
                self.reg_expr(&x, &expr.span, expr.id, v)
            }
            ExprKind::Div(left, right) => {
                let (left2, right2) =
                    self.deduce_call2_type(env, "op div", left, right, v);
                let x = ExprKind::Divide(left2, right2);
                self.reg_expr(&x, &expr.span, expr.id, v)
            }
            ExprKind::Mod(left, right) => {
                let (left2, right2) =
                    self.deduce_call2_type(env, "op mod", left, right, v);
                let x = ExprKind::Divide(left2, right2);
                self.reg_expr(&x, &expr.span, expr.id, v)
            }
            _ => todo!("{:?}", expr.kind),
        }
    }

    fn deduce_field_type(
        &mut self,
        env: &dyn TypeEnv,
        labeled_expr: &LabeledExpr,
        label_terms: &mut BTreeMap<Label, Term>,
        labeled_expr_list: &mut Vec<LabeledExpr>,
    ) {
        let v2 = self.variable();
        let e2 = self.deduce_expr_type(env, &labeled_expr.expr, &v2);
        if let Some(label_name) = &labeled_expr.label {
            let label = Label::from(&label_name.name);
            label_terms.insert(label, Term::Variable(v2));
        } else {
            // Anonymous field - generate ordinal name
            let ordinal = label_terms.len() + 1;
            let label = Label::Ordinal(ordinal);
            label_terms.insert(label, Term::Variable(v2));
        }
        labeled_expr_list.push(LabeledExpr {
            label: labeled_expr.label.clone(),
            expr: e2,
        });
    }

    fn deduce_match_list_type(
        &mut self,
        env: &dyn TypeEnv,
        match_list: &[Match],
        label_names: &mut BTreeSet<String>,
        arg_variable: &Rc<Var>,
        result_variable: &Rc<Var>,
    ) -> Vec<Match> {
        // Collect label names from RecordPat patterns
        for match_ in match_list {
            if let PatKind::Record(fields, _) = &match_.pat.kind {
                for f in fields {
                    if let PatField::Labeled(_, name, _) = f {
                        label_names.insert(name.clone());
                    }
                }
            }
        }

        // Process each match
        match_list
            .iter()
            .map(|match_| {
                let mut term_map = Vec::new();

                let pat2 = self.deduce_pat_type(
                    env,
                    &match_.pat,
                    &mut term_map,
                    &arg_variable,
                );

                let env2 = env.bind_all(&term_map);
                let exp2 = self.deduce_expr_type(
                    &*env2,
                    &match_.expr,
                    result_variable,
                );

                Match {
                    pat: pat2,
                    expr: exp2,
                }
            })
            .collect()
    }

    fn deduce_apply_type(
        &mut self,
        env: &dyn TypeEnv,
        fun: &Expr,
        arg: &Expr,
        v_result: &Rc<Var>,
    ) -> (Box<Expr>, Box<Expr>) {
        let v_fn = self.variable();
        let v_arg = self.variable();
        self.fn_term(&v_arg, v_result, &v_fn);
        let arg2 = if let ExprKind::RecordSelector(name) = &arg.kind {
            // "apply" is "f #field" and has type "v";
            // "f" has type "v_arg -> v" and also "v_fn";
            // "#field" has type "v_arg" and also "v_rec -> v_field".
            // When we resolve "v_rec" we can then deduce "v_field".
            let v_rec = self.variable();
            let v_field = self.variable();
            self.deduce_record_selector_type(env, name, &v_rec, &v_field);
            self.fn_term(&v_rec, &v_field, &v_arg);
            self.reg_expr(&arg.kind, &arg.span, arg.id, &v_arg)
        } else {
            self.deduce_expr_type(env, arg, &v_arg)
        };

        let fun2 = if let ExprKind::RecordSelector(name) = &fun.kind {
            // "apply" is "#field arg" and has type "v";
            // "#field" has type "v_arg -> v";
            // "arg" has type "v_arg".
            // When we resolve "v_arg" we can then deduce "v".
            self.deduce_record_selector_type(env, name, &v_arg, v_result)
        } else {
            self.deduce_apply_fn_type(env, fun, &v_fn, &v_arg, v_result)
        };

        /*
        if let ExprKind::Identifier(name) = fun2.kind {
            let builtIn = BUILTIN_BY_NAME.get(name);
            if (builtIn.is_some()) {
                builtIn.unwrap().prefer(|t| {preferredTypes.add(v, t)});
            }
        }
         */

        (fun2, arg2)
    }

    /// Deduces the datatype of a function being applied to an argument. If the
    /// function is overloaded, the argument will help us resolve the
    /// overloading.
    ///
    /// Parameters:
    /// * `env` Compile-time environment
    /// * `fun` Function expression (often an identifier)
    /// * `v_fun` Variable for the function type
    /// * `_v_arg` Variable for the argument type
    /// * `_v` Variable for the result type
    ///
    /// Returns the function expression with its type deduced.
    fn deduce_apply_fn_type(
        &mut self,
        env: &dyn TypeEnv,
        fun: &Expr,
        v_fun: &Rc<Var>,
        _v_arg: &Rc<Var>,
        _v: &Rc<Var>,
    ) -> Box<Expr> {
        self.deduce_expr_type(env, fun, v_fun)
    }

    fn deduce_record_selector_type(
        &mut self,
        _env: &dyn TypeEnv,
        name: &String,
        v_rec: &Rc<Var>,
        v_field: &Rc<Var>,
    ) -> Box<Expr> {
        // Create a function type: record -> field
        let v_fn = self.variable();
        self.fn_term(v_rec, v_field, &v_fn);

        // Create a record selector expression
        let selector_kind = ExprKind::RecordSelector(name.clone());
        // Minimal span since we don't have the original
        let span = Span::zero("".into());
        self.reg_expr(&selector_kind, &span, None, v_field)
    }

    fn deduce_call2_type(
        &mut self,
        env: &dyn TypeEnv,
        op: &str,
        left: &Expr,
        right: &Expr,
        v: &Rc<Var>,
    ) -> (Box<Expr>, Box<Expr>) {
        let fun =
            Box::new(ExprKind::Identifier(op.to_string()).spanned(&left.span));
        let arg = Box::new(
            ExprKind::Tuple(vec![
                Box::new(left.clone()),
                Box::new(right.clone()),
            ])
            .spanned(&left.span),
        );
        let (_fun, arg) = self.deduce_apply_type(env, &fun, &arg, &v);
        if let ExprKind::Tuple(args) = arg.kind
            && args.len() == 2
        {
            (args.first().unwrap().clone(), args.get(1).unwrap().clone())
        } else {
            panic!("{:?}", left.kind)
        }
    }

    fn deduce_call3_type(
        &mut self,
        env: &dyn TypeEnv,
        op: &str,
        a0: &Expr,
        a1: &Expr,
        a2: &Expr,
        v: &Rc<Var>,
    ) -> (Box<Expr>, Box<Expr>, Box<Expr>) {
        let fun =
            Box::new(ExprKind::Identifier(op.to_string()).spanned(&a0.span));
        let arg = Box::new(
            ExprKind::Tuple(vec![
                Box::new(a0.clone()),
                Box::new(a1.clone()),
                Box::new(a2.clone()),
            ])
            .spanned(&a0.span),
        );
        let (_fun, arg) = self.deduce_apply_type(env, &fun, &arg, &v);
        if let ExprKind::Tuple(args) = arg.kind
            && args.len() == 3
        {
            (
                args.first().unwrap().clone(),
                args.get(1).unwrap().clone(),
                args.get(2).unwrap().clone(),
            )
        } else {
            panic!("{:?}", op)
        }
    }

    fn deduce_pat_call2_type(
        &mut self,
        env: &dyn TypeEnv,
        op: &str,
        left: &Pat,
        right: &Pat,
        term_map: &mut Vec<(String, Term)>,
        v: &Rc<Var>,
    ) -> (Box<Pat>, Box<Pat>) {
        let v_arg0 = self.variable();
        let v_arg1 = self.variable();
        let left2 = self.deduce_pat_type(env, &left, term_map, &v_arg0);
        let right2 = self.deduce_pat_type(env, &right, term_map, &v_arg1);

        let term_fn = env
            .get(op, self)
            .unwrap_or_else(|| todo!("function '{}' not found", op));
        let v_fn = self.term_to_variable(&term_fn);
        let v_arg = self.variable();
        let arg = vec![Term::Variable(v_arg0), Term::Variable(v_arg1)];
        self.tuple_term(arg.as_ref(), &v_arg);
        self.fn_term(&v_arg, v, &v_fn);
        (left2, right2)
    }

    /// Given a branch of a `fn`, deduces its type.
    ///
    /// For example, `fn 0 => 1 | n => n mod 2` has two branches, and they each
    /// have the type `int -> int`.
    ///
    /// It is useful to treat the branches separately because each generates
    /// its own environment. The second branch creates an environment with that
    /// binds the parameter to `n`.
    fn deduce_match_type(
        &mut self,
        env: &dyn TypeEnv,
        match_: &Match,
        v_param: &Rc<Var>,
        v_result: &Rc<Var>,
    ) -> Match {
        let mut term_map = Vec::new();
        let pat = match_.pat.clone();
        let pat2 = self.deduce_pat_type(env, &pat, &mut term_map, &v_param);
        let env2 = env.bind_all(&term_map);
        let expr = match_.expr.clone();
        let expr2 = self.deduce_expr_type(&*env2, &expr, &v_result);
        Match {
            pat: pat2,
            expr: expr2,
        }
    }

    /// Converts a type to a unification term.
    fn type_to_term<'a>(
        &mut self,
        type_: &Type,
        v: &'a Rc<Var>,
    ) -> &'a Rc<Var> {
        match type_ {
            Type::Primitive(prim) => {
                let _type_name = prim.as_str();
                let op = self.unifier.op(_type_name, Some(0));
                let sequence = &Term::Sequence(self.unifier.atom(op));
                self.equiv(sequence, v)
            }
            Type::Fn(param, result) => {
                let v_param = self.variable();
                self.type_to_term(param, &v_param);
                let v_result = self.variable();
                self.type_to_term(result, &v_result);
                self.fn_term(&v_param, &v_result, v)
            }
            _ => todo!("{:?}", type_),
        }
    }

    /// Creates a term for a primitive type and associates it with a variable.
    fn primitive_term<'a>(
        &mut self,
        prim_type: &PrimitiveType,
        v: &'a Rc<Var>,
    ) -> &'a Rc<Var> {
        let moniker = prim_type.as_str();
        let op = self.unifier.op(moniker, Some(0));
        let sequence = self.unifier.atom(op);
        self.equiv(&Term::Sequence(sequence), v)
    }

    /// Creates a term for a function type and associates it with a variable.
    fn fn_term<'a>(
        &mut self,
        param_type: &Rc<Var>,
        result_type: &Rc<Var>,
        v: &'a Rc<Var>,
    ) -> &'a Rc<Var> {
        let sequence = self.unifier.apply2(
            self.fn_op.clone(),
            Term::Variable(param_type.clone()),
            Term::Variable(result_type.clone()),
        );
        self.equiv(&Term::Sequence(sequence), v)
    }

    /// Creates a term for a list type and associates it with a variable.
    fn list_term<'a>(&mut self, term: Term, v: &'a Rc<Var>) -> &'a Rc<Var> {
        let sequence = self.unifier.apply1(self.list_op.clone(), term);
        self.equiv(&Term::Sequence(sequence), v)
    }

    /// Creates a term for a bag type and associates it with a variable.
    fn bag_term<'a>(&mut self, term: Term, v: &'a Rc<Var>) -> &'a Rc<Var> {
        let sequence = self.unifier.apply1(self.bag_op.clone(), term);
        self.equiv(&Term::Sequence(sequence), v)
    }

    /// Creates a term for a record type and associates it with a variable.
    fn record_term<'a>(
        &mut self,
        label_types: &BTreeMap<Label, Term>,
        v: &'a Rc<Var>,
    ) -> &'a Rc<Var> {
        assert!(label_types.keys().is_sorted());
        let label_terms = label_types.values().cloned().collect::<Vec<_>>();

        if Label::are_contiguous(label_types.keys().cloned())
            && label_types.len() != 1
        {
            return self.tuple_term(&label_terms, v);
        }

        let label = Self::record_label_from_set(label_types.keys().cloned());
        let op = self.unifier.op(&label, Some(label_types.len()));
        let sequence = self.unifier.apply(op, &label_terms);
        self.equiv(&Term::Sequence(sequence), v)
    }

    fn tuple_term<'a>(
        &mut self,
        types: &[Term],
        v: &'a Rc<Var>,
    ) -> &'a Rc<Var> {
        if types.is_empty() {
            self.primitive_term(&PrimitiveType::Unit, v)
        } else {
            let sequence = self.unifier.apply(self.tuple_op.clone(), types);
            self.equiv(&Term::Sequence(sequence), v)
        }
    }

    fn type_term<'a>(
        &mut self,
        type_: &Type,
        subst: &Subst,
        v: &'a Rc<Var>,
    ) -> &'a Rc<Var> {
        match type_ {
            Type::Primitive(prim_type) => self.primitive_term(prim_type, v),
            Type::Variable(type_var) => {
                if let Some(term) = subst.get(type_var) {
                    self.equiv(&term, v)
                } else {
                    v
                }
            }
            Type::Alias(_name, type_, _args) => {
                // During type inference, we pretend that an alias type is its
                // underlying type. For example, if we have 'type t = int', and
                // 'val i = 1: t', we treat 'i' as having type 'int'.
                //
                // After type inference is complete, we can deduce the true type
                // bottom-up. Thus, '[1: t]' has "t list" as its type.
                self.type_term(&type_, subst, v)
            }
            Type::Data(name, arguments) => {
                if name == "bag" {
                    assert_eq!(arguments.len(), 1);
                    let v2 = self.variable();
                    self.type_term(&arguments[0], subst, &v2);
                    return self.bag_term(Term::Variable(v2), v);
                }
                let mut terms = Vec::new();
                for argument in arguments {
                    let v2 = self.variable();
                    self.type_to_term(argument, &v2);
                    terms.push(Term::Variable(v2));
                }
                let op = self.unifier.op(&name, Some(terms.len()));
                let sequence = self.unifier.apply(op, &terms);
                self.equiv(&Term::Sequence(sequence), v)
            }
            Type::Fn(param_type, result_type) => {
                let v2 = self.variable();
                self.type_term(&param_type, subst, &v2);
                let v3 = self.variable();
                self.type_term(&result_type, subst, &v3);
                self.fn_term(&v2, &v3, v)
            }
            Type::Tuple(args) => {
                let mut terms: Vec<Term> = Vec::new();
                for arg in args {
                    let v2 = self.variable();
                    self.type_term(arg, subst, &v2);
                    terms.push(Term::Variable(v2))
                }
                self.tuple_term(&terms, v)
            }
            Type::Record(progressive, arg_name_types) => {
                let mut map: BTreeMap<Label, Term> = BTreeMap::new();
                if *progressive {
                    let v2 = self.variable();
                    self.primitive_term(&PrimitiveType::Unit, &v2);
                    let label = Label::from(PROGRESSIVE_LABEL);
                    map.insert(label, Term::Variable(v2));
                }
                for (label, t) in arg_name_types {
                    let v2 = self.variable();
                    self.type_term(t, &subst, &v2);
                    map.insert(label.clone(), Term::Variable(v2));
                }
                if map.is_empty() {
                    self.primitive_term(&PrimitiveType::Unit, v)
                } else if Label::are_contiguous(map.keys().cloned()) {
                    self.tuple_term(
                        &map.values().cloned().collect::<Vec<_>>(),
                        v,
                    )
                } else {
                    let label =
                        Self::record_label_from_set(map.keys().cloned());
                    let op = self.unifier.op(label.as_str(), Some(map.len()));
                    let terms = map.values().cloned().collect::<Vec<_>>();
                    let sequence = self.unifier.apply(op, &terms);
                    self.equiv(&Term::Sequence(sequence), v)
                }
            }
            Type::List(element_type) => {
                let v2 = self.variable();
                self.type_term(element_type, subst, &v2);
                self.list_term(Term::Variable(v2), v)
            }
            Type::Forall(type_, parameter_count) => {
                let mut subst2 = subst.clone();
                for i in 0..*parameter_count {
                    let type_var = TypeVariable::new(i);
                    subst2 =
                        subst2.plus(&type_var, Term::Variable(self.variable()));
                }
                self.type_term(&type_, &subst2, v)
            }
            Type::Multi(types) => {
                // We cannot convert an overloaded type into a term; it would
                // have to be a term plus constraint(s). Luckily, this method is
                // called only to generate a plausible type for a record such as
                // the Relational structure, so it works if we just return the
                // first type.
                self.type_term(&types[0], subst, v)
            }
            _ => {
                panic!("unknown type: {:?}", type_);
            }
        }
    }

    /// Inverse of `record_label_from_set`. Extracts field names from a
    /// sequence.
    fn field_list(sequence: &Sequence) -> Option<Vec<String>> {
        match sequence.op.name.as_str() {
            "record" => Some(Vec::new()),
            "tuple" => {
                let size = sequence.terms.len();
                Some(ordinal_names(size))
            }
            s if s.starts_with("record:") => {
                let fields: Vec<String> = sequence
                    .op
                    .name
                    .split(':')
                    .skip(1) // Skip "record" prefix
                    .map(std::string::ToString::to_string)
                    .collect();
                Some(fields)
            }
            _ => None,
        }
    }

    /// Inverse of `field_list`. Creates a record label from field names.
    fn record_label_from_set<I>(labels: I) -> String
    where
        I: IntoIterator<Item = Label>,
    {
        let mut s = "record".to_string();
        for label in labels {
            s.push(':');
            s.push_str(&label.to_string());
        }
        s
    }

    /// Generates ordinal names for tuple fields: ["1", "2", "3", ...]
    fn tuple_ordinal_names(size: usize) -> Vec<String> {
        (1..=size).map(|i| i.to_string()).collect()
    }

    /// Creates a type variable.
    fn variable(&mut self) -> Rc<Var> {
        self.unifier.variable()
    }

    /// Converts a term to a variable.
    fn term_to_variable(&mut self, term: &Term) -> Rc<Var> {
        match term {
            Term::Variable(v) => v.clone(),
            Term::Sequence(_) => {
                let v = self.variable();
                self.equiv(&term, &v).clone()
            }
        }
    }

    /// Converts a variable to a sequence.
    fn variable_to_sequence(&self, _v: &Rc<Var>) -> Option<Sequence> {
        None // TODO
    }

    /// Declares that a term is equivalent to a variable.
    /// Creates an association between a term and a variable,
    /// declaring that they are equivalent.
    fn equiv<'a>(&mut self, term: &Term, v: &'a Rc<Var>) -> &'a Rc<Var> {
        self.terms.push((v.clone(), term.clone()));
        &v
    }

    /// Registers a term for an AST node for an expression.
    fn reg_expr(
        &mut self,
        kind: &ExprKind<Expr>,
        span: &Span,
        id: Option<i32>,
        v: &Rc<Var>,
    ) -> Box<Expr> {
        let id2 = id.unwrap_or_else(|| self.next_id());
        self.node_var_map.insert(id2, v.clone());
        Box::new(Expr {
            kind: kind.clone(),
            span: span.clone(),
            id: Some(id2),
        })
    }

    /// Registers a term for an AST node for an expression.
    fn reg_pat(
        &mut self,
        kind: &PatKind,
        span: &Span,
        id: Option<i32>,
        v: &Rc<Var>,
    ) -> Box<Pat> {
        let id2 = id.unwrap_or_else(|| self.next_id());
        self.node_var_map.insert(id2, v.clone());
        Box::new(Pat {
            kind: kind.clone(),
            span: span.clone(),
            id: Some(id2),
        })
    }

    /// Registers a term for an AST node for a type.
    fn reg_type(
        &mut self,
        kind: &TypeKind,
        span: &Span,
        v: &Rc<Var>,
    ) -> Box<AstType> {
        Box::new(AstType {
            kind: kind.clone(),
            span: span.clone(),
            id: Some(v.id),
        })
    }

    fn deduce_val_bind_type(
        &mut self,
        env: &dyn TypeEnv,
        val_bind: &ValBind,
        term_map: &mut Vec<(String, Term)>,
        v: &Rc<Var>,
    ) -> ValBind {
        let pat = self.deduce_pat_type(env, &val_bind.pat, term_map, &v);
        let expr = self.deduce_expr_type(env, &val_bind.expr, &v);
        ValBind {
            pat,
            expr,
            ..val_bind.clone()
        }
    }

    fn literal_type(literal_kind: &LiteralKind) -> PrimitiveType {
        match literal_kind {
            LiteralKind::Int(_) => PrimitiveType::Int,
            LiteralKind::Real(_) => PrimitiveType::Real,
            LiteralKind::String(_) => PrimitiveType::String,
            LiteralKind::Char(_) => PrimitiveType::Char,
            LiteralKind::Bool(_) => PrimitiveType::Bool,
            LiteralKind::Unit => PrimitiveType::Unit,
            LiteralKind::Fn(_) => todo!("Implement Fn literal type"),
        }
    }

    fn deduce_pat_type(
        &mut self,
        env: &dyn TypeEnv,
        pat: &Pat,
        term_map: &mut Vec<(String, Term)>,
        v: &Rc<Var>,
    ) -> Box<Pat> {
        match &pat.kind {
            PatKind::Identifier(name) => {
                if let Some(_) = env.get(name, self)
                    && (name == "SOME" // HACK
                        || name == "NONE"
                        || name == "nil"
                        || name == "op ::")
                {
                    // If the identifier is in the environment, we assume that
                    // it is a constructor (such as `SOME` or `nil`).
                    let kind = PatKind::Constructor(name.clone(), None);
                    let pat2 = Box::new(kind.spanned(&pat.span()));
                    return self.deduce_pat_type(env, &pat2, term_map, v);
                }
                term_map.push((name.clone(), Term::Variable(v.clone())));
                self.reg_pat(&pat.kind, &pat.span, pat.id, &v)
            }
            PatKind::Wildcard => self.reg_pat(&pat.kind, &pat.span, pat.id, &v),
            PatKind::Literal(literal) => {
                self.primitive_term(&Self::literal_type(&literal.kind), v);
                self.reg_pat(&pat.kind, &pat.span, pat.id, &v)
            }
            PatKind::Constructor(name, arg) => {
                // Consider the constructor "SOME". For type deduction, we
                // treat "SOME" as a function with a type scheme "forall 'a,
                // 'a -> option 'a". And then "SOME x" has the type "int option"
                // if and only if "x" has type "int".
                let term = env.get(name, self).unwrap_or_else(|| {
                    todo!("constructor '{}' not found", name)
                });
                let arg2 = if let Some(a) = arg {
                    let v_arg = self.unifier.variable();
                    let v_fun = self.term_to_variable(&term);
                    self.fn_term(&v_arg, v, &v_fun);
                    Some(self.deduce_pat_type(env, a, term_map, &v_arg))
                } else {
                    self.equiv(&term, v);
                    None
                };
                let x = PatKind::Constructor(name.clone(), arg2);
                self.reg_pat(&x, &pat.span, pat.id, &v)
            }
            PatKind::Cons(left, right) => {
                let (left2, right2) = self.deduce_pat_call2_type(
                    env, "op ::", left, right, term_map, v,
                );
                let x = PatKind::Cons(left2, right2);
                self.reg_pat(&x, &pat.span, pat.id, &v)
            }
            PatKind::Annotated(pat, type_) => {
                let pat2 = self.deduce_pat_type(env, pat, term_map, &v);
                let type2 = self.deduce_type_type(env, type_, &v);
                self.reg_pat(
                    &PatKind::Annotated(pat2.clone(), type2),
                    &pat2.span,
                    pat2.id,
                    &v,
                )
            }
            PatKind::Tuple(pat_list) if pat_list.is_empty() => {
                // They wrote an empty tuple. Treat it as a unit literal.
                let unit_literal = LiteralKind::Unit.spanned(&pat.span);
                let pat2 =
                    Box::new(PatKind::Literal(unit_literal).spanned(&pat.span));
                self.deduce_pat_type(env, &pat2, term_map, &v)
            }
            PatKind::Tuple(pat_list) if pat_list.len() == 1 => {
                // A pattern in parentheses is not a tuple.
                let p = pat_list.first().unwrap().clone();
                self.deduce_pat_type(env, &p, term_map, &v)
            }
            PatKind::Tuple(pat_list) => {
                let mut pat_list2 = Vec::new();
                let mut terms = Vec::new();
                for pat in pat_list {
                    let v2 = self.variable();
                    let pat2 = self.deduce_pat_type(env, pat, term_map, &v2);
                    pat_list2.push(pat2);
                    terms.push(Term::Variable(v2));
                }
                self.tuple_term(&terms, &v);
                self.reg_pat(&PatKind::Tuple(pat_list2), &pat.span, pat.id, &v)
            }
            PatKind::Record(fields, ellipsis) => {
                // The algorithm in Morel-Java is more complicated than we have
                // implemented here.
                //
                // First, determine the set of field names.
                //
                // If the pattern is in a 'case', we know the field names from
                // the argument. But if we are in a function, we require at
                // least one of the patterns to not be a wildcard and not have
                // an ellipsis. For example, in
                //
                //  fun f {a=1,...} = 1 | f {b=2,...} = 2
                //
                // we cannot deduce whether a 'c' field is allowed.
                let mut fields2 = Vec::new();
                let mut map = BTreeMap::<Label, Term>::new();
                for field in fields {
                    match field {
                        PatField::Labeled(span, name, pat) => {
                            let v2 = self.variable();
                            let pat2 =
                                self.deduce_pat_type(env, pat, term_map, &v2);
                            fields2.push(PatField::Labeled(
                                span.clone(),
                                name.clone(),
                                pat2,
                            ));
                            map.insert(
                                Label::from(name.clone()),
                                Term::Variable(v2),
                            );
                        }
                        PatField::Anonymous(span, pat) => {
                            let v2 = self.variable();
                            let pat2 =
                                self.deduce_pat_type(env, pat, term_map, &v2);
                            let name = self.implicit_pat_label(pat);
                            fields2.push(PatField::Labeled(
                                span.clone(),
                                name.clone(),
                                pat2,
                            ));
                            map.insert(
                                Label::from(name.clone()),
                                Term::Variable(v2),
                            );
                        }
                        PatField::Ellipsis(_span) => {
                            // ignore
                        }
                    };
                }
                self.record_term(&map, &v);
                self.reg_pat(
                    &PatKind::Record(fields2, *ellipsis),
                    &pat.span,
                    pat.id,
                    &v,
                )
            }
            _ => todo!("{:?}", pat.kind),
        }
    }

    /// Derives an implicit label from a pattern; logs a warning and returns a
    /// fake label if that is not possible.
    fn implicit_pat_label(&mut self, pat: &Pat) -> String {
        if let Some(label) = implicit_pat_label_opt(pat) {
            label
        } else {
            let message = format!("cannot derive label for pattern {}", pat);
            let span = pat.span.clone();
            self.warnings.push(Warning { span, message });
            "implicit".to_string()
        }
    }
}

impl TypeSchemeResolver for TypeResolver {
    fn deduce_type_scheme(&mut self, type_scheme: &TypeScheme) -> Rc<Var> {
        let env = EmptyTypeEnv;
        let v = self.variable();
        self.deduce_type_scheme(&env, &type_scheme, &v);
        v
    }
}

/// Ensures that a statement is a declaration.
/// An expression 'e' is wrapped as a value declaration 'val it = e'.
fn ensure_decl(statement: &Statement) -> Decl {
    match &statement.kind {
        StatementKind::Decl(_) => Decl::from_statement(statement),
        StatementKind::Expr(e) => Decl {
            kind: DeclKind::Val(
                false,
                false,
                vec![ValBind::of(
                    Box::new(Pat {
                        kind: PatKind::Identifier("it".to_string()),
                        span: statement.span.clone(),
                        id: statement.id,
                    }),
                    None,
                    Box::new(Expr {
                        kind: e.clone(),
                        span: statement.span.clone(),
                        id: statement.id,
                    }),
                )],
            ),
            span: statement.span.clone(),
            id: statement.id,
        },
    }
}

/// Workspace for converting types to terms.
#[allow(dead_code)]
struct TypeToTermConverter<'a> {
    env: &'a dyn TypeEnv,
    type_resolver: &'a mut TypeResolver,
    type_variables: BTreeMap<String, Box<TypeVariable>>,
}

#[allow(dead_code)]
impl<'a> TypeToTermConverter<'a> {
    /// Converts a type scheme into a type term.
    ///
    /// Requires [TypeToTermConverter.type_variables] has been populated with
    /// all type variables that can possibly occur. (Generally the first N
    /// variables, `'a`, `'b`, ...)
    fn type_scheme_term(
        &mut self,
        type_scheme: &TypeScheme,
        v: &Rc<Var>,
    ) -> Box<AstType> {
        let mut subst = Subst::Empty;
        for i in 0..type_scheme.var_count {
            let type_variable = self.type_variables.values().nth(i).unwrap();
            let v = self.type_resolver.variable();
            subst = subst.plus(type_variable, Term::Variable(v));
        }
        self.type_term(&type_scheme.type_, &subst, v)
    }

    /// Converts an AST node representing a type into a type term.
    /// Registers the type term and returns the modified AST node.
    fn type_term(
        &mut self,
        type_node: &AstType,
        subst: &Subst,
        v: &Rc<Var>,
    ) -> Box<AstType> {
        match &type_node.kind {
            TypeKind::App(args, t) => {
                if let TypeKind::Id(name) = t.kind.clone() {
                    let mut terms = Vec::new();
                    let mut args2 = Vec::new();
                    for arg in args {
                        let v2 = self.type_resolver.variable();
                        terms.push(Term::Variable(v2.clone()));
                        let arg2 = self.type_term(arg, subst, &v2);
                        args2.push(*arg2);
                    }
                    let op = self
                        .type_resolver
                        .unifier
                        .op(name.as_str(), Some(terms.len()));
                    let apply = self.type_resolver.unifier.apply(op, &terms);
                    self.type_resolver.equiv(&Term::Sequence(apply), &v);
                    let x = TypeKind::App(args2, t.clone());
                    self.type_resolver.reg_type(&x, &type_node.span, &v)
                } else {
                    panic!("{:?}", type_node.kind)
                }
            }
            TypeKind::Id(name) => {
                let p = PrimitiveType::parse_name(name).unwrap();
                self.type_resolver.primitive_term(&p, &v);
                self.type_resolver.reg_type(
                    &type_node.kind,
                    &type_node.span,
                    &v,
                )
            }
            TypeKind::Fn(param, result) => {
                let v4 = self.type_resolver.variable();
                let param2 = self.type_term(param, subst, &v4);
                let v5 = self.type_resolver.variable();
                let result2 = self.type_term(result, subst, &v5);
                self.type_resolver.fn_term(&v4, &v5, &v);
                self.type_resolver.reg_type(
                    &TypeKind::Fn(param2, result2),
                    &type_node.span,
                    &v,
                )
            }
            TypeKind::Record(fields) => {
                let mut fields2 = Vec::new();
                let mut label_types = BTreeMap::<Label, Term>::new();
                for field in fields {
                    let v2 = self.type_resolver.variable();
                    fields2.push(TypeField {
                        label: field.label.clone(),
                        type_: *self.type_term(&field.type_, subst, &v2),
                    });
                    label_types.insert(
                        Label::from(field.label.name.clone()),
                        Term::Variable(v2),
                    );
                }
                self.type_resolver.record_term(&label_types, &v);
                self.type_resolver.reg_type(
                    &TypeKind::Record(fields2),
                    &type_node.span,
                    &v,
                )
            }
            TypeKind::Tuple(types) => {
                let mut types2 = Vec::new();
                let mut terms = Vec::new();
                for t in types {
                    let v2 = self.type_resolver.variable();
                    terms.push(Term::Variable(v2.clone()));
                    types2.push(*self.type_term(&t, subst, &v2));
                }
                self.type_resolver.tuple_term(&terms, &v);
                self.type_resolver.reg_type(
                    &TypeKind::Tuple(types2),
                    &type_node.span,
                    &v,
                )
            }
            TypeKind::Var(name) => {
                let type_variable = self.type_variables.get(name).unwrap();
                let term = subst.get(type_variable).unwrap();
                self.type_resolver.equiv(&term, &v);
                Box::new(TypeKind::Var(name.clone()).spanned(&type_node.span))
            }
            TypeKind::Unit => {
                self.type_resolver.primitive_term(&PrimitiveType::Unit, &v);
                self.type_resolver.reg_type(
                    &TypeKind::Unit,
                    &type_node.span,
                    &v,
                )
            }
            _ => todo!("{:?}", type_node.kind),
        }
    }
}

/// Returns the implicit label for when an expression occurs within a record,
/// or null if no label can be deduced.
///
/// For example,
///
/// ```sml
/// {x.a, y, z = x.b + 2}
/// ```
///
/// is equivalent to
///
/// ```sml
/// {a = x.a, y = y, z = x.b + 2}
/// ```
///
/// because a field reference `x.a` has implicit label `a`, and
/// a variable reference `y` has implicit label `y`. The expression
/// `x.b + 2` has no implicit label.
///
#[allow(dead_code)]
fn implicit_expr_label_opt(expr: &Expr) -> Option<String> {
    match &expr.kind {
        ExprKind::Current => Some("current".to_string()),
        ExprKind::Ordinal => Some("ordinal".to_string()),
        ExprKind::Identifier(name) => Some(name.clone()),
        ExprKind::Aggregate(left, _) => implicit_expr_label_opt(left),
        ExprKind::Apply(left, _) => match &left.kind {
            ExprKind::RecordSelector(name) => Some(name.clone()),
            _ => None,
        },
        _ => None,
    }
}

fn implicit_pat_label_opt(pat: &Pat) -> Option<String> {
    match &pat.kind {
        PatKind::Identifier(name) => Some(name.clone()),
        PatKind::Annotated(pat, _type) => implicit_pat_label_opt(pat),
        _ => None,
    }
}

/// Compile-time error or warning.
#[allow(dead_code)]
struct Warning {
    #[allow(dead_code)]
    span: Span,
    #[allow(dead_code)]
    message: String,
}

const W_INCONSISTENT_PARAMETERS: &str = "parameter or result \
constraints of clauses don't agree [tycon mismatch]";
