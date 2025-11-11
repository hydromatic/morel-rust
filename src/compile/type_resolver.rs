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
#![allow(clippy::needless_borrow)]
#![allow(clippy::collapsible_if)]

use crate::compile::type_env::{
    BindType, EmptyTypeEnv, TypeEnv, TypeSchemeResolver,
};
use crate::compile::types;
use crate::compile::types::Label;
use crate::compile::types::{PrimitiveType, Subst, Type, TypeVariable};
use crate::shell::error::Error;
use crate::syntax::ast::{
    Decl, DeclKind, Expr, ExprKind, FunBind, LabeledExpr, LiteralKind, Match,
    MorelNode, Pat, PatField, PatKind, Span, Statement, StatementKind, Step,
    StepKind, Type as AstType, TypeField, TypeKind, TypeScheme, ValBind,
};
use crate::unify::unifier::{
    Action, NullTracer, Op, Sequence, Substitution, Term, Unifier, Var,
};
use std::cell::OnceCell;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::fmt::{Debug, Display, Formatter};
use std::iter::zip;
use std::rc::Rc;
use types::ordinal_names;

/// A field of this name indicates that a record type is progressive.
pub const PROGRESSIVE_LABEL: &str = "z$dummy";

/// Result of type resolution containing the resolved AST and type information.
#[derive(Clone, Debug)]
pub struct Resolved {
    pub decl: Decl,
    pub type_map: TypeMap,
    pub bindings: Vec<TypeBinding>,
    pub base_line: usize,
    pub warnings: Vec<Warning>,
}

/// Maps AST nodes to their resolved types.
#[derive(Clone, Debug)]
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

#[derive(Clone)]
struct Triple {
    root_env: Rc<dyn TypeEnv>,
    env: Rc<dyn TypeEnv>,
    v: Rc<Var>,
    c: Option<Rc<Var>>,
}

impl Triple {
    fn new(
        root_env: Rc<dyn TypeEnv>,
        env: Rc<dyn TypeEnv>,
        v: Rc<Var>,
        c: Option<Rc<Var>>,
    ) -> Self {
        Triple {
            root_env,
            env,
            v,
            c,
        }
    }

    fn with_env(&self, env: &Rc<dyn TypeEnv>) -> Self {
        Self::new(
            self.root_env.clone(),
            env.clone(),
            self.v.clone(),
            self.c.clone(),
        )
    }

    fn with_c(&self, c: Rc<Var>) -> Self {
        Self::new(
            self.root_env.clone(),
            self.env.clone(),
            self.v.clone(),
            Some(c),
        )
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
                // lint: sort until '#}' where '##["]'
                "bag" => {
                    assert_eq!(sequence.terms.len(), 1);
                    let type_ = self.term_type(&sequence.terms[0]);
                    Box::new(Type::Bag(type_))
                }
                "bool" | "char" | "int" | "real" | "string" | "unit" => {
                    let primitive_type =
                        PrimitiveType::parse_name(&sequence.op.name).unwrap();
                    Box::new(Type::Primitive(primitive_type))
                }
                "either" => {
                    assert_eq!(sequence.terms.len(), 2);
                    let arg1 = *self.term_type(&sequence.terms[0]);
                    let arg2 = *self.term_type(&sequence.terms[1]);
                    Box::new(Type::Data(
                        sequence.op.name.clone(),
                        vec![arg1, arg2],
                    ))
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
                "option" | "descending" => {
                    assert_eq!(sequence.terms.len(), 1);
                    let args = vec![*self.term_type(&sequence.terms[0])];
                    Box::new(Type::Data(sequence.op.name.clone(), args))
                }
                "order" => {
                    assert_eq!(sequence.terms.len(), 0);
                    Box::new(Type::Data(sequence.op.name.clone(), vec![]))
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
                "vector" => {
                    assert_eq!(sequence.terms.len(), 1);
                    let args = vec![*self.term_type(&sequence.terms[0])];
                    Box::new(Type::Data(sequence.op.name.clone(), args))
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
#[derive(Clone, Debug)]
pub struct TypeBinding {
    pub name: String,
    pub resolved_type: Type,
    pub kind: BindingKind,
}

/// Kind of binding (value, type constructor, etc.).
#[derive(Clone, PartialEq, Debug)]
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

    /// Stack of `compute` clauses.
    compute_stack: Vec<Triple>,

    /// Cached operators for common type-constructors.
    list_op: Rc<Op>,
    bag_op: Rc<Op>,
    tuple_op: Rc<Op>,
    arg_op: Rc<Op>,
    overload_op: Rc<Op>,
    record_op: Rc<Op>,
    fn_op: Rc<Op>,
    actions: Vec<(Rc<Var>, Rc<dyn Action>)>,
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
            compute_stack: Vec::new(),
            actions: Vec::new(),
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
    ) -> Result<Resolved, Error> {
        self.terms.clear();

        let decl = ensure_decl(statement);
        let mut term_map = Vec::new();
        let decl2 = self.deduce_decl_type(env, &decl, &mut term_map)?;

        // Create term pairs for unification
        let term_pairs: Vec<(Term, Term)> = self
            .terms
            .iter()
            .map(|(var, term)| (term.clone(), Term::Variable(var.clone())))
            .collect();

        let substitution = match self.unifier.unify(
            term_pairs.as_ref(),
            &NullTracer,
            self.actions.as_ref(),
        ) {
            Ok(x) => {
                if false {
                    eprintln!(
                        "Unification result: {:?}\n{}",
                        x.clone(),
                        self.terms_to_string()
                    );
                }
                x
            }
            Err(x) => {
                let string = self.terms_to_string();
                panic!(
                    "Unification failed: {}\n\
                        term pairs: {}\n",
                    x, string
                )
            }
        };

        // Create a map with the results of unification.
        let mut type_map = TypeMap::new(&self.node_var_map);
        for (v, term) in substitution.substitutions {
            type_map.var_term_map.insert(v, term);
        }

        // If the code begins with a comment, compute the offset of the first
        // line of code after the comment. This allows us to report the correct
        // position of errors when there are commented-out lines before them.
        let pest_span = decl2.span.to_pest_span();
        let start = pest_span.start_pos();
        let base_line = if start.line_col().1 == 1 {
            start.line_col().0 - 1
        } else {
            0
        };

        // Extract bindings from the declaration
        let mut bindings = Vec::new();
        Self::collect_bindings_from_decl(&decl2, &type_map, &mut bindings);

        Ok(Resolved {
            decl: decl2,
            type_map,
            bindings,
            base_line,
            warnings: self.warnings.clone(),
        })
    }

    /// Collects bindings from a declaration.
    fn collect_bindings_from_decl(
        decl: &Decl,
        type_map: &TypeMap,
        bindings: &mut Vec<TypeBinding>,
    ) {
        match &decl.kind {
            DeclKind::Val(_rec, _inst, val_binds) => {
                for val_bind in val_binds {
                    Self::collect_bindings_from_pat(
                        &val_bind.pat,
                        type_map,
                        bindings,
                    );
                }
            }
            DeclKind::Fun(_fun_binds) => {
                // Fun declarations are converted to Val declarations,
                // so this shouldn't happen
            }
            _ => {
                // Other declaration types don't create value bindings
            }
        }
    }

    /// Collects bindings from a pattern.
    fn collect_bindings_from_pat(
        pat: &Pat,
        type_map: &TypeMap,
        bindings: &mut Vec<TypeBinding>,
    ) {
        match &pat.kind {
            PatKind::Identifier(name) => {
                if let Some(id) = pat.id {
                    if let Some(resolved_type) = type_map.get_type(id) {
                        bindings.push(TypeBinding {
                            name: name.clone(),
                            resolved_type: *resolved_type,
                            kind: BindingKind::Val,
                        });
                    }
                }
            }
            PatKind::As(name, inner_pat) => {
                // The 'as' pattern binds the name
                if let Some(id) = pat.id {
                    if let Some(resolved_type) = type_map.get_type(id) {
                        bindings.push(TypeBinding {
                            name: name.clone(),
                            resolved_type: *resolved_type,
                            kind: BindingKind::Val,
                        });
                    }
                }
                // Also collect from the inner pattern
                Self::collect_bindings_from_pat(inner_pat, type_map, bindings);
            }
            PatKind::Tuple(pats) => {
                for p in pats {
                    Self::collect_bindings_from_pat(p, type_map, bindings);
                }
            }
            PatKind::List(pats) => {
                for p in pats {
                    Self::collect_bindings_from_pat(p, type_map, bindings);
                }
            }
            PatKind::Record(fields, _ellipsis) => {
                for field in fields {
                    match field {
                        PatField::Labeled(_span, _name, p) => {
                            Self::collect_bindings_from_pat(
                                p, type_map, bindings,
                            );
                        }
                        PatField::Anonymous(_span, p) => {
                            Self::collect_bindings_from_pat(
                                p, type_map, bindings,
                            );
                        }
                        PatField::Ellipsis(_span) => {}
                    }
                }
            }
            PatKind::Cons(left, right) => {
                Self::collect_bindings_from_pat(left, type_map, bindings);
                Self::collect_bindings_from_pat(right, type_map, bindings);
            }
            PatKind::Annotated(inner_pat, _type) => {
                Self::collect_bindings_from_pat(inner_pat, type_map, bindings);
            }
            PatKind::Constructor(_name, Some(inner_pat)) => {
                Self::collect_bindings_from_pat(inner_pat, type_map, bindings);
            }
            _ => {
                // Other patterns don't create bindings
            }
        }
    }

    /// Deduces a declaration's type.
    fn deduce_decl_type(
        &mut self,
        env: &dyn TypeEnv,
        decl: &Decl,
        term_map: &mut Vec<(String, Term)>,
    ) -> Result<Decl, Error> {
        match &decl.kind {
            DeclKind::Val(rec, inst, val_binds) => {
                let x = &self.deduce_val_decl_type(
                    env, *rec, *inst, val_binds, term_map,
                )?;
                Ok(self.reg_decl(&x, &decl.span, decl.id))
            }
            DeclKind::Fun(fun_binds) => {
                let val_decl = self.convert_fun_to_val(env, fun_binds);
                self.deduce_decl_type(env, &val_decl, term_map)
            }
            DeclKind::Signature(_) => {
                // Signatures don't have types themselves in the type system.
                // They are purely compile-time constructs for defining
                // interfaces. For now, we just return the original
                // declaration unchanged.
                // TODO: Implement proper signature type checking once
                // structures are added.
                Ok(decl.clone())
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
    /// If there is a type annotation, it is applied to the body of the
    /// innermost `fn`: `fun sum x y: int = x + y` becomes
    /// `val rec sum = fn x => fn y => ((x + y): int)`.
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
    ) -> Decl {
        let val_bind_list: Vec<ValBind> = fun_binds
            .iter()
            .map(|fun_bind| self.convert_fun_bind_to_val_bind(env, fun_bind))
            .collect();

        let x = DeclKind::Val(true, false, val_bind_list);
        let span = Span::sum(fun_binds, |b| b.span.clone());
        x.spanned(&span.unwrap())
    }

    fn convert_fun_bind_to_val_bind(
        &mut self,
        _env: &dyn TypeEnv,
        fun_bind: &FunBind,
    ) -> ValBind {
        let vars: Vec<Pat>;
        let mut expr: Expr;
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
                    pat: self.pat_tuple(&span, &fun_match.pats),
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

            let x = ExprKind::Case(
                Box::new(self.id_tuple(&span, &var_names)),
                match_list,
            );
            expr = x.spanned(&span);
        }

        if let Some(type_) = type_annotation {
            let x = ExprKind::Annotated(Box::new(expr), type_);
            expr = x.spanned(&span);
        }

        for var in vars.iter().rev() {
            let pat = var.clone();
            let kind = ExprKind::Fn(vec![Match { pat, expr }]);
            expr = kind.spanned(&span);
        }

        ValBind {
            pat: PatKind::Identifier(fun_bind.name.clone()).spanned(&span),
            type_annotation: None,
            expr,
        }
    }

    fn all_the_same<T: PartialEq>(list: &[T]) -> bool {
        list.iter().all(|x| list.iter().all(|y| x == y))
    }

    /// Converts a list of variable names to a variable or tuple.
    ///
    /// For example, `["x"]` becomes `x` (an `Id`), and `["x", "y"]`
    /// becomes `(x, y)` (a `Tuple` of `Id`s).
    fn id_tuple(&self, span: &Span, vars: &[String]) -> Expr {
        let id_list: Vec<Expr> = vars
            .iter()
            .map(|v| ExprKind::Identifier(v.to_string()).spanned(span))
            .collect();

        if id_list.len() == 1 {
            id_list.into_iter().next().unwrap()
        } else {
            ExprKind::Tuple(id_list).spanned(span)
        }
    }

    /// Converts a list of patterns to a singleton pattern or tuple pattern.
    fn pat_tuple(&self, span: &Span, pat_list: &[Pat]) -> Pat {
        if pat_list.is_empty() {
            PatKind::Literal(LiteralKind::Unit.spanned(span)).spanned(span)
        } else if pat_list.len() == 1 {
            pat_list.first().unwrap().clone()
        } else {
            PatKind::Tuple(pat_list.to_vec())
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
    ) -> Result<DeclKind, Error> {
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
                self.deduce_val_bind_type(&*env2, &val_bind, term_map, &var)?;
            val_binds2.push(val_bind2);
        }

        Ok(DeclKind::Val(rec, inst, val_binds2))
    }

    /// Converts a type AST node to a type term.
    fn deduce_type_type(
        &mut self,
        env: &dyn TypeEnv,
        type_: &AstType,
        v: &Rc<Var>,
    ) -> AstType {
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
    ) -> AstType {
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
    fn deduce_expr_type(
        &mut self,
        env: &dyn TypeEnv,
        expr: &Expr,
        v: &Rc<Var>,
    ) -> Result<Expr, Error> {
        Ok(match &expr.kind {
            // lint: sort until '#}' where '##ExprKind::'
            ExprKind::AndAlso(left, right) => {
                let (left2, right2) =
                    self.deduce_call2_type(env, "op andalso", left, right, v)?;
                let x = ExprKind::AndAlso(Box::new(left2), Box::new(right2));
                self.reg_expr(&x, &expr.span, expr.id, v)
            }
            ExprKind::Annotated(e, t) => {
                let e2 = self.deduce_expr_type(env, e, v)?;
                let t2 = self.deduce_type_type(env, &t, v);
                let x = ExprKind::Annotated(Box::new(e2), Box::new(t2));
                self.reg_expr(&x, &expr.span, expr.id, v)
            }
            ExprKind::Append(left, right) => {
                let (left2, right2) =
                    self.deduce_call2_type(env, "op @", left, right, v)?;
                let x = ExprKind::Append(Box::new(left2), Box::new(right2));
                self.reg_expr(&x, &expr.span, expr.id, v)
            }
            ExprKind::Apply(left, right) => {
                let (left2, right2) =
                    self.deduce_apply_type(env, &left, &right, v)?;
                let apply2 = ExprKind::Apply(Box::new(left2), Box::new(right2));
                self.reg_expr(&apply2, &expr.span, expr.id, v)
            }
            ExprKind::Caret(left, right) => {
                let (left2, right2) =
                    self.deduce_call2_type(env, "op ^", left, right, v)?;
                let x = ExprKind::Caret(Box::new(left2), Box::new(right2));
                self.reg_expr(&x, &expr.span, expr.id, v)
            }
            ExprKind::Case(e, match_list) => {
                let v_e = self.unifier.variable();
                let e2 = self.deduce_expr_type(env, e, &v_e)?;
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
                )?;

                let x = ExprKind::Case(Box::new(e2), match_list2);
                self.reg_expr(&x, &expr.span, expr.id, v)
            }
            ExprKind::Cons(left, right) => {
                let (left2, right2) =
                    self.deduce_call2_type(env, "op ::", left, right, v)?;
                let x = ExprKind::Cons(Box::new(left2), Box::new(right2));
                self.reg_expr(&x, &expr.span, expr.id, v)
            }
            ExprKind::Div(left, right) => {
                let (left2, right2) =
                    self.deduce_call2_type(env, "op div", left, right, v)?;
                let x = ExprKind::Div(Box::new(left2), Box::new(right2));
                self.reg_expr(&x, &expr.span, expr.id, v)
            }
            ExprKind::Divide(left, right) => {
                let (left2, right2) =
                    self.deduce_call2_type(env, "op /", left, right, v)?;
                let x = ExprKind::Divide(Box::new(left2), Box::new(right2));
                self.reg_expr(&x, &expr.span, expr.id, v)
            }
            ExprKind::Elements => {
                self.check_in_compute(env, &expr.span)?;
                let step_env = self.compute_stack.last().unwrap();
                self.equiv(&Term::Variable(step_env.clone().c.unwrap()), v);
                self.reg_expr(&expr.kind, &expr.span, expr.id, &v)
            }
            ExprKind::Equal(left, right) => {
                let (left2, right2) =
                    self.deduce_call2_type(env, "op =", left, right, v)?;
                let x = ExprKind::Equal(Box::new(left2), Box::new(right2));
                self.reg_expr(&x, &expr.span, expr.id, v)
            }
            ExprKind::Exists(steps) => {
                let steps2 = self.deduce_query_type(env, expr, steps, v)?;
                let x = ExprKind::Exists(steps2);
                self.reg_expr(&x, &expr.span, expr.id, v)
            }
            ExprKind::Fn(matches) => {
                let mut matches2 = Vec::new();
                let v_param = self.variable();
                let v_result = self.variable();
                for match_ in matches {
                    matches2.push(
                        self.deduce_match_type(
                            env, match_, &v_param, &v_result,
                        )?,
                    );
                }
                self.fn_term(&v_param, &v_result, v);
                let fn2 = &ExprKind::Fn(matches2);
                self.reg_expr(fn2, &expr.span, expr.id, v)
            }
            ExprKind::Forall(steps) => {
                let steps2 = self.deduce_query_type(env, expr, steps, v)?;
                let x = ExprKind::Forall(steps2);
                self.reg_expr(&x, &expr.span, expr.id, v)
            }
            ExprKind::From(steps) => {
                let steps2 = self.deduce_query_type(env, expr, steps, v)?;
                let x = ExprKind::From(steps2);
                self.reg_expr(&x, &expr.span, expr.id, v)
            }
            ExprKind::GreaterThan(left, right) => {
                let (left2, right2) =
                    self.deduce_call2_type(env, "op >", left, right, v)?;
                let x =
                    ExprKind::GreaterThan(Box::new(left2), Box::new(right2));
                self.reg_expr(&x, &expr.span, expr.id, v)
            }
            ExprKind::GreaterThanOrEqual(left, right) => {
                let (left2, right2) =
                    self.deduce_call2_type(env, "op >=", left, right, v)?;
                let x = ExprKind::GreaterThanOrEqual(
                    Box::new(left2),
                    Box::new(right2),
                );
                self.reg_expr(&x, &expr.span, expr.id, v)
            }
            ExprKind::Identifier(name) => {
                let lookup_result =
                    if let Some(bare_name) = name.strip_prefix("op ") {
                        // Try "op <name>" first, then fall back to bare name
                        env.get(name, self).or_else(|| env.get(bare_name, self))
                    } else {
                        env.get(name, self)
                    };
                match lookup_result {
                    Some(BindType::Val(term))
                    | Some(BindType::Constructor(term)) => {
                        self.equiv(&term, v);
                    }
                    None => {
                        todo!("identifier '{}' not found", name);
                    }
                }
                self.reg_expr(&expr.kind, &expr.span, expr.id, v)
            }
            ExprKind::If(a0, a1, a2) => {
                let (a02, a12, a22) =
                    self.deduce_call3_type(env, "op if", a0, a1, a2, v)?;
                let x =
                    ExprKind::If(Box::new(a02), Box::new(a12), Box::new(a22));
                self.reg_expr(&x, &expr.span, expr.id, v)
            }
            ExprKind::Implies(left, right) => {
                let (left2, right2) =
                    self.deduce_call2_type(env, "op implies", left, right, v)?;
                let x = ExprKind::Implies(Box::new(left2), Box::new(right2));
                self.reg_expr(&x, &expr.span, expr.id, v)
            }
            ExprKind::LessThan(left, right) => {
                let (left2, right2) =
                    self.deduce_call2_type(env, "op <", left, right, v)?;
                let x = ExprKind::LessThan(Box::new(left2), Box::new(right2));
                self.reg_expr(&x, &expr.span, expr.id, v)
            }
            ExprKind::LessThanOrEqual(left, right) => {
                let (left2, right2) =
                    self.deduce_call2_type(env, "op <=", left, right, v)?;
                let x = ExprKind::LessThanOrEqual(
                    Box::new(left2),
                    Box::new(right2),
                );
                self.reg_expr(&x, &expr.span, expr.id, v)
            }
            ExprKind::Let(decl_list, expr) => {
                let mut term_map = Vec::new();
                let mut decl_list2 = Vec::new();
                for decl in decl_list {
                    let decl2 =
                        self.deduce_decl_type(env, decl, &mut term_map)?;
                    decl_list2.push(decl2);
                }
                let env2 = env.bind_all(term_map.as_ref());
                let expr2 = self.deduce_expr_type(&*env2, expr, v)?;
                let x = ExprKind::Let(decl_list2, Box::new(expr2));
                self.reg_expr(&x, &expr.span, expr.id, v)
            }
            ExprKind::List(expr_list) => {
                let v_element = self.variable();
                let x = if expr_list.is_empty() {
                    // Don't link v0 to anything. It becomes a type variable.
                    expr.kind.clone()
                } else {
                    let mut expr_list2 = Vec::new();
                    expr_list2.push(self.deduce_expr_type(
                        env,
                        expr_list.first().unwrap(),
                        &v_element,
                    )?);
                    for expr in expr_list.iter().skip(1) {
                        let v2 = self.variable();
                        expr_list2.push(self.deduce_expr_type(env, expr, &v2)?);
                        self.equiv(&Term::Variable(v2), &v_element.clone());
                    }
                    ExprKind::List(expr_list2)
                };
                self.list_term(Term::Variable(v_element), v);
                self.reg_expr(&x, &expr.span, expr.id, v)
            }
            ExprKind::Literal(lit) => {
                let resolved_type = Self::literal_type(&lit.kind);
                self.primitive_term(&resolved_type, v);
                self.reg_expr(&expr.kind, &expr.span, expr.id, v)
            }
            ExprKind::Minus(left, right) => {
                let (left2, right2) =
                    self.deduce_call2_type(env, "op -", left, right, v)?;
                let x = ExprKind::Minus(Box::new(left2), Box::new(right2));
                self.reg_expr(&x, &expr.span, expr.id, v)
            }
            ExprKind::Mod(left, right) => {
                let (left2, right2) =
                    self.deduce_call2_type(env, "op mod", left, right, v)?;
                let x = ExprKind::Mod(Box::new(left2), Box::new(right2));
                self.reg_expr(&x, &expr.span, expr.id, v)
            }
            ExprKind::Negate(e) => {
                let e2 =
                    self.deduce_call1_type(env, "op ~", e, &expr.span, v)?;
                let x = ExprKind::Negate(Box::new(e2));
                self.reg_expr(&x, &expr.span, expr.id, v)
            }
            ExprKind::NotEqual(left, right) => {
                let (left2, right2) =
                    self.deduce_call2_type(env, "op <>", left, right, v)?;
                let x = ExprKind::NotEqual(Box::new(left2), Box::new(right2));
                self.reg_expr(&x, &expr.span, expr.id, v)
            }
            ExprKind::OpSection(name) => {
                let op_name = format!("op {}", name);
                match env.get(&op_name, self).or_else(|| env.get(name, self)) {
                    Some(BindType::Val(term))
                    | Some(BindType::Constructor(term)) => {
                        self.equiv(&term, v);
                    }
                    None => {
                        todo!("identifier '{}' not found", op_name);
                    }
                }
                self.reg_expr(&expr.kind, &expr.span, expr.id, v)
            }
            ExprKind::OrElse(left, right) => {
                let (left2, right2) =
                    self.deduce_call2_type(env, "op orelse", left, right, v)?;
                let x = ExprKind::OrElse(Box::new(left2), Box::new(right2));
                self.reg_expr(&x, &expr.span, expr.id, v)
            }
            ExprKind::Plus(left, right) => {
                let (left2, right2) =
                    self.deduce_call2_type(env, "op +", left, right, v)?;
                let x = ExprKind::Plus(Box::new(left2), Box::new(right2));
                self.reg_expr(&x, &expr.span, expr.id, v)
            }
            ExprKind::Record(with_expr, labeled_expr_list) => {
                let mut field_vars = Vec::new(); // never read
                let labeled_expr_list2 = self.deduce_record_type(
                    env,
                    labeled_expr_list,
                    &mut field_vars,
                    v,
                )?;
                let x = ExprKind::Record(with_expr.clone(), labeled_expr_list2);
                self.reg_expr(&x, &expr.span, expr.id, v)
            }
            ExprKind::Times(left, right) => {
                let (left2, right2) =
                    self.deduce_call2_type(env, "op *", left, right, v)?;
                let x = ExprKind::Times(Box::new(left2), Box::new(right2));
                self.reg_expr(&x, &expr.span, expr.id, v)
            }
            ExprKind::Tuple(expr_list) => {
                let mut terms = Vec::new();
                let mut expr_list2 = Vec::new();
                for e in expr_list {
                    let v2 = self.variable();
                    expr_list2.push(self.deduce_expr_type(env, e, &v2)?);
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
            _ => todo!("{:?}", expr.kind),
        })
    }

    /// Deduces a query's type.
    ///
    /// A query is a `from`, `forall` or `exists` expression.
    fn deduce_query_type(
        &mut self,
        env: &dyn TypeEnv,
        query: &Expr,
        steps: &[Step],
        v: &Rc<Var>,
    ) -> Result<Vec<Step>, Error> {
        let mut field_vars = Vec::new();
        let mut steps2 = Vec::new();

        // An empty "from" is "unit list". Ordered.
        let v11 = self.variable();
        let c11 = self.variable();
        self.record_term(&BTreeMap::new(), &v11);
        self.list_term(Term::Variable(v11.clone()), &c11);
        // Create an Rc<dyn TypeEnv> from the borrowed env
        let env_rc = env.bind_all(&[]);
        let mut p = Triple::new(env_rc.clone(), env_rc.clone(), v11, Some(c11));

        for (i, step) in steps.iter().enumerate() {
            let last_step = i == steps.len() - 1;

            // Validate step placement before processing
            match step.kind {
                StepKind::Compute(_)
                | StepKind::Into(_)
                | StepKind::Require(_) => {
                    match (&step.kind, &query.kind) {
                        (StepKind::Require(_), ExprKind::Forall(_)) => Ok(()),
                        (StepKind::Compute(_), ExprKind::From(_)) => Ok(()),
                        (StepKind::Into(_), ExprKind::From(_)) => Ok(()),
                        _ => {
                            let message = format!(
                                "'{}' step must not occur in '{}'",
                                step.kind.clause(),
                                query.kind.clause()
                            );
                            Err(Error::Compile(message, step.span.clone()))
                        }
                    }?;

                    if !last_step {
                        let message = format!(
                            "'{}' step must be last in '{}'",
                            step.kind.clause(),
                            query.kind.clause()
                        );
                        return Err(Error::Compile(
                            message,
                            steps[i + 1].span.clone(),
                        ));
                    }
                }
                _ => {}
            }

            let p_next =
                self.deduce_step_type(&step, &p, &mut field_vars, &mut steps2)?;
            p = p_next;
        }

        // "forall" query must have "require" as the last step.
        if matches!(query.kind, ExprKind::Forall(_)) {
            if steps.is_empty() {
                return missing_format(&query, &query.span);
            }
            if let Some(step) = steps.last()
                && !matches!(step.kind, StepKind::Require(_))
            {
                return missing_format(&query, &step.span);
            }
        }

        // The result is a list of the element type, or bool for exists/forall,
        // or a singleton for compute/into.
        if matches!(query.kind, ExprKind::Exists(_) | ExprKind::Forall(_)) {
            self.primitive_term(&PrimitiveType::Bool, &v);
        } else if matches!(
            steps.last().map(|s| &s.kind),
            Some(StepKind::Compute(_)) | Some(StepKind::Into(_))
        ) {
            self.equiv(&Term::Variable(p.v), v);
        } else {
            self.equiv(&Term::Variable(p.c.unwrap()), v);
        };

        Ok(steps2)
    }

    /// Deduces a single step's type.
    ///
    /// The `Triple` argument `p` represents the element and collection
    /// types of the input to the step, and the return `Triple` represents
    /// the output type.
    fn deduce_step_type(
        &mut self,
        step: &Step,
        p: &Triple,
        field_vars: &mut Vec<(String, Rc<Var>)>,
        steps2: &mut Vec<Step>,
    ) -> Result<Triple, Error> {
        match &step.kind {
            // lint: sort until '#}' where '##StepKind::'
            StepKind::Compute(expr) => self.deduce_compute_step_type(
                p, expr, &step.span, field_vars, steps2,
            ),
            StepKind::Distinct => {
                steps2.push(step.clone());
                Ok(p.clone())
            }
            StepKind::Except(distinct, exprs)
            | StepKind::Intersect(distinct, exprs)
            | StepKind::Union(distinct, exprs) => self.deduce_set_step_type(
                p, &step.kind, *distinct, exprs, &step.span, steps2,
            ),
            StepKind::Group(key_expr, compute_expr) => self
                .deduce_group_step_type(
                    p,
                    key_expr,
                    compute_expr.as_deref(),
                    &step.span,
                    field_vars,
                    steps2,
                ),
            StepKind::Into(expr) => {
                self.deduce_into_step_type(p, expr, &step.span, steps2)
            }
            StepKind::Order(expr) => {
                let v = self.unifier.variable();
                let expr2 = self.deduce_expr_type(&*p.env, expr, &v)?;
                let expr3 = self.validate_order(&expr2);
                let step2 = StepKind::Order(Box::new(expr3));
                steps2.push(step2.spanned(&step.span));
                Ok(p.clone())
            }
            StepKind::Require(expr) => {
                let v = self.unifier.variable();
                let expr2 = self.deduce_expr_type(&*p.env, expr, &v)?;
                self.primitive_term(&PrimitiveType::Bool, &v);
                let step2 = StepKind::Require(Box::new(expr2));
                steps2.push(step2.spanned(&step.span));
                Ok(p.clone())
            }
            StepKind::Scan(pat, expr, condition) => self.deduce_scan_step_type(
                p,
                pat,
                false,
                Some(&**expr),
                condition,
                &step.span,
                field_vars,
                steps2,
            ),
            StepKind::ScanEq(pat, expr) => self.deduce_scan_step_type(
                p,
                pat,
                true,
                Some(&**expr),
                &None,
                &step.span,
                field_vars,
                steps2,
            ),
            StepKind::ScanExtent(pat) => self.deduce_scan_step_type(
                p, pat, true, None, &None, &step.span, field_vars, steps2,
            ),
            StepKind::Skip(expr) => {
                let v = self.unifier.variable();
                let expr2 = self.deduce_expr_type(&*p.env, expr, &v)?;
                self.primitive_term(&PrimitiveType::Int, &v);
                let step2 = StepKind::Skip(Box::new(expr2));
                steps2.push(step2.spanned(&step.span));
                Ok(p.clone())
            }
            StepKind::Take(expr) => {
                let v = self.unifier.variable();
                let expr2 = self.deduce_expr_type(&*p.env, expr, &v)?;
                self.primitive_term(&PrimitiveType::Int, &v);
                let step2 = StepKind::Take(Box::new(expr2));
                steps2.push(step2.spanned(&step.span));
                Ok(p.clone())
            }
            StepKind::Through(pat, expr) => self.deduce_through_step_type(
                p, pat, expr, &step.span, field_vars, steps2,
            ),
            StepKind::Unorder => {
                let c = self.variable();
                self.bag_term(Term::Variable(p.v.clone()), &c);
                steps2.push(StepKind::Unorder.spanned(&step.span));
                Ok(p.with_c(c))
            }
            StepKind::Where(expr) => {
                let v = self.unifier.variable();
                let expr2 = self.deduce_expr_type(&*p.env, expr, &v)?;
                self.primitive_term(&PrimitiveType::Bool, &v);
                let step2 = StepKind::Where(Box::new(expr2));
                steps2.push(step2.spanned(&step.span));
                Ok(p.clone())
            }
            StepKind::Yield(expr) => self.deduce_yield_step_type(
                p, expr, &step.span, field_vars, steps2,
            ),
        }
    }

    /// Deduces a Scan step's type.
    ///
    /// Examples:
    /// * "from i in [1, 2, 3]";
    /// * "join d in departments on d.deptno = e.deptno"
    ///   (has `condition`);
    /// * "from i in [1, 2, 3], j = i + 1" (has `eq` = true).
    fn deduce_scan_step_type(
        &mut self,
        p: &Triple,
        pat: &Pat,
        eq: bool,
        expr: Option<&Expr>,
        condition: &Option<Box<Expr>>,
        span: &Span,
        field_vars: &mut Vec<(String, Rc<Var>)>,
        steps: &mut Vec<Step>,
    ) -> Result<Triple, Error> {
        // Deduce the type of the expression being iterated over
        let v0 = self.variable();
        let c0 = self.variable();

        self.list_term(Term::Variable(v0.clone()), &c0);
        let expr2 = self.deduce_expr_type(
            &*p.env,
            expr.unwrap(),
            if eq { &v0 } else { &c0 },
        )?;

        // Deduce the type of the pattern and bind variables.
        let mut term_map = Vec::new();
        let pat2 = self.deduce_pat_type(&*p.env, pat, &mut term_map, &v0);

        // Build a new environment with pattern bindings.
        let mut env_builder = p.env.builder();
        for (name, term) in &term_map {
            env_builder.push(name.clone(), term.clone());
            let v = self.term_to_variable(term);
            self.reg_expr(&ExprKind::Identifier(name.clone()), span, None, &v);
            field_vars.push((name.clone(), v));
        }
        let env4 = env_builder.build();

        // Determine collection type - simplified for now, just use list.
        // TODO: Implement full collection type logic from Java
        // (is_list_or_bag_matching_input, is_list_if_both_are_lists,
        // may_be_bag_or_list)
        let v = self.field_var(field_vars, true);
        let c = self.unifier.variable();
        self.list_term(Term::Variable(v.clone()), &c);

        // Handle the condition, if present.
        let condition2 = if let Some(cond) = condition {
            let v5 = self.variable();
            let condition2 = self.deduce_expr_type(&*env4, cond, &v5)?;
            self.primitive_term(&PrimitiveType::Bool, &v5);
            Some(Box::new(condition2))
        } else {
            None
        };

        let step = StepKind::Scan(Box::new(pat2), Box::new(expr2), condition2);
        steps.push(step.spanned(span));

        Ok(Triple::new(p.root_env.clone(), env4, v, Some(c)))
    }

    /// Deduces a Yield step's type (e.g., "yield i + 4").
    fn deduce_yield_step_type(
        &mut self,
        p: &Triple,
        expr: &Expr,
        span: &Span,
        field_vars: &mut Vec<(String, Rc<Var>)>,
        steps2: &mut Vec<Step>,
    ) -> Result<Triple, Error> {
        // The yield expression determines the new element type
        let v6 = self.variable();
        let expr2 = self.deduce_expr_type(&*p.env, expr, &v6)?;

        let step = StepKind::Yield(Box::new(expr2.clone()));
        steps2.push(step.spanned(span));

        // Output is ordered iff input is ordered. Yield behaves like a
        // 'map' function with these overloaded forms:
        //  * map: 'a -> 'b -> 'a list -> 'b list
        //  * map: 'a -> 'b -> 'a bag -> 'b bag
        let c6 = self.variable();
        self.list_term(Term::Variable(v6.clone()), &c6);

        let mut envs = p.env.builder();
        if let ExprKind::Record(with, labeled_exprs) = expr2.kind {
            let mut v = None;
            if let Some(with) = with
                && let Some(id) = with.id
            {
                v = self.node_var_map.get(&id);
            }
            if let None = v
                && let Some(id) = expr2.id
            {
                v = self.node_var_map.get(&id);
            }
            if let Some(v) = v
                && let Some(vt) = self.terms.iter().find(|vt| vt.0 == *v)
                && let Term::Sequence(seq) = &vt.1
            {
                // Clone the terms to avoid holding immutable borrow of self
                let seq_terms = seq.terms.clone();
                field_vars.clear();
                assert_eq!(labeled_exprs.len(), seq_terms.len());
                for (labeled_expr, term) in zip(labeled_exprs, seq_terms.iter())
                {
                    if let Some(label) = labeled_expr.get_label() {
                        field_vars.push((
                            label.clone(),
                            self.term_to_variable(&term),
                        ));
                        envs.push(label, term.clone());
                    } else {
                        return Err(Error::Compile(
                            format!(
                                "cannot derive label for expression {}",
                                labeled_expr.expr.span.code()
                            ),
                            labeled_expr.expr.span.clone(),
                        ));
                    }
                }
            }
        } else {
            let label = expr
                .implicit_label_opt()
                .unwrap_or_else(|| ExprKind::Current.clause().to_string());
            envs.push(label.clone(), Term::Variable(v6.clone()));
            field_vars.clear();
            field_vars.push((label, v6.clone()));
        }
        let env = envs.build();

        Ok(Triple::new(p.root_env.clone(), env, v6, Some(c6)))
    }

    /// Deduces a set operation step's type (Union/Except/Intersect).
    fn deduce_set_step_type(
        &mut self,
        p: &Triple,
        step_kind: &StepKind,
        distinct: bool,
        exprs: &[Expr],
        span: &Span,
        steps2: &mut Vec<Step>,
    ) -> Result<Triple, Error> {
        // All branches must have the same element type
        // Start with current collection's element type
        let element_type = p.v.clone();

        // Collect terms for all collections
        let mut terms = vec![Term::Variable(p.c.clone().unwrap())];
        let mut exprs2 = Vec::new();

        // Deduce each argument expression and unify with element type
        for expr in exprs {
            let c_arg = self.variable();
            let expr2 = self.deduce_expr_type(&*p.root_env, expr, &c_arg)?;
            exprs2.push(expr2);

            // Extract the element type from this collection and unify with
            // the common element type.
            let v_arg = self.variable();
            self.list_term(Term::Variable(v_arg.clone()), &c_arg);
            self.equiv(&Term::Variable(v_arg), &element_type);

            terms.push(Term::Variable(c_arg));
        }

        // Result collection has the same element type
        let c_result = self.variable();
        self.list_term(Term::Variable(element_type), &c_result);

        // Create the appropriate step with deduced expressions
        let step2 = match step_kind {
            StepKind::Union(_, _) => StepKind::Union(distinct, exprs2),
            StepKind::Except(_, _) => StepKind::Except(distinct, exprs2),
            StepKind::Intersect(_, _) => StepKind::Intersect(distinct, exprs2),
            _ => unreachable!(),
        };
        steps2.push(step2.spanned(span));

        Ok(Triple::new(
            p.root_env.clone(),
            p.env.clone(),
            p.v.clone(),
            Some(c_result),
        ))
    }

    /// Throws if the current expression is not within a `compute` clause.
    fn check_in_compute(
        &mut self,
        env: &dyn TypeEnv,
        span: &Span,
    ) -> Result<(), Error> {
        if env.get(ExprKind::Elements.clause(), self).is_some() {
            Ok(())
        } else {
            Err(Error::Compile(
                format!(
                    "'{}' is only valid in a '{}' clause",
                    ExprKind::Elements.clause(),
                    StepKind::Compute(Expr::empty()).clause()
                ),
                span.clone(),
            ))
        }
    }

    /// Validates a Group step. Throws an error if labels cannot be derived
    /// for non-record expressions in group or compute clauses, or if there are
    /// duplicate field names between key and compute.
    ///
    /// This validation only applies to non-atom groups. An atom group is one
    /// where the total field count is 1, and neither expression is a singleton
    /// record.
    ///
    /// Returns whether the Group's output is an atom.
    fn validate_group(
        key_expr: &Expr,
        compute_expr: Option<&Expr>,
    ) -> Result<bool, Error> {
        // Count fields in key and compute expressions.
        let key_field_count = Self::field_count(key_expr);
        let compute_field_count =
            compute_expr.as_ref().map_or(0, |e| Self::field_count(e));

        // Check if this is an atom group (returns a single value, not a
        // record).
        let is_atom = (key_field_count + compute_field_count == 1)
            && !Self::is_singleton_record(Some(key_expr))
            && !Self::is_singleton_record(compute_expr);

        // Only validate non-atom groups.
        if !is_atom {
            // Validate key expression: if it's a record, check all fields;
            // if not a record, check that a label can be derived.
            if let ExprKind::Record(_, labeled_exprs) = &key_expr.kind {
                Self::validate_record_fields(labeled_exprs, "group")?;
            } else if key_expr.implicit_label_opt().is_none() {
                return Err(Error::Compile(
                    "cannot derive label for group expression".to_string(),
                    key_expr.span.clone(),
                ));
            }

            // Validate compute expression: if it's a record, check all fields;
            // if not a record, check that a label can be derived.
            if let Some(compute) = compute_expr {
                if let ExprKind::Record(_, labeled_exprs) = &compute.kind {
                    Self::validate_record_fields(labeled_exprs, "compute")?;
                } else if compute.implicit_label_opt().is_none() {
                    return Err(Error::Compile(
                        "cannot derive label for compute expression"
                            .to_string(),
                        compute.span.clone(),
                    ));
                }
            }

            // Check for duplicate field names between key and compute.
            Self::check_duplicate_field_names(key_expr, compute_expr)?;
        }

        Ok(is_atom)
    }

    /// Validates that all fields in a record have labels (either explicit or
    /// derivable implicitly).
    fn validate_record_fields(
        labeled_exprs: &[LabeledExpr],
        context: &str,
    ) -> Result<(), Error> {
        for labeled_expr in labeled_exprs {
            // Check if field has an explicit label or can derive one
            if labeled_expr.get_label().is_none() {
                return Err(Error::Compile(
                    format!("cannot derive label for {} expression", context),
                    labeled_expr.expr.span.clone(),
                ));
            }
        }
        Ok(())
    }

    /// Checks for duplicate field names between key and compute expressions.
    fn check_duplicate_field_names(
        key_expr: &Expr,
        compute_expr: Option<&Expr>,
    ) -> Result<(), Error> {
        let mut names = HashSet::new();

        // Collect field names from the key expression.
        Self::collect_field_names(key_expr, &mut names);

        // Check for duplicate field names in the compute expression.
        if let Some(compute) = compute_expr {
            if let ExprKind::Record(_, labeled_exprs) = &compute.kind {
                for labeled_expr in labeled_exprs {
                    if let Some(label) = labeled_expr.get_label() {
                        if !names.insert(label.clone()) {
                            return Err(Error::Compile(
                                format!(
                                    "Duplicate field name '{}' in group",
                                    label
                                ),
                                compute.span.clone(),
                            ));
                        }
                    }
                }
            }
        }

        Ok(())
    }

    /// Collects field names from an expression into the given set.
    fn collect_field_names(expr: &Expr, names: &mut HashSet<String>) {
        match &expr.kind {
            ExprKind::Record(_, labeled_exprs) => {
                for labeled_expr in labeled_exprs {
                    if let Some(label) = labeled_expr.get_label() {
                        names.insert(label);
                    }
                }
            }
            _ => {
                // For non-record expressions, use the implicit label if
                // available.
                if let Some(label) = expr.implicit_label_opt() {
                    names.insert(label);
                }
            }
        }
    }

    /// Returns the number of fields in an expression.
    /// For records, returns the number of labeled expressions.
    /// For other expressions, returns 1.
    fn field_count(expr: &Expr) -> usize {
        match &expr.kind {
            ExprKind::Record(_, labeled_exprs) => labeled_exprs.len(),
            _ => 1,
        }
    }

    /// Returns true if the expression is a singleton record (a record with
    /// exactly one field).
    fn is_singleton_record(expr: Option<&Expr>) -> bool {
        if let Some(expr) = expr
            && let ExprKind::Record(_, labeled_exprs) = &expr.kind
            && labeled_exprs.len() == 1
        {
            true
        } else {
            false
        }
    }

    /// Deduces a Group step's type.
    fn deduce_group_step_type(
        &mut self,
        p: &Triple,
        key_expr: &Expr,
        compute_expr: Option<&Expr>,
        span: &Span,
        field_vars: &mut Vec<(String, Rc<Var>)>,
        steps2: &mut Vec<Step>,
    ) -> Result<Triple, Error> {
        // Deduce whether the result is an atom, and if not an atom, make sure
        // that a unique label can be derived for each field.
        let atom = Self::validate_group(key_expr, compute_expr)?;

        field_vars.clear();

        // Process key expression(s). If the key is a record, process each
        // field; otherwise treat as a single field.
        let key_expr2;
        let v_key = self.variable();
        let mut group_env_builder = p.root_env.builder();

        if let ExprKind::Record(_with, labeled_exprs) = &key_expr.kind {
            let labeled_exprs2 = self.deduce_record_type(
                &*p.env,
                labeled_exprs,
                field_vars,
                &v_key,
            )?;

            key_expr2 = self.reg_expr(
                &ExprKind::Record(None, labeled_exprs2),
                &key_expr.span,
                key_expr.id,
                &v_key,
            );
        } else {
            key_expr2 = self.deduce_expr_type(&*p.env, key_expr, &v_key)?;
            if let Some(key_label) = key_expr2.implicit_label_opt() {
                field_vars.push((key_label, v_key));
            } else {
                field_vars
                    .push((ExprKind::Current.clause().to_string(), v_key));
            }
        }

        // Create the environment for the next step. It includes all key and
        // compute fields, and the "elements" variable.
        field_vars.iter().for_each(|(label, v)| {
            group_env_builder.push(label.clone(), Term::Variable(v.clone()));
        });
        group_env_builder.push(
            ExprKind::Elements.clause().to_string(),
            Term::Variable(p.c.clone().unwrap()),
        );
        let group_env = group_env_builder.build();

        // Process the compute expression, if present.
        let compute_expr2 = if let Some(compute) = compute_expr {
            self.compute_stack.push(p.with_env(&group_env));

            let v_compute = self.variable();
            let result = if let ExprKind::Record(_with, labeled_exprs) =
                &compute.kind
            {
                // Multiple compute fields.
                let mut labeled_exprs2 = Vec::new();
                let start = field_vars.len();
                for labeled_expr in labeled_exprs {
                    let v_field = self.variable();
                    let expr2 = self.deduce_expr_type(
                        &*group_env,
                        &labeled_expr.expr,
                        &v_field,
                    )?;
                    let label = labeled_expr
                        .get_label()
                        .unwrap_or_else(|| "agg".to_string());

                    field_vars.push((label, v_field));

                    labeled_exprs2.push(LabeledExpr {
                        label: labeled_expr.label.clone(),
                        expr: expr2,
                    });
                }
                let mut map: BTreeMap<Label, Term> = BTreeMap::new();
                field_vars.iter().skip(start).for_each(|fv| {
                    map.insert(
                        Label::String(fv.0.clone()),
                        Term::Variable(fv.1.clone()),
                    );
                });
                self.record_term(&map, &v_compute);
                let x = ExprKind::Record(None, labeled_exprs2);
                Some(Box::new(self.reg_expr(
                    &x,
                    &compute.span,
                    compute.id,
                    &v_compute,
                )))
            } else {
                // Single compute expression.
                let expr2 =
                    self.deduce_expr_type(&*group_env, compute, &v_compute)?;
                let label = expr2
                    .implicit_label_opt()
                    .unwrap_or_else(|| "compute".to_string());
                field_vars.push((label, v_compute));
                Some(Box::new(expr2))
            };

            self.compute_stack.pop();
            result
        } else {
            None
        };

        // Build the result type based on field_vars.
        // If there is a single field with the default label "key" and no
        // compute, return the atom type. Likewise, return the atom type if
        // there is no key (empty tuple) and a single compute field.
        let v_result = if field_vars.len() == 1 && atom {
            field_vars[0].1.clone()
        } else {
            self.field_var(field_vars, false)
        };
        let c_result = self.variable();

        // Output is ordered iff input is ordered (list or bag).
        self.list_term(Term::Variable(v_result.clone()), &c_result);

        let step2 = StepKind::Group(Box::new(key_expr2), compute_expr2);
        steps2.push(step2.spanned(span));

        Ok(Triple::new(
            p.root_env.clone(),
            group_env,
            v_result,
            Some(c_result),
        ))
    }

    /// Deduces a Compute step's type.
    ///
    /// `compute` is similar to `group` but has no key, aggregates over the
    /// entire collection, and returns a single element (not a collection).
    fn deduce_compute_step_type(
        &mut self,
        p: &Triple,
        compute_expr: &Expr,
        span: &Span,
        field_vars: &mut Vec<(String, Rc<Var>)>,
        steps2: &mut Vec<Step>,
    ) -> Result<Triple, Error> {
        field_vars.clear();

        // Bind 'elements' to the current collection
        let mut compute_env_builder = p.root_env.builder();
        compute_env_builder.push(
            ExprKind::Elements.clause().to_string(),
            Term::Variable(p.c.clone().unwrap()),
        );
        let compute_env = compute_env_builder.build();
        self.compute_stack.push(p.with_env(&compute_env));

        // Process compute expression
        let compute_expr2;
        if let ExprKind::Record(_with, labeled_exprs) = &compute_expr.kind {
            // Multiple compute fields
            let mut labeled_exprs2 = Vec::new();
            for labeled_expr in labeled_exprs {
                let v_field = self.variable();
                let expr2 = self.deduce_expr_type(
                    &*compute_env,
                    &labeled_expr.expr,
                    &v_field,
                )?;
                let label = labeled_expr
                    .get_label()
                    .unwrap_or_else(|| "agg".to_string());

                field_vars.push((label, v_field));

                labeled_exprs2.push(LabeledExpr {
                    label: labeled_expr.label.clone(),
                    expr: expr2,
                });
            }
            compute_expr2 = Expr {
                kind: ExprKind::Record(None, labeled_exprs2),
                span: compute_expr.span.clone(),
                id: compute_expr.id,
            };
        } else {
            // Single compute expression - return the value directly.
            let v_compute = self.variable();
            compute_expr2 =
                self.deduce_expr_type(&*compute_env, compute_expr, &v_compute)?;
            field_vars.clear(); // Don't wrap in a record.
            field_vars.push(("compute".to_string(), v_compute.clone()));
        }

        self.compute_stack.pop();

        // Compute returns a singleton (not a collection). If it is a single
        // expression, return it directly; if record, use field_var.
        let v_result = if field_vars.len() == 1 && field_vars[0].0 == "compute"
        {
            field_vars[0].1.clone()
        } else {
            self.field_var(field_vars, false)
        };

        let step2 = StepKind::Compute(Box::new(compute_expr2));
        steps2.push(step2.spanned(span));

        // Return as a singleton (no collection variable).
        let result_env = p.root_env.bind_all(&[]);
        Ok(Triple::new(
            p.root_env.clone(),
            result_env,
            v_result,
            None, // Compute produces a singleton, not a collection.
        ))
    }

    /// Deduces an Into step's type.
    ///
    /// `into` is a terminal step that applies a function. For example
    ///
    /// ```sml
    /// from i in [1,2,3] into f
    /// ```
    ///
    /// If `f`'s type is `int list -> string`, the result type is `string`.
    fn deduce_into_step_type(
        &mut self,
        p: &Triple,
        expr: &Expr,
        span: &Span,
        steps2: &mut Vec<Step>,
    ) -> Result<Triple, Error> {
        let v_result = self.variable();
        let v_fn = self.variable();

        // Deduce the type of the function expression.
        let expr2 = self.deduce_expr_type(&*p.env, expr, &v_fn)?;

        // The function must have type: current_collection -> result.
        // Create the function type: c -> v_result.
        self.fn_term(&p.c.clone().unwrap(), &v_result, &v_fn);

        let step2 = StepKind::Into(Box::new(expr2));
        steps2.push(step2.spanned(span));

        // Into produces a singleton (not a collection).
        let result_env = p.root_env.bind_all(&[]);
        Ok(Triple::new(
            p.root_env.clone(),
            result_env,
            v_result,
            None, // Singleton result.
        ))
    }

    /// Deduces a `Through` step's type.
    ///
    /// `through` invokes a table function. Consider
    ///
    /// ```sml
    /// from i in [1,2,3] through p in f
    /// ```
    ///
    /// If `f`'s type is `int list -> string list`, and `p`'s type is `string`,
    /// the result type is `string list`.
    fn deduce_through_step_type(
        &mut self,
        p: &Triple,
        pat: &Pat,
        expr: &Expr,
        span: &Span,
        field_vars: &mut Vec<(String, Rc<Var>)>,
        steps2: &mut Vec<Step>,
    ) -> Result<Triple, Error> {
        let v_element = self.variable();
        let c_result = self.variable();

        // The input collection (p.c) is either a bag of p.v or a list of p.v.
        self.may_be_bag_or_list(&p.c.clone().unwrap(), &p.v);

        // Deduce the pattern type.
        let mut term_map = Vec::new();
        let pat2 =
            self.deduce_pat_type(&*p.root_env, pat, &mut term_map, &v_element);

        // The function must have type: current_collection -> result_collection.
        let v_fn = self.variable();
        self.fn_term(&p.c.clone().unwrap(), &c_result, &v_fn);

        let expr2 = self.deduce_expr_type(&*p.env, expr, &v_fn)?;

        // The result collection may be a bag or list.
        self.may_be_bag_or_list(&c_result, &v_element);

        let step2 = StepKind::Through(Box::new(pat2.clone()), Box::new(expr2));
        steps2.push(step2.spanned(span));

        // Build the environment with pattern bindings added to existing env.
        let mut env5 = p.env.clone();
        // Keep the existing field_vars and add new ones from the pattern.
        for (name, term) in term_map {
            env5 = env5.bind(name.clone(), term.clone());
            if let Term::Variable(v) = &term {
                field_vars.push((name, v.clone()));
            }
        }

        // The result element type is a record of all field_vars.
        let v_result = self.variable();
        let mut map: BTreeMap<Label, Term> = BTreeMap::new();
        for (name, var) in field_vars.iter() {
            map.insert(Label::from(name.clone()), Term::Variable(var.clone()));
        }
        self.record_term(&map, &v_result);

        Ok(Triple::new(
            p.root_env.clone(),
            env5,
            v_result,
            Some(c_result),
        ))
    }

    fn field_var(
        &mut self,
        field_vars: &[(String, Rc<Var>)],
        atom: bool,
    ) -> Rc<Var> {
        if field_vars.is_empty() {
            let v = self.variable();
            self.primitive_term(&PrimitiveType::Unit, &v).clone()
        } else if field_vars.len() == 1 && atom {
            field_vars[0].1.clone()
        } else {
            let mut map: BTreeMap<Label, Term> = BTreeMap::new();
            field_vars.iter().for_each(|fv| {
                map.insert(
                    Label::String(fv.0.clone()),
                    Term::Variable(fv.1.clone()),
                );
            });
            let v = self.variable();
            self.record_term(&map, &v).clone()
        }
    }

    fn deduce_field_type(
        &mut self,
        env: &dyn TypeEnv,
        labeled_expr: &LabeledExpr,
        label_terms: &mut BTreeMap<Label, Term>,
        labeled_expr_list: &mut Vec<LabeledExpr>,
    ) -> Result<(), Error> {
        let v2 = self.variable();
        let e2 = self.deduce_expr_type(env, &labeled_expr.expr, &v2)?;
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
        Ok(())
    }

    fn deduce_match_list_type(
        &mut self,
        env: &dyn TypeEnv,
        match_list: &[Match],
        label_names: &mut BTreeSet<String>,
        arg_variable: &Rc<Var>,
        result_variable: &Rc<Var>,
    ) -> Result<Vec<Match>, Error> {
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
                )?;

                Ok(Match {
                    pat: pat2,
                    expr: exp2,
                })
            })
            .collect()
    }

    fn deduce_apply_type(
        &mut self,
        env: &dyn TypeEnv,
        fun: &Expr,
        arg: &Expr,
        v_result: &Rc<Var>,
    ) -> Result<(Expr, Expr), Error> {
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
            self.deduce_record_selector_type(
                env, name, &arg.span, &v_rec, &v_field,
            );
            self.fn_term(&v_rec, &v_field, &v_arg);
            self.reg_expr(&arg.kind, &arg.span, arg.id, &v_arg)
        } else {
            self.deduce_expr_type(env, arg, &v_arg)?
        };

        let fun2 = if let ExprKind::RecordSelector(name) = &fun.kind {
            // "apply" is "#field arg" and has type "v";
            // "#field" has type "v_arg -> v";
            // "arg" has type "v_arg".
            // When we resolve "v_arg", we can then deduce "v".
            let span = fun.span.union(&arg.span);
            self.deduce_record_selector_type(env, name, &span, &v_arg, v_result)
        } else {
            self.deduce_apply_fn_type(env, fun, &v_fn, &v_arg, v_result)?
        };

        /*
        if let ExprKind::Identifier(name) = fun2.kind {
            let builtIn = BUILTIN_BY_NAME.get(name);
            if (builtIn.is_some()) {
                builtIn.unwrap().prefer(|t| {preferredTypes.add(v, t)});
            }
        }
         */

        Ok((fun2, arg2))
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
    ) -> Result<Expr, Error> {
        self.deduce_expr_type(env, fun, v_fun)
    }

    fn deduce_record_selector_type(
        &mut self,
        _env: &dyn TypeEnv,
        field_name: &str,
        span: &Span,
        v_rec: &Rc<Var>,
        v_field: &Rc<Var>,
    ) -> Expr {
        // Create a function type: record -> field
        let v_fn = self.variable();
        self.fn_term(v_rec, v_field, &v_fn);

        struct ActionImpl {
            field_name: String,
            v_field: Rc<Var>,
        }
        impl Action for ActionImpl {
            fn accept(
                &self,
                _variable: &Var,
                term: &Term,
                substitution: &Substitution,
                term_pairs: &mut Vec<(Term, Term)>,
            ) {
                // This function is called when we know the record type (v_rec).
                // So now we can deduce the type of the field (v_field).
                // If, say, v_rec is "{a: int, b: real}" and field_name = "b"
                // (selector is "#b") we can deduce that v_field is "real".
                if let Term::Sequence(sequence) = term
                    && let Some(field_list) = TypeResolver::field_list(sequence)
                    && let Some(i) =
                        field_list.iter().position(|f| *f == self.field_name)
                {
                    let result2 = substitution
                        .resolve_term(&Term::Variable(self.v_field.clone()));
                    let term = sequence.terms.get(i).unwrap();
                    let term2 = substitution.resolve_term(term);
                    term_pairs.push((result2, term2));
                }
            }
        }
        self.actions.push((
            v_rec.clone(),
            Rc::new(ActionImpl {
                field_name: field_name.to_string(),
                v_field: v_field.clone(),
            }),
        ));

        // Create a record selector expression
        let selector_kind = ExprKind::RecordSelector(field_name.to_string());
        self.reg_expr(&selector_kind, &span, None, &v_fn)
    }

    fn deduce_record_type(
        &mut self,
        env: &dyn TypeEnv,
        labeled_expr_list: &Vec<LabeledExpr>,
        field_vars: &mut Vec<(String, Rc<Var>)>,
        v: &Rc<Var>,
    ) -> Result<Vec<LabeledExpr>, Error> {
        // First, create a copy of expressions and their labels,
        // sorted into the order that they will appear in the record
        // type.
        let mut label_expr_map: BTreeMap<Label, LabeledExpr> = BTreeMap::new();
        for labeled_expr in labeled_expr_list {
            let label = if let Some(name) = labeled_expr.get_label() {
                Label::from(name)
            } else {
                // Field has no label, so generate a temporary name.
                // FIXME The temporary name might overlap with later
                // explicit labels.
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
            field_vars.push((label.to_string(), v2.clone()));

            let e2 = self.deduce_expr_type(env, &labeled_expr.expr, &v2)?;
            labeled_expr_list2.push(LabeledExpr {
                expr: e2,
                ..labeled_expr.clone()
            });
            label_terms.insert(label.clone(), Term::Variable(v2));
        }
        self.record_term(&label_terms, v);
        Ok(labeled_expr_list2)
    }

    fn deduce_call1_type(
        &mut self,
        env: &dyn TypeEnv,
        op: &str,
        arg: &Expr,
        span: &Span,
        v: &Rc<Var>,
    ) -> Result<Expr, Error> {
        let fun = ExprKind::Identifier(op.to_string()).spanned(&span);
        let (_fun, arg2) = self.deduce_apply_type(env, &fun, &arg, &v)?;
        Ok(arg2)
    }

    fn deduce_call2_type(
        &mut self,
        env: &dyn TypeEnv,
        op: &str,
        left: &Expr,
        right: &Expr,
        v: &Rc<Var>,
    ) -> Result<(Expr, Expr), Error> {
        let fun = ExprKind::Identifier(op.to_string()).spanned(&left.span);
        let arg = ExprKind::Tuple(vec![left.clone(), right.clone()])
            .spanned(&left.span);
        let (_fun, arg) = self.deduce_apply_type(env, &fun, &arg, &v)?;
        if let ExprKind::Tuple(args) = arg.kind
            && args.len() == 2
        {
            Ok((args.first().unwrap().clone(), args.get(1).unwrap().clone()))
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
    ) -> Result<(Expr, Expr, Expr), Error> {
        let fun =
            Box::new(ExprKind::Identifier(op.to_string()).spanned(&a0.span));
        let arg = Box::new(
            ExprKind::Tuple(vec![a0.clone(), a1.clone(), a2.clone()])
                .spanned(&a0.span),
        );
        let (_fun, arg) = self.deduce_apply_type(env, &fun, &arg, &v)?;
        if let ExprKind::Tuple(args) = arg.kind
            && args.len() == 3
        {
            Ok((
                args.first().unwrap().clone(),
                args.get(1).unwrap().clone(),
                args.get(2).unwrap().clone(),
            ))
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
    ) -> (Pat, Pat) {
        let v_arg0 = self.variable();
        let v_arg1 = self.variable();
        let left2 = self.deduce_pat_type(env, &left, term_map, &v_arg0);
        let right2 = self.deduce_pat_type(env, &right, term_map, &v_arg1);

        let v_fn = match env.get(op, self) {
            Some(BindType::Val(term_fn))
            | Some(BindType::Constructor(term_fn)) => {
                self.term_to_variable(&term_fn)
            }
            None => {
                todo!("function '{}' not found", op);
            }
        };
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
    ) -> Result<Match, Error> {
        let mut term_map = Vec::new();
        let pat = match_.pat.clone();
        let pat2 = self.deduce_pat_type(env, &pat, &mut term_map, &v_param);
        let env2 = env.bind_all(&term_map);
        let expr = match_.expr.clone();
        let expr2 = self.deduce_expr_type(&*env2, &expr, &v_result)?;
        Ok(Match {
            pat: pat2,
            expr: expr2,
        })
    }

    /// Converts a type to a unification term.
    //
    // Internally, use [Self::type_term], which allows a [Subst].
    pub fn type_to_term(&mut self, type_: &Type) -> Rc<Var> {
        let v = self.variable();
        self.type_term(type_, &Subst::Empty, &v);
        v.clone()
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

    /// Ensures all terms are lists if they are all lists.
    /// Used for Union/Except/Intersect operations.
    fn is_list_if_all_are_lists(
        &mut self,
        args: &[Term],
        c: &Rc<Var>,
        v: &Rc<Var>,
    ) {
        if args.is_empty() {
            panic!("no args");
        }
        let arg0 = &args[0];
        let v0 = self.term_to_variable(arg0);

        // First argument may be bag or list
        self.may_be_bag_or_list(&v0, v);
        self.may_be_bag_or_list(c, v);

        // Check all other arguments
        for arg in &args[1..] {
            let vi = self.term_to_variable(arg);
            self.may_be_bag_or_list(&vi, v);
            self.is_list_if_both_are_lists(&v0, v, &vi, v, c, v);
        }
    }

    /// Helper for set operations: if both inputs are lists, output is a list.
    fn is_list_if_both_are_lists(
        &mut self,
        v1: &Rc<Var>,
        e1: &Rc<Var>,
        v2: &Rc<Var>,
        e2: &Rc<Var>,
        v3: &Rc<Var>,
        e3: &Rc<Var>,
    ) {
        // If v1 is list<e1> and v2 is list<e2>, then v3 is list<e3>
        let list_e1 = Term::Variable(e1.clone());
        let list_e2 = Term::Variable(e2.clone());
        let list_e3 = Term::Variable(e3.clone());

        let seq1 = self.unifier.apply1(self.list_op.clone(), list_e1);
        let seq2 = self.unifier.apply1(self.list_op.clone(), list_e2);
        let seq3 = self.unifier.apply1(self.list_op.clone(), list_e3);

        // This is a conditional constraint - not fully implemented yet
        // For now, just assume list semantics
        self.equiv(&Term::Sequence(seq1.clone()), v1);
        self.equiv(&Term::Sequence(seq2), v2);
        self.equiv(&Term::Sequence(seq3), v3);
    }

    /// Marks that a variable may be either a bag or list.
    fn may_be_bag_or_list(&mut self, c: &Rc<Var>, v: &Rc<Var>) {
        // For now, assume list semantics
        let list_v = Term::Variable(v.clone());
        let seq = self.unifier.apply1(self.list_op.clone(), list_v);
        self.equiv(&Term::Sequence(seq), c);
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

        if label_types.is_empty() {
            return self.primitive_term(&PrimitiveType::Unit, v);
        }

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

    pub(crate) fn type_term(
        &mut self,
        type_: &Type,
        subst: &Subst,
        v: &Rc<Var>,
    ) {
        match type_ {
            // lint: sort until '#}' where '##Type::'
            Type::Alias(_name, type_, _args) => {
                // During type inference, we pretend that an alias type is its
                // underlying type. For example, if we have 'type t = int', and
                // 'val i = 1: t', we treat 'i' as having type 'int'.
                //
                // After type inference is complete, we can deduce the true type
                // bottom-up. Thus, '[1: t]' has "t list" as its type.
                self.type_term(&type_, subst, v)
            }
            Type::Bag(element_type) => {
                let v2 = self.variable();
                self.type_term(element_type, subst, &v2);
                self.bag_term(Term::Variable(v2), v);
            }
            Type::Data(name, arguments) => {
                if name == "bag" {
                    assert_eq!(arguments.len(), 1);
                    let v2 = self.variable();
                    self.type_term(&arguments[0], subst, &v2);
                    self.bag_term(Term::Variable(v2), v);
                } else if name == "either" {
                    assert_eq!(arguments.len(), 2);
                    // Either requires a tuple of the two type arguments
                    let v1 = self.variable();
                    self.type_term(&arguments[0], subst, &v1);
                    let v2 = self.variable();
                    self.type_term(&arguments[1], subst, &v2);
                    let op = self.unifier.op("either", Some(2));
                    let sequence = self
                        .unifier
                        .apply(op, &[Term::Variable(v1), Term::Variable(v2)]);
                    self.equiv(&Term::Sequence(sequence), v);
                } else {
                    let mut terms = Vec::new();
                    for argument in arguments {
                        let v2 = self.variable();
                        self.type_term(argument, subst, &v2);
                        terms.push(Term::Variable(v2));
                    }
                    let op = self.unifier.op(&name, Some(terms.len()));
                    let sequence = self.unifier.apply(op, &terms);
                    self.equiv(&Term::Sequence(sequence), v);
                }
            }
            Type::Fn(param_type, result_type) => {
                let v2 = self.variable();
                self.type_term(&param_type, subst, &v2);
                let v3 = self.variable();
                self.type_term(&result_type, subst, &v3);
                self.fn_term(&v2, &v3, v);
            }
            Type::Forall(type_, parameter_count) => {
                let mut subst2 = subst.clone();
                for i in 0..*parameter_count {
                    let type_var = TypeVariable::new(i);
                    subst2 =
                        subst2.plus(&type_var, Term::Variable(self.variable()));
                }
                self.type_term(&type_, &subst2, v);
            }
            Type::List(element_type) => {
                let v2 = self.variable();
                self.type_term(element_type, subst, &v2);
                self.list_term(Term::Variable(v2), v);
            }
            Type::Multi(types) => {
                // We cannot convert an overloaded type into a term; it would
                // have to be a term plus constraint(s). Luckily, this method is
                // called only to generate a plausible type for a record such as
                // the Relational structure, so it works if we just return the
                // first type.
                self.type_term(&types[0], subst, v);
            }
            Type::Named(arguments, name) => {
                let mut terms = Vec::new();
                for argument in arguments {
                    let v2 = self.variable();
                    self.type_term(argument, subst, &v2);
                    terms.push(Term::Variable(v2));
                }
                let op = self.unifier.op(&name, Some(terms.len()));
                let sequence = self.unifier.apply(op, &terms);
                self.equiv(&Term::Sequence(sequence), v);
            }
            Type::Primitive(prim_type) => {
                self.primitive_term(prim_type, v);
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
                    self.primitive_term(&PrimitiveType::Unit, v);
                } else if Label::are_contiguous(map.keys().cloned()) {
                    self.tuple_term(
                        &map.values().cloned().collect::<Vec<_>>(),
                        v,
                    );
                } else {
                    let label =
                        Self::record_label_from_set(map.keys().cloned());
                    let op = self.unifier.op(label.as_str(), Some(map.len()));
                    let terms = map.values().cloned().collect::<Vec<_>>();
                    let sequence = self.unifier.apply(op, &terms);
                    self.equiv(&Term::Sequence(sequence), v);
                }
            }
            Type::Tuple(args) => {
                let mut terms: Vec<Term> = Vec::new();
                for arg in args {
                    let v2 = self.variable();
                    self.type_term(arg, subst, &v2);
                    terms.push(Term::Variable(v2))
                }
                self.tuple_term(&terms, v);
            }
            Type::Variable(type_var) => {
                if let Some(term) = subst.get(type_var) {
                    self.equiv(&term, v);
                }
            }
        }
    }

    /// Splits a string into a list of substrings, using a separator
    /// character, taking into account quoted substrings.
    ///
    /// For example, `split_quoted("a,'b,c',d", ',', '\'')` returns the list
    /// `["a", "b,c", "d"]`.
    fn split_quoted(s: &str, sep: char, quote: char) -> Vec<String> {
        if s.is_empty() {
            return Vec::new();
        }

        let mut result = Vec::new();
        let mut current = String::new();
        let mut in_quote = false;

        for c in s.chars() {
            if c == quote {
                in_quote = !in_quote;
            } else if c == sep && !in_quote {
                result.push(current.clone());
                current.clear();
            } else {
                current.push(c);
            }
        }

        // Add the last part
        result.push(current);

        result
    }

    /// Inverse of [TypeResolver::split_quoted].
    ///
    /// For example, `join_quoted(&["a", "b,c", "d"], ',', '\'')` returns
    /// `"a,'b,c',d"`.
    fn join_quoted<I>(strings: I, sep: char, quote: char) -> String
    where
        I: IntoIterator,
        I::Item: AsRef<str>,
    {
        let mut result = String::new();
        let mut first = true;

        for s in strings {
            if !first {
                result.push(sep);
            }
            first = false;

            let s_ref = s.as_ref();
            // Quote the string if it contains the separator
            if s_ref.contains(sep) {
                result.push(quote);
                result.push_str(s_ref);
                result.push(quote);
            } else {
                result.push_str(s_ref);
            }
        }

        result
    }

    /// Inverse of [TypeResolver::record_label_from_set]. Extracts field names
    /// from a sequence.
    fn field_list(sequence: &Sequence) -> Option<Vec<String>> {
        match sequence.op.name.as_str() {
            "record" => Some(Vec::new()),
            "tuple" => {
                let size = sequence.terms.len();
                Some(ordinal_names(size))
            }
            s if s.starts_with("record:") => {
                let fields =
                    Self::split_quoted(&s["record:".len()..], ':', '`');
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
        let label_strs: Vec<String> =
            labels.into_iter().map(|l| l.to_string()).collect();
        format!("record:{}", Self::join_quoted(&label_strs, ':', '`'))
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
    ) -> Expr {
        let id2 = id.unwrap_or_else(|| self.next_id());
        self.node_var_map.insert(id2, v.clone());
        Expr {
            kind: kind.clone(),
            span: span.clone(),
            id: Some(id2),
        }
    }

    /// Registers a term for an AST node for a pattern.
    fn reg_pat(
        &mut self,
        kind: &PatKind,
        span: &Span,
        id: Option<i32>,
        v: &Rc<Var>,
    ) -> Pat {
        let id2 = id.unwrap_or_else(|| self.next_id());
        self.node_var_map.insert(id2, v.clone());
        Pat {
            kind: kind.clone(),
            span: span.clone(),
            id: Some(id2),
        }
    }

    /// Registers a term for an AST node for a declaration.
    fn reg_decl(
        &mut self,
        kind: &DeclKind,
        span: &Span,
        id: Option<i32>,
    ) -> Decl {
        let id2 = id.unwrap_or_else(|| self.next_id());
        Decl {
            kind: kind.clone(),
            span: span.clone(),
            id: Some(id2),
        }
    }

    /// Registers a term for an AST node for a type.
    fn reg_type(
        &mut self,
        kind: &TypeKind,
        span: &Span,
        v: &Rc<Var>,
    ) -> AstType {
        AstType {
            kind: kind.clone(),
            span: span.clone(),
            id: Some(v.id),
        }
    }

    fn deduce_val_bind_type(
        &mut self,
        env: &dyn TypeEnv,
        val_bind: &ValBind,
        term_map: &mut Vec<(String, Term)>,
        v: &Rc<Var>,
    ) -> Result<ValBind, Error> {
        let pat = self.deduce_pat_type(env, &val_bind.pat, term_map, &v);
        let expr = self.deduce_expr_type(env, &val_bind.expr, &v)?;
        Ok(ValBind {
            pat,
            expr,
            ..val_bind.clone()
        })
    }

    fn literal_type(literal_kind: &LiteralKind) -> PrimitiveType {
        match literal_kind {
            // lint: sort until '#}' where '##LiteralKind::'
            LiteralKind::Bool(_) => PrimitiveType::Bool,
            LiteralKind::Char(_) => PrimitiveType::Char,
            LiteralKind::Fn(_) => todo!("Implement Fn literal type"),
            LiteralKind::Int(_) => PrimitiveType::Int,
            LiteralKind::Real(_) => PrimitiveType::Real,
            LiteralKind::String(_) => PrimitiveType::String,
            LiteralKind::Unit => PrimitiveType::Unit,
        }
    }

    fn deduce_pat_type(
        &mut self,
        env: &dyn TypeEnv,
        pat: &Pat,
        term_map: &mut Vec<(String, Term)>,
        v: &Rc<Var>,
    ) -> Pat {
        match &pat.kind {
            // lint: sort until '#}' where '##PatKind::[^ ]* =>'
            PatKind::Annotated(pat, type_) => {
                let pat2 = self.deduce_pat_type(env, pat, term_map, &v);
                let type2 = self.deduce_type_type(env, type_, &v);
                self.reg_pat(
                    &PatKind::Annotated(
                        Box::new(pat2.clone()),
                        Box::new(type2),
                    ),
                    &pat2.span,
                    pat2.id,
                    &v,
                )
            }
            PatKind::Cons(left, right) => {
                let (left2, right2) = self
                    .deduce_pat_call2_type(env, "::", left, right, term_map, v);
                let x = PatKind::Cons(Box::new(left2), Box::new(right2));
                self.reg_pat(&x, &pat.span, pat.id, &v)
            }
            PatKind::Constructor(name, arg) => {
                // Consider the constructor "SOME". For type deduction, we
                // treat "SOME" as a function with a type scheme "forall 'a,
                // 'a -> option 'a". And then "SOME x" has the type "int option"
                // if and only if "x" has type "int".
                let term = match env.get(name, self) {
                    Some(BindType::Constructor(term)) => term,
                    Some(BindType::Val(_)) => {
                        todo!("not a constructor '{}'", name);
                    }
                    None => {
                        todo!("constructor '{}' not found", name);
                    }
                };
                let arg2 = if let Some(a) = arg {
                    let v_arg = self.unifier.variable();
                    let v_fun = self.term_to_variable(&term);
                    self.fn_term(&v_arg, v, &v_fun);
                    Some(self.deduce_pat_type(env, a, term_map, &v_arg))
                } else {
                    self.equiv(&term, v);
                    None
                };
                let x = PatKind::Constructor(name.clone(), arg2.map(Box::new));
                self.reg_pat(&x, &pat.span, pat.id, &v)
            }
            PatKind::Identifier(name) => {
                if let Some(BindType::Constructor(_)) = env.get(name, self) {
                    // The identifier is a constructor, such as `SOME` or `nil`.
                    let kind = PatKind::Constructor(name.clone(), None);
                    let pat2 = Box::new(kind.spanned(&pat.span()));
                    return self.deduce_pat_type(env, &pat2, term_map, v);
                }
                term_map.push((name.clone(), Term::Variable(v.clone())));
                self.reg_pat(&pat.kind, &pat.span, pat.id, &v)
            }
            PatKind::List(pats) => {
                let v2 = self.variable();
                let pats2 = pats
                    .iter()
                    .map(|p| self.deduce_pat_type(env, p, term_map, &v2))
                    .collect();
                self.list_term(Term::Variable(v2), &v);
                self.reg_pat(&PatKind::List(pats2), &pat.span, pat.id, &v)
            }
            PatKind::Literal(literal) => {
                self.primitive_term(&Self::literal_type(&literal.kind), v);
                self.reg_pat(&pat.kind, &pat.span, pat.id, &v)
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
            PatKind::Wildcard => self.reg_pat(&pat.kind, &pat.span, pat.id, &v),
            _ => todo!("{:?}", pat.kind),
        }
    }

    /// Derives an implicit label from a pattern; logs a warning and returns a
    /// fake label if that is not possible.
    fn implicit_pat_label(&mut self, pat: &Pat) -> String {
        if let Some(label) = pat.implicit_label_opt() {
            label
        } else {
            let message = format!("cannot derive label for pattern {}", pat);
            let span = pat.span.clone();
            self.warnings.push(Warning { span, message });
            "implicit".to_string()
        }
    }

    /// Validates an order expression. If it contains a record whose fields are
    /// not in alphabetical order, emits a warning.
    fn validate_order(&mut self, expr: &Expr) -> Expr {
        self.validate_order_rec(expr)
    }

    /// Recursively validates order expressions, checking for records with
    /// non-alphabetically ordered fields.
    fn validate_order_rec(&mut self, expr: &Expr) -> Expr {
        match &expr.kind {
            ExprKind::Record(ty, labeled_exprs) => {
                // Collect labels with their span start positions.
                let labels_with_spans: Vec<(&str, usize)> = labeled_exprs
                    .iter()
                    .filter_map(|le| {
                        le.label
                            .as_ref()
                            .map(|l| (l.name.as_str(), l.span.start_pos()))
                    })
                    .collect();

                // Check if labels are in alphabetical order, but only if
                // the spans are in source order (meaning they haven't
                // been
                // reordered yet).
                if !labels_with_spans.is_empty() {
                    let label_strs: Vec<&str> = labels_with_spans
                        .iter()
                        .map(|(name, _)| *name)
                        .collect();

                    // Check if spans are in increasing order (source order).
                    let spans_in_order =
                        labels_with_spans.windows(2).all(|w| w[0].1 <= w[1].1);

                    if spans_in_order {
                        // Only check alphabetical order if fields are still in
                        // source order.
                        let mut sorted_labels = label_strs.clone();
                        sorted_labels.sort();

                        if label_strs != sorted_labels {
                            let message =
                                "Sorting on a record whose fields are not in \
                                 alphabetical order. Sort order may not be \
                                 what you expect."
                                    .to_string();
                            self.warnings.push(Warning {
                                span: expr.span.clone(),
                                message,
                            });
                        }
                    }
                }

                // Recursively validate the field expressions.
                let new_labeled_exprs: Vec<LabeledExpr> = labeled_exprs
                    .iter()
                    .map(|le| LabeledExpr {
                        label: le.label.clone(),
                        expr: self.validate_order_rec(&le.expr),
                    })
                    .collect();

                Expr {
                    kind: ExprKind::Record(ty.clone(), new_labeled_exprs),
                    span: expr.span.clone(),
                    id: expr.id,
                }
            }
            ExprKind::Tuple(exprs) => {
                let new_exprs: Vec<Expr> =
                    exprs.iter().map(|e| self.validate_order_rec(e)).collect();
                Expr {
                    kind: ExprKind::Tuple(new_exprs),
                    span: expr.span.clone(),
                    id: expr.id,
                }
            }
            _ => expr.clone(),
        }
    }

    /// Converts the terms to a string for debugging, with each term-pair on a
    /// separate line. Variables with ordinals (e.g. T0, T1) are sorted before
    /// variables without ordinals (e.g. X, Y).
    pub fn terms_to_string(&self) -> String {
        let mut pairs: Vec<_> = self.terms.iter().collect();
        pairs.sort_by(|(v0, _), (v1, _)| {
            v1.id.cmp(&v0.id).then(v0.name.cmp(&v1.name))
        });
        pairs
            .into_iter()
            .map(|(var, term)| format!("{} = {}\n", var, term))
            .collect()
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
                    &Pat {
                        kind: PatKind::Identifier("it".to_string()),
                        span: statement.span.clone(),
                        id: statement.id,
                    },
                    None,
                    &Expr {
                        kind: e.clone(),
                        span: statement.span.clone(),
                        id: statement.id,
                    },
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
    ) -> AstType {
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
    ) -> AstType {
        match &type_node.kind {
            // lint: sort until '#}' where '##TypeKind::'
            TypeKind::App(args, t) => {
                if let TypeKind::Id(name) = t.kind.clone() {
                    let mut terms = Vec::new();
                    let mut args2 = Vec::new();
                    let flat_args = AstType::flatten(args);
                    for arg in flat_args {
                        let v2 = self.type_resolver.variable();
                        terms.push(Term::Variable(v2.clone()));
                        let arg2 = self.type_term(&arg, subst, &v2);
                        args2.push(arg2);
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
            TypeKind::Fn(param, result) => {
                let v4 = self.type_resolver.variable();
                let param2 = self.type_term(param, subst, &v4);
                let v5 = self.type_resolver.variable();
                let result2 = self.type_term(result, subst, &v5);
                self.type_resolver.fn_term(&v4, &v5, &v);
                self.type_resolver.reg_type(
                    &TypeKind::Fn(Box::new(param2), Box::new(result2)),
                    &type_node.span,
                    &v,
                )
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
            TypeKind::Record(fields) => {
                let mut fields2 = Vec::new();
                let mut label_types = BTreeMap::<Label, Term>::new();
                for field in fields {
                    let v2 = self.type_resolver.variable();
                    fields2.push(TypeField {
                        label: field.label.clone(),
                        type_: self.type_term(&field.type_, subst, &v2),
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
                    types2.push(self.type_term(&t, subst, &v2));
                }
                self.type_resolver.tuple_term(&terms, &v);
                self.type_resolver.reg_type(
                    &TypeKind::Tuple(types2),
                    &type_node.span,
                    &v,
                )
            }
            TypeKind::Unit => {
                self.type_resolver.primitive_term(&PrimitiveType::Unit, &v);
                self.type_resolver.reg_type(
                    &TypeKind::Unit,
                    &type_node.span,
                    &v,
                )
            }
            TypeKind::Var(name) => {
                let type_variable = self.type_variables.get(name).unwrap();
                let term = subst.get(type_variable).unwrap();
                self.type_resolver.equiv(&term, &v);
                TypeKind::Var(name.clone()).spanned(&type_node.span)
            }
            _ => todo!("{:?}", type_node.kind),
        }
    }
}

impl LabeledExpr {
    /// Returns an explicit or implicit label, or None if no label can
    /// be derived. For example, the fields of the record
    /// ```sml
    /// {a = 1, b, c + 2}
    /// ```
    /// have explicit label `a`, implicit label `b`, and no label.
    pub fn get_label(&self) -> Option<String> {
        self.label
            .as_ref()
            .map(|label| label.name.clone())
            .or_else(|| self.expr.implicit_label_opt())
    }
}

/// Compile-time error or warning.
#[derive(Clone, Debug)]
pub struct Warning {
    pub span: Span,
    pub message: String,
}

const W_INCONSISTENT_PARAMETERS: &str = "parameter or result \
constraints of clauses don't agree [tycon mismatch]";

fn missing_format<T>(query: &Expr, span: &Span) -> Result<T, Error> {
    let require = StepKind::Require(Expr::empty());
    let message = format!(
        "last step of '{}' must be '{}'",
        query.kind.clause(),
        require.clause()
    );
    Err(Error::Compile(message, span.clone()))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::compile::types::{PrimitiveType, Type, TypeVariable};

    /// Tests [TypeResolver::split_quoted] and [TypeResolver::join_quoted].
    #[test]
    fn test_split_join() {
        fn check_split_join(s: &str, expected: &[&str]) {
            let result = TypeResolver::split_quoted(s, ',', '\'');
            assert_eq!(result, expected);
            assert_eq!(TypeResolver::join_quoted(expected, ',', '\''), s);
        }

        check_split_join("", &[]);
        check_split_join("a,'b,c',d", &["a", "b,c", "d"]);
        check_split_join(",a,,bc,", &["", "a", "", "bc", ""]);
        // Test with colon separator and backtick quote (what we use for
        // record fields)
        let result = TypeResolver::split_quoted("a:`b:c`:d", ':', '`');
        assert_eq!(result, vec!["a", "b:c", "d"]);
        assert_eq!(
            TypeResolver::join_quoted(&["a", "b:c", "d"], ':', '`'),
            "a:`b:c`:d"
        );
    }

    /// Tests conversion of the following type scheme to unifier terms:
    /// ```sml
    /// forall 'a: int * ('a * 'a -> bool)
    /// ```
    #[test]
    fn test_type_to_term() {
        let mut resolver = TypeResolver::new();

        // Create a tuple with primitive types:
        //
        let tv = TypeVariable::new(0);
        let tuple_type = Type::Forall(
            Box::new(Type::Tuple(vec![
                Type::Primitive(PrimitiveType::Int),
                Type::Fn(
                    Box::new(Type::Tuple(vec![
                        Type::Variable(tv.clone()),
                        Type::Variable(tv.clone()),
                    ])),
                    Box::new(Type::Primitive(PrimitiveType::Bool)),
                ),
            ])),
            1,
        );

        // Convert to term
        let result_var = resolver.type_to_term(&tuple_type);
        let s = resolver.terms_to_string();
        let x = r#"T0 = tuple(T2, T3)
T2 = int
T3 = fn(T4, T7)
T4 = tuple(T5, T6)
T5 = T1
T6 = T1
T7 = bool
"#;
        assert_eq!(s, x);
        assert!(result_var.id < 0);
    }
}
