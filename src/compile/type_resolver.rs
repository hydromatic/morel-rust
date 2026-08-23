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
// Several helper methods (deduce_field_type, is_list_if_all_are_lists,
// etc.) and a Type variant remain after porting from morel-java; keep
// as future-use surface.
#![allow(dead_code)]

use crate::compile::library;
use crate::compile::pat_coverage::check_coverage;
use crate::compile::postfix::{PostfixKind, peel_type, postfix_dispatch};
use crate::compile::type_env::{BindType, SchemeTypeEnv, TypeEnv};
use crate::compile::types;
use crate::compile::types::Label;
use crate::compile::types::{
    Predicate, PrimitiveType, Subst, Type, TypeVariable,
};
use crate::eval::code::{LIBRARY, Lib};
use crate::eval::file::TypedValue;
use crate::shell::error::Error;
use crate::syntax::ast::Label as AstLabel;

/// Field names of the expressions record modifiers are applied to,
/// keyed by the extent of each expression's span.
type ModifierFields = Rc<RefCell<HashMap<(usize, usize), Vec<String>>>>;
use crate::syntax::ast::{
    Absent, DatatypeBind, Decl, DeclKind, Exists, Expr, ExprKind, FunBind,
    JoinType, LabeledExpr, Literal, LiteralKind, Match, Modifier, ModifierVerb,
    MorelNode, Pat, PatField, PatKind, RangeItem, Span, Statement,
    StatementKind, Step, StepKind, Type as AstType, TypeField, TypeKind,
    TypeScheme, ValBind,
};
use crate::syntax::parser;
use crate::unify::unifier::{
    Action, COLLECTION_OP_NAME, Constraint, ConstraintAction, NullTracer,
    ORDERED_OP_NAME, Op, OpDef, Sequence, Substitution, Term,
    UNORDERED_OP_NAME, Unifier, Var,
};
use std::cell::{OnceCell, RefCell};
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::fmt::{self, Debug, Display, Formatter};
use std::iter::{once, zip};
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
    /// Compile-time errors detected during resolution (e.g. "match
    /// redundant"). The caller should report these as errors, but may
    /// still use the resolved declaration for `Sys.planEx`.
    pub errors: Vec<(String, Span)>,
}

/// Maps AST nodes to their resolved types.
#[derive(Clone, Debug)]
pub struct TypeMap {
    // Maps from AST node ID to unifier variable.
    pub node_var_map: HashMap<i32, Var>,
    // Maps from unifier variables to terms.
    pub var_term_map: HashMap<Var, Term>,
    // Reference to operator definitions for looking up operator names.
    pub op_defs: Rc<Vec<OpDef>>,
    /// Maps unifier variables to type alias names. Used during
    /// type reconstruction to wrap resolved types in `Type::Alias`.
    pub var_alias_map: HashMap<Var, String>,
    /// Constructor sets for user-defined datatypes. Maps datatype
    /// name → list of constructor names. Used by the coverage
    /// checker to determine whether a set of constructor patterns
    /// is exhaustive.
    pub datatype_constructors: HashMap<String, Vec<String>>,
    /// Constructor argument types. Maps constructor name → argument
    /// type. Used by the pretty printer to format record arguments
    /// with field names.
    pub constructor_arg_types: HashMap<String, Type>,
    /// The expanded core type of each `type` binding declared by this
    /// statement; see
    /// [`TypeResolver::expanded_type_binds`](TypeResolver::expanded_type_binds).
    pub expanded_type_binds: HashMap<String, Type>,
    /// Overload constraints that were still unresolved when unification
    /// finished: `(name, type term, candidate instance terms)`. They become
    /// the predicates of a qualified type; see
    /// [`get_qualified_type`](TypeMap::get_qualified_type).
    pub predicate_terms: Vec<(String, Term, Vec<Term>)>,
}

impl TypeMap {
    pub fn new(
        node_var_map: &HashMap<i32, Var>,
        op_defs: Rc<Vec<OpDef>>,
    ) -> Self {
        Self {
            node_var_map: node_var_map.clone(),
            var_term_map: HashMap::new(),
            op_defs,
            expanded_type_binds: HashMap::new(),
            predicate_terms: Vec::new(),
            var_alias_map: HashMap::new(),
            datatype_constructors: HashMap::new(),
            constructor_arg_types: HashMap::new(),
        }
    }

    /// Gets the type for an AST node.
    pub fn get_type(&self, id: i32) -> Option<Rc<Type>> {
        self.get_type_inner(id, false)
    }

    /// Gets the type for an AST node, optionally wrapping in
    /// `Type::Alias` if the node's variable carries a type alias.
    pub fn get_type_with_alias(&self, id: i32) -> Option<Rc<Type>> {
        self.get_type_inner(id, true)
    }

    /// Fully resolves a term, following variables through
    /// [`var_term_map`](TypeMap::var_term_map), and collects the variables
    /// that remain free.
    fn collect_free_vars(&self, term: &Term, vars: &mut Vec<Var>) {
        match term {
            Term::Variable(v) => match self.var_term_map.get(v) {
                Some(t) => self.collect_free_vars(&t.clone(), vars),
                None => {
                    if !vars.contains(v) {
                        vars.push(*v);
                    }
                }
            },
            Term::Sequence(seq) => {
                seq.terms
                    .iter()
                    .for_each(|t| self.collect_free_vars(t, vars));
            }
        }
    }

    /// If any deduced overload predicate constrains the type variables of the
    /// AST node `id`, returns the node's type qualified by those predicates;
    /// otherwise `None`.
    ///
    /// The predicates and the body are converted together, so that they share
    /// one type-variable numbering: `{foo : 'a -> 'b} => 'a -> 'b`.
    pub fn get_qualified_type(&self, id: i32) -> Option<Rc<Type>> {
        if self.predicate_terms.is_empty() {
            return None;
        }
        let var = self.node_var_map.get(&id)?;
        let body_term = self
            .var_term_map
            .get(var)
            .cloned()
            .unwrap_or(Term::Variable(*var));
        let mut body_vars = Vec::new();
        self.collect_free_vars(&body_term, &mut body_vars);
        if body_vars.is_empty() {
            return None;
        }
        let matching: Vec<&(String, Term, Vec<Term>)> = self
            .predicate_terms
            .iter()
            .filter(|(_, t, _)| {
                let mut vars = Vec::new();
                self.collect_free_vars(t, &mut vars);
                vars.iter().any(|v| body_vars.contains(v))
            })
            .collect();
        if matching.is_empty() {
            return None;
        }
        LIBRARY.with(|lib| {
            let mut c = TermToTypeConverter {
                type_map: self,
                lib,
                var_map: BTreeMap::new(),
                with_alias: false,
            };
            let body = c.term_type(&body_term);
            let predicates = matching
                .iter()
                .map(|(name, t, candidates)| Predicate {
                    name: name.clone(),
                    type_: c.term_type(t),
                    candidates: candidates
                        .iter()
                        .map(|ct| c.term_type(ct))
                        .collect(),
                })
                .collect();
            Some(Rc::new(Type::Qualified(predicates, body)))
        })
    }

    /// Resolves a unification variable directly to a Type. Used
    /// to capture overload instance types after deduction.
    pub fn var_to_type(&self, var: &Var) -> Option<Type> {
        let term = self
            .var_term_map
            .get(var)
            .cloned()
            .unwrap_or(Term::Variable(*var));
        LIBRARY.with(|lib| {
            let mut c = TermToTypeConverter {
                type_map: self,
                lib,
                var_map: BTreeMap::new(),
                with_alias: false,
            };
            Some((*c.term_type(&term)).clone())
        })
    }

    fn get_type_inner(&self, id: i32, with_alias: bool) -> Option<Rc<Type>> {
        if let Some(var) = self.node_var_map.get(&id) {
            let term = self
                .var_term_map
                .get(var)
                .cloned()
                .unwrap_or(Term::Variable(*var));
            // When with_alias, replace inlined sub-Sequences
            // that match an alias var's concrete term with
            // Variable(alias_var), so term_type can detect them.
            let term = if with_alias {
                self.reinstate_alias_refs(&term)
            } else {
                term
            };
            let type_ = LIBRARY.with(|lib| {
                let mut c = TermToTypeConverter {
                    type_map: self,
                    lib,
                    var_map: BTreeMap::new(),
                    with_alias,
                };
                c.term_type(&term)
            });
            // Check if this node's var has a top-level alias.
            if with_alias {
                if let Some(alias_name) = self.var_alias_map.get(var) {
                    return Some(Rc::new(Type::Alias(
                        alias_name.clone(),
                        type_,
                        vec![],
                    )));
                }
            }
            return Some(type_);
        }
        None
    }

    /// For a composite term, replaces sub-terms that resolve to the
    /// same concrete value as an alias var with `Variable(alias_var)`.
    /// This reverses the unifier's inlining so that `term_type` can
    /// detect aliases in sub-types (e.g. `list(int)` → `list(myInt)`).
    fn reinstate_alias_refs(&self, term: &Term) -> Term {
        if self.var_alias_map.is_empty() {
            return term.clone();
        }
        // Collect alias var → concrete term pairs.
        let alias_concrete: Vec<(Var, Term)> = self
            .var_alias_map
            .keys()
            .filter_map(|v| {
                let mut current = *v;
                loop {
                    match self.var_term_map.get(&current) {
                        Some(Term::Variable(next)) => current = *next,
                        Some(term) => return Some((*v, term.clone())),
                        None => return None,
                    }
                }
            })
            .collect();
        if alias_concrete.is_empty() {
            return term.clone();
        }
        self.reinstate_in_term(term, &alias_concrete)
    }

    fn reinstate_in_term(
        &self,
        term: &Term,
        alias_concrete: &[(Var, Term)],
    ) -> Term {
        match term {
            Term::Sequence(seq) if !seq.terms.is_empty() => {
                let new_terms: Vec<Term> = seq
                    .terms
                    .iter()
                    .map(|t| {
                        match t {
                            // If the sub-term is already an inlined
                            // Sequence, leave it — the unifier inlined
                            // it because there was no alias var in the
                            // chain.
                            Term::Sequence(_) => t.clone(),
                            // If the sub-term is a Variable, resolve
                            // it and check if it matches an alias.
                            Term::Variable(v) => {
                                let concrete = {
                                    let mut current = *v;
                                    loop {
                                        match self.var_term_map.get(&current) {
                                            Some(Term::Variable(next)) => {
                                                current = *next
                                            }
                                            Some(term) => {
                                                break Some(term.clone());
                                            }
                                            None => break None,
                                        }
                                    }
                                };
                                if let Some(concrete) = &concrete {
                                    for (alias_var, alias_term) in
                                        alias_concrete
                                    {
                                        if concrete == alias_term {
                                            return Term::Variable(*alias_var);
                                        }
                                    }
                                }
                                t.clone()
                            }
                        }
                    })
                    .collect();
                Term::Sequence(Sequence {
                    op: seq.op,
                    terms: new_terms.into(),
                })
            }
            _ => term.clone(),
        }
    }

    /// Ensures that a type is closed.
    pub fn ensure_closed(&self, _type_: Type) -> Type {
        todo!()
    }
}

pub trait Typed {
    fn get_type(&self, type_map: &TypeMap) -> Option<Rc<Type>>;
}

impl Typed for Expr {
    fn get_type(&self, type_map: &TypeMap) -> Option<Rc<Type>> {
        type_map.get_type(self.id?)
    }
}

impl Typed for ValBind {
    fn get_type(&self, type_map: &TypeMap) -> Option<Rc<Type>> {
        self.expr.get_type(type_map)
    }
}

impl Typed for Pat {
    fn get_type(&self, type_map: &TypeMap) -> Option<Rc<Type>> {
        type_map.get_type(self.id?)
    }
}

/// The collection kind of an aggregate function's input parameter.
/// Determines how the TypeResolver constrains the aggregate input.
/// Outcome of eagerly tunnelling a safe-navigation receiver type (see
/// `tunnel_safe_eager`).
enum SafeTunnel {
    /// The result type term (the field's type re-wrapped in the receiver's
    /// functor layers).
    Resolved(Term),
    /// The receiver type is not yet determinable; the caller should register
    /// a deferred action instead.
    Defer,
    /// A type error was found and reported.
    Errored,
}

enum CollectionKind {
    /// Function expects list input (e.g. `count: 'a list -> int`).
    List,
    /// Function expects bag input.
    Bag,
    /// Function is overloaded with both list and bag variants.
    /// Link to input ordering.
    MatchInput,
    /// Function type is unknown (anonymous lambda). Allow either,
    /// default based on query ordering.
    Unknown,
}

/// Name under which a step binds `ordinal` in the type environment.
///
/// `ordinal` counts the rows arriving at a step, so it is bound by the
/// step that produces them -- exactly as `current` is. Resolving it
/// through the environment, rather than by tracking query depth on the
/// side, is what makes it agree with `current` about which rows an
/// occurrence counts: an expression evaluated once per execution of a
/// query (the collection its first step scans, a `take` or `skip` count,
/// an operand of `union`, `except` or `intersect`, or the function of a
/// `through` or an `into`) is deduced in the enclosing environment, and
/// so reads the enclosing row.
///
/// The name holds a `$`, so that it is not one a user can write: a query
/// may bind a field of its own called `ordinal`, and `` `ordinal` ``
/// must still reach that field. Mirrors morel-java's `Z_ORDINAL`.
const ORDINAL: &str = "$ordinal";

// What [`ORDINAL`] binds is not the occurrence's own type -- that is
// always `int` -- but the *collection* whose rows it counts, put there by
// the step that produced them. Reading it is what decides which step an
// `ordinal` belongs to. A sentinel type for the invalid cases is not
// available: "not in a query" is absence from the environment, but
// "unordered" cannot be decided when the binding is made, because the
// collection may still be a type variable -- `[0..4]` is one. So that
// check is deferred to `ordinal_validations`, and runs once the types
// are resolved.

#[derive(Clone)]
struct Triple {
    root_env: Rc<dyn TypeEnv>,
    env: Rc<dyn TypeEnv>,
    v: Var,
    c: Option<Var>,
    /// Whether the collection is ordered (list) or unordered (bag).
    /// Used to validate that `ordinal` is only used in ordered queries.
    ordered: bool,
}

impl Triple {
    fn new(
        root_env: Rc<dyn TypeEnv>,
        env: Rc<dyn TypeEnv>,
        v: Var,
        c: Option<Var>,
    ) -> Self {
        Triple {
            root_env,
            env,
            v,
            c,
            ordered: true,
        }
    }

    fn with_env(&self, env: &Rc<dyn TypeEnv>) -> Self {
        Self {
            root_env: self.root_env.clone(),
            env: env.clone(),
            v: self.v,
            c: self.c,
            ordered: self.ordered,
        }
    }

    fn with_c(&self, c: Var) -> Self {
        Self {
            root_env: self.root_env.clone(),
            env: self.env.clone(),
            v: self.v,
            c: Some(c),
            ordered: self.ordered,
        }
    }

    fn with_ordered(&self, ordered: bool) -> Self {
        Self {
            root_env: self.root_env.clone(),
            env: self.env.clone(),
            v: self.v,
            c: self.c,
            ordered,
        }
    }
}

struct TermToTypeConverter<'a> {
    type_map: &'a TypeMap,
    lib: &'a Lib,
    var_map: BTreeMap<i32, Rc<Type>>,
    /// When true, check each variable for a type alias annotation
    /// and wrap the result in `Type::Alias`.
    with_alias: bool,
}

impl<'a> TermToTypeConverter<'a> {
    /// Returns whether `term` is the orderedness atom of a list, following
    /// variable links to a concrete atom. An orderedness that nothing
    /// constrained reads back as a bag, so it yields `false`.
    fn is_ordered(&self, term: &Term) -> bool {
        match term {
            Term::Sequence(seq) => {
                self.type_map.op_defs[seq.op.0 as usize].name == ORDERED_OP_NAME
            }
            Term::Variable(v) => match self.type_map.var_term_map.get(v) {
                Some(t) => self.is_ordered(t),
                None => false,
            },
        }
    }

    /// Converts a term to a type.
    fn term_type(&mut self, term: &Term) -> Rc<Type> {
        match term {
            Term::Sequence(sequence) => {
                let op_name =
                    &self.type_map.op_defs[sequence.op.0 as usize].name;
                match op_name.as_str() {
                    // lint: sort until '#}' where '##["]'
                    "$collection" => {
                        // A collection term is a list or a bag, according to
                        // its orderedness; an orderedness that nothing
                        // constrained reads back as a bag.
                        assert_eq!(sequence.terms.len(), 2);
                        let type_ = self.term_type(&sequence.terms[0]);
                        let ordered = self.is_ordered(&sequence.terms[1]);
                        self.lib.intern(if ordered {
                            Type::List(type_)
                        } else {
                            Type::Bag(type_)
                        })
                    }
                    "bag" => {
                        assert_eq!(sequence.terms.len(), 1);
                        let type_ = self.term_type(&sequence.terms[0]);
                        self.lib.intern(Type::Bag(type_))
                    }
                    "bool" | "char" | "int" | "real" | "string" | "unit"
                    | "word" => {
                        let primitive_type =
                            PrimitiveType::parse_name(op_name).unwrap();
                        self.lib.intern(Type::Primitive(primitive_type))
                    }
                    "fn" => {
                        assert_eq!(sequence.terms.len(), 2);
                        let param_type = self.term_type(&sequence.terms[0]);
                        let result_type = self.term_type(&sequence.terms[1]);
                        self.lib.intern(Type::Fn(param_type, result_type))
                    }
                    "list" => {
                        assert_eq!(sequence.terms.len(), 1);
                        let type_ = self.term_type(&sequence.terms[0]);
                        self.lib.intern(Type::List(type_))
                    }
                    "tuple" => {
                        let types: Vec<Rc<Type>> = sequence
                            .terms
                            .iter()
                            .map(|t| self.term_type(t))
                            .collect();
                        self.lib.intern(Type::Tuple(types))
                    }
                    s if s.starts_with("record") => {
                        let labels = TypeResolver::field_list(
                            &self.type_map.op_defs,
                            sequence,
                        )
                        .unwrap();
                        let mut fields = BTreeMap::<Label, Rc<Type>>::new();
                        let mut progressive = false;
                        for (label, term) in zip(labels, sequence.terms.iter())
                        {
                            // The synthetic `z$dummy` label flags a
                            // progressive record; strip it here so the
                            // returned `Type::Record` carries the flag
                            // instead of leaking the dummy field.
                            if label == PROGRESSIVE_LABEL {
                                progressive = true;
                                continue;
                            }
                            fields.insert(
                                Label::from(label),
                                self.term_type(term),
                            );
                        }
                        self.lib.intern(Type::Record(progressive, fields))
                    }
                    _ => {
                        // Every other named type — built-in
                        // (`option`, `either`, `range`, `variant`, …)
                        // or user-declared — lowers uniformly to
                        // `Type::Data`. Arity is enforced by the
                        // unifier; assertions here would be
                        // redundant.
                        let args: Vec<Rc<Type>> = sequence
                            .terms
                            .iter()
                            .map(|t| self.term_type(t))
                            .collect();
                        self.lib.intern(Type::Data(op_name.to_string(), args))
                    }
                }
            }
            Term::Variable(v) => {
                // Check if this variable carries a type alias,
                // either directly or by resolving to the same
                // concrete term as an alias var.
                let alias_name = if self.with_alias {
                    self.find_alias_for_var(v)
                } else {
                    None
                };
                let inner = if let Some(term) =
                    self.type_map.var_term_map.get(v)
                {
                    self.term_type(term)
                } else {
                    let id = self.var_map.len();
                    self.var_map
                        .entry(v.id)
                        .or_insert_with(|| {
                            self.lib.intern(Type::Variable(TypeVariable { id }))
                        })
                        .clone()
                };
                if let Some(name) = alias_name {
                    self.lib.intern(Type::Alias(name, inner, vec![]))
                } else {
                    inner
                }
            }
        }
    }

    /// Finds an alias for variable `v`. First checks if `v` itself
    /// has an alias (direct hit). If not, resolves `v` to its
    /// concrete term and checks if any alias var resolves to the
    /// same concrete term (equivalence class match).
    fn find_alias_for_var(&self, v: &Var) -> Option<String> {
        // Direct hit: v itself has an alias.
        if let Some(name) = self.type_map.var_alias_map.get(v) {
            return Some(name.clone());
        }
        // Follow the chain from v; if any intermediate var has alias,
        // use it.
        let mut current = *v;
        while let Some(Term::Variable(next)) =
            self.type_map.var_term_map.get(&current)
        {
            if let Some(name) = self.type_map.var_alias_map.get(next) {
                return Some(name.clone());
            }
            current = *next;
        }
        // Resolve v to its concrete term and check if any alias var
        // resolves to the same term. This handles cases where the
        // unifier resolved both v and the alias var to the same
        // concrete term without linking them.
        let v_term = self.resolve_to_concrete(v);
        for (alias_var, name) in &self.type_map.var_alias_map {
            if alias_var == v {
                continue;
            }
            let alias_term = self.resolve_to_concrete(alias_var);
            if v_term == alias_term {
                return Some(name.clone());
            }
        }
        None
    }

    /// Resolves a var to its concrete (non-Variable) term.
    fn resolve_to_concrete(&self, v: &Var) -> Option<Term> {
        let mut current = *v;
        loop {
            match self.type_map.var_term_map.get(&current) {
                Some(Term::Variable(next)) => current = *next,
                Some(term) => return Some(term.clone()),
                None => return None,
            }
        }
    }
}

impl Display for TypeMap {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
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
    node_var_map: HashMap<i32, Var>,

    /// List of (variable, term) pairs where the term is equivalent to the
    /// variable. Will be the input to the unifier.
    terms: Vec<(Var, Term)>,
    unifier: Unifier,
    next_id: i32,

    /// Stack of `compute` clauses.
    compute_stack: Vec<Triple>,

    /// Nesting depth of `over` (aggregate) expressions. Greater than zero while
    /// deducing an aggregate's sub-expressions, so a nested `over` (e.g.
    /// `min over (max over j)`) can be rejected.
    aggregate_depth: usize,

    /// How many queries (`from`, `exists`, `forall`) have been deduced so
    /// far. A `let` declaration whose count grows while it is deduced
    /// contains a query, and is not generalized; see
    /// [`bind_decl_generalized`](Self::bind_decl_generalized).
    query_count: usize,

    /// Cached operators for common type-constructors.
    ///
    /// A collection is a single term, `$collection(element, orderedness)`,
    /// where orderedness is the atom `ordered` (a list) or `unordered` (a
    /// bag), or a variable. Orderedness therefore flows through inference
    /// like any other attribute.
    collection_op: Op,
    ordered_op: Op,
    unordered_op: Op,
    tuple_op: Op,
    arg_op: Op,
    overload_op: Op,
    record_op: Op,
    fn_op: Op,
    int_op: Op,
    actions: Vec<(Var, Rc<dyn Action>)>,

    /// Shared scope for explicit type variables within a declaration.
    ///
    /// In SML, all occurrences of `'a` in `fun f (x: 'a) (y: 'a) = ...` refer
    /// to the same type. This map is cleared at the start of each val-bind and
    /// accumulates the fresh unifier variables allocated for each `'a`-style
    /// annotation so that repeated occurrences resolve to the same variable.
    decl_type_vars: BTreeMap<String, Var>,

    /// User-defined type aliases, populated from `type` declarations
    /// and `datatype` declarations.
    pub type_aliases: HashMap<String, Type>,

    /// The expanded core type of each `type` binding declared by this
    /// statement, so that `type t = t list` displays its expansion.
    pub expanded_type_binds: HashMap<String, Type>,

    /// Parameter count (arity) of every user-declared datatype seen
    /// so far (added by `deduce_datatype_decl_type` or seeded by
    /// the session from prior statements). Built-in datatype
    /// arities are *not* stored here — they're read on demand from
    /// `library::BuiltInDatatype` / `library::BuiltInEqtype` via
    /// `library::builtin_type_arity`. A redeclaration overwrites the
    /// previous entry.
    pub user_datatype_arities: HashMap<String, usize>,

    /// Constructor bindings from `datatype` declarations, stored
    /// here during `deduce_datatype_decl_type` and merged into
    /// `Resolved::bindings` at the end of `deduce_type`.
    datatype_bindings: Vec<TypeBinding>,

    /// Constructor sets from datatype declarations in previous
    /// statements. Seeded by `Session::deduce_type_inner` so that
    /// the coverage checker can see them.
    pub prior_datatype_constructors: HashMap<String, Vec<String>>,
    /// Constructor arg types from previous statements.
    pub prior_constructor_arg_types: HashMap<String, Type>,

    /// Whether to check pattern coverage (exhaustiveness and redundancy).
    /// Controlled by the `matchCoverageEnabled` property; default is true.
    pub match_coverage_enabled: bool,

    /// Variables that should default to `int` if still free after
    /// unification. Populated when `op +`, `op -`, `op *`, or `op ~` are
    /// used without enough context to determine whether they operate on `int`
    /// or `real`. Matches Standard ML semantics: numeric operators prefer
    /// `int`.
    preferred_vars: Vec<Var>,
    /// Collection variables in aggregate inputs that should default to
    /// list (if ordered=true) or bag (if ordered=false) when
    /// unconstrained after unification. Each entry is
    /// (collection_var, element_var, ordered).
    preferred_collection_vars: Vec<(Var, Var, bool)>,

    /// Maps unifier variables to type alias names. When a type annotation
    /// references an alias (e.g. `val x: myInt = 5`), we record the
    /// variable → alias name so that the reconstructed type preserves
    /// the alias (e.g. `myInt` instead of `int`).
    var_alias_map: HashMap<Var, String>,

    /// Errors from record selector actions, populated during unification.
    field_errors: Rc<RefCell<Vec<(String, Span)>>>,

    /// Type variables whose value is a [`TypedValue`] (currently the
    /// `Sys.file` global). The field-selector action consults this
    /// map when a field is missing from a progressive record: it
    /// calls `discover_field` on the underlying value to widen the
    /// type, and rebinds the field's type variable from the value's
    /// fresh type. Populated by the session's env wrapper at lookup
    /// time.
    pub typed_values: Rc<RefCell<HashMap<Var, Rc<dyn TypedValue>>>>,

    /// Set by the field-selector action when it widens a
    /// progressive record by calling [`TypedValue::discover_field`].
    /// [`Self::deduce_type`] checks this after each unification
    /// round; if true, it resets the per-round state and re-runs
    /// against the now-wider record type. Cleared at the start of
    /// each round.
    pub retry_requested: Rc<RefCell<bool>>,

    /// Record selectors to validate after unification.
    /// Each entry is (record_var, field_name, span).
    field_selectors: Vec<(Var, String, Span)>,

    /// Collections that an `ordinal` counts the rows of, with the span of
    /// the occurrence. Checked for orderedness once the types are
    /// resolved; see [`ORDINAL`].
    ordinal_validations: Vec<(Term, Span)>,

    /// Field names of an expression a record modifier is applied to,
    /// keyed by the extent of its span, learned when unification
    /// settled its type. Survives a retry -- the next attempt reads it
    /// before deducing, and can then desugar. morel-java's `fieldNames`.
    modifier_fields: ModifierFields,

    /// Records whose modifiers could not be desugared, to report after
    /// unification if a later attempt does not desugar them.
    /// (labels the modifiers mention, span)
    modifier_validations: Vec<(Vec<String>, Span)>,

    /// Overloaded operator instances. Maps name to list of
    /// candidate terms (the types of each `val inst` binding).
    overloads: HashMap<String, Vec<Term>>,

    /// New overload instances added by THIS statement (not seeded
    /// from previous). Used by Session to persist them.
    pub new_overloads: HashMap<String, Vec<Var>>,

    /// Seeded overload instance types from previous statements.
    /// At the start of each statement, these are converted to
    /// fresh Terms in the current unifier.
    pub seed_overloads: HashMap<String, Vec<Type>>,

    /// Constraints to pass to the unifier for overload resolution.
    overload_constraints: Vec<Constraint>,
}

impl Default for TypeResolver {
    fn default() -> Self {
        Self::new()
    }
}

/// Checks that a `right join`/`full join` source expression does not reference
/// the query's input. Such a source may have rows that match no input row, so
/// it must not depend on earlier-step variables, nor on `current`/`ordinal`.
///
/// Best-effort: it catches the common direct references with a precise span
/// (the offending reference). References it misses — inside a nested query or
/// a shadowing scope — are tolerated, matching morel-java's
/// `TypeResolver.checkJoinSourceIndependent`.
fn check_join_source_independent(
    expr: &Expr,
    input_names: &HashSet<String>,
) -> Result<(), Error> {
    let mut shadowed: HashSet<String> = HashSet::new();
    join_source_walk(expr, input_names, &mut shadowed)
}

fn join_source_ref_error(name: &str, span: &Span) -> Error {
    Error::Compile(
        format!(
            "join source must not reference '{}' (right and full joins must \
             be independent)",
            name
        ),
        span.clone(),
    )
}

/// Returns an error message if a numeric literal is outside its type's
/// representable range: `int` is signed 32-bit, `word` is unsigned 64-bit.
/// Returns `None` for in-range or non-numeric literals.
fn literal_range_error(kind: &LiteralKind) -> Option<String> {
    match kind {
        LiteralKind::Int(s) => {
            let parsed = s.replace('~', "-").parse::<i128>().ok();
            let in_range = parsed.is_some_and(|n| i32::try_from(n).is_ok());
            (!in_range)
                .then(|| format!("literal '{}' is too large for type int", s))
        }
        LiteralKind::Word(s) => parser::parse_word_literal(s)
            .is_none()
            .then(|| format!("literal '{}' is too large for type word", s)),
        _ => None,
    }
}

/// Returns an error message if a character constant does not contain exactly
/// one character (e.g. `#""` or `#"ab"`), using Standard ML's wording. The
/// parser accepts any content between the quotes; this check, run at type
/// resolution, rejects a constant that is not length one, whether it is used
/// as an expression or a pattern. Returns `None` for a valid character
/// constant or a non-character literal.
fn char_literal_error(kind: &LiteralKind) -> Option<String> {
    match kind {
        LiteralKind::Char(s) => parser::unquote_char_literal(s)
            .is_err()
            .then(|| "character constant not length one".to_string()),
        _ => None,
    }
}

fn join_source_walk(
    e: &Expr,
    input: &HashSet<String>,
    shadowed: &mut HashSet<String>,
) -> Result<(), Error> {
    use ExprKind as E;
    match &e.kind {
        E::Identifier(name)
            if input.contains(name) && !shadowed.contains(name) =>
        {
            return Err(join_source_ref_error(name, &e.span));
        }
        E::Current => {
            return Err(join_source_ref_error("current", &e.span));
        }
        E::Ordinal => {
            return Err(join_source_ref_error("ordinal", &e.span));
        }
        E::Plus(a, b)
        | E::Minus(a, b)
        | E::Times(a, b)
        | E::Divide(a, b)
        | E::Div(a, b)
        | E::Mod(a, b)
        | E::Caret(a, b)
        | E::Compose(a, b)
        | E::Equal(a, b)
        | E::NotEqual(a, b)
        | E::LessThan(a, b)
        | E::LessThanOrEqual(a, b)
        | E::GreaterThan(a, b)
        | E::GreaterThanOrEqual(a, b)
        | E::Elem(a, b)
        | E::NotElem(a, b)
        | E::AndAlso(a, b)
        | E::OrElse(a, b)
        | E::Implies(a, b)
        | E::Aggregate(a, b)
        | E::Cons(a, b)
        | E::Append(a, b)
        | E::Apply(a, b) => {
            join_source_walk(a, input, shadowed)?;
            join_source_walk(b, input, shadowed)?;
        }
        E::Negate(a) | E::Raise(a) | E::Annotated(a, _) => {
            join_source_walk(a, input, shadowed)?;
        }
        E::If(a, b, c) => {
            join_source_walk(a, input, shadowed)?;
            join_source_walk(b, input, shadowed)?;
            join_source_walk(c, input, shadowed)?;
        }
        E::Tuple(xs) | E::List(xs) => {
            for x in xs {
                join_source_walk(x, input, shadowed)?;
            }
        }
        E::Record(base, fields, _) => {
            if let Some(b) = base {
                join_source_walk(b, input, shadowed)?;
            }
            for le in fields {
                join_source_walk(&le.expr, input, shadowed)?;
            }
        }
        E::Case(exp, matches) => {
            join_source_walk(exp, input, shadowed)?;
            for m in matches {
                join_source_walk_match(&m.pat, &m.expr, input, shadowed)?;
            }
        }
        E::Fn(matches) => {
            for m in matches {
                join_source_walk_match(&m.pat, &m.expr, input, shadowed)?;
            }
        }
        E::Let(decls, body) => {
            let added = join_source_shadow_decls(decls, shadowed);
            let result = join_source_walk(body, input, shadowed);
            for n in &added {
                shadowed.remove(n);
            }
            result?;
        }
        // Nested queries refer to their own input, not ours; do not descend
        // (mirrors morel-java's query-depth guard).
        _ => {}
    }
    Ok(())
}

/// Collects the names bound by a pattern. Unlike
/// [`Pat::for_each_id_pat`](crate::syntax::ast::Pat::for_each_id_pat), it does
/// not need frame-slot ids (which are not assigned during type resolution).
fn join_source_pat_names(pat: &Pat, out: &mut Vec<String>) {
    match &pat.kind {
        PatKind::Identifier(name) => out.push(name.clone()),
        PatKind::As(name, p) => {
            out.push(name.clone());
            join_source_pat_names(p, out);
        }
        PatKind::Annotated(p, _) => join_source_pat_names(p, out),
        PatKind::Constructor(_, Some(p)) => join_source_pat_names(p, out),
        PatKind::Cons(h, t) => {
            join_source_pat_names(h, out);
            join_source_pat_names(t, out);
        }
        PatKind::Tuple(pats) | PatKind::List(pats) => {
            for p in pats {
                join_source_pat_names(p, out);
            }
        }
        PatKind::Record(fields, _) => {
            for field in fields {
                match field {
                    PatField::Labeled(_, _, p) | PatField::Anonymous(_, p) => {
                        join_source_pat_names(p, out)
                    }
                }
            }
        }
        _ => {}
    }
}

/// Walks a `fn`/`case` match arm with the pattern's bound names shadowed.
fn join_source_walk_match(
    pat: &Pat,
    body: &Expr,
    input: &HashSet<String>,
    shadowed: &mut HashSet<String>,
) -> Result<(), Error> {
    let mut names: Vec<String> = Vec::new();
    join_source_pat_names(pat, &mut names);
    let mut added: Vec<String> = Vec::new();
    for name in names {
        if shadowed.insert(name.clone()) {
            added.push(name);
        }
    }
    let result = join_source_walk(body, input, shadowed);
    for n in &added {
        shadowed.remove(n);
    }
    result
}

/// Adds the names bound by `let` declarations to `shadowed`, returning the
/// names actually added (so the caller can remove exactly those).
fn join_source_shadow_decls(
    decls: &[Decl],
    shadowed: &mut HashSet<String>,
) -> Vec<String> {
    let mut added: Vec<String> = Vec::new();
    for d in decls {
        match &d.kind {
            DeclKind::Val(_, _, binds) => {
                for b in binds {
                    let mut names: Vec<String> = Vec::new();
                    join_source_pat_names(&b.pat, &mut names);
                    for name in names {
                        if shadowed.insert(name.clone()) {
                            added.push(name);
                        }
                    }
                }
            }
            DeclKind::Fun(funs) => {
                for fb in funs {
                    if shadowed.insert(fb.name.clone()) {
                        added.push(fb.name.clone());
                    }
                }
            }
            _ => {}
        }
    }
    added
}

impl TypeResolver {
    /// Returns the declared parameter count (arity) of a type
    /// constructor by name, or `None` if it isn't a known one.
    /// Consults both built-in types (via [`library::BuiltInDatatype`]
    /// / [`library::BuiltInEqtype`] strum properties) and
    /// user-declared datatypes accumulated in
    /// `self.user_datatype_arities`.
    fn arity_of_type_ctor(&self, name: &str) -> Option<usize> {
        library::builtin_type_arity(name)
            .or_else(|| self.user_datatype_arities.get(name).copied())
    }

    /// Expands an AST type to a core type, resolving every named type
    /// against `aliases` (the aliases and datatypes in scope) and the
    /// built-in type constructors. A type alias is transparent, so it is
    /// replaced by its (already expanded) body.
    ///
    /// Returns the offending name and span if a name is not bound to a type.
    fn expand_ast_type(
        &self,
        ast_type: &AstType,
        aliases: &HashMap<String, Type>,
    ) -> Result<Type, (String, Span)> {
        let unbound =
            |name: &str| Err((name.to_string(), ast_type.span.clone()));
        match &ast_type.kind {
            TypeKind::Con(_) | TypeKind::Expression(_) | TypeKind::Var(_) => {
                // A type variable, `typeof e`, or a constructor: not
                // expanded here. Fall back to the unexpanded lowering, or
                // to `unit` if that is not possible.
                Ok(ast_type_to_core_type(ast_type)
                    .unwrap_or(Type::Primitive(PrimitiveType::Unit)))
            }
            TypeKind::Composite(_) => {
                // Already reported by `validate_ast_type`.
                Ok(Type::Primitive(PrimitiveType::Unit))
            }
            TypeKind::Fn(a, b) => Ok(Type::Fn(
                Rc::new(self.expand_ast_type(a, aliases)?),
                Rc::new(self.expand_ast_type(b, aliases)?),
            )),
            TypeKind::Id(name) => {
                if let Some(p) = PrimitiveType::parse_name(name) {
                    Ok(Type::Primitive(p))
                } else if let Some(t) = aliases.get(name) {
                    Ok(t.clone())
                } else if library::builtin_type_arity(name.as_str()) == Some(0)
                {
                    Ok(Type::Data(name.clone(), vec![]))
                } else {
                    unbound(name)
                }
            }
            TypeKind::Record(fields) => {
                let mut field_map: BTreeMap<Label, Rc<Type>> = BTreeMap::new();
                for field in fields {
                    field_map.insert(
                        Label::from(field.label.name.clone()),
                        Rc::new(self.expand_ast_type(&field.type_, aliases)?),
                    );
                }
                Ok(Type::Record(false, field_map))
            }
            TypeKind::Tuple(types) => {
                let mut args = Vec::with_capacity(types.len());
                for t in types {
                    args.push(Rc::new(self.expand_ast_type(t, aliases)?));
                }
                Ok(Type::Tuple(args))
            }
            TypeKind::Unit => Ok(Type::Primitive(PrimitiveType::Unit)),
            TypeKind::App(args, base) => {
                let TypeKind::Id(name) = &base.kind else {
                    return Ok(Type::Primitive(PrimitiveType::Unit));
                };
                let flat_args = AstType::flatten(args);
                let mut args2 = Vec::with_capacity(flat_args.len());
                for a in &flat_args {
                    args2.push(Rc::new(self.expand_ast_type(a, aliases)?));
                }
                if args2.len() == 1 {
                    match name.as_str() {
                        "list" => {
                            return Ok(Type::List(args2.pop().unwrap()));
                        }
                        "bag" => {
                            return Ok(Type::Bag(args2.pop().unwrap()));
                        }
                        _ => {}
                    }
                }
                if self.arity_of_type_ctor(name).is_some() {
                    Ok(Type::Data(name.clone(), args2))
                } else {
                    Err((name.clone(), base.span.clone()))
                }
            }
        }
    }

    /// Walks an AST type and pushes errors for invalid forms:
    /// standalone `(t1, ..., tn)` tuple types, and wrong-arity
    /// applications of known type constructors. Used by code paths
    /// (datatype/type declarations) that lower types via
    /// [`ast_type_to_core_type_with_vars`], which silently swallows
    /// errors.
    fn validate_ast_type(&self, ast_type: &AstType) {
        match &ast_type.kind {
            TypeKind::Composite(types) => {
                self.field_errors.borrow_mut().push((
                    "tuple types must be written 't1 * ... * tn', \
                     not '(t1, ..., tn)'"
                        .to_string(),
                    ast_type.span.clone(),
                ));
                for t in types {
                    self.validate_ast_type(t);
                }
            }
            TypeKind::App(args, base) => {
                let flat_args = AstType::flatten(args);
                if let TypeKind::Id(name) = &base.kind
                    && let Some(expected) = self.arity_of_type_ctor(name)
                    && expected != flat_args.len()
                {
                    let actual = flat_args.len();
                    self.field_errors.borrow_mut().push((
                        format!(
                            "type constructor {} given {} argument{}, \
                             wants {}",
                            name,
                            actual,
                            if actual == 1 { "" } else { "s" },
                            expected,
                        ),
                        ast_type.span.clone(),
                    ));
                }
                for arg in &flat_args {
                    self.validate_ast_type(arg);
                }
            }
            TypeKind::Fn(a, b) => {
                self.validate_ast_type(a);
                self.validate_ast_type(b);
            }
            TypeKind::Tuple(types) => {
                for t in types {
                    self.validate_ast_type(t);
                }
            }
            TypeKind::Record(fields) => {
                for f in fields {
                    self.validate_ast_type(&f.type_);
                }
            }
            TypeKind::Con(_)
            | TypeKind::Id(_)
            | TypeKind::Unit
            | TypeKind::Var(_)
            | TypeKind::Expression(_) => {}
        }
    }

    /// Creates a new type resolver.
    pub fn new() -> Self {
        let mut unifier = Unifier::new(true);
        let collection_op = unifier.op(COLLECTION_OP_NAME, Some(2));
        let ordered_op = unifier.op(ORDERED_OP_NAME, Some(0));
        let unordered_op = unifier.op(UNORDERED_OP_NAME, Some(0));
        let tuple_op = unifier.op("tuple", None);
        let arg_op = unifier.op("$arg", None);
        let overload_op = unifier.op("overload", None);
        let record_op = unifier.op("record", None);
        let fn_op = unifier.op("fn", Some(2));
        let int_op = unifier.op("int", Some(0));
        Self {
            warnings: Vec::new(),
            node_var_map: HashMap::new(),
            compute_stack: Vec::new(),
            aggregate_depth: 0,
            query_count: 0,
            actions: Vec::new(),
            terms: Vec::new(),
            next_id: 0,
            unifier,
            collection_op,
            ordered_op,
            unordered_op,
            tuple_op,
            arg_op,
            overload_op,
            record_op,
            fn_op,
            decl_type_vars: BTreeMap::new(),
            type_aliases: HashMap::new(),
            expanded_type_binds: HashMap::new(),
            user_datatype_arities: HashMap::new(),
            datatype_bindings: Vec::new(),
            prior_datatype_constructors: HashMap::new(),
            prior_constructor_arg_types: HashMap::new(),
            match_coverage_enabled: true,
            int_op,
            preferred_vars: Vec::new(),
            preferred_collection_vars: Vec::new(),
            var_alias_map: HashMap::new(),
            field_errors: Rc::new(RefCell::new(Vec::new())),
            field_selectors: Vec::new(),
            ordinal_validations: Vec::new(),
            modifier_fields: Rc::new(RefCell::new(HashMap::new())),
            modifier_validations: Vec::new(),
            typed_values: Rc::new(RefCell::new(HashMap::new())),
            retry_requested: Rc::new(RefCell::new(false)),
            overloads: HashMap::new(),
            new_overloads: HashMap::new(),
            seed_overloads: HashMap::new(),
            overload_constraints: Vec::new(),
        }
    }

    /// Formats a record/tuple type name for error messages.
    fn type_name(
        op_defs: &[OpDef],
        sequence: &Sequence,
        field_list: &[String],
    ) -> String {
        let is_tuple = field_list.len() >= 2
            && field_list
                .iter()
                .enumerate()
                .all(|(i, l)| l == &(i + 1).to_string());
        if is_tuple {
            let type_names: Vec<String> = sequence
                .terms
                .iter()
                .map(|t| match t {
                    Term::Sequence(s) => op_defs[s.op.0 as usize].name.clone(),
                    Term::Variable(_) => "'a".to_string(),
                })
                .collect();
            type_names.join(" * ")
        } else {
            let parts: Vec<String> = field_list
                .iter()
                .zip(sequence.terms.iter())
                .map(|(label, term)| {
                    let type_name = match term {
                        Term::Sequence(s) => {
                            op_defs[s.op.0 as usize].name.clone()
                        }
                        Term::Variable(_) => "'a".to_string(),
                    };
                    format!("{}:{}", label, type_name)
                })
                .collect();
            format!("{{{}}}", parts.join(", "))
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
        // A progressive-record receiver may trigger
        // [`TypedValue::discover_field`] mid-unification (via the
        // field-selector action). When that happens the resolver
        // sets `retry_requested`; we restart from a clean slate so
        // the next pass sees the widened type. Bounded to a few
        // iterations — each successful discovery strictly widens the
        // underlying File, so the loop terminates either with full
        // resolution or with a genuine missing-field error.
        const MAX_PROGRESSIVE_RETRIES: usize = 16;
        let seed_overloads_save = std::mem::take(&mut self.seed_overloads);
        let mut retry_count = 0;
        loop {
            *self.retry_requested.borrow_mut() = false;
            let attempt = self.deduce_type_inner(
                env,
                statement,
                seed_overloads_save.clone(),
            );
            if !*self.retry_requested.borrow()
                || retry_count >= MAX_PROGRESSIVE_RETRIES
            {
                return attempt;
            }
            retry_count += 1;
            self.reset_for_progressive_retry();
        }
    }

    /// Resets the per-statement mutable state so [`Self::deduce_type`]
    /// can run another pass against a widened progressive type.
    /// Shared cross-round state (the typed-values map, the
    /// retry-requested flag, the accumulated overloads/aliases) is
    /// preserved.
    fn reset_for_progressive_retry(&mut self) {
        self.terms.clear();
        self.actions.clear();
        self.field_errors.borrow_mut().clear();
        self.field_selectors.clear();
        self.ordinal_validations.clear();
        // `modifier_fields` is deliberately kept: it is what the next
        // attempt knows that this one did not.
        self.modifier_validations.clear();
        self.typed_values.borrow_mut().clear();
        self.node_var_map.clear();
        self.overload_constraints.clear();
        self.preferred_vars.clear();
        self.var_alias_map.clear();
        self.datatype_bindings.clear();
        self.decl_type_vars.clear();
        // Fresh unifier — keep the cached op references in sync.
        self.unifier = Unifier::new(true);
        self.collection_op = self.unifier.op(COLLECTION_OP_NAME, Some(2));
        self.ordered_op = self.unifier.op(ORDERED_OP_NAME, Some(0));
        self.unordered_op = self.unifier.op(UNORDERED_OP_NAME, Some(0));
        self.tuple_op = self.unifier.op("tuple", None);
        self.arg_op = self.unifier.op("$arg", None);
        self.overload_op = self.unifier.op("overload", None);
        self.record_op = self.unifier.op("record", None);
        self.fn_op = self.unifier.op("fn", Some(2));
        self.int_op = self.unifier.op("int", Some(0));
        self.overloads.clear();
        self.new_overloads.clear();
        self.next_id = 0;
    }

    fn deduce_type_inner(
        &mut self,
        env: &dyn TypeEnv,
        statement: &Statement,
        seed: HashMap<String, Vec<Type>>,
    ) -> Result<Resolved, Error> {
        self.terms.clear();

        // Seed overloads from previous statements: convert each
        // accumulated instance Type to a fresh Term in the
        // current unifier.
        for (name, types) in seed {
            for t in types {
                let v = self.type_to_term(&t);
                self.overloads
                    .entry(name.clone())
                    .or_default()
                    .push(Term::Variable(v));
            }
        }

        let decl = ensure_decl(statement);
        let mut term_map = Vec::new();
        let decl2 = self.deduce_decl_type(env, &decl, &mut term_map)?;

        // Create term pairs for unification
        let term_pairs: Vec<(Term, Term)> = self
            .terms
            .iter()
            .map(|(var, term)| (term.clone(), Term::Variable(*var)))
            .collect();

        let unify_result = match self.unifier.unify_with_constraints(
            term_pairs.as_ref(),
            &NullTracer,
            self.actions.as_ref(),
            &self.overload_constraints,
        ) {
            Ok(x) => x,
            Err(x) => {
                return Err(Error::Compile(
                    format!("Cannot deduce type: {}", x.reason()),
                    decl.span.clone(),
                ));
            }
        };

        // Check for field-not-found errors from record selectors
        // (populated during unification by ActionImpl::accept).
        if let Some((msg, span)) = self.field_errors.borrow().first() {
            return Err(Error::Compile(msg.clone(), span.clone()));
        }

        // Create a map with the results of unification.
        let mut type_map =
            TypeMap::new(&self.node_var_map, Rc::clone(&self.unifier.op_defs));
        let residual_constraints = unify_result.residual_constraints;
        let substitution = unify_result.substitution;
        for (v, term) in substitution.substitutions.clone() {
            type_map.var_term_map.insert(v, term);
        }

        type_map.expanded_type_binds = self.expanded_type_binds.clone();

        // A record whose modifiers were never desugared, because the
        // fields of its base never became known. morel-java's
        // `checkRecordModifiers` reports the same thing.
        if let Some((wanted, span)) = self.modifier_validations.first() {
            let fields = wanted
                .iter()
                .map(|f| format!("#{}", f))
                .collect::<Vec<_>>()
                .join(", ");
            return Err(Error::Compile(
                format!(
                    "unresolved flex record (can't tell what fields there \
                     are besides {})",
                    fields
                ),
                span.clone(),
            ));
        }

        // Now that the types are resolved, check that every `ordinal`
        // counts the rows of an ordered collection. It cannot be checked
        // when the binding is made: a scan's collection may still be a
        // type variable then, as `[0..4]`'s is.
        for (term, span) in &self.ordinal_validations {
            let var = match term {
                Term::Variable(v) => *v,
                Term::Sequence(_) => continue,
            };
            if !matches!(type_map.var_to_type(&var), Some(Type::List(_))) {
                return Err(Error::Compile(
                    "cannot use 'ordinal' in unordered query".to_string(),
                    span.clone(),
                ));
            }
        }

        // Turn any overload constraint that was never resolved (its argument
        // type never became concrete) into a predicate of a qualified type.
        for i in residual_constraints {
            let constraint = &self.overload_constraints[i];
            if let Some(name) = &constraint.name {
                type_map.predicate_terms.push((
                    name.clone(),
                    Term::Variable(constraint.var),
                    constraint.candidates.clone(),
                ));
            }
        }

        // Default unconstrained numeric-operator type variables to `int`.
        // When the user writes e.g. `op +` without context, the element-type
        // variable is free; Standard ML specifies that numeric operators
        // prefer `int` in that case.
        //
        // We follow variable chains: if `pv` maps to `Var(v2)` and `v2` has
        // no concrete term, default `v2` to `int`. This handles cases where
        // `pv` is not the canonical representative in the union-find.
        if !self.preferred_vars.is_empty() {
            let int_term = Term::Sequence(self.unifier.atom(self.int_op));
            for &pv in &self.preferred_vars {
                let mut current = pv;
                loop {
                    match type_map.var_term_map.get(&current).cloned() {
                        None => {
                            // `current` is the canonical free variable;
                            // default it to `int`.
                            type_map
                                .var_term_map
                                .insert(current, int_term.clone());
                            break;
                        }
                        Some(Term::Variable(next)) => {
                            current = next;
                        }
                        Some(Term::Sequence(_)) => {
                            // Already bound to a concrete type; leave it.
                            break;
                        }
                    }
                }
            }
            self.preferred_vars.clear();
        }

        // Default unconstrained aggregate-input collection variables
        // to list (ordered) or bag (unordered).
        if !self.preferred_collection_vars.is_empty() {
            let preferred = self.preferred_collection_vars.clone();
            for (pv, elem_var, ordered) in preferred {
                let mut current = pv;
                loop {
                    match type_map.var_term_map.get(&current).cloned() {
                        None => {
                            // Unconstrained: default based on ordering.
                            let orderedness = if ordered {
                                self.ordered_atom()
                            } else {
                                self.unordered_atom()
                            };
                            let term = Term::Sequence(self.collection_term(
                                Term::Variable(elem_var),
                                orderedness,
                            ));
                            type_map.var_term_map.insert(current, term);
                            break;
                        }
                        Some(Term::Variable(next)) => {
                            current = next;
                        }
                        Some(Term::Sequence(_)) => {
                            // Already bound; leave it.
                            break;
                        }
                    }
                }
            }
            self.preferred_collection_vars.clear();
        }

        // Compute the base-line offset: how many lines of comments/blank lines
        // precede the first code token.  We use `decl.span` (= statement.span)
        // rather than `decl2.span` because for `fun` declarations the
        // converted val-decl span starts after the `fun` keyword (col > 1).
        // The statement span always starts at column 1 (at the leading keyword
        // or opening parenthesis), so `line - 1` is exactly the number of
        // leading comment/blank lines — matching morel-java's parser.zero().
        let pest_span = decl.span.to_pest_span();
        let start = pest_span.start_pos();
        let base_line = start.line_col().0.saturating_sub(1);

        // Transfer alias mappings from the resolver (before collecting
        // bindings, which needs alias info for Type::Alias wrapping).
        type_map.var_alias_map = self.var_alias_map.clone();

        // Extract bindings from the declaration
        let mut bindings = Vec::new();
        Self::collect_bindings_from_decl(&decl2, &type_map, &mut bindings);
        // Merge in constructor bindings from datatype declarations.
        bindings.append(&mut self.datatype_bindings);

        // Seed with constructor sets from previous statements, then
        // add any new ones from this statement.
        type_map.datatype_constructors =
            self.prior_datatype_constructors.clone();
        type_map.constructor_arg_types =
            self.prior_constructor_arg_types.clone();
        if let DeclKind::Datatype(datatype_binds) = &decl.kind {
            for db in datatype_binds {
                let con_names: Vec<String> =
                    db.constructors.iter().map(|c| c.name.clone()).collect();
                type_map
                    .datatype_constructors
                    .insert(db.name.clone(), con_names);
                // Store constructor argument types for the pretty
                // printer (e.g. record arguments).
                for con in &db.constructors {
                    if let Some(ast_type) = &con.type_ {
                        if let Some(arg_type) = ast_type_to_core_type_with_vars(
                            ast_type,
                            &db.type_vars,
                        ) {
                            type_map
                                .constructor_arg_types
                                .insert(con.name.clone(), arg_type);
                        }
                    }
                }
            }
        }

        // Check pattern coverage (exhaustiveness and redundancy), unless
        // disabled by the matchCoverageEnabled property. Coverage errors
        // (e.g. "match redundant") are collected into `errors` rather than
        // propagated via `Result` so that the caller can still record the
        // resolved declaration for `Sys.planEx`.
        let mut errors: Vec<(String, Span)> = Vec::new();
        if self.match_coverage_enabled {
            match check_coverage(&decl2, &type_map) {
                Ok(ws) => self.warnings.extend(ws),
                Err(Error::Compile(msg, span)) => errors.push((msg, span)),
                Err(e) => return Err(e),
            }
        }

        Ok(Resolved {
            decl: decl2,
            type_map,
            bindings,
            base_line,
            warnings: self.warnings.clone(),
            errors,
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

    /// Collects bindings from a pattern. `alias` is the name of a
    /// type alias from an enclosing `Annotated` pattern, if any.
    fn collect_bindings_from_pat(
        pat: &Pat,
        type_map: &TypeMap,
        bindings: &mut Vec<TypeBinding>,
    ) {
        Self::collect_bindings_from_pat2(pat, type_map, bindings, None);
    }

    fn collect_bindings_from_pat2(
        pat: &Pat,
        type_map: &TypeMap,
        bindings: &mut Vec<TypeBinding>,
        alias: Option<&str>,
    ) {
        match &pat.kind {
            PatKind::Identifier(name) => {
                if let Some(id) = pat.id {
                    if let Some(resolved_type) = if alias.is_some() {
                        type_map.get_type(id)
                    } else {
                        type_map.get_type_with_alias(id)
                    } {
                        let resolved_type = if let Some(alias_name) = alias {
                            Rc::new(Type::Alias(
                                alias_name.to_string(),
                                resolved_type,
                                vec![],
                            ))
                        } else {
                            resolved_type
                        };
                        bindings.push(TypeBinding {
                            name: name.clone(),
                            resolved_type: (*resolved_type).clone(),
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
                            resolved_type: (*resolved_type).clone(),
                            kind: BindingKind::Val,
                        });
                    }
                }
                // Also collect from the inner pattern
                Self::collect_bindings_from_pat2(
                    inner_pat, type_map, bindings, alias,
                );
            }
            PatKind::Tuple(pats) => {
                for p in pats {
                    Self::collect_bindings_from_pat2(
                        p, type_map, bindings, None,
                    );
                }
            }
            PatKind::List(pats) => {
                for p in pats {
                    Self::collect_bindings_from_pat2(
                        p, type_map, bindings, None,
                    );
                }
            }
            PatKind::Record(fields, _ellipsis) => {
                for field in fields {
                    match field {
                        PatField::Labeled(_span, _name, p) => {
                            Self::collect_bindings_from_pat2(
                                p, type_map, bindings, None,
                            );
                        }
                        PatField::Anonymous(_span, p) => {
                            Self::collect_bindings_from_pat2(
                                p, type_map, bindings, None,
                            );
                        }
                    }
                }
            }
            PatKind::Cons(left, right) => {
                Self::collect_bindings_from_pat2(
                    left, type_map, bindings, None,
                );
                Self::collect_bindings_from_pat2(
                    right, type_map, bindings, None,
                );
            }
            PatKind::Annotated(inner_pat, ann_type) => {
                // If the annotation references a type alias, pass the
                // alias name down so that the binding's resolved type
                // is wrapped in Type::Alias.
                let alias_name: Option<&str> =
                    if let TypeKind::Id(name) = &ann_type.kind {
                        // Check if the annotation type id maps to a var
                        // with an alias. The annotation's id is the Var's
                        // id (set by reg_type), so look it up directly.
                        if let Some(ann_id) = ann_type.id {
                            let var = Var { id: ann_id };
                            if type_map.var_alias_map.contains_key(&var) {
                                Some(name.as_str())
                            } else {
                                None
                            }
                        } else {
                            None
                        }
                    } else {
                        None
                    };
                Self::collect_bindings_from_pat2(
                    inner_pat, type_map, bindings, alias_name,
                );
            }
            PatKind::Constructor(_name, Some(inner_pat)) => {
                Self::collect_bindings_from_pat2(
                    inner_pat, type_map, bindings, None,
                );
            }
            _ => {
                // Other patterns don't create bindings
            }
        }
    }

    /// Deduces a declaration's type.
    /// Binds the declarations of a `let` into the environment, generalizing
    /// value bindings so that they can be used polymorphically in the body
    /// (Hindley-Milner let-polymorphism).
    ///
    /// Generalization works at the term level: we solve the constraints so
    /// far, find which of the binding's type variables are local (not
    /// reachable from any variable that existed before the declaration), and
    /// bind a scheme that, on each use, copies the binding's resolved type
    /// term with fresh variables for those local variables. Non-value
    /// bindings (the value restriction) are bound monomorphically, exactly as
    /// before.
    fn bind_decl_generalized(
        &mut self,
        env: &Rc<dyn TypeEnv>,
        term_map: &[(String, Term)],
        prior_vars: &[Var],
        prior_query_count: usize,
        decl: &Decl,
    ) -> Rc<dyn TypeEnv> {
        // A declaration that contains a relational query compiles to a
        // stack-based plan that our term-copy generalization does not
        // preserve, so it is not generalized.
        if self.query_count != prior_query_count {
            return env.bind_all(term_map);
        }
        let value_names = Self::generalizable_names(decl);
        if value_names.is_empty() {
            return env.bind_all(term_map);
        }

        // Solve the constraints accumulated so far. Actions (e.g. flex-record
        // field resolution) affect only this local solve, so it is
        // side-effect free and we can run it as often as we like.
        let term_pairs: Vec<(Term, Term)> = self
            .terms
            .iter()
            .map(|(var, term)| (term.clone(), Term::Variable(*var)))
            .collect();
        let Ok(unify_result) = self.unifier.unify_with_constraints(
            &term_pairs,
            &NullTracer,
            self.actions.as_ref(),
            &self.overload_constraints,
        ) else {
            return env.bind_all(term_map);
        };
        let subst = unify_result.substitution;

        // The type variables that are free in the enclosing environment:
        // everything reachable by resolving a variable that existed before
        // this declaration. A binding variable is generalizable only if it is
        // not one of these.
        let mut env_vars: HashSet<Var> = HashSet::new();
        for v in prior_vars {
            let mut vars = Vec::new();
            subst
                .resolve_term(&Term::Variable(*v))
                .collect_vars(&mut vars);
            env_vars.extend(vars);
        }

        let mut env2 = env.clone();
        for (name, term) in term_map {
            if !value_names.contains(name) {
                env2 = env2.bind(name.clone(), term.clone());
                continue;
            }
            let resolved = subst.resolve_term(term);
            let mut binding_vars = Vec::new();
            resolved.collect_vars(&mut binding_vars);
            if self.overlaps_action(&binding_vars, &subst) {
                // The binding's type is determined in part by a
                // field-resolution action (a flex/progressive record whose
                // fields come from how it is used). Generalizing creates
                // fresh variables that would not carry that action, so bind
                // it monomorphically.
                env2 = env2.bind(name.clone(), term.clone());
                continue;
            }
            let gen_vars: Vec<Var> = binding_vars
                .into_iter()
                .filter(|v| !env_vars.contains(v))
                .collect();
            if gen_vars.is_empty() {
                // Monomorphic.
                env2 = env2.bind(name.clone(), term.clone());
            } else {
                env2 = Rc::new(SchemeTypeEnv {
                    parent: env2,
                    name: name.clone(),
                    term: resolved,
                    gen_vars,
                });
            }
        }
        env2
    }

    /// Returns whether any of `binding_vars` is the target of a pending
    /// field-resolution action (that is, a flex/progressive record whose
    /// fields are supplied later). A binding whose type depends on such an
    /// action cannot be generalized by copying its term, because the copy's
    /// fresh variables would not carry the action.
    fn overlaps_action(
        &self,
        binding_vars: &[Var],
        subst: &Substitution,
    ) -> bool {
        self.actions.iter().any(|(action_var, _)| {
            let mut action_vars = Vec::new();
            subst
                .resolve_term(&Term::Variable(*action_var))
                .collect_vars(&mut action_vars);
            action_vars.iter().any(|v| binding_vars.contains(v))
        })
    }

    /// Returns the names bound by `decl` that may be generalized: names bound
    /// (by an identifier pattern) to a syntactic value, in a non-instance
    /// value declaration.
    ///
    /// The value restriction (only generalizing syntactic values) keeps
    /// generalization sound. Recursive (`fun`) bindings may be generalized:
    /// within the definition the name is monomorphic (recursion is not
    /// polymorphic), but it is generalized for use in the body.
    fn generalizable_names(decl: &Decl) -> HashSet<String> {
        let mut names = HashSet::new();
        if let DeclKind::Val(_rec, inst, val_binds) = &decl.kind
            && !inst
        {
            for val_bind in val_binds {
                if let PatKind::Identifier(name) = &val_bind.pat.kind
                    && Self::is_value_expr(&val_bind.expr)
                {
                    names.insert(name.clone());
                }
            }
        }
        names
    }

    /// Returns whether an expression is a syntactic value.
    fn is_value_expr(expr: &Expr) -> bool {
        matches!(
            expr.kind,
            ExprKind::Fn(_) | ExprKind::Identifier(_) | ExprKind::Literal(_)
        )
    }

    fn deduce_decl_type(
        &mut self,
        env: &dyn TypeEnv,
        decl: &Decl,
        term_map: &mut Vec<(String, Term)>,
    ) -> Result<Decl, Error> {
        match &decl.kind {
            // lint: sort until '#}' where '##DeclKind::'
            DeclKind::Datatype(datatype_binds) => {
                self.deduce_datatype_decl_type(env, datatype_binds, term_map)?;
                Ok(decl.clone())
            }
            DeclKind::FloatingAttr(_) => {
                // Floating attributes carry no type; pass through unchanged.
                Ok(decl.clone())
            }
            DeclKind::Fun(fun_binds) => {
                let val_decl = self.convert_fun_to_val(env, fun_binds);
                self.deduce_decl_type(env, &val_decl, term_map)
            }
            DeclKind::Over(name) => {
                // Register the name as an overloaded operator.
                // At this point we don't know the type; instances
                // will be added by subsequent `val inst` decls.
                // We bind to a fresh variable so the name is in
                // scope for later decls.
                let v = self.variable();
                term_map.push((name.clone(), Term::Variable(v)));
                Ok(decl.clone())
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
            DeclKind::Type(type_binds) => {
                // 'type myInt = int' declarations register a type alias
                // in the resolver. The alias maps the new name to the
                // resolved core type of the RHS, so subsequent uses of
                // 'myInt' in type position resolve to 'int'.
                //
                // A 'type' declaration is not recursive, and the bindings
                // of a 'type ... and ...' group are simultaneous, so each
                // body is resolved against the aliases in scope *before*
                // the declaration: a name that the group itself binds
                // means the definition being displaced. An alias is
                // transparent, so it is expanded.
                let prior_aliases = self.type_aliases.clone();
                let mut expanded = Vec::with_capacity(type_binds.len());
                for tb in type_binds {
                    self.validate_ast_type(&tb.type_);
                    match self.expand_ast_type(&tb.type_, &prior_aliases) {
                        Ok(rhs_type) => {
                            expanded.push((tb.name.clone(), rhs_type));
                        }
                        Err((name, span)) => {
                            self.field_errors.borrow_mut().push((
                                format!("unbound type constructor: {}", name),
                                span,
                            ));
                            return Ok(decl.clone());
                        }
                    }
                }
                for (name, rhs_type) in expanded {
                    self.type_aliases.insert(name.clone(), rhs_type.clone());
                    self.expanded_type_binds.insert(name, rhs_type);
                }
                Ok(decl.clone())
            }
            DeclKind::Val(rec, inst, val_binds) => {
                let x = &self.deduce_val_decl_type(
                    env, *rec, *inst, val_binds, term_map,
                )?;
                Ok(self.reg_decl(&x, &decl.span, decl.id))
            }
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
                // Use the arm span (fun_match.span) for the pattern, so that
                // coverage error messages point to the whole arm rather than
                // just the argument pattern position.
                let mut arm_pat = self.pat_tuple(&span, &fun_match.pats);
                arm_pat.span = fun_match.span.clone();
                match_list.push(Match {
                    pat: arm_pat,
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

    /// Builds the AST for `Range.<method>`, i.e.
    /// `Apply(RecordSelector(method), Identifier("Range"))`.
    fn range_method(span: &Span, method: &str) -> Expr {
        ExprKind::Apply(
            Box::new(
                ExprKind::RecordSelector(method.to_string()).spanned(span),
            ),
            Box::new(ExprKind::Identifier("Range".to_string()).spanned(span)),
        )
        .spanned(span)
    }

    /// Converts one [`RangeItem`] to the AST for a `Range` constructor
    /// application (`POINT e`, `CLOSED (lo, hi)`, etc.).
    fn range_item_to_expr(item: &RangeItem, span: &Span) -> Expr {
        let id = |name: &str| ExprKind::Identifier(name.to_string());
        let apply = |name: &str, arg: Expr| {
            ExprKind::Apply(Box::new(id(name).spanned(span)), Box::new(arg))
                .spanned(span)
        };
        let pair = |lo: &Expr, hi: &Expr| {
            ExprKind::Tuple(vec![lo.clone(), hi.clone()]).spanned(span)
        };
        match item {
            RangeItem::Point(e) => apply("POINT", e.clone()),
            RangeItem::Closed(lo, hi) => apply("CLOSED", pair(lo, hi)),
            RangeItem::ClosedOpen(lo, hi) => apply("CLOSED_OPEN", pair(lo, hi)),
            RangeItem::OpenClosed(lo, hi) => apply("OPEN_CLOSED", pair(lo, hi)),
            RangeItem::Open(lo, hi) => apply("OPEN", pair(lo, hi)),
            RangeItem::AtLeast(e) => apply("AT_LEAST", e.clone()),
            RangeItem::GreaterThan(e) => apply("GREATER_THAN", e.clone()),
            RangeItem::AtMost(e) => apply("AT_MOST", e.clone()),
            RangeItem::LessThan(e) => apply("LESS_THAN", e.clone()),
            RangeItem::All => id("ALL").spanned(span),
        }
    }

    /// Builds the desugared AST for `x elem [r1, r2, ...]` (or `notelem`):
    /// `Range.contains r1 x orelse Range.contains r2 x orelse ...`,
    /// wrapped in `not (...)` for `notelem`.
    fn elem_on_range_list(
        x: &Expr,
        items: &[RangeItem],
        not: bool,
        span: &Span,
    ) -> Expr {
        if items.is_empty() {
            return ExprKind::Literal(LiteralKind::Bool(not).spanned(span))
                .spanned(span);
        }
        let mut disjunction: Option<Expr> = None;
        for item in items {
            let range_exp = Self::range_item_to_expr(item, span);
            let contains = Self::range_method(span, "contains");
            let applied =
                ExprKind::Apply(Box::new(contains), Box::new(range_exp))
                    .spanned(span);
            let test = ExprKind::Apply(Box::new(applied), Box::new(x.clone()))
                .spanned(span);
            disjunction = Some(match disjunction {
                None => test,
                Some(d) => {
                    ExprKind::OrElse(Box::new(d), Box::new(test)).spanned(span)
                }
            });
        }
        let d = disjunction.unwrap();
        if not {
            ExprKind::Apply(
                Box::new(ExprKind::Identifier("not".to_string()).spanned(span)),
                Box::new(d),
            )
            .spanned(span)
        } else {
            d
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

    /// Deduces the types of a `datatype` declaration.
    ///
    /// For each `DatatypeBind` in the declaration, registers the
    /// datatype's name as a type alias so that self-referential
    /// constructor types (e.g. `'a tree` in
    /// `Node of 'a tree * 'a * 'a tree`) resolve correctly, then
    /// registers each constructor in `term_map` so that later
    /// expressions can reference it.
    ///
    /// For mutually recursive datatypes (`datatype ... and ...`),
    /// all names are registered first (Phase 1) so that any bind
    /// can reference any sibling's type.
    fn deduce_datatype_decl_type(
        &mut self,
        _env: &dyn TypeEnv,
        datatype_binds: &[DatatypeBind],
        term_map: &mut Vec<(String, Term)>,
    ) -> Result<(), Error> {
        // Phase 1: Register each datatype's name as a type alias
        // so that constructor types can reference it (including
        // self-references and mutual references). Publish the arity
        // to `user_datatype_arities` so that `(t1, …, tn) name` in a
        // later annotation is arity-checked. A redeclaration with a
        // new arity overwrites the previous entry.
        for db in datatype_binds {
            let type_var_types: Vec<Rc<Type>> = (0..db.type_vars.len())
                .map(|i| Rc::new(Type::Variable(TypeVariable::new(i))))
                .collect();
            let data_type = Type::Data(db.name.clone(), type_var_types);
            self.type_aliases.insert(db.name.clone(), data_type);
            self.user_datatype_arities
                .insert(db.name.clone(), db.type_vars.len());
        }

        // Phase 2: For each datatype, process constructors and
        // register them in term_map.
        for db in datatype_binds {
            let param_count = db.type_vars.len();
            let type_var_types: Vec<Rc<Type>> = (0..param_count)
                .map(|i| Rc::new(Type::Variable(TypeVariable::new(i))))
                .collect();
            let data_type = Type::Data(db.name.clone(), type_var_types);

            for con in &db.constructors {
                // Build the constructor's type:
                //   nullary  → datatype  (e.g. Empty : 'a tree)
                //   with arg → Fn(arg_type, datatype)
                let con_type = if let Some(ast_type) = &con.type_ {
                    // Surface composite/arity errors that would
                    // otherwise be swallowed by the unwrap_or below.
                    self.validate_ast_type(ast_type);
                    let arg_core = ast_type_to_core_type_with_vars(
                        ast_type,
                        &db.type_vars,
                    )
                    .unwrap_or(Type::Primitive(PrimitiveType::Unit));
                    Type::Fn(Rc::new(arg_core), Rc::new(data_type.clone()))
                } else {
                    data_type.clone()
                };

                // Wrap in Forall if the datatype has type
                // parameters. This makes the constructor
                // polymorphic (e.g. `Empty : forall 1 'a tree`).
                let scheme = if param_count > 0 {
                    Type::Forall(Rc::new(con_type), param_count)
                } else {
                    con_type
                };

                // Convert to a term and register.
                let v = self.variable();
                self.type_term(&scheme, &Subst::Empty, &v);
                term_map.push((con.name.clone(), Term::Variable(v)));

                // Store for cross-statement propagation.
                self.datatype_bindings.push(TypeBinding {
                    name: con.name.clone(),
                    resolved_type: scheme,
                    kind: BindingKind::Constructor,
                });
            }
        }
        Ok(())
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
                    let var = *v_pat_supplier.get_or_init(|| self.variable());
                    env_holder.push(name.clone(), Term::Variable(var));
                }
            }
        }

        let env2 = env_holder.build();
        let mut val_binds2 = Vec::new();

        // Third pass: deduce types for each binding
        for (val_bind, v_supplier) in map0 {
            let var = *v_supplier.get_or_init(|| self.variable());
            let val_bind2 =
                self.deduce_val_bind_type(&*env2, &val_bind, term_map, &var)?;
            // If this is an 'val inst' binding, store the
            // binding's var as a candidate for the overloaded
            // operator's instance set.
            if inst {
                if let PatKind::Identifier(name) = &val_bind2.pat.kind {
                    self.overloads
                        .entry(name.clone())
                        .or_default()
                        .push(Term::Variable(var));
                    self.new_overloads
                        .entry(name.clone())
                        .or_default()
                        .push(var);
                }
            }
            val_binds2.push(val_bind2);
        }

        Ok(DeclKind::Val(rec, inst, val_binds2))
    }

    /// Converts a type AST node to a type term.
    fn deduce_type_type(
        &mut self,
        env: &dyn TypeEnv,
        type_: &AstType,
        v: &Var,
    ) -> AstType {
        let mut converter = TypeToTermConverter {
            type_resolver: self,
            env,
            type_variables: BTreeMap::new(),
            extra_type_vars: BTreeMap::new(),
        };
        converter.type_term(type_, &Subst::Empty, v)
    }

    fn deduce_type_scheme(
        &mut self,
        env: &dyn TypeEnv,
        type_scheme: &TypeScheme,
        v: &Var,
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
            extra_type_vars: BTreeMap::new(),
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
        v: &Var,
    ) -> Result<Expr, Error> {
        Ok(match &expr.kind {
            // lint: sort until '#}' where '##ExprKind::'
            ExprKind::Aggregate(f, e) => {
                // 'over' is valid only inside a 'compute' clause, and not
                // nested inside another 'over'.
                if self.compute_stack.is_empty() {
                    return Err(Error::Compile(
                        "'over' is only valid in 'compute'".to_string(),
                        expr.span.clone(),
                    ));
                }
                if self.aggregate_depth > 0 {
                    return Err(Error::Compile(
                        "'over' is not valid in 'over'".to_string(),
                        expr.span.clone(),
                    ));
                }
                let step_env = self.compute_stack.last().unwrap().clone();
                // The `over` expression (e) refers to pre-group variables
                // (e.g. `a` in `compute sum over a`), so resolve it against
                // the pre-group environment, not the post-group environment.
                let v_e = self.variable();
                // Mark that we are inside an `over` while resolving its
                // sub-expressions, so a nested `over` is rejected.
                self.aggregate_depth += 1;
                let e2 = self.deduce_expr_type(&*step_env.env, e, &v_e)?;
                // f has type: collection(type_of_e) -> v.
                // Determine the collection kind from the aggregate
                // function's declared type:
                //  - list-only (e.g. count: 'a list -> int): list_term
                //  - bag-only: bag_term
                //  - overloaded: match input ordering
                //  - anonymous/unknown: is_collection_of + default
                let v_elements = self.variable();
                let kind = self.aggregate_collection_kind(env, f);
                match kind {
                    CollectionKind::List => {
                        self.list_term(Term::Variable(v_e), &v_elements);
                    }
                    CollectionKind::Bag => {
                        self.bag_term(Term::Variable(v_e), &v_elements);
                    }
                    CollectionKind::MatchInput => {
                        // Link to the input's orderedness.
                        if let Some(c) = step_env.c {
                            self.same_orderedness(
                                &v_elements,
                                &v_e,
                                &c,
                                &step_env.v,
                            );
                        } else {
                            self.list_term(Term::Variable(v_e), &v_elements);
                        }
                    }
                    CollectionKind::Unknown => {
                        // Anonymous function: allow either, default
                        // based on query ordering.
                        self.is_collection_of(&v_elements, &v_e);
                        self.preferred_collection_vars.push((
                            v_elements,
                            v_e,
                            step_env.ordered,
                        ));
                    }
                }
                let v_fn = self.variable();
                self.fn_term(&v_elements, v, &v_fn);
                let f2 = self.deduce_expr_type(env, f, &v_fn)?;
                self.aggregate_depth -= 1;
                let x = ExprKind::Aggregate(Box::new(f2), Box::new(e2));
                self.reg_expr(&x, &expr.span, expr.id, v)
            }
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
                    && let Some(field_list) =
                        Self::field_list(&self.unifier.op_defs, &sequence)
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
            ExprKind::Current => {
                // 'current' is bound in the query environment for each step.
                match env.get("current", self) {
                    Some(BindType::Val(term))
                    | Some(BindType::Constructor(term)) => {
                        self.equiv(&term, v);
                    }
                    None => {
                        return Err(Error::Compile(
                            "'current' is only valid in a query".into(),
                            expr.span.clone(),
                        ));
                    }
                }
                self.reg_expr(&expr.kind, &expr.span, expr.id, v)
            }
            ExprKind::Div(left, right) => {
                let (left2, right2) =
                    self.deduce_call2_type(env, "op div", left, right, v)?;
                self.preferred_vars.push(*v);
                let x = ExprKind::Div(Box::new(left2), Box::new(right2));
                self.reg_expr(&x, &expr.span, expr.id, v)
            }
            ExprKind::Divide(left, right) => {
                let (left2, right2) =
                    self.deduce_call2_type(env, "op /", left, right, v)?;
                let x = ExprKind::Divide(Box::new(left2), Box::new(right2));
                self.reg_expr(&x, &expr.span, expr.id, v)
            }
            ExprKind::Elem(left, right) => {
                // Special case: `x elem [r1, r2, ...]` where the RHS
                // contains range items is rewritten to a short-circuiting
                // chain of `Range.contains` calls, so the list (which may
                // be infinite) is never materialized.
                if let ExprKind::RangeList(items) = &right.kind {
                    let call = Self::elem_on_range_list(
                        left, items, false, &expr.span,
                    );
                    return self.deduce_expr_type(env, &call, v);
                }
                // 'elem' works on both lists and bags.
                let v_elem = self.variable();
                let left2 = self.deduce_expr_type(env, left, &v_elem)?;
                let v_coll = self.variable();
                self.is_collection_of(&v_coll, &v_elem);
                let right2 = self.deduce_expr_type(env, right, &v_coll)?;
                self.primitive_term(&PrimitiveType::Bool, v);
                let x = ExprKind::Elem(Box::new(left2), Box::new(right2));
                self.reg_expr(&x, &expr.span, expr.id, v)
            }
            ExprKind::Elements => {
                if self.compute_stack.is_empty() {
                    return Err(Error::Compile(
                        format!(
                            "'{}' is only valid in a '{}' clause",
                            ExprKind::Elements.clause(),
                            StepKind::Compute(Expr::empty()).clause()
                        ),
                        expr.span.clone(),
                    ));
                }
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
                self.prefer_left_int(&left2);
                let x =
                    ExprKind::GreaterThan(Box::new(left2), Box::new(right2));
                self.reg_expr(&x, &expr.span, expr.id, v)
            }
            ExprKind::GreaterThanOrEqual(left, right) => {
                let (left2, right2) =
                    self.deduce_call2_type(env, "op >=", left, right, v)?;
                self.prefer_left_int(&left2);
                let x = ExprKind::GreaterThanOrEqual(
                    Box::new(left2),
                    Box::new(right2),
                );
                self.reg_expr(&x, &expr.span, expr.id, v)
            }
            ExprKind::Identifier(name) => {
                // If the name is overloaded, add a constraint
                // that v must match one of the candidate types.
                if let Some(candidates) = self.overloads.get(name).cloned() {
                    // Name the constraint if the overload is user-declared
                    // ('over'/'inst'), so that if it is never resolved it
                    // becomes a predicate of a qualified type, and so that a
                    // failure names the overload. A built-in overload (e.g.
                    // 'only') keeps the old behaviour.
                    self.overload_constraints.push(
                        if library::BuiltInFunction::is_built_in_overload(name)
                        {
                            Constraint::new(*v, candidates)
                        } else {
                            Constraint::named(*v, candidates, name)
                        },
                    );
                    return Ok(
                        self.reg_expr(&expr.kind, &expr.span, expr.id, v)
                    );
                }
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
                        return Err(Error::Compile(
                            format!(
                                "unbound variable or constructor: {}",
                                name
                            ),
                            expr.span.clone(),
                        ));
                    }
                }
                // `abs` is overloaded for `int` and `real`; prefer `int`
                // when unconstrained, matching the default-to-int behavior
                // of `op ~`.
                if name == "abs" {
                    let v_elem = self.variable();
                    let fn_seq = self.unifier.apply2(
                        self.fn_op,
                        Term::Variable(v_elem),
                        Term::Variable(v_elem),
                    );
                    self.equiv(&Term::Sequence(fn_seq), v);
                    self.preferred_vars.push(v_elem);
                }
                self.reg_expr(&expr.kind, &expr.span, expr.id, v)
            }
            ExprKind::If(a0, a1, a2) => {
                // `if cond then e1 else e2` is not a function: the condition is
                // `bool`, and `e1`, `e2` and the result share a type. It lowers
                // to a `case` in the resolver, so only the taken branch is
                // evaluated.
                let v_cond = self.variable();
                self.primitive_term(&PrimitiveType::Bool, &v_cond);
                let a02 = self.deduce_expr_type(env, a0, &v_cond)?;
                let a12 = self.deduce_expr_type(env, a1, v)?;
                let a22 = self.deduce_expr_type(env, a2, v)?;
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
                self.prefer_left_int(&left2);
                let x = ExprKind::LessThan(Box::new(left2), Box::new(right2));
                self.reg_expr(&x, &expr.span, expr.id, v)
            }
            ExprKind::LessThanOrEqual(left, right) => {
                let (left2, right2) =
                    self.deduce_call2_type(env, "op <=", left, right, v)?;
                self.prefer_left_int(&left2);
                let x = ExprKind::LessThanOrEqual(
                    Box::new(left2),
                    Box::new(right2),
                );
                self.reg_expr(&x, &expr.span, expr.id, v)
            }
            ExprKind::Let(decl_list, expr) => {
                // Save overload state so let-bound `over`/`val inst`
                // declarations don't leak to outer scope.
                let saved_overloads = self.overloads.clone();
                let saved_new_overloads = self.new_overloads.clone();
                // Each successive decl must see the bindings of the
                // previous decls. We track the accumulated bindings
                // in `term_map` and rebuild a running env that starts
                // from the original `env` plus all bindings seen so
                // far. Without this, a let body like
                //   let val ten = 6 + 4 val eleven = ten + 1 in ... end
                // fails type-checking because `ten` is not yet in
                // scope when `val eleven = ten + 1` is processed.
                let mut term_map = Vec::new();
                let mut decl_list2 = Vec::new();
                let mut running_env: Rc<dyn TypeEnv> = env.bind_all(&[]);
                for decl in decl_list {
                    // Snapshot the variables that exist before this
                    // declaration; any variable the declaration introduces
                    // that is not reachable from one of these is local, and
                    // can be generalized (let-polymorphism).
                    let prior_vars = self.unifier.variables();
                    let prior_query_count = self.query_count;
                    let decl2 = self.deduce_decl_type(
                        &*running_env,
                        decl,
                        &mut term_map,
                    )?;
                    running_env = self.bind_decl_generalized(
                        &running_env,
                        &term_map,
                        &prior_vars,
                        prior_query_count,
                        &decl2,
                    );
                    decl_list2.push(decl2);
                    term_map.clear();
                }
                let env2 = running_env;
                let expr2 = self.deduce_expr_type(&*env2, expr, v)?;
                // Restore overload state.
                self.overloads = saved_overloads;
                self.new_overloads = saved_new_overloads;
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
                if let LiteralKind::Fn(builtin) = &lit.kind {
                    // Built-in function literal (inserted by the
                    // postfix-call rewrite). Its type is the
                    // built-in's declared type;
                    // instantiate fresh unification variables for any
                    // Forall-quantified type variables.
                    let builtin_type = builtin.get_type();
                    let v_builtin = self.type_to_term(&builtin_type);
                    self.equiv(&Term::Variable(v_builtin), v);
                    self.reg_expr(&expr.kind, &expr.span, expr.id, v)
                } else {
                    // Reject numeric literals outside their type's range, and
                    // character constants that are not exactly one character.
                    if let Some(msg) = literal_range_error(&lit.kind)
                        .or_else(|| char_literal_error(&lit.kind))
                    {
                        return Err(Error::Compile(msg, expr.span.clone()));
                    }
                    let resolved_type = Self::literal_type(&lit.kind);
                    self.primitive_term(&resolved_type, v);
                    self.reg_expr(&expr.kind, &expr.span, expr.id, v)
                }
            }
            ExprKind::Minus(left, right) => {
                let (left2, right2) =
                    self.deduce_call2_type(env, "op -", left, right, v)?;
                self.preferred_vars.push(*v);
                let x = ExprKind::Minus(Box::new(left2), Box::new(right2));
                self.reg_expr(&x, &expr.span, expr.id, v)
            }
            ExprKind::Mod(left, right) => {
                let (left2, right2) =
                    self.deduce_call2_type(env, "op mod", left, right, v)?;
                self.preferred_vars.push(*v);
                let x = ExprKind::Mod(Box::new(left2), Box::new(right2));
                self.reg_expr(&x, &expr.span, expr.id, v)
            }
            ExprKind::Negate(e) => {
                let e2 =
                    self.deduce_call1_type(env, "op ~", e, &expr.span, v)?;
                self.preferred_vars.push(*v);
                let x = ExprKind::Negate(Box::new(e2));
                self.reg_expr(&x, &expr.span, expr.id, v)
            }
            ExprKind::NotElem(left, right) => {
                // Special case: `x notelem [r1, r2, ...]` with range items
                // is rewritten to `not (Range.contains r1 x orelse ...)`.
                if let ExprKind::RangeList(items) = &right.kind {
                    let call =
                        Self::elem_on_range_list(left, items, true, &expr.span);
                    return self.deduce_expr_type(env, &call, v);
                }
                // 'notelem' works on both lists and bags.
                let v_elem = self.variable();
                let left2 = self.deduce_expr_type(env, left, &v_elem)?;
                let v_coll = self.variable();
                self.is_collection_of(&v_coll, &v_elem);
                let right2 = self.deduce_expr_type(env, right, &v_coll)?;
                self.primitive_term(&PrimitiveType::Bool, v);
                let x = ExprKind::NotElem(Box::new(left2), Box::new(right2));
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
                        return Err(Error::Compile(
                            format!(
                                "unbound variable or constructor: {}",
                                op_name
                            ),
                            expr.span.clone(),
                        ));
                    }
                }
                // Overloaded numeric operators prefer `int` when
                // unconstrained (Standard ML semantics). Add a fresh
                // element-type variable and record it in `preferred_vars`
                // so that, if still free after unification, it defaults
                // to `int`. Arithmetic ops (+, -, *, ~) return the element
                // type; comparison ops (<, <=, >, >=) return `bool`.
                let arith = matches!(
                    name.as_str(),
                    "+" | "-" | "*" | "~" | "div" | "mod"
                );
                let compare = matches!(name.as_str(), "<" | "<=" | ">" | ">=");
                if arith || compare {
                    let v_elem = self.variable();
                    let v_arg = if name == "~" {
                        Term::Variable(v_elem)
                    } else {
                        let seq = self.unifier.apply2(
                            self.tuple_op,
                            Term::Variable(v_elem),
                            Term::Variable(v_elem),
                        );
                        Term::Sequence(seq)
                    };
                    let result_term = if compare {
                        let v_bool = self.variable();
                        self.primitive_term(&PrimitiveType::Bool, &v_bool);
                        Term::Variable(v_bool)
                    } else {
                        Term::Variable(v_elem)
                    };
                    let fn_seq =
                        self.unifier.apply2(self.fn_op, v_arg, result_term);
                    self.equiv(&Term::Sequence(fn_seq), v);
                    self.preferred_vars.push(v_elem);
                }
                self.reg_expr(&expr.kind, &expr.span, expr.id, v)
            }
            ExprKind::OrElse(left, right) => {
                let (left2, right2) =
                    self.deduce_call2_type(env, "op orelse", left, right, v)?;
                let x = ExprKind::OrElse(Box::new(left2), Box::new(right2));
                self.reg_expr(&x, &expr.span, expr.id, v)
            }
            ExprKind::Ordinal => {
                match env.get(ORDINAL, self) {
                    None => {
                        return Err(Error::Compile(
                            "'ordinal' is only valid in a query".to_string(),
                            expr.span.clone(),
                        ));
                    }
                    Some(BindType::Val(t)) | Some(BindType::Constructor(t)) => {
                        self.ordinal_validations.push((t, expr.span.clone()));
                    }
                }
                // 'ordinal' is a row counter with type int.
                self.primitive_term(&PrimitiveType::Int, v);
                self.reg_expr(&expr.kind, &expr.span, expr.id, v)
            }
            ExprKind::Plus(left, right) => {
                let (left2, right2) =
                    self.deduce_call2_type(env, "op +", left, right, v)?;
                self.preferred_vars.push(*v);
                let x = ExprKind::Plus(Box::new(left2), Box::new(right2));
                self.reg_expr(&x, &expr.span, expr.id, v)
            }
            ExprKind::Raise(e) => {
                // `raise e` expects `e : exn` and itself can have any type
                // (since it never returns).
                let v_exn = self.variable();
                let exn_type = Type::Data("exn".to_string(), vec![]);
                self.type_term(&exn_type, &Subst::Empty, &v_exn);
                let e2 = self.deduce_expr_type(env, e, &v_exn)?;
                let x = ExprKind::Raise(Box::new(e2));
                self.reg_expr(&x, &expr.span, expr.id, v)
            }
            ExprKind::RangeList(items) => {
                // Desugar `[r1, r2, ...]` (with at least one range item)
                // into `Range.flatten [POINT/CLOSED/... applications]`.
                let span = &expr.span;
                let range_exps: Vec<Expr> = items
                    .iter()
                    .map(|it| Self::range_item_to_expr(it, span))
                    .collect();
                let list = ExprKind::List(range_exps).spanned(span);
                let flatten_fn = Self::range_method(span, "flatten");
                let call =
                    ExprKind::Apply(Box::new(flatten_fn), Box::new(list))
                        .spanned(span);
                self.deduce_expr_type(env, &call, v)?
            }
            ExprKind::Record(base, _, modifiers)
                if base.is_some() && !modifiers.is_empty() =>
            {
                // A record with modifiers becomes nested `let`s, but only
                // once we know which fields there are to destructure.
                let base = base.as_ref().unwrap();
                let Some(desugared) =
                    self.desugar_modifiers(env, expr, base, modifiers)?
                else {
                    // The fields of the base are not known yet. Deduce
                    // the modifiers' expressions -- in the enclosing
                    // environment, because without the field names there
                    // is nothing to shadow them -- so that every node
                    // has a type, and leave the record's own type
                    // unconstrained. An action asks for another attempt
                    // if unification settles the base; if it never does,
                    // the check after unification reports an unresolved
                    // flex record. morel-java's
                    // `deduceUnresolvedRecordType`.
                    for m in modifiers {
                        match m {
                            Modifier::Assign(_, _, args) => {
                                for a in args {
                                    let vv = self.variable();
                                    self.deduce_expr_type(env, &a.expr, &vv)?;
                                }
                            }
                            Modifier::All(_, _, e) => {
                                let vv = self.variable();
                                self.deduce_expr_type(env, e, &vv)?;
                            }
                            Modifier::Remove(..) | Modifier::Rename(..) => {}
                        }
                    }
                    // The error points at the base, as morel-java's
                    // does: it is the base's type that is not known.
                    self.modifier_validations
                        .push((modifier_labels(modifiers), base.span.clone()));
                    return Ok(
                        self.reg_expr(&expr.kind, &expr.span, expr.id, v)
                    );
                };
                self.deduce_expr_type(env, &desugared, v)?
            }
            ExprKind::Record(with_expr, labeled_expr_list, _) => {
                let mut field_vars = Vec::new(); // never read
                let (with_expr2, labeled_expr_list2) =
                    if let Some(base) = with_expr {
                        // `{base with f=e, ...}`: the result has the same type
                        // as the base. Deduce the base into `v` so the result
                        // type equals the full base type. For each override
                        // `f = e`, deduce `e` into the same variable as field
                        // `f` in the base record, so the override's type
                        // propagates back into the base field type.
                        let base2 = self.deduce_expr_type(env, base, v)?;
                        // After deducing the base, look up its record sequence
                        // so we can tie each override to the matching field.
                        let base_seq = self.variable_to_sequence(v);
                        let mut overrides = Vec::new();
                        for labeled_expr in labeled_expr_list {
                            // Use the base field's variable when available, so
                            // the override type unifies with the field type.
                            let v_ov = if let Some(seq) = &base_seq
                                && let Some(label) = labeled_expr.get_label()
                                && let Some(fv) = self.field_var_of(seq, &label)
                            {
                                fv
                            } else {
                                self.variable()
                            };
                            let e2 = self.deduce_expr_type(
                                env,
                                &labeled_expr.expr,
                                &v_ov,
                            )?;
                            overrides.push(LabeledExpr {
                                expr: e2,
                                ..labeled_expr.clone()
                            });
                        }
                        (Some(Box::new(base2)), overrides)
                    } else {
                        let labeled_expr_list2 = self.deduce_record_type(
                            env,
                            labeled_expr_list,
                            &mut field_vars,
                            v,
                        )?;
                        (None, labeled_expr_list2)
                    };
                let x =
                    ExprKind::Record(with_expr2, labeled_expr_list2, vec![]);
                self.reg_expr(&x, &expr.span, expr.id, v)
            }
            ExprKind::RecordSelector(name) => {
                // A bare record selector (e.g. `#a`) that is not applied to
                // a record cannot have its flex record resolved, because we
                // cannot tell what other fields the record has. morel-java
                // reports the same error.
                return Err(Error::Compile(
                    format!(
                        "unresolved flex record (can't tell what fields there are besides #{})",
                        name
                    ),
                    expr.span.clone(),
                ));
            }
            ExprKind::Times(left, right) => {
                let (left2, right2) =
                    self.deduce_call2_type(env, "op *", left, right, v)?;
                self.preferred_vars.push(*v);
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
            ExprKind::TypeString(operand) => {
                let v_operand = self.variable();
                let operand2 =
                    self.deduce_expr_type(env, operand, &v_operand)?;
                self.primitive_term(&PrimitiveType::String, v);
                let x = ExprKind::TypeString(Box::new(operand2));
                self.reg_expr(&x, &expr.span, expr.id, v)
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
        v: &Var,
    ) -> Result<Vec<Step>, Error> {
        let mut field_vars = Vec::new();
        let mut steps2 = Vec::new();

        // An empty "from" is "unit list". Ordered.
        let v11 = self.variable();
        let c11 = self.variable();
        self.record_term(&BTreeMap::new(), &v11);
        self.list_term(Term::Variable(v11), &c11);
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
            // The rows this step produces are the rows the next step's
            // `ordinal` counts, so bind it here; an expression that is
            // evaluated once per execution of the query rather than once
            // per row is deduced in `root_env` and so does not see it.
            p = self.bind_ordinal(&p_next);
        }
        self.query_count += 1;

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
        field_vars: &mut Vec<(String, Var)>,
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
            StepKind::Group(binder, key_expr, compute_expr) => self
                .deduce_group_step_type(
                    p,
                    binder.as_deref(),
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
                // Validate field ordering on the original expression before
                // deduce_record_type reorders fields alphabetically.
                self.validate_order(expr);
                let expr2 = self.deduce_expr_type(&*p.env, expr, &v)?;
                let step2 = StepKind::Order(Box::new(expr2));
                steps2.push(step2.spanned(&step.span));
                // 'order' always produces an ordered (list) collection.
                let c = self.unifier.variable();
                self.list_term(Term::Variable(p.v), &c);
                Ok(p.with_c(c).with_ordered(true))
            }
            StepKind::Require(expr) => {
                let v = self.unifier.variable();
                let expr2 = self.deduce_expr_type(&*p.env, expr, &v)?;
                self.primitive_term(&PrimitiveType::Bool, &v);
                let step2 = StepKind::Require(Box::new(expr2));
                steps2.push(step2.spanned(&step.span));
                Ok(p.clone())
            }
            StepKind::Scan(join_type, pat, expr, condition) => self
                .deduce_scan_step_type(
                    p,
                    *join_type,
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
                JoinType::Inner,
                pat,
                true,
                Some(&**expr),
                &None,
                &step.span,
                field_vars,
                steps2,
            ),
            StepKind::ScanExtent(pat) => self.deduce_scan_extent_step_type(
                p, pat, &step.span, field_vars, steps2,
            ),
            StepKind::Skip(expr) => {
                let v = self.unifier.variable();
                // 'current' from the current query is not available in skip;
                // only outer-query bindings (root_env) are in scope.
                let expr2 = self.deduce_expr_type(&*p.root_env, expr, &v)?;
                self.primitive_term(&PrimitiveType::Int, &v);
                let step2 = StepKind::Skip(Box::new(expr2));
                steps2.push(step2.spanned(&step.span));
                Ok(p.clone())
            }
            StepKind::Take(expr) => {
                let v = self.unifier.variable();
                // 'current' from the current query is not available in take;
                // only outer-query bindings (root_env) are in scope.
                let expr2 = self.deduce_expr_type(&*p.root_env, expr, &v)?;
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
                self.bag_term(Term::Variable(p.v), &c);
                steps2.push(StepKind::Unorder.spanned(&step.span));
                Ok(p.with_c(c).with_ordered(false))
            }
            StepKind::Where(expr) => {
                let v = self.unifier.variable();
                let expr2 = self.deduce_expr_type(&*p.env, expr, &v)?;
                self.primitive_term(&PrimitiveType::Bool, &v);
                let step2 = StepKind::Where(Box::new(expr2));
                steps2.push(step2.spanned(&step.span));
                Ok(p.clone())
            }
            StepKind::Yield(binder, expr) => self.deduce_yield_step_type(
                p,
                binder.as_deref(),
                expr,
                &step.span,
                field_vars,
                steps2,
            ),
            StepKind::YieldAll(binder, expr) => self
                .deduce_yield_all_step_type(
                    p,
                    binder.as_deref(),
                    expr,
                    &step.span,
                    field_vars,
                    steps2,
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
        join_type: JoinType,
        pat: &Pat,
        eq: bool,
        expr: Option<&Expr>,
        condition: &Option<Box<Expr>>,
        span: &Span,
        field_vars: &mut Vec<(String, Var)>,
        steps: &mut Vec<Step>,
    ) -> Result<Triple, Error> {
        // A `right`/`full join` source must be independent of the input (it may
        // produce rows that match no input row). `field_vars` at this point
        // holds only the input (earlier-step) fields.
        if matches!(join_type, JoinType::Right | JoinType::Full) {
            if let Some(e) = expr {
                let input_names: HashSet<String> =
                    field_vars.iter().map(|(n, _)| n.clone()).collect();
                check_join_source_independent(e, &input_names)?;
            }
        }

        // Deduce the type of the expression being iterated over
        let v0 = self.variable();
        let c0 = self.variable();

        // The scan expression may be a list or bag; defer the element-type
        // constraint until c0 is resolved (instead of forcing list here).
        if !eq {
            self.is_collection_of(&c0, &v0);
        }
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
        // Output collection type matches the input's list/bag kind.
        let v = self.field_var(field_vars, true);

        // Bind 'current' to the element type. For a single scan
        // (even if the pattern destructures into multiple fields),
        // use v0 so that 'current' maps to the frame slot directly.
        // For joins (multiple scans accumulated in field_vars from
        // prior steps), use the compound record type.
        let is_first_scan = term_map.len() == field_vars.len();
        let v_current = if is_first_scan { v0 } else { v };
        env_builder.push("current".to_string(), Term::Variable(v_current));
        let env4 = env_builder.build();

        // The collection of candidate pairs. It is created here, before the
        // constraints that give it a type, because an `on` condition is
        // evaluated once per candidate pair: an `ordinal` in it counts
        // pairs, so this is the collection whose orderedness decides
        // whether the count means anything -- and it is ordered only if
        // both inputs are. An `ordinal` in the extent still counts the
        // rows arriving at the step, reading the binding the previous step
        // left, because no pair exists when the extent is evaluated.
        let c = self.unifier.variable();

        // Handle the condition, if present. (For an outer join the condition
        // sees the raw, unwrapped types, so deduce it before wrapping.)
        let condition2 = if let Some(cond) = condition {
            let v5 = self.variable();
            let mut builder = env4.builder();
            builder.push(ORDINAL.to_string(), Term::Variable(c));
            let env5 = builder.build();
            let condition2 = self.deduce_expr_type(&*env5, cond, &v5)?;
            self.primitive_term(&PrimitiveType::Bool, &v5);
            Some(Box::new(condition2))
        } else {
            None
        };

        // An outer join wraps one or both sides in `option` downstream:
        // `left join` wraps this scan's (right) fields, `right join` wraps the
        // input's (left) fields, and `full join` wraps both. Re-bind the
        // affected variables to `option`-wrapped types and rebuild the output
        // record and environment. (The condition above saw the raw types.)
        let wrap_left = matches!(join_type, JoinType::Right | JoinType::Full);
        let wrap_right = matches!(join_type, JoinType::Left | JoinType::Full);
        let (v, env4) = if (wrap_left || wrap_right) && !eq {
            let option_op = self.unifier.op("option", Some(1));
            let start = field_vars.len() - term_map.len();
            // Rebuild from the root env (the input/left vars may now be
            // wrapped, so we cannot start from `p.env`).
            let mut wrapped = p.root_env.builder();
            for (i, entry) in field_vars.iter_mut().enumerate() {
                let wrap = if i >= start { wrap_right } else { wrap_left };
                let (name, raw_var) = entry.clone();
                let var = if wrap {
                    let wrapped_var = self.variable();
                    let seq =
                        self.unifier.apply1(option_op, Term::Variable(raw_var));
                    self.equiv(&Term::Sequence(seq), &wrapped_var);
                    *entry = (name.clone(), wrapped_var);
                    wrapped_var
                } else {
                    raw_var
                };
                wrapped.push(name, Term::Variable(var));
            }
            let v_wrapped = self.field_var(field_vars, true);
            wrapped.push("current".to_string(), Term::Variable(v_wrapped));
            (v_wrapped, wrapped.build())
        } else {
            (v, env4)
        };

        // The output collection's element type is the (possibly wrapped)
        // record `v`, and its list/bag kind matches the scan's input.
        if eq {
            // ScanEq (= expr): output inherits the preceding collection type.
            self.same_orderedness(&p.c.unwrap(), &p.v, &c, &v);
        } else if steps.is_empty() {
            // The first scan: the query has the same orderedness as its
            // source.
            self.same_orderedness(&c0, &v0, &c, &v);
        } else {
            // A comma-join: the query is a list only if both the input and
            // the source are lists, otherwise a bag.
            let v1 = self.variable();
            let v2 = self.variable();
            self.meet_collections(&p.c.unwrap(), &v1, &c0, &v2, &c, &v);
            self.is_collection_of(&c0, &v0);
        }

        // ScanEq steps must stay as ScanEq in the output so that the
        // resolver can wrap the element expression in a singleton list.
        // Normal scans (and join scans with a condition) become Scan.
        let step = if eq {
            StepKind::ScanEq(Box::new(pat2), Box::new(expr2))
        } else {
            StepKind::Scan(
                join_type,
                Box::new(pat2),
                Box::new(expr2),
                condition2,
            )
        };
        steps.push(step.spanned(span));

        // Determine ordering: ordered iff previous state is ordered
        // AND this scan's input is a list (not bag).
        let scan_ordered = if eq {
            p.ordered
        } else {
            p.ordered && self.var_is_list(&c0)
        };

        let mut triple = Triple::new(p.root_env.clone(), env4, v, Some(c));
        triple.ordered = scan_ordered;
        Ok(triple)
    }

    /// Deduces the type of a scan-extent step — `from p` (or
    /// `join p`) with no explicit source. The variable `p` is
    /// unbounded; later phases of compilation invert any
    /// surrounding `where` predicates to derive a generator. For
    /// now we just allocate a fresh type variable for the pattern
    /// and re-emit the same kind in the typed step list.
    fn deduce_scan_extent_step_type(
        &mut self,
        p: &Triple,
        pat: &Pat,
        span: &Span,
        field_vars: &mut Vec<(String, Var)>,
        steps: &mut Vec<Step>,
    ) -> Result<Triple, Error> {
        let v0 = self.variable();
        let mut term_map = Vec::new();
        let pat2 = self.deduce_pat_type(&*p.env, pat, &mut term_map, &v0);

        let mut env_builder = p.env.builder();
        for (name, term) in &term_map {
            env_builder.push(name.clone(), term.clone());
            let v = self.term_to_variable(term);
            self.reg_expr(&ExprKind::Identifier(name.clone()), span, None, &v);
            field_vars.push((name.clone(), v));
        }
        let v = self.field_var(field_vars, true);
        let is_first_scan = term_map.len() == field_vars.len();
        let v_current = if is_first_scan { v0 } else { v };
        env_builder.push("current".to_string(), Term::Variable(v_current));
        let env4 = env_builder.build();

        // Output collection's element type is `v`; output collection
        // kind defaults to bag (the natural choice for an enumerated
        // extent — `from p where p > 0 andalso p < 5` is a bag).
        let c = self.unifier.variable();
        self.bag_term(Term::Variable(v), &c);

        steps.push(StepKind::ScanExtent(Box::new(pat2)).spanned(span));

        let mut triple = Triple::new(p.root_env.clone(), env4, v, Some(c));
        triple.ordered = false;
        Ok(triple)
    }

    /// Returns `p` with `ordinal` bound in its environment, so that a
    /// later step's `ordinal` resolves to the rows `p` produces.
    ///
    /// When those rows are unordered `ordinal` is bound to
    /// [`ORDINAL_UNORDERED_TYPE`] instead, so that
    /// [`ExprKind::Ordinal`] can tell a `bag` from no query at all.
    fn bind_ordinal(&mut self, p: &Triple) -> Triple {
        match p.c {
            Some(c) => {
                let mut builder = p.env.builder();
                builder.push(ORDINAL.to_string(), Term::Variable(c));
                p.with_env(&builder.build())
            }
            // A step with no collection -- `compute`, `into` -- produces
            // no rows to count, so it leaves the binding alone.
            None => p.with_env(&p.env.clone()),
        }
    }

    /// Deduces a Yield step's type (e.g., "yield i + 4").
    ///
    /// A binder (`yield r = e`) names the whole output row `r`, an atom that
    /// behaves like a scan variable: the output type is unwrapped (no
    /// `{r: ..}`), fields are reached through `r`, `current` equals `r`, and
    /// bare field names are not in scope. A binder forces the atom path even
    /// for a record literal, so its fields are not scattered.
    fn deduce_yield_step_type(
        &mut self,
        p: &Triple,
        binder: Option<&str>,
        expr: &Expr,
        span: &Span,
        field_vars: &mut Vec<(String, Var)>,
        steps2: &mut Vec<Step>,
    ) -> Result<Triple, Error> {
        // The yield expression determines the new element type
        let v6 = self.variable();
        let expr2 = self.deduce_expr_type(&*p.env, expr, &v6)?;

        let step =
            StepKind::Yield(binder.map(String::from), Box::new(expr2.clone()));
        steps2.push(step.spanned(span));

        // Output collection kind matches the input (yield changes the
        // element type from `p.v` to `v6` but doesn't reorder/group).
        // Without this, queries inside an enclosing expression (e.g.
        // `let … in from … yield … end`) read the from's type from
        // the type_map and see `list` even when the from_builder
        // computes `bag` — because the type_map's collection-kind
        // entry was hard-coded to `list_term` regardless of input.
        let c6 = self.variable();
        self.same_orderedness(&p.c.unwrap(), &p.v, &c6, &v6);

        let mut envs = p.env.builder();
        // A `yield` step binds the fields of the record it yields, and
        // the `let`s in between do not change that: `desugar_modifiers`
        // turns a record with modifiers into one `let` per modifier,
        // whose body is the record the last modifier produced, and its
        // fields are the step's fields. The same goes for a `let` the
        // user wrote.
        let yielded = let_body(&expr2);
        if binder.is_none()
            && let ExprKind::Record(with, labeled_exprs, _) = yielded.kind
        {
            let mut v = None;
            if let Some(with) = with
                && let Some(id) = with.id
            {
                v = self.node_var_map.get(&id);
            }
            if let None = v
                && let Some(id) = yielded.id
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
            // Non-record yield (tuple, scalar): the previous row
            // bindings are no longer in scope. Build the new
            // environment from the root (outer) env, not the
            // current step env.
            envs = p.root_env.builder();
            // A binder ("yield r = e") names the whole row 'r'; otherwise use
            // the expression's implicit label, falling back to "current".
            let label = binder
                .map(String::from)
                .or_else(|| expr.implicit_label_opt())
                .unwrap_or_else(|| ExprKind::Current.clause().to_string());
            envs.push(label.clone(), Term::Variable(v6));
            field_vars.clear();
            field_vars.push((label, v6));
        }
        envs.push("current".to_string(), Term::Variable(v6));
        let env = envs.build();

        Ok(Triple::new(p.root_env.clone(), env, v6, Some(c6)))
    }

    /// Deduces the type of a `yieldAll` step.
    ///
    /// `yieldAll e` evaluates the collection-valued expression `e` for each
    /// input row and emits each of its elements, flattening the result --
    /// the relational equivalent of flatMap (monadic bind). It is
    /// type-checked here as a first-class step, so that a type error points
    /// at `e` itself and `current` resolves against the element type; it is
    /// lowered to a scan followed by a yield in the resolver. Flatten
    /// semantics: the prior bindings are dropped, and each element of `e`
    /// becomes a row, visible downstream as `current`.
    ///
    /// A binder (`yieldAll r in e`) names each flattened element `r`, a
    /// scan-variable-like name that combines with a following `join`;
    /// otherwise the element is visible only as `current`.
    fn deduce_yield_all_step_type(
        &mut self,
        p: &Triple,
        binder: Option<&str>,
        expr: &Expr,
        span: &Span,
        field_vars: &mut Vec<(String, Var)>,
        steps2: &mut Vec<Step>,
    ) -> Result<Triple, Error> {
        // `e` must evaluate to a list or a bag (of element type `elem`).
        let elem = self.variable();
        let c0 = self.variable();
        let expr2 = self.deduce_expr_type(&*p.env, expr, &c0)?;
        // Added after deducing `e`, so that a non-collection `e` is reported
        // as "conflict: bag(T) vs bool" rather than the other way round.
        self.is_collection_of(&c0, &elem);

        // The output is a list if both the input and `e` are lists, and a
        // bag if either is a bag -- the same rule as a comma-join scan.
        let c = self.unifier.variable();
        let v1 = self.variable();
        let v2 = self.variable();
        self.meet_collections(&p.c.unwrap(), &v1, &c0, &v2, &c, &elem);

        let step =
            StepKind::YieldAll(binder.map(String::from), Box::new(expr2));
        steps2.push(step.spanned(span));

        // The prior row bindings are dropped. A binder ("yieldAll r in e")
        // names each element 'r'; otherwise the element is visible only as
        // "current". Either way `current` is bound to the element type.
        // Build the new environment from the root (outer) env.
        let label = binder.map_or_else(|| "current".to_string(), String::from);
        let mut envs = p.root_env.builder();
        envs.push(label.clone(), Term::Variable(elem));
        envs.push("current".to_string(), Term::Variable(elem));
        let env = envs.build();
        field_vars.clear();
        field_vars.push((label, elem));

        let mut triple = Triple::new(p.root_env.clone(), env, elem, Some(c));
        triple.ordered = p.ordered && self.var_is_list(&c0);
        Ok(triple)
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
        let element_type = p.v;

        // Collect terms for all collections
        let mut terms = vec![Term::Variable(p.c.unwrap())];
        let mut exprs2 = Vec::new();

        // Deduce each argument expression and unify with element type.
        // Each argument may be a list or bag.
        for expr in exprs {
            let c_arg = self.variable();
            let expr2 = self.deduce_expr_type(&*p.root_env, expr, &c_arg)?;
            exprs2.push(expr2);

            terms.push(Term::Variable(c_arg));
        }

        // The result is a list if every input is a list, otherwise a bag;
        // all inputs have the common element type.
        let c_result = self.variable();
        self.meet_all_collections(&terms, &c_result, &element_type);

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
            p.v,
            Some(c_result),
        ))
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
            if let ExprKind::Record(_, labeled_exprs, _) = &key_expr.kind {
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
                if let ExprKind::Record(_, labeled_exprs, _) = &compute.kind {
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
    ///
    /// On the first duplicate, reports the offending label's source
    /// position (the label's span when it is explicit, or the field
    /// expression's span when the label is implicit). A duplicate within
    /// a single record (e.g. `group {a = e.x, a = e.y}`) is reported as
    /// "in record"; a duplicate that straddles the key and the compute
    /// (e.g. `group {sum = e.x} compute sum over e.y`) is reported as
    /// "in group". The within-record duplicate is caught during record
    /// typing and the cross-record duplicate is caught by the
    /// group-level check.
    fn check_duplicate_field_names(
        key_expr: &Expr,
        compute_expr: Option<&Expr>,
    ) -> Result<(), Error> {
        let mut seen: HashSet<String> = HashSet::new();
        Self::check_record_duplicates(key_expr, &mut seen)?;
        if let Some(compute) = compute_expr {
            Self::check_record_duplicates(compute, &mut seen)?;
        }
        Ok(())
    }

    /// Visits each labeled field of `expr` (or the single implicit-label
    /// field if `expr` is not a record). Reports duplicates within the
    /// same record as "in record", and duplicates against the already-seen
    /// set as "in group". The offending span is the label's span when the
    /// label is explicit, or the expression's span when the label is
    /// implicit.
    fn check_record_duplicates(
        expr: &Expr,
        seen: &mut HashSet<String>,
    ) -> Result<(), Error> {
        let mut local: HashSet<String> = HashSet::new();
        let mut visit = |name: String, span: &Span| -> Result<(), Error> {
            if !local.insert(name.clone()) {
                return Err(Error::Compile(
                    format!("duplicate field '{}' in record", name),
                    span.clone(),
                ));
            }
            if !seen.insert(name.clone()) {
                return Err(Error::Compile(
                    format!("duplicate field name '{}' in group", name),
                    span.clone(),
                ));
            }
            Ok(())
        };
        match &expr.kind {
            ExprKind::Record(_, labeled_exprs, _) => {
                for labeled_expr in labeled_exprs {
                    if let Some(label) = labeled_expr.get_label() {
                        visit(label, labeled_expr.label_span())?;
                    }
                }
            }
            _ => {
                if let Some(label) = expr.implicit_label_opt() {
                    visit(label, &expr.span)?;
                }
            }
        }
        Ok(())
    }

    /// Returns the number of fields in an expression.
    /// For records, returns the number of labeled expressions.
    /// For other expressions, returns 1.
    fn field_count(expr: &Expr) -> usize {
        match &expr.kind {
            ExprKind::Record(_, labeled_exprs, _) => labeled_exprs.len(),
            _ => 1,
        }
    }

    /// Returns true if the expression is a singleton record (a record with
    /// exactly one field).
    fn is_singleton_record(expr: Option<&Expr>) -> bool {
        if let Some(expr) = expr
            && let ExprKind::Record(_, labeled_exprs, _) = &expr.kind
            && labeled_exprs.len() == 1
        {
            true
        } else {
            false
        }
    }

    /// Deduces a Group step's type.
    ///
    /// A binder (`group g = {keys} compute {aggs}`) names the whole group row
    /// -- the union of the key and computed fields -- `g`, an atom; only `g`
    /// is exposed downstream.
    fn deduce_group_step_type(
        &mut self,
        p: &Triple,
        binder: Option<&str>,
        key_expr: &Expr,
        compute_expr: Option<&Expr>,
        span: &Span,
        field_vars: &mut Vec<(String, Var)>,
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

        if let ExprKind::Record(_with, labeled_exprs, _) = &key_expr.kind {
            let labeled_exprs2 = self.deduce_record_type(
                &*p.env,
                labeled_exprs,
                field_vars,
                &v_key,
            )?;

            key_expr2 = self.reg_expr(
                &ExprKind::Record(None, labeled_exprs2, vec![]),
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
            group_env_builder.push(label.clone(), Term::Variable(*v));
        });
        group_env_builder.push(
            ExprKind::Elements.clause().to_string(),
            Term::Variable(p.c.unwrap()),
        );
        let group_env = group_env_builder.build();

        // Process the compute expression, if present.
        let compute_expr2 = if let Some(compute) = compute_expr {
            // Push a triple so that `Aggregate`'s `over` expression can resolve
            // the pre-group variables (e.g. `a` in `compute sum over a`) and
            // the group key fields (e.g. `k` in `group {k = i + 2} compute {…
            // over (i + j + k)}`). Its env is the pre-group env extended with
            // the key fields (`field_vars` holds only the key fields here; the
            // compute fields are added afterwards). The compute expressions
            // themselves are evaluated against `group_env` below.
            let mut over_env_builder = p.env.builder();
            field_vars.iter().for_each(|(label, v)| {
                over_env_builder.push(label.clone(), Term::Variable(*v));
            });
            let over_env = over_env_builder.build();
            self.compute_stack.push(p.with_env(&over_env));

            let v_compute = self.variable();
            let result = if let ExprKind::Record(_with, labeled_exprs, _) =
                &compute.kind
            {
                // Multiple compute fields. Sort into BTreeMap order
                // (alphabetical by label) so that evaluation order
                // matches the record type's field order.
                let mut sorted_exprs: Vec<_> = labeled_exprs.iter().collect();
                sorted_exprs.sort_by_key(|le| {
                    le.get_label()
                        .or_else(|| le.expr.implicit_label_opt())
                        .unwrap_or_default()
                });
                let mut labeled_exprs2 = Vec::new();
                let start = field_vars.len();
                for labeled_expr in &sorted_exprs {
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
                        Term::Variable(fv.1),
                    );
                });
                self.record_term(&map, &v_compute);
                let x = ExprKind::Record(None, labeled_exprs2, vec![]);
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
            field_vars[0].1
        } else {
            self.field_var(field_vars, false)
        };

        // A binder ("group g = {..} compute {..}") names the whole group row
        // (keys and computed fields) 'g', an atom; expose only 'g' downstream.
        if let Some(binder) = binder {
            field_vars.clear();
            field_vars.push((binder.to_string(), v_result));
        }

        let c_result = self.variable();

        // Output collection kind matches the input — group on a list
        // produces a list, group on a bag produces a bag. Without
        // this propagation, an enclosing `let ... in from ... group
        // ... end` reads the result type as `list` even when the
        // from is a bag.
        self.same_orderedness(&p.c.unwrap(), &p.v, &c_result, &v_result);

        let step2 = StepKind::Group(
            binder.map(String::from),
            Box::new(key_expr2),
            compute_expr2,
        );
        steps2.push(step2.spanned(span));

        // Build the environment for subsequent steps (e.g. yield). It
        // includes all key fields AND all compute output fields.
        let mut post_group_env_builder = p.root_env.builder();
        field_vars.iter().for_each(|(label, v)| {
            post_group_env_builder.push(label.clone(), Term::Variable(*v));
        });
        // A binder ("group g = ...") makes `current` equal the binder row, so
        // `current.f` and `g.f` are interchangeable in a following step.
        if binder.is_some() {
            post_group_env_builder
                .push("current".to_string(), Term::Variable(v_result));
        }
        let post_group_env = post_group_env_builder.build();

        Ok(Triple::new(
            p.root_env.clone(),
            post_group_env,
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
        field_vars: &mut Vec<(String, Var)>,
        steps2: &mut Vec<Step>,
    ) -> Result<Triple, Error> {
        field_vars.clear();

        // Bind 'elements' to the current collection.
        // Use p.env so that scan variables from preceding steps
        // (e.g. `r` in `from r in elements`) are visible in the
        // 'over' expression.
        let mut compute_env_builder = p.env.builder();
        compute_env_builder.push(
            ExprKind::Elements.clause().to_string(),
            Term::Variable(p.c.unwrap()),
        );
        let compute_env = compute_env_builder.build();
        self.compute_stack.push(p.with_env(&compute_env));

        // Process compute expression
        let mut compute_expr2;
        if let ExprKind::Record(_with, labeled_exprs, _) = &compute_expr.kind {
            // Multiple compute fields. Sort into BTreeMap order
            // (alphabetical by label) so that evaluation order
            // matches the record type's field order.
            let mut sorted_exprs: Vec<_> = labeled_exprs.iter().collect();
            sorted_exprs.sort_by_key(|le| {
                le.get_label()
                    .or_else(|| le.expr.implicit_label_opt())
                    .unwrap_or_default()
            });
            let mut labeled_exprs2 = Vec::new();
            for labeled_expr in &sorted_exprs {
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
                kind: ExprKind::Record(None, labeled_exprs2, vec![]),
                span: compute_expr.span.clone(),
                id: compute_expr.id,
                attributes: Vec::new(),
            };
        } else {
            // Single compute expression - return the value directly.
            let v_compute = self.variable();
            compute_expr2 =
                self.deduce_expr_type(&*compute_env, compute_expr, &v_compute)?;
            field_vars.clear(); // Don't wrap in a record.
            field_vars.push(("compute".to_string(), v_compute));
        }

        self.compute_stack.pop();

        // Compute returns a singleton (not a collection). If it is a single
        // expression, return it directly; if record, use field_var.
        let v_result = if field_vars.len() == 1 && field_vars[0].0 == "compute"
        {
            field_vars[0].1
        } else {
            self.field_var(field_vars, false)
        };

        // Register the compute expression so the resolver can look up
        // its type. For record expressions, the individual fields were
        // registered above but the record wrapper itself was not.
        let id = compute_expr2.id.unwrap_or_else(|| self.next_id());
        compute_expr2.id = Some(id);
        self.node_var_map.insert(id, v_result);

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

        // How the function's parameter links to the input depends on the
        // function's own type.
        // The function is applied to the finished collection in the
        // enclosing scope -- `from ... into f` becomes `f (from ...)` --
        // so it is deduced in `root_env`, not the query's own env. A query
        // variable referenced inside it is then an ordinary unbound
        // variable rather than a read of a leftover row slot.
        let kind = match p.c {
            Some(_) => self.aggregate_collection_kind(&*p.root_env, expr),
            // No input collection; nothing to link to.
            None => CollectionKind::Unknown,
        };
        let c_param = match kind {
            CollectionKind::Unknown => {
                // A user-defined function whose type is not yet available.
                // Link directly to `p.c`, which preserves record-type
                // propagation: without it, a field access in the function's
                // body would be left on an unresolved `'a`.
                if let Some(c_in) = p.c {
                    c_in
                } else {
                    let c_param = self.variable();
                    self.constrain_bag_or_list(&c_param, &p.v);
                    c_param
                }
            }
            CollectionKind::Bag => {
                // A bag-only function: decouple from the input's ordering, so
                // that it also works with a list input.
                let c_param = self.variable();
                self.bag_term(Term::Variable(p.v), &c_param);
                c_param
            }
            CollectionKind::List => {
                // A list-only function: decouple from the input's ordering.
                let c_param = self.variable();
                self.list_term(Term::Variable(p.v), &c_param);
                c_param
            }
            CollectionKind::MatchInput => {
                // Overloaded or polymorphic: link to the input's ordering.
                let c_param = self.variable();
                self.same_orderedness(&c_param, &p.v, &p.c.unwrap(), &p.v);
                c_param
            }
        };
        self.fn_term(&c_param, &v_result, &v_fn);
        let expr2 = self.deduce_expr_type(&*p.root_env, expr, &v_fn)?;

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
        field_vars: &mut Vec<(String, Var)>,
        steps2: &mut Vec<Step>,
    ) -> Result<Triple, Error> {
        let v_element = self.variable();
        let c_result = self.variable();

        // The input collection (p.c) is either a bag of p.v or a list of p.v.
        self.is_collection_of(&p.c.unwrap(), &p.v);

        // Deduce the pattern type.
        let mut term_map = Vec::new();
        let pat2 =
            self.deduce_pat_type(&*p.root_env, pat, &mut term_map, &v_element);

        // The function must have type: current_collection -> result_collection.
        let v_fn = self.variable();
        self.fn_term(&p.c.unwrap(), &c_result, &v_fn);

        // The function is applied to the whole collection, once per
        // execution of the query, so it is deduced in the enclosing scope:
        // `current` and `ordinal` in it read the enclosing row, and are
        // errors at the top level, where there is none.
        let expr2 = self.deduce_expr_type(&*p.root_env, expr, &v_fn)?;

        // The result collection may be a bag or list.
        self.is_collection_of(&c_result, &v_element);

        let step2 = StepKind::Through(Box::new(pat2.clone()), Box::new(expr2));
        steps2.push(step2.spanned(span));

        // A Through replaces the entire collection: only the new
        // pattern's bindings survive. Clear previous field_vars and
        // rebuild the environment from root_env.
        field_vars.clear();
        let mut env_builder = p.root_env.builder();
        for (name, term) in term_map {
            env_builder.push(name.clone(), term.clone());
            let v = self.term_to_variable(&term);
            field_vars.push((name, v));
        }
        env_builder.push("current".to_string(), Term::Variable(v_element));
        let env5 = env_builder.build();

        let v_result = self.field_var(field_vars, true);

        Ok(Triple::new(
            p.root_env.clone(),
            env5,
            v_result,
            Some(c_result),
        ))
    }
    fn field_var(&mut self, field_vars: &[(String, Var)], atom: bool) -> Var {
        if field_vars.is_empty() {
            let v = self.variable();
            *self.primitive_term(&PrimitiveType::Unit, &v)
        } else if field_vars.len() == 1 && atom {
            field_vars[0].1
        } else {
            let mut map: BTreeMap<Label, Term> = BTreeMap::new();
            field_vars.iter().for_each(|fv| {
                map.insert(Label::String(fv.0.clone()), Term::Variable(fv.1));
            });
            let v = self.variable();
            *self.record_term(&map, &v)
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
        arg_variable: &Var,
        result_variable: &Var,
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
        v_result: &Var,
    ) -> Result<(Expr, Expr), Error> {
        // Postfix method-call pattern:
        //   Apply(Apply(RecordSelector(name), recv), arg)
        // If the receiver's type resolves to a non-record for which a
        // postfix method `name` is defined, rewrite the call into a
        // direct application of the built-in and let normal Apply
        // type inference handle it. Receivers that *are* records with
        // a field `name` fall through to the existing RecordSelector
        // handling below.
        if let ExprKind::Apply(inner_fn, recv) = &fun.kind
            && let ExprKind::RecordSelector(method_name) = &inner_fn.kind
            && let Some(result) = self.try_postfix_rewrite(
                env,
                method_name.as_str(),
                recv,
                arg,
                v_result,
            )?
        {
            return Ok(result);
        }

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
        } else if let ExprKind::SafeRecordSelector(name) = &fun.kind {
            // Safe navigation "arg?.field": tunnel through the receiver's
            // functor layers (option, list, bag, vector) to the record,
            // then wrap the field's type in the same layers.
            let span = fun.span.union(&arg.span);
            self.deduce_safe_record_selector_type(name, &span, &v_arg, v_result)
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
        v_fun: &Var,
        _v_arg: &Var,
        _v: &Var,
    ) -> Result<Expr, Error> {
        self.deduce_expr_type(env, fun, v_fun)
    }

    /// Attempts the postfix method-call rewrite.
    /// Called from `deduce_apply_type` when the outer Apply has a
    /// `RecordSelector` in its inner-function slot.
    ///
    /// Deduces the receiver eagerly, reads its resolved constructor
    /// shape from `self.terms`, and if a postfix built-in is defined
    /// for that shape, rewrites the call to `Apply(Literal(Fn), arg')`
    /// and re-runs `deduce_apply_type` on the rewritten form. Returns
    /// `Ok(None)` if the receiver is a genuine record (so the caller
    /// should fall through to ordinary field-projection handling) or
    /// if the shape can't be determined yet.
    fn try_postfix_rewrite(
        &mut self,
        env: &dyn TypeEnv,
        method_name: &str,
        recv: &Expr,
        arg: &Expr,
        v_result: &Var,
    ) -> Result<Option<(Expr, Expr)>, Error> {
        // Deduce the receiver (eagerly — this may recurse if recv is
        // itself a postfix call).
        let v_recv = self.variable();
        let recv2 = self.deduce_expr_type(env, recv, &v_recv)?;

        // Follow `self.terms` to find the constructor shape, if any.
        let recv_term = self.resolve_during_deduce(&v_recv);
        let recv_type_opt = self.shape_to_type(&recv_term);

        // If the receiver is a record with a field of this name,
        // leave the tree alone — it's ordinary field projection.
        if let Some(t) = &recv_type_opt
            && let Type::Record(_, fields) = peel_type(t)
            && fields.keys().any(|k| k.to_string() == method_name)
        {
            return Ok(None);
        }

        // Look up postfix dispatch.
        let Some(recv_type) = recv_type_opt else {
            // Receiver type not yet determinable: fall through.
            return Ok(None);
        };
        let Some((builtin, kind)) = postfix_dispatch(method_name, &recv_type)
        else {
            // Not a built-in. Check whether `method_name` is a
            // user-defined function in scope (e.g. a let-bound
            // `fun name self = …`). If so, rewrite the apply tree
            // to a direct call so normal Apply type inference
            // picks up the function's result type — without this,
            // the outer Apply slot stays as a fresh variable and
            // the runtime resolver later reuses it as the result
            // type, leaving the value typed `'a`.
            if matches!(env.get(method_name, self), Some(BindType::Val(_))) {
                let span = recv.span.union(&arg.span);
                let name_id = Expr {
                    kind: ExprKind::Identifier(method_name.to_string()),
                    span: recv.span.clone(),
                    id: None,
                    attributes: Vec::new(),
                };
                // Calling convention mirrors
                // `resolver::build_user_postfix_call`:
                //   arg = `()`              → name recv
                //   arg = `(a, b, …)` tuple → name (recv, a, b, …)
                //   otherwise                → name (recv, arg)
                let new_arg = match &arg.kind {
                    ExprKind::Literal(l)
                        if matches!(l.kind, LiteralKind::Unit) =>
                    {
                        recv.clone()
                    }
                    ExprKind::Tuple(elts) => {
                        let mut parts = vec![recv.clone()];
                        parts.extend(elts.iter().cloned());
                        Expr {
                            kind: ExprKind::Tuple(parts),
                            span: span.clone(),
                            id: None,
                            attributes: Vec::new(),
                        }
                    }
                    _ => Expr {
                        kind: ExprKind::Tuple(vec![recv.clone(), arg.clone()]),
                        span: span.clone(),
                        id: None,
                        attributes: Vec::new(),
                    },
                };
                let (fun2, arg2) =
                    self.deduce_apply_type(env, &name_id, &new_arg, v_result)?;
                return Ok(Some((fun2, arg2)));
            }
            return Ok(None);
        };

        // Build `Literal(Fn(builtin))` as the new function.
        let span = recv.span.clone();
        let fn_literal = Literal {
            kind: LiteralKind::Fn(builtin),
            span: span.clone(),
        };
        let new_fun = Expr {
            kind: ExprKind::Literal(fn_literal),
            span: span.clone(),
            id: None,
            attributes: Vec::new(),
        };

        // Curried2 nests two Applies: `Apply(Apply(fn, recv), arg)`.
        // Other kinds collapse to a single Apply with a built argument.
        if let PostfixKind::Curried2 = kind {
            let v_inner = self.variable();
            let (fun_inner, arg_inner) =
                self.deduce_apply_type(env, &new_fun, &recv2, &v_inner)?;
            let inner_apply = Expr {
                kind: ExprKind::Apply(Box::new(fun_inner), Box::new(arg_inner)),
                span,
                id: None,
                attributes: Vec::new(),
            };
            let (fun2, arg2) =
                self.deduce_apply_type(env, &inner_apply, arg, v_result)?;
            return Ok(Some((fun2, arg2)));
        }

        // Build the rewritten argument expression.
        let new_arg = self.build_postfix_arg(kind, &recv2, arg)?;

        // Recursively deduce the rewritten Apply. The result must
        // share `v_result` with the outer call so the surrounding
        // context sees the correct type.
        let (fun2, arg2) =
            self.deduce_apply_type(env, &new_fun, &new_arg, v_result)?;
        Ok(Some((fun2, arg2)))
    }

    /// Builds the argument expression for a rewritten postfix call.
    /// Unary methods discard the supplied argument (which should be
    /// `()`); tupled methods splice the receiver in as the first
    /// tuple element.
    fn build_postfix_arg(
        &mut self,
        kind: PostfixKind,
        recv: &Expr,
        arg: &Expr,
    ) -> Result<Expr, Error> {
        let span = recv.span.union(&arg.span);
        Ok(match kind {
            PostfixKind::Unary => recv.clone(),
            PostfixKind::Tupled2 => Expr {
                kind: ExprKind::Tuple(vec![recv.clone(), arg.clone()]),
                span,
                id: None,
                attributes: Vec::new(),
            },
            PostfixKind::Tupled3 => {
                // If the user wrote `r.m (a, b)`, `arg` is already a
                // tuple `(a, b)`; splice recv in. Otherwise treat as
                // a two-element tuple.
                let mut parts = vec![recv.clone()];
                if let ExprKind::Tuple(elts) = &arg.kind {
                    parts.extend(elts.iter().cloned());
                } else {
                    parts.push(arg.clone());
                }
                Expr {
                    kind: ExprKind::Tuple(parts),
                    span,
                    id: None,
                    attributes: Vec::new(),
                }
            }
            PostfixKind::Curried2 | PostfixKind::Curried2Rev => {
                // Curried variants are rewritten as nested Applies in
                // the caller, not via this helper, so these branches
                // are unreachable in practice.
                unreachable!("Curried* handled before build_postfix_arg")
            }
        })
    }

    /// Chases variable chains in `self.terms` (the partial equations
    /// accumulated during deduction) to find a concrete `Sequence`
    /// term for `v`, or returns `None` if the variable is still
    /// unbound or forms a cycle.
    ///
    /// First tries direct chasing through `self.terms`. If that
    /// fails, falls back to running a partial unification on the
    /// accumulated equations so that variables nested inside
    /// Sequences (e.g. the result var of a function-application
    /// equation) can still be resolved.
    fn resolve_during_deduce(&self, v: &Var) -> Option<Term> {
        let mut current = Term::Variable(*v);
        let mut visited: HashSet<i32> = HashSet::new();
        loop {
            match &current {
                Term::Variable(var) => {
                    if !visited.insert(var.id) {
                        break;
                    }
                    let found = self
                        .terms
                        .iter()
                        .rev()
                        .find(|(v0, _)| v0 == var)
                        .map(|(_, t)| t.clone());
                    match found {
                        Some(t) => current = t,
                        None => break,
                    }
                }
                Term::Sequence(_) => return Some(current.clone()),
            }
        }
        // Fallback: run partial unification to resolve variables that
        // only appear inside Sequence terms in self.terms (e.g. the
        // result var of `v_fn = v_arg -> v_result` is bound only via
        // structural unification, not as a direct entry).
        let term_pairs: Vec<(Term, Term)> = self
            .terms
            .iter()
            .map(|(var, term)| (term.clone(), Term::Variable(*var)))
            .collect();
        let subst = self
            .unifier
            .unify(&term_pairs, &NullTracer, self.actions.as_ref())
            .ok()?;
        let resolved = subst.resolve_term(&Term::Variable(*v));
        match resolved {
            Term::Sequence(_) => Some(resolved),
            _ => None,
        }
    }

    /// Converts a resolved `Term::Sequence` to a `Type` shape
    /// suitable for postfix dispatch. Only needs to handle the
    /// primitive and container constructors that postfix_dispatch
    /// keys on; other shapes return `None` (no dispatch).
    fn shape_to_type(&self, term: &Option<Term>) -> Option<Rc<Type>> {
        let term = term.as_ref()?;
        let Term::Sequence(seq) = term else {
            return None;
        };
        let op_name = self.unifier.op_defs[seq.op.0 as usize].name.clone();
        match op_name.as_str() {
            "int" => Some(Rc::new(Type::Primitive(PrimitiveType::Int))),
            "real" => Some(Rc::new(Type::Primitive(PrimitiveType::Real))),
            "char" => Some(Rc::new(Type::Primitive(PrimitiveType::Char))),
            "bool" => Some(Rc::new(Type::Primitive(PrimitiveType::Bool))),
            "string" => Some(Rc::new(Type::Primitive(PrimitiveType::String))),
            "unit" => Some(Rc::new(Type::Primitive(PrimitiveType::Unit))),
            "word" => Some(Rc::new(Type::Primitive(PrimitiveType::Word))),
            COLLECTION_OP_NAME => {
                // A list or bag, according to its orderedness; the element
                // type is unresolved here, but postfix_dispatch only keys on
                // the collection constructor.
                let element = Rc::new(Type::Primitive(PrimitiveType::Unit));
                Some(Rc::new(if self.term_is_ordered(&seq.terms[1]) {
                    Type::List(element)
                } else {
                    Type::Bag(element)
                }))
            }
            s if let Some(arity) = library::builtin_type_arity(s) => {
                // Any other built-in named type (`option`, `range`,
                // `continuous_set`, …): postfix_dispatch only keys
                // on the data-type name, so the element-type slots
                // are filled with placeholders.
                let args = (0..arity)
                    .map(|_| Rc::new(Type::Primitive(PrimitiveType::Unit)))
                    .collect();
                Some(Rc::new(Type::Data(op_name.to_string(), args)))
            }
            _ => None,
        }
    }

    fn deduce_record_selector_type(
        &mut self,
        _env: &dyn TypeEnv,
        field_name: &str,
        span: &Span,
        v_rec: &Var,
        v_field: &Var,
    ) -> Expr {
        // Create a function type: record -> field
        let v_fn = self.variable();
        self.fn_term(v_rec, v_field, &v_fn);

        struct ActionImpl {
            field_name: String,
            v_field: Var,
            errors: Rc<RefCell<Vec<(String, Span)>>>,
            span: Span,
            found: RefCell<bool>,
            typed_values: Rc<RefCell<HashMap<Var, Rc<dyn TypedValue>>>>,
            retry_requested: Rc<RefCell<bool>>,
        }
        impl Action for ActionImpl {
            fn accept(
                &self,
                variable: &Var,
                term: &Term,
                substitution: &Substitution,
                op_defs: &[OpDef],
                term_pairs: &mut Vec<(Term, Term)>,
            ) {
                // This function is called when we know the record type (v_rec).
                // So now we can deduce the type of the field (v_field).
                // If, say, v_rec is "{a: int, b: real}" and field_name = "b"
                // (selector is "#b") we can deduce that v_field is "real".
                //
                // Use the unifier's CURRENT `op_defs` (passed in by the
                // unifier when the action fires), not a snapshot taken at
                // action-creation time. Otherwise, ops registered between
                // creation and fire are absent from the snapshot — and
                // because `Unifier::define_op` calls `Rc::make_mut` on its
                // `Rc<Vec<OpDef>>`, the snapshot is silently split off,
                // so the action would index into a stale vec and panic
                // with "index out of bounds".
                if let Term::Sequence(sequence) = term {
                    if let Some(field_list) =
                        TypeResolver::field_list(op_defs, sequence)
                    {
                        if let Some(i) = field_list
                            .iter()
                            .position(|f| *f == self.field_name)
                        {
                            let result2 = substitution
                                .resolve_term(&Term::Variable(self.v_field));
                            let term = sequence.terms.get(i).unwrap();
                            let term2 = substitution.resolve_term(term);
                            term_pairs.push((result2, term2));
                            *self.found.borrow_mut() = true;
                            // Clear any previous error — a successful
                            // lookup supersedes earlier failures.
                            self.errors
                                .borrow_mut()
                                .retain(|(_, s)| s != &self.span);
                            // Propagate the [`TypedValue`] from the
                            // parent record to the field's variable
                            // so later field-access on this field
                            // can trigger expansion too. (E.g.,
                            // `file.scott` makes `scott` a typed
                            // value, so `file.scott.depts` can
                            // discover `depts`.)
                            self.propagate_typed_value(
                                *variable,
                                self.v_field,
                                substitution,
                            );
                        } else if !*self.found.borrow() {
                            // Field is missing from the record type.
                            // If the record is progressive, try to
                            // widen via the receiver's `TypedValue`
                            // (which triggers a retry) and suppress
                            // the error either way: the
                            // post-resolution widening pass walks
                            // the core decl and can discover the
                            // field via a `valueOf` walk that
                            // reaches Files through record literals,
                            // tuple destructuring, etc. — paths the
                            // unifier-time `TypedValue` map does not
                            // cover.
                            if field_list.iter().any(|f| f == PROGRESSIVE_LABEL)
                            {
                                self.try_discover(*variable, substitution);
                                return;
                            }
                            self.errors.borrow_mut().push((
                                format!(
                                    "no field '{}' in type '{}'",
                                    self.field_name,
                                    TypeResolver::type_name(
                                        op_defs,
                                        sequence,
                                        &field_list,
                                    )
                                ),
                                self.span.clone(),
                            ));
                        }
                    }
                }
            }
        }
        impl ActionImpl {
            /// Tries to widen the receiver's [`TypedValue`] to
            /// include `field_name`. Sets `retry_requested` if the
            /// widening succeeded, so [`TypeResolver::deduce_type`]
            /// re-runs against the now-wider record. Caller has
            /// already verified the record carries
            /// [`PROGRESSIVE_LABEL`].
            fn try_discover(&self, receiver: Var, substitution: &Substitution) {
                let typed_values = self.typed_values.borrow();
                let receiver_root =
                    substitution.resolve_term(&Term::Variable(receiver));
                for (var, tv) in typed_values.iter() {
                    let var_root =
                        substitution.resolve_term(&Term::Variable(*var));
                    if var_root == receiver_root
                        && tv.discover_field(&self.field_name)
                    {
                        *self.retry_requested.borrow_mut() = true;
                        return;
                    }
                }
            }

            /// When a field of a progressive record is successfully
            /// resolved on a receiver that has a [`TypedValue`],
            /// register the corresponding child value under the
            /// field's variable. This lets the resolver discover
            /// fields one level deeper on subsequent accesses. If
            /// the child is `Unexpanded`, expand it and request a
            /// retry — the field's recorded type in the parent
            /// record was built from the still-unexpanded child and
            /// needs to be rebuilt against the expanded child.
            fn propagate_typed_value(
                &self,
                receiver: Var,
                v_field: Var,
                substitution: &Substitution,
            ) {
                use crate::eval::file::{File, FileState};
                let typed_values = self.typed_values.borrow();
                let receiver_root =
                    substitution.resolve_term(&Term::Variable(receiver));
                // Find the receiver's TypedValue.
                let receiver_tv: Option<Rc<dyn TypedValue>> = typed_values
                    .iter()
                    .find(|(var, _)| {
                        substitution.resolve_term(&Term::Variable(**var))
                            == receiver_root
                    })
                    .map(|(_, tv)| Rc::clone(tv));
                drop(typed_values);
                let Some(tv) = receiver_tv else { return };
                // Currently only `File` carries discoverable
                // children; if we add other `TypedValue`
                // implementors we'll need a more general way to
                // project a child value.
                let file = tv.as_any().downcast_ref::<File>();
                let Some(file) = file else { return };
                let child = match &*file.state.borrow() {
                    FileState::Directory { entries } => entries
                        .get(&Label::from(self.field_name.clone()))
                        .cloned(),
                    _ => None,
                };
                if let Some(c) = child {
                    // Expand the child one level so its type widens
                    // from `{...}` to e.g. `{answers:_ list, ...}`
                    // for a directory or `_ list` for a data file.
                    // If expansion changes the child's state, the
                    // recorded field type in the parent is stale —
                    // request a retry so the resolver rebuilds
                    // against the now-widened child.
                    let needed =
                        matches!(*c.state.borrow(), FileState::Unexpanded);
                    if needed {
                        c.expand();
                        *self.retry_requested.borrow_mut() = true;
                    }
                    let v_field_root = match substitution
                        .resolve_term(&Term::Variable(v_field))
                    {
                        Term::Variable(v) => v,
                        _ => v_field,
                    };
                    self.typed_values
                        .borrow_mut()
                        .insert(v_field_root, c as Rc<dyn TypedValue>);
                }
            }
        }
        self.actions.push((
            *v_rec,
            Rc::new(ActionImpl {
                field_name: field_name.to_string(),
                v_field: *v_field,
                errors: self.field_errors.clone(),
                span: span.clone(),
                found: RefCell::new(false),
                typed_values: Rc::clone(&self.typed_values),
                retry_requested: Rc::clone(&self.retry_requested),
            }),
        ));

        // Record for post-unification validation.
        self.field_selectors.push((
            *v_rec,
            field_name.to_string(),
            span.clone(),
        ));

        // Create a record selector expression
        let selector_kind = ExprKind::RecordSelector(field_name.to_string());
        self.reg_expr(&selector_kind, &span, None, &v_fn)
    }

    /// Eagerly tunnels the (already-deduced) receiver type `v_rec` through its
    /// functor layers to a record, looks up `field_name`, and returns the
    /// field's type re-wrapped in those functor layers as a unifier term.
    /// Returns [`SafeTunnel::Defer`] if the receiver type is not yet
    /// determinable (the caller then registers a deferred action), or
    /// [`SafeTunnel::Errored`] after reporting a type error.
    fn tunnel_safe_eager(
        &self,
        field_name: &str,
        v_rec: &Var,
        span: &Span,
    ) -> SafeTunnel {
        // Build a substitution from the constraints gathered so far and use
        // it to *deeply* resolve the receiver type. (We can't use
        // `resolve_during_deduce`, which stops at the first sequence in
        // `self.terms` without resolving its element terms — that leaves the
        // element of an inline `list`/`bag` literal an unresolved variable.)
        let term_pairs: Vec<(Term, Term)> = self
            .terms
            .iter()
            .map(|(var, term)| (term.clone(), Term::Variable(*var)))
            .collect();
        let Ok(subst) = self.unifier.unify(
            term_pairs.as_ref(),
            &NullTracer,
            self.actions.as_ref(),
        ) else {
            return SafeTunnel::Defer;
        };
        let op_defs = Rc::clone(&self.unifier.op_defs);
        // Each tunnelled layer is kept whole, so that its non-element terms
        // (e.g. a collection's orderedness) can be restored when re-wrapping.
        let mut functors: Vec<Sequence> = Vec::new();
        let mut current = subst.resolve_term(&Term::Variable(*v_rec));
        loop {
            let Term::Sequence(seq) = current.clone() else {
                // An unresolved type variable. If we haven't tunnelled
                // through any functor yet, the receiver type isn't known —
                // defer. Otherwise the element can never be a record, so
                // `?.field` is a type error.
                if functors.is_empty() {
                    return SafeTunnel::Defer;
                }
                self.field_errors.borrow_mut().push((
                    format!(
                        "reference to field {field_name} of non-record \
                         type 'a"
                    ),
                    span.clone(),
                ));
                return SafeTunnel::Errored;
            };
            let op_name = op_defs[seq.op.0 as usize].name.as_str();
            if is_safe_nav_functor(op_name) {
                current = subst.resolve_term(&seq.terms[0]);
                functors.push(seq);
                continue;
            }
            if functors.is_empty() {
                self.field_errors.borrow_mut().push((
                    format!(
                        "'?.' applied to non-functor type {op_name} \
                         (expected option, list, bag or vector)"
                    ),
                    span.clone(),
                ));
                return SafeTunnel::Errored;
            }
            let Some(fields) = TypeResolver::field_list(&op_defs, &seq) else {
                // Tunnelled to a leaf type that is not a record/tuple.
                self.field_errors.borrow_mut().push((
                    format!(
                        "reference to field {field_name} of non-record \
                         type {op_name}"
                    ),
                    span.clone(),
                ));
                return SafeTunnel::Errored;
            };
            let Some(i) = fields.iter().position(|f| f == field_name) else {
                let type_name =
                    TypeResolver::type_name(&op_defs, &seq, &fields);
                self.field_errors.borrow_mut().push((
                    format!("no field '{field_name}' in type '{type_name}'"),
                    span.clone(),
                ));
                return SafeTunnel::Errored;
            };
            let mut result = subst.resolve_term(&seq.terms[i]);
            for layer in functors.iter().rev() {
                result = Term::Sequence(rewrap(layer, result));
            }
            return SafeTunnel::Resolved(result);
        }
    }

    /// Deduces the type of a safe-navigation selector `arg?.field`.
    ///
    /// Registers an action on the receiver type `v_rec` that tunnels through
    /// the receiver's functor layers (option, list, bag, vector) down to a
    /// record, looks up `field`, and unifies the result type `v_field` with
    /// the field's type re-wrapped in those same functor layers. For example
    /// a receiver of type `{x:int} option` makes the result `int option`.
    fn deduce_safe_record_selector_type(
        &mut self,
        field_name: &str,
        span: &Span,
        v_rec: &Var,
        v_field: &Var,
    ) -> Expr {
        // Create a function type: receiver -> result
        let v_fn = self.variable();
        self.fn_term(v_rec, v_field, &v_fn);

        // Prefer eager resolution: if the receiver's type is already
        // determinable (it usually is — it was deduced just above), tunnel
        // it now and unify the result directly. This avoids the action's
        // inability to re-fire when an inner functor element resolves later
        // than the receiver (e.g. an inline `[SOME {y=1}, NONE]`).
        match self.tunnel_safe_eager(field_name, v_rec, span) {
            SafeTunnel::Resolved(result) => {
                self.equiv(&result, v_field);
                let selector_kind =
                    ExprKind::SafeRecordSelector(field_name.to_string());
                return self.reg_expr(&selector_kind, span, None, &v_fn);
            }
            SafeTunnel::Errored => {
                let selector_kind =
                    ExprKind::SafeRecordSelector(field_name.to_string());
                return self.reg_expr(&selector_kind, span, None, &v_fn);
            }
            SafeTunnel::Defer => {} // fall through to the deferred action
        }

        struct SafeNavAction {
            field_name: String,
            v_field: Var,
            errors: Rc<RefCell<Vec<(String, Span)>>>,
            span: Span,
        }
        impl Action for SafeNavAction {
            fn accept(
                &self,
                _variable: &Var,
                term: &Term,
                substitution: &Substitution,
                op_defs: &[OpDef],
                term_pairs: &mut Vec<(Term, Term)>,
            ) {
                // This action may fire several times as the receiver type
                // resolves; clear any error from a previous (less resolved)
                // firing so the final state reflects the resolved type.
                self.errors.borrow_mut().retain(|(_, s)| s != &self.span);

                // Tunnel through functor layers (option, list, bag, vector)
                // to the record, collecting the ops so the field's type can
                // be re-wrapped in the same layers.
                let mut functors: Vec<Sequence> = Vec::new();
                let mut current = substitution.resolve_term(term);
                loop {
                    let seq = match &current {
                        Term::Sequence(seq) => seq.clone(),
                        // Not yet a concrete type; defer.
                        _ => return,
                    };
                    let op_name = op_defs[seq.op.0 as usize].name.as_str();
                    if is_safe_nav_functor(op_name) {
                        current = substitution.resolve_term(&seq.terms[0]);
                        functors.push(seq);
                        continue;
                    }
                    if functors.is_empty() {
                        self.errors.borrow_mut().push((
                            "'?.' applied to non-functor type (expected \
                             option, list, bag or vector)"
                                .to_string(),
                            self.span.clone(),
                        ));
                        return;
                    }
                    let Some(field_list) =
                        TypeResolver::field_list(op_defs, &seq)
                    else {
                        self.errors.borrow_mut().push((
                            format!(
                                "reference to field {} of non-record type",
                                self.field_name
                            ),
                            self.span.clone(),
                        ));
                        return;
                    };
                    let Some(i) =
                        field_list.iter().position(|f| *f == self.field_name)
                    else {
                        self.errors.borrow_mut().push((
                            format!("no field '{}' in type", self.field_name),
                            self.span.clone(),
                        ));
                        return;
                    };
                    let field_term = substitution.resolve_term(&seq.terms[i]);
                    let mut result = field_term;
                    for layer in functors.iter().rev() {
                        result = Term::Sequence(rewrap(layer, result));
                    }
                    let vf = substitution
                        .resolve_term(&Term::Variable(self.v_field));
                    term_pairs.push((vf, result));
                    return;
                }
            }
        }

        self.actions.push((
            *v_rec,
            Rc::new(SafeNavAction {
                field_name: field_name.to_string(),
                v_field: *v_field,
                errors: self.field_errors.clone(),
                span: span.clone(),
            }),
        ));

        let selector_kind =
            ExprKind::SafeRecordSelector(field_name.to_string());
        self.reg_expr(&selector_kind, span, None, &v_fn)
    }

    fn deduce_record_type(
        &mut self,
        env: &dyn TypeEnv,
        labeled_expr_list: &Vec<LabeledExpr>,
        field_vars: &mut Vec<(String, Var)>,
        v: &Var,
    ) -> Result<Vec<LabeledExpr>, Error> {
        // First, create a copy of expressions and their labels,
        // sorted into the order that they will appear in the record
        // type.
        let mut label_expr_map: BTreeMap<Label, LabeledExpr> = BTreeMap::new();
        for labeled_expr in labeled_expr_list {
            let label = if let Some(name) = labeled_expr.get_label() {
                Label::from(name)
            } else {
                // No explicit label, and no label derivable from the
                // expression (e.g. `{0 = 0}` — `0` is rejected as a
                // label token, so the whole field becomes the
                // expression `0 = 0`, which has no implicit label).
                return Err(Error::Compile(
                    format!(
                        "cannot derive label for expression {}",
                        labeled_expr.expr.span.code()
                    ),
                    labeled_expr.expr.span.clone(),
                ));
            };
            if label_expr_map.contains_key(&label) {
                return Err(Error::Compile(
                    format!("duplicate field '{}' in record", label),
                    labeled_expr.label_span().clone(),
                ));
            }
            label_expr_map.insert(label, labeled_expr.clone());
        }

        // Second, duplicate the record expression and its labels.
        let mut label_terms: BTreeMap<Label, Term> = BTreeMap::new();
        let mut labeled_expr_list2 = Vec::new();
        for (label, labeled_expr) in &label_expr_map {
            let v2 = self.variable();
            field_vars.push((label.to_string(), v2));

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
        v: &Var,
    ) -> Result<Expr, Error> {
        let fun = ExprKind::Identifier(op.to_string()).spanned(&span);
        let (_fun, arg2) = self.deduce_apply_type(env, &fun, &arg, &v)?;
        Ok(arg2)
    }

    /// Marks the type variable of the given expression as preferring `int`
    /// when unconstrained. Used by overloaded comparison operators whose
    /// result type is `bool` (so the expression's own variable is not the
    /// element type).
    fn prefer_left_int(&mut self, left: &Expr) {
        if let Some(id) = left.id
            && let Some(&v_elem) = self.node_var_map.get(&id)
        {
            self.preferred_vars.push(v_elem);
        }
    }

    fn deduce_call2_type(
        &mut self,
        env: &dyn TypeEnv,
        op: &str,
        left: &Expr,
        right: &Expr,
        v: &Var,
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

    fn deduce_pat_call2_type(
        &mut self,
        env: &dyn TypeEnv,
        op: &str,
        left: &Pat,
        right: &Pat,
        term_map: &mut Vec<(String, Term)>,
        v: &Var,
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
        v_param: &Var,
        v_result: &Var,
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
    pub fn type_to_term(&mut self, type_: &Type) -> Var {
        let v = self.variable();
        // For `Forall` types the `type_term` Forall handler creates fresh
        // unification vars for the bound type variables itself, so we pass an
        // empty substitution and let it do the work.
        //
        // For non-Forall types (e.g. `Type::Fn(List(Var(0)), List(Var(0)))`)
        // we must pre-populate the substitution so that every occurrence of
        // the same TypeVariable id maps to the *same* fresh Var — proper
        // polymorphic instantiation.
        let subst = if matches!(type_, Type::Forall(..)) {
            Subst::Empty
        } else {
            let var_count = Self::max_type_var_count(type_);
            let mut s = Subst::Empty;
            for i in 0..var_count {
                let type_var = TypeVariable::new(i);
                s = s.plus(&type_var, Term::Variable(self.variable()));
            }
            s
        };
        self.type_term(type_, &subst, &v);
        v
    }

    /// Returns the number of distinct type variable IDs found in `type_`
    /// (i.e., one more than the maximum id, or 0 if there are none).
    fn max_type_var_count(type_: &Type) -> usize {
        match type_ {
            Type::Variable(tv) => tv.id + 1,
            Type::Fn(a, b) => {
                Self::max_type_var_count(a).max(Self::max_type_var_count(b))
            }
            Type::List(t) | Type::Bag(t) => Self::max_type_var_count(t),
            Type::Qualified(predicates, t) => predicates
                .iter()
                .map(|p| Self::max_type_var_count(&p.type_))
                .chain(once(Self::max_type_var_count(t)))
                .max()
                .unwrap_or(0),
            Type::Tuple(ts) | Type::Data(_, ts) | Type::Named(ts, _) => ts
                .iter()
                .map(|t| Self::max_type_var_count(t))
                .max()
                .unwrap_or(0),
            Type::Record(_, fields) => fields
                .values()
                .map(|t| Self::max_type_var_count(t))
                .max()
                .unwrap_or(0),
            Type::Alias(_, inner, args) => {
                let inner_count = Self::max_type_var_count(inner);
                let args_count = args
                    .iter()
                    .map(|t| Self::max_type_var_count(t))
                    .max()
                    .unwrap_or(0);
                inner_count.max(args_count)
            }
            Type::Forall(inner, _) => Self::max_type_var_count(inner),
            Type::Primitive(_) => 0,
        }
    }

    /// Creates a term for a primitive type and associates it with a variable.
    fn primitive_term<'a>(
        &mut self,
        prim_type: &PrimitiveType,
        v: &'a Var,
    ) -> &'a Var {
        let moniker = prim_type.as_str();
        let op = self.unifier.op(moniker, Some(0));
        let sequence = self.unifier.atom(op);
        self.equiv(&Term::Sequence(sequence), v)
    }

    /// Creates a term for a function type and associates it with a variable.
    fn fn_term<'a>(
        &mut self,
        param_type: &Var,
        result_type: &Var,
        v: &'a Var,
    ) -> &'a Var {
        let sequence = self.unifier.apply2(
            self.fn_op,
            Term::Variable(*param_type),
            Term::Variable(*result_type),
        );
        self.equiv(&Term::Sequence(sequence), v)
    }

    /// Creates a collection term, `$collection(elem, orderedness)`.
    fn collection_term(&mut self, elem: Term, orderedness: Term) -> Sequence {
        self.unifier.apply2(self.collection_op, elem, orderedness)
    }

    /// Returns the atom that denotes an ordered collection (a list).
    fn ordered_atom(&self) -> Term {
        Term::Sequence(self.unifier.atom(self.ordered_op))
    }

    /// Returns the atom that denotes an unordered collection (a bag).
    fn unordered_atom(&self) -> Term {
        Term::Sequence(self.unifier.atom(self.unordered_op))
    }

    /// Creates a term for a list type and associates it with a variable.
    fn list_term<'a>(&mut self, term: Term, v: &'a Var) -> &'a Var {
        let ordered = self.ordered_atom();
        let sequence = self.collection_term(term, ordered);
        self.equiv(&Term::Sequence(sequence), v)
    }

    /// Creates a term for a bag type and associates it with a variable.
    fn bag_term<'a>(&mut self, term: Term, v: &'a Var) -> &'a Var {
        let unordered = self.unordered_atom();
        let sequence = self.collection_term(term, unordered);
        self.equiv(&Term::Sequence(sequence), v)
    }

    /// Adds a constraint that `c` is a collection of `v`. The orderedness is
    /// left to be determined; if nothing else constrains it, the collection
    /// defaults to a bag when the type is read back.
    ///
    /// This corresponds to Java's `isCollectionOf(c, v)`.
    fn is_collection_of(&mut self, c: &Var, v: &Var) {
        let o = self.variable();
        let sequence =
            self.collection_term(Term::Variable(*v), Term::Variable(o));
        self.equiv(&Term::Sequence(sequence), c);
    }

    /// Adds a constraint that `c1` and `c2` are collections (of `v1` and
    /// `v2`) with the same orderedness.
    ///
    /// With the unified representation the element/orderedness relationship
    /// is intrinsic to the collection term, so this is plain unification on a
    /// shared orderedness variable rather than a deferred list/bag
    /// disjunction.
    ///
    /// This corresponds to Java's `sameOrderedness(c1, v1, c2, v2)`.
    fn same_orderedness(&mut self, c1: &Var, v1: &Var, c2: &Var, v2: &Var) {
        let o = self.variable();
        let seq1 = self.collection_term(Term::Variable(*v1), Term::Variable(o));
        self.equiv(&Term::Sequence(seq1), c1);
        let seq2 = self.collection_term(Term::Variable(*v2), Term::Variable(o));
        self.equiv(&Term::Sequence(seq2), c2);
    }

    /// Adds a constraint that `c` (of `v`) is the meet of collections `c0`
    /// (of `v0`) and `c1` (of `v1`): a list if both inputs are lists,
    /// otherwise a bag.
    ///
    /// This corresponds to Java's `meetCollections(c0, v0, c1, v1, c, v)`.
    fn meet_collections(
        &mut self,
        c0: &Var,
        v0: &Var,
        c1: &Var,
        v1: &Var,
        c: &Var,
        v: &Var,
    ) {
        // Each of c0, c1, c is a collection; the result orderedness is the
        // meet of the two input orderednesses (a list only if both inputs are
        // lists, otherwise a bag).
        let o0 = self.variable();
        let o1 = self.variable();
        let o = self.variable();
        let seq0 =
            self.collection_term(Term::Variable(*v0), Term::Variable(o0));
        self.equiv(&Term::Sequence(seq0), c0);
        let seq1 =
            self.collection_term(Term::Variable(*v1), Term::Variable(o1));
        self.equiv(&Term::Sequence(seq1), c1);
        let seq = self.collection_term(Term::Variable(*v), Term::Variable(o));
        self.equiv(&Term::Sequence(seq), c);
        self.meet_orderedness(&o, &o0, &o1);
    }

    /// Adds a constraint that orderedness `o` is the meet of `o0` and `o1`:
    /// ordered if both are ordered, otherwise unordered.
    fn meet_orderedness(&mut self, o: &Var, o0: &Var, o1: &Var) {
        let ordered = self.ordered_atom();
        let unordered = self.unordered_atom();
        let ordered_action =
            ConstraintAction::Equiv(Term::Variable(*o), ordered.clone());
        let unordered_action =
            ConstraintAction::Equiv(Term::Variable(*o), unordered.clone());
        let pair = |resolver: &Self, left: &Term, right: &Term| {
            Term::Sequence(resolver.unifier.apply2(
                resolver.arg_op,
                left.clone(),
                right.clone(),
            ))
        };
        let candidates = vec![
            pair(self, &ordered, &ordered),
            pair(self, &ordered, &unordered),
            pair(self, &unordered, &ordered),
            pair(self, &unordered, &unordered),
        ];
        let actions = vec![
            ordered_action,
            unordered_action.clone(),
            unordered_action.clone(),
            unordered_action,
        ];
        let arg = pair(self, &Term::Variable(*o0), &Term::Variable(*o1));
        let arg_var = self.term_to_variable(&arg);
        self.overload_constraints
            .push(Constraint::with_actions(arg_var, candidates, actions));
    }

    /// Adds a constraint that `c` (of `v`) is the meet of the collections in
    /// `args`: a list if all inputs are lists, otherwise a bag.
    ///
    /// This corresponds to Java's `meetCollections(args, c, v)`.
    fn meet_all_collections(&mut self, args: &[Term], c: &Var, v: &Var) {
        assert!(!args.is_empty(), "no args");
        let arg0 = self.term_to_variable(&args[0]);
        self.is_collection_of(&arg0, v);
        self.is_collection_of(c, v);
        for arg in &args[1..] {
            let vi = self.term_to_variable(arg);
            self.is_collection_of(&vi, v);
            self.meet_collections(&arg0, v, &vi, v, c, v);
        }
    }

    /// Returns whether variable `c` already resolves to a concrete collection
    /// given the constraints gathered so far.
    /// Builds a substitution from `self.terms` (as `tunnel_safe_eager` does)
    /// and resolves `c`; a non-collection or still-unresolved variable yields
    /// `false`. Used by `into` to tell a function whose type pins the
    /// collection kind (`into sum` → `bag`) from a kind-agnostic one
    /// (`into process`).
    fn resolves_to_collection(&self, c: &Var) -> bool {
        let term_pairs: Vec<(Term, Term)> = self
            .terms
            .iter()
            .map(|(var, term)| (term.clone(), Term::Variable(*var)))
            .collect();
        let Ok(subst) = self.unifier.unify(
            term_pairs.as_ref(),
            &NullTracer,
            self.actions.as_ref(),
        ) else {
            return false;
        };
        match subst.resolve_term(&Term::Variable(*c)) {
            Term::Sequence(seq) => seq.op == self.collection_op,
            _ => false,
        }
    }

    /// Adds an overload constraint that `c` must be a list or a bag of
    /// element type `v`. Unlike [`is_collection_of`](Self::is_collection_of)
    /// -- which lets the orderedness stay a free variable -- this fails type
    /// resolution with "no valid overloads" when `c` resolves to a
    /// non-collection, and selects the list-or-bag kind once `c` is known.
    fn constrain_bag_or_list(&mut self, c: &Var, v: &Var) {
        let elem = Term::Variable(*v);
        let ordered = self.ordered_atom();
        let unordered = self.unordered_atom();
        let list_seq = self.collection_term(elem.clone(), ordered);
        let bag_seq = self.collection_term(elem, unordered);
        self.overload_constraints.push(Constraint::new(
            *c,
            vec![Term::Sequence(list_seq), Term::Sequence(bag_seq)],
        ));
    }

    /// Returns whether `term` is the orderedness atom of a list, following
    /// variable links to a concrete atom if necessary. Returns `None` if the
    /// orderedness is still a free variable.
    fn orderedness_of(&self, term: &Term) -> Option<bool> {
        match term {
            Term::Sequence(seq) if seq.op == self.ordered_op => Some(true),
            Term::Sequence(seq) if seq.op == self.unordered_op => Some(false),
            Term::Sequence(_) => None,
            Term::Variable(v) => {
                for (var, t) in self.terms.iter().rev() {
                    if var == v {
                        return self.orderedness_of(t);
                    }
                }
                None
            }
        }
    }

    /// As [`orderedness_of`](Self::orderedness_of), but an orderedness that
    /// is not yet determined reads back as a bag, so it yields `false`.
    fn term_is_ordered(&self, term: &Term) -> bool {
        self.orderedness_of(term).unwrap_or(false)
    }

    /// Inspects the aggregate function's declared type to determine
    /// its collection kind:
    /// - Identifier with list param → List
    /// - Identifier with bag param → Bag
    /// - Overloaded identifier → MatchInput
    /// - Anonymous (lambda) → Unknown
    fn aggregate_collection_kind(
        &mut self,
        env: &dyn TypeEnv,
        f: &Expr,
    ) -> CollectionKind {
        if let ExprKind::Identifier(name) = &f.kind {
            // An overloaded name is polymorphic.
            if self.overloads.contains_key(name) {
                return CollectionKind::MatchInput;
            }
            // Look up the function type in the environment.
            return match env.get(name, self) {
                Some(BindType::Val(t) | BindType::Constructor(t)) => {
                    self.agg_kind_of_term(&t)
                }
                // Type not available (a user-defined function in the current
                // compilation unit).
                None => CollectionKind::Unknown,
            };
        }
        // For qualified names (e.g. `Relational.nonEmpty`, `Fn.id`), extract
        // the member's type from the structure.
        if let ExprKind::Apply(fun, arg) = &f.kind
            && let ExprKind::RecordSelector(field_name) = &fun.kind
            && let ExprKind::Identifier(struct_name) = &arg.kind
            && let Some(BindType::Val(t) | BindType::Constructor(t)) =
                env.get(struct_name, self)
            && let Term::Sequence(seq) = self.resolve_var_term(&t)
            && let Some(fields) =
                TypeResolver::field_list(&self.unifier.op_defs, &seq)
            && let Some(i) = fields.iter().position(|f| f == field_name)
        {
            return self.agg_kind_of_term(&seq.terms[i]);
        }
        // An anonymous function, or any other expression: link to the input's
        // orderedness.
        CollectionKind::MatchInput
    }

    /// Resolves `term` by following variable links in the equations gathered
    /// so far.
    fn resolve_var_term(&self, term: &Term) -> Term {
        let mut current = term.clone();
        let mut visited = HashSet::new();
        while let Term::Variable(v) = &current {
            if !visited.insert(*v) {
                break;
            }
            let mut next = None;
            for (var, t) in self.terms.iter().rev() {
                if var == v {
                    next = Some(t.clone());
                    break;
                }
            }
            match next {
                Some(t) => current = t,
                None => break,
            }
        }
        current
    }

    /// Returns the collection kind implied by the type term of an aggregate
    /// function: a collection parameter fixes the kind, anything else is
    /// polymorphic.
    ///
    /// This corresponds to Java's `aggKindOfType`.
    fn agg_kind_of_term(&self, term: &Term) -> CollectionKind {
        let Term::Sequence(seq) = self.resolve_var_term(term) else {
            return CollectionKind::MatchInput;
        };
        if seq.op != self.fn_op || seq.terms.len() != 2 {
            return CollectionKind::MatchInput;
        }
        match self.resolve_var_term(&seq.terms[0]) {
            Term::Sequence(param) if param.op == self.collection_op => {
                if self.term_is_ordered(&param.terms[1]) {
                    CollectionKind::List
                } else {
                    CollectionKind::Bag
                }
            }
            _ => CollectionKind::MatchInput,
        }
    }

    /// Returns whether collection variable `v` is known to be ordered (a
    /// list) or unordered (a bag), or `None` if neither has been established.
    ///
    /// A variable typically has several equations: the `$collection(v0, o)`
    /// that [`is_collection_of`](Self::is_collection_of) adds, whose
    /// orderedness is still free, plus whatever its source contributed. So
    /// keep looking until an equation gives a concrete answer.
    fn var_orderedness(
        &self,
        v: &Var,
        visited: &mut HashSet<Var>,
    ) -> Option<bool> {
        if !visited.insert(*v) {
            return None;
        }
        for (var, term) in self.terms.iter().rev() {
            if var == v {
                match term {
                    Term::Sequence(seq) if seq.op == self.collection_op => {
                        if let Some(ordered) =
                            self.orderedness_of(&seq.terms[1])
                        {
                            return Some(ordered);
                        }
                    }
                    // A concrete term that is not a collection.
                    Term::Sequence(_) => return Some(false),
                    // Variable mapped to another variable; follow the chain.
                    Term::Variable(v2) => {
                        if let Some(ordered) = self.var_orderedness(v2, visited)
                        {
                            return Some(ordered);
                        }
                    }
                }
            }
        }
        None
    }

    /// Returns whether collection variable `v` is a list. An orderedness that
    /// has not been established is treated as unordered, so that `ordinal` is
    /// rejected rather than silently allowed.
    fn var_is_list(&self, v: &Var) -> bool {
        self.var_orderedness(v, &mut HashSet::new())
            .unwrap_or(false)
    }

    /// Creates a term for a record type and associates it with a variable.
    fn record_term<'a>(
        &mut self,
        label_types: &BTreeMap<Label, Term>,
        v: &'a Var,
    ) -> &'a Var {
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

    fn tuple_term<'a>(&mut self, types: &[Term], v: &'a Var) -> &'a Var {
        if types.is_empty() {
            self.primitive_term(&PrimitiveType::Unit, v)
        } else {
            let sequence = self.unifier.apply(self.tuple_op, types);
            self.equiv(&Term::Sequence(sequence), v)
        }
    }

    /// Returns a substitution that maps each type variable in `type_` to a
    /// fresh unifier variable, so that a stored (closed) type can be
    /// instantiated with variables that do not clash with any others.
    fn fresh_subst(&mut self, type_: &Type) -> Subst {
        let mut ids = Vec::new();
        Self::collect_type_var_ids(type_, &mut ids);
        let mut subst = Subst::Empty;
        for id in ids {
            let v = self.variable();
            subst = subst.plus(&TypeVariable::new(id), Term::Variable(v));
        }
        subst
    }

    /// Collects the ordinals of the type variables that occur in a type.
    fn collect_type_var_ids(type_: &Type, ids: &mut Vec<usize>) {
        match type_ {
            Type::Variable(tv) => {
                if !ids.contains(&tv.id) {
                    ids.push(tv.id);
                }
            }
            Type::Fn(a, b) => {
                Self::collect_type_var_ids(a, ids);
                Self::collect_type_var_ids(b, ids);
            }
            Type::Alias(_, t, args) => {
                Self::collect_type_var_ids(t, ids);
                args.iter().for_each(|a| Self::collect_type_var_ids(a, ids));
            }
            Type::List(t) | Type::Bag(t) | Type::Forall(t, _) => {
                Self::collect_type_var_ids(t, ids);
            }
            Type::Tuple(ts) | Type::Data(_, ts) | Type::Named(ts, _) => {
                ts.iter().for_each(|t| Self::collect_type_var_ids(t, ids));
            }
            Type::Record(_, fields) => {
                fields
                    .values()
                    .for_each(|t| Self::collect_type_var_ids(t, ids));
            }
            Type::Qualified(predicates, t) => {
                predicates
                    .iter()
                    .for_each(|p| Self::collect_type_var_ids(&p.type_, ids));
                Self::collect_type_var_ids(t, ids);
            }
            Type::Primitive(_) => {}
        }
    }

    pub(crate) fn type_term(&mut self, type_: &Type, subst: &Subst, v: &Var) {
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
            Type::Qualified(predicates, type_) => {
                // Instantiating a qualified type: re-create each predicate's
                // overload constraint (with fresh variables for each candidate
                // instance), so that it is resolved or re-deferred at this use
                // site. The predicate's own variables are shared with the body
                // via `subst`.
                for predicate in predicates {
                    let v_pred = self.variable();
                    self.type_term(&predicate.type_, subst, &v_pred);
                    let candidates = predicate
                        .candidates
                        .iter()
                        .map(|candidate| {
                            let subst2 = self.fresh_subst(candidate);
                            let v_cand = self.variable();
                            self.type_term(candidate, &subst2, &v_cand);
                            Term::Variable(v_cand)
                        })
                        .collect();
                    self.overload_constraints.push(Constraint::named(
                        v_pred,
                        candidates,
                        &predicate.name,
                    ));
                }
                self.type_term(type_, subst, v);
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
    fn field_list(
        op_defs: &[OpDef],
        sequence: &Sequence,
    ) -> Option<Vec<String>> {
        let op_name = &op_defs[sequence.op.0 as usize].name;
        match op_name.as_str() {
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
    pub(crate) fn variable(&mut self) -> Var {
        self.unifier.variable()
    }

    /// Converts a term to a variable.
    fn term_to_variable(&mut self, term: &Term) -> Var {
        match term {
            Term::Variable(v) => *v,
            Term::Sequence(_) => {
                let v = self.variable();
                *self.equiv(&term, &v)
            }
        }
    }

    /// Converts a variable to a sequence.
    /// Returns a pattern that destructures a record into its fields, so
    /// that a modifier's expressions can refer to them by name. A label
    /// that is not identifier-shaped -- a tuple's `1`, `2` -- cannot be
    /// a variable name and could not be written in a modifier's
    /// expression anyway, so it is left to the ellipsis; the desugaring
    /// reaches those fields with a selector instead.
    fn fields_pat_of(span: &Span, fields: &[String]) -> Pat {
        PatKind::Record(
            fields
                .iter()
                .filter(|f| is_name(f))
                .map(|f| {
                    PatField::Labeled(
                        span.clone(),
                        f.clone(),
                        PatKind::Identifier(f.clone()).spanned(span),
                    )
                })
                .collect(),
            true,
        )
        .spanned(span)
    }

    /// Turns a record's modifiers into nested `let`s. Each modifier
    /// becomes
    ///
    /// ```text
    /// let val {f1, f2, ...} = <previous> in {<new fields>} end
    /// ```
    ///
    /// so that the modifier's expressions see the fields of the record
    /// the previous modifier produced -- `{r replace sal = sal * 12.0}`
    /// multiplies the old `sal` -- and the record it builds says which
    /// fields survive. Mirrors morel-java's `desugarModifiers`.
    fn desugar_modifiers(
        &mut self,
        env: &dyn TypeEnv,
        record: &Expr,
        base: &Expr,
        modifiers: &[Modifier],
    ) -> Result<Option<Expr>, Error> {
        let span = &record.span;
        let mut exp = base.clone();
        let Some(mut fields) = self.record_field_names(env, base)? else {
            return Ok(None);
        };
        for modifier in modifiers {
            let rec_name = free_name(&fields, "$rec");
            // Two declarations, not one binding of each: the second
            // reads the first, and bindings within one `val` are
            // parallel.
            let mut decls = vec![
                DeclKind::Val(
                    false,
                    false,
                    vec![ValBind::of(
                        &PatKind::Identifier(rec_name.clone()).spanned(span),
                        None,
                        &exp,
                    )],
                )
                .spanned(span),
            ];
            let mut val_binds = vec![ValBind::of(
                &Self::fields_pat_of(span, &fields),
                None,
                &id(span, &rec_name),
            )];
            let args: Vec<(String, Expr)> = match modifier {
                Modifier::Assign(verb, lenient, assignments) => assign_fields(
                    span,
                    &rec_name,
                    *verb,
                    *lenient,
                    assignments,
                    &fields,
                )?,
                Modifier::All(verb, lenient, all_expr) => {
                    let Some(all_fields) =
                        self.record_field_names(env, all_expr)?
                    else {
                        return Ok(None);
                    };
                    let name = free_name(&fields, "$all");
                    val_binds.push(ValBind::of(
                        &PatKind::Identifier(name.clone()).spanned(span),
                        None,
                        all_expr,
                    ));
                    assign_all_fields(
                        span,
                        &rec_name,
                        &all_expr.span,
                        *verb,
                        *lenient,
                        &fields,
                        &all_fields,
                        &name,
                    )?
                }
                Modifier::Remove(verb, labels) => {
                    remove_fields(span, &rec_name, *verb, labels, &fields)?
                }
                Modifier::Rename(args) => {
                    rename_fields(span, &rec_name, args, &fields)?
                }
            };
            fields = args.iter().map(|(f, _)| f.clone()).collect();
            fields.sort();
            let body = ExprKind::Record(
                None,
                args.into_iter()
                    .map(|(label, e)| {
                        LabeledExpr::new(Some(AstLabel::new(&label, span)), &e)
                    })
                    .collect(),
                vec![],
            )
            .spanned(span);
            decls.push(DeclKind::Val(false, false, val_binds).spanned(span));
            exp = ExprKind::Let(decls, Box::new(body)).spanned(span);
        }
        Ok(Some(exp))
    }

    /// Returns the field names of a record-valued expression, in label
    /// order, or `None` if they are not known yet.
    ///
    /// A previous attempt may have learned them; otherwise deducing the
    /// expression and resolving the constraints so far may settle them.
    /// When neither does -- because only a use further down the
    /// declaration will settle the type -- an action records them when
    /// unification gets there, and asks for another attempt, which
    /// finds them in the cache. Mirrors morel-java's
    /// `modifierFieldNames`.
    fn record_field_names(
        &mut self,
        env: &dyn TypeEnv,
        expr: &Expr,
    ) -> Result<Option<Vec<String>>, Error> {
        let key = expr.span.extent();
        if let Some(names) = self.modifier_fields.borrow().get(&key) {
            return Ok(Some(names.clone()));
        }
        let v = self.variable();
        self.deduce_expr_type(env, expr, &v)?;
        let names =
            self.resolve_during_deduce(&v).and_then(|term| match term {
                Term::Sequence(seq) => self.term_field_names(&seq),
                Term::Variable(_) => None,
            });
        if let Some(names) = names {
            self.modifier_fields.borrow_mut().insert(key, names.clone());
            Ok(Some(names))
        } else {
            self.remember_fields_when_known(v, key);
            Ok(None)
        }
    }

    /// The field names of a record or tuple term. `unit` is the record
    /// with no fields, so its names are the empty list, not `None`;
    /// otherwise `{{} extend i = 1}` would never desugar.
    fn term_field_names(&self, seq: &Sequence) -> Option<Vec<String>> {
        if self.unifier.op_defs[seq.op.0 as usize].name == "unit" {
            return Some(Vec::new());
        }
        Self::field_list(&self.unifier.op_defs, seq)
    }

    /// Registers an action so that when `v` resolves to a record type,
    /// the field names of the expression spanning `key` are remembered
    /// and another attempt is asked for.
    fn remember_fields_when_known(&mut self, v: Var, key: (usize, usize)) {
        struct RememberFields {
            key: (usize, usize),
            fields: ModifierFields,
            retry_requested: Rc<RefCell<bool>>,
        }
        impl Action for RememberFields {
            fn accept(
                &self,
                _variable: &Var,
                term: &Term,
                _substitution: &Substitution,
                op_defs: &[OpDef],
                _term_pairs: &mut Vec<(Term, Term)>,
            ) {
                let Term::Sequence(seq) = term else {
                    return;
                };
                let names = if op_defs[seq.op.0 as usize].name == "unit" {
                    Some(Vec::new())
                } else {
                    TypeResolver::field_list(op_defs, seq)
                };
                if let Some(names) = names
                    && self
                        .fields
                        .borrow_mut()
                        .insert(self.key, names)
                        .is_none()
                {
                    // Each attempt learns at least one more, so the
                    // retry loop terminates.
                    *self.retry_requested.borrow_mut() = true;
                }
            }
        }
        self.actions.push((
            v,
            Rc::new(RememberFields {
                key,
                fields: Rc::clone(&self.modifier_fields),
                retry_requested: Rc::clone(&self.retry_requested),
            }),
        ));
    }

    fn variable_to_sequence(&self, v: &Var) -> Option<Sequence> {
        // Search terms in reverse for the most recently added term for v.
        for (var, term) in self.terms.iter().rev() {
            if var == v {
                if let Term::Sequence(seq) = term {
                    return Some(seq.clone());
                }
            }
        }
        None
    }

    /// Given a record sequence and a field label, returns the unifier variable
    /// associated with that field, or None if it cannot be determined.
    fn field_var_of(&self, seq: &Sequence, label: &str) -> Option<Var> {
        let fields = Self::field_list(&self.unifier.op_defs, seq)?;
        let pos = fields.iter().position(|f| f == label)?;
        match &seq.terms[pos] {
            Term::Variable(v) => Some(*v),
            _ => None,
        }
    }

    /// Declares that a term is equivalent to a variable.
    /// Creates an association between a term and a variable,
    /// declaring that they are equivalent.
    fn equiv<'a>(&mut self, term: &Term, v: &'a Var) -> &'a Var {
        self.terms.push((*v, term.clone()));
        &v
    }

    /// Registers a term for an AST node for an expression.
    fn reg_expr(
        &mut self,
        kind: &ExprKind<Expr>,
        span: &Span,
        id: Option<i32>,
        v: &Var,
    ) -> Expr {
        let id2 = id.unwrap_or_else(|| self.next_id());
        self.node_var_map.insert(id2, *v);
        Expr {
            kind: kind.clone(),
            span: span.clone(),
            id: Some(id2),
            attributes: Vec::new(),
        }
    }

    /// Registers a term for an AST node for a pattern.
    fn reg_pat(
        &mut self,
        kind: &PatKind,
        span: &Span,
        id: Option<i32>,
        v: &Var,
    ) -> Pat {
        let id2 = id.unwrap_or_else(|| self.next_id());
        self.node_var_map.insert(id2, *v);
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
    fn reg_type(&mut self, kind: &TypeKind, span: &Span, v: &Var) -> AstType {
        AstType {
            kind: kind.clone(),
            span: span.clone(),
            id: Some(v.id),
            attributes: Vec::new(),
        }
    }

    fn deduce_val_bind_type(
        &mut self,
        env: &dyn TypeEnv,
        val_bind: &ValBind,
        term_map: &mut Vec<(String, Term)>,
        v: &Var,
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
            LiteralKind::Word(_) => PrimitiveType::Word,
        }
    }

    fn deduce_pat_type(
        &mut self,
        env: &dyn TypeEnv,
        pat: &Pat,
        term_map: &mut Vec<(String, Term)>,
        v: &Var,
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
                    Some(BindType::Constructor(term))
                    | Some(BindType::Val(term)) => term,
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
                // "true"/"false" parse as identifiers (id_pat fires before
                // literal_pat).  Rewrite to a bool literal pattern so that
                // pattern matching at runtime distinguishes the two values.
                if name == "true" || name == "false" {
                    let lit_kind = LiteralKind::Bool(name == "true");
                    let kind = PatKind::Literal(lit_kind.spanned(&pat.span()));
                    let pat2 = Box::new(kind.spanned(&pat.span()));
                    return self.deduce_pat_type(env, &pat2, term_map, v);
                }
                if let Some(BindType::Constructor(_)) = env.get(name, self) {
                    // The identifier is a constructor, such as `SOME` or `nil`.
                    let kind = PatKind::Constructor(name.clone(), None);
                    let pat2 = Box::new(kind.spanned(&pat.span()));
                    return self.deduce_pat_type(env, &pat2, term_map, v);
                }
                term_map.push((name.clone(), Term::Variable(*v)));
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
                // Reject a character constant that is not exactly one
                // character (e.g. `#"ab"`). Recorded rather than returned
                // because `deduce_pat_type` cannot fail; caught at the end of
                // `deduce`, before the pattern is resolved.
                if let Some(msg) = char_literal_error(&literal.kind) {
                    self.field_errors
                        .borrow_mut()
                        .push((msg, pat.span.clone()));
                }
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
                    };
                }
                if *ellipsis {
                    // Open record pattern: v may have more fields than
                    // named here. Register a single Action on v that,
                    // once v's full record type is known, unifies each
                    // named field's variable with the actual field type
                    // from v. Multiple actions per variable are not
                    // supported (HashMap), so we collect all named
                    // fields into one combined action.
                    let pattern_fields: Vec<(String, Var)> = map
                        .iter()
                        .filter_map(|(label, term)| {
                            if let (Label::String(name), Term::Variable(vf)) =
                                (label, term)
                            {
                                Some((name.clone(), *vf))
                            } else {
                                None
                            }
                        })
                        .collect();
                    struct OpenRecordAction {
                        pattern_fields: Vec<(String, Var)>,
                    }
                    impl Action for OpenRecordAction {
                        fn accept(
                            &self,
                            _variable: &Var,
                            term: &Term,
                            substitution: &Substitution,
                            op_defs: &[OpDef],
                            term_pairs: &mut Vec<(Term, Term)>,
                        ) {
                            // The unifier's own table, not a snapshot
                            // taken when the action was registered: an
                            // op created in between would not be in it,
                            // and looking the sequence's op up would run
                            // off the end.
                            if let Term::Sequence(seq) = term
                                && let Some(field_list) =
                                    TypeResolver::field_list(op_defs, seq)
                            {
                                for (field_name, v_field) in
                                    &self.pattern_fields
                                {
                                    if let Some(i) = field_list
                                        .iter()
                                        .position(|f| f == field_name)
                                    {
                                        let v_field_term = substitution
                                            .resolve_term(&Term::Variable(
                                                *v_field,
                                            ));
                                        let field_term = substitution
                                            .resolve_term(
                                                seq.terms.get(i).unwrap(),
                                            );
                                        term_pairs
                                            .push((v_field_term, field_term));
                                    }
                                }
                            }
                        }
                    }
                    self.actions.push((
                        *v,
                        Rc::new(OpenRecordAction { pattern_fields }),
                    ));
                } else {
                    self.record_term(&map, &v);
                }
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
            PatKind::As(name, inner_pat) => {
                // 'p as inner_pat' binds 'p' and 'inner_pat' to the same
                // value, hence the same type. Recurse into the inner
                // pattern with the same type variable, then add a
                // term-map entry for the outer name.
                let pat2 = self.deduce_pat_type(env, inner_pat, term_map, &v);
                term_map.push((name.clone(), Term::Variable(*v)));
                self.reg_pat(
                    &PatKind::As(name.clone(), Box::new(pat2)),
                    &pat.span,
                    pat.id,
                    &v,
                )
            }
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
            ExprKind::Record(ty, labeled_exprs, modifiers) => {
                // Collect labels with their span start positions.
                // For explicit labels ({name = e.name}), use the label span.
                // For implicit labels ({e.name}), use the expression span.
                let labels_with_spans: Vec<(String, usize)> = labeled_exprs
                    .iter()
                    .filter_map(|le| {
                        le.get_label().map(|name| {
                            let pos = le.label.as_ref().map_or_else(
                                || le.expr.span.start_pos(),
                                |l| l.span.start_pos(),
                            );
                            (name, pos)
                        })
                    })
                    .collect();

                // Check if labels are in alphabetical order, but only if
                // the spans are in source order (meaning they haven't
                // been
                // reordered yet).
                if !labels_with_spans.is_empty() {
                    let label_strs: Vec<&str> = labels_with_spans
                        .iter()
                        .map(|(name, _)| name.as_str())
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
                    kind: ExprKind::Record(
                        ty.clone(),
                        new_labeled_exprs,
                        modifiers.clone(),
                    ),
                    span: expr.span.clone(),
                    id: expr.id,
                    attributes: expr.attributes.clone(),
                }
            }
            ExprKind::Tuple(exprs) => {
                let new_exprs: Vec<Expr> =
                    exprs.iter().map(|e| self.validate_order_rec(e)).collect();
                Expr {
                    kind: ExprKind::Tuple(new_exprs),
                    span: expr.span.clone(),
                    id: expr.id,
                    attributes: expr.attributes.clone(),
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
            // Sort by ID first, then by name for deterministic output.
            v1.id.cmp(&v0.id).then_with(|| {
                self.unifier.var_name(v0).cmp(&self.unifier.var_name(v1))
            })
        });
        pairs
            .into_iter()
            .map(|(var, term)| {
                format!(
                    "{} = {}\n",
                    self.unifier.var_name(var),
                    self.unifier.term_string(term)
                )
            })
            .collect()
    }
}

/// Best-effort conversion of an AST [`AstType`] to a core [`Type`],
/// used to register the right-hand side of a `type myInt = ...`
/// declaration as a type alias. Only the simple shapes that
/// type-alias.smli exercises (primitive ids, tuples, function types,
/// applications of `list`/`bag`/`option`) are supported; anything
/// else returns `None` and the alias is silently dropped.
/// Like [`ast_type_to_core_type`], but also resolves type
/// variables (e.g. `'x`) from a list of type parameter names.
/// Used when converting constructor argument types in a datatype
/// declaration, where the type parameters are known.
pub(crate) fn ast_type_to_core_type_with_vars(
    ast_type: &AstType,
    type_vars: &[String],
) -> Option<Type> {
    match &ast_type.kind {
        TypeKind::Var(name) => {
            let index = type_vars.iter().position(|v| v == name)?;
            Some(Type::Variable(TypeVariable::new(index)))
        }
        TypeKind::Tuple(types) => {
            let cores: Vec<Rc<Type>> = types
                .iter()
                .filter_map(|t| ast_type_to_core_type_with_vars(t, type_vars))
                .map(Rc::new)
                .collect();
            if cores.len() == types.len() {
                Some(Type::Tuple(cores))
            } else {
                None
            }
        }
        TypeKind::Fn(t1, t2) => {
            let c1 = ast_type_to_core_type_with_vars(t1, type_vars)?;
            let c2 = ast_type_to_core_type_with_vars(t2, type_vars)?;
            Some(Type::Fn(Rc::new(c1), Rc::new(c2)))
        }
        TypeKind::App(args, t) => {
            // Flatten Composite args (e.g. `('a, 'b) tree` is parsed
            // as `App([Composite(['a, 'b])], Id("tree"))` — flatten
            // to `['a, 'b]`).
            let flat_args = AstType::flatten(args);
            if let TypeKind::Id(name) = &t.kind
                && flat_args.len() == 1
            {
                let arg_core =
                    ast_type_to_core_type_with_vars(&flat_args[0], type_vars)?;
                return Some(match name.as_str() {
                    "list" => Type::List(Rc::new(arg_core)),
                    "bag" => Type::Bag(Rc::new(arg_core)),
                    _ => Type::Data(name.clone(), vec![Rc::new(arg_core)]),
                });
            }
            if let TypeKind::Id(name) = &t.kind {
                let arg_cores: Vec<Rc<Type>> = flat_args
                    .iter()
                    .filter_map(|a| {
                        ast_type_to_core_type_with_vars(a, type_vars)
                    })
                    .map(Rc::new)
                    .collect();
                if arg_cores.len() == flat_args.len() {
                    return Some(Type::Data(name.clone(), arg_cores));
                }
            }
            None
        }
        TypeKind::Id(name) => {
            // Try the base function first (handles primitives
            // and known built-in types). If that fails, treat as
            // a user-defined datatype reference with no type
            // parameters (e.g. `inttree`).
            ast_type_to_core_type(ast_type)
                .or_else(|| Some(Type::Data(name.clone(), vec![])))
        }
        _ => ast_type_to_core_type(ast_type),
    }
}

pub(crate) fn ast_type_to_core_type(ast_type: &AstType) -> Option<Type> {
    match &ast_type.kind {
        TypeKind::Id(name) => PrimitiveType::parse_name(name)
            .map(Type::Primitive)
            .or_else(|| {
                // Bare name of a built-in datatype/eqtype: build a
                // placeholder `Type::Data` with no args; later
                // unification fills in fresh type variables.
                library::builtin_type_arity(name.as_str())
                    .map(|_| Type::Data(name.clone(), vec![]))
            }),
        TypeKind::Tuple(types) => {
            let cores: Vec<Rc<Type>> = types
                .iter()
                .filter_map(ast_type_to_core_type)
                .map(Rc::new)
                .collect();
            if cores.len() == types.len() {
                Some(Type::Tuple(cores))
            } else {
                None
            }
        }
        TypeKind::Fn(t1, t2) => {
            let c1 = ast_type_to_core_type(t1)?;
            let c2 = ast_type_to_core_type(t2)?;
            Some(Type::Fn(Rc::new(c1), Rc::new(c2)))
        }
        TypeKind::App(args, t) => {
            // Recognise applications of the parameterised collection
            // types: `int list`, `int bag`, `int option`, `int vector`.
            if let TypeKind::Id(name) = &t.kind
                && args.len() == 1
            {
                let arg_core = ast_type_to_core_type(&args[0])?;
                return Some(match name.as_str() {
                    "list" => Type::List(Rc::new(arg_core)),
                    "bag" => Type::Bag(Rc::new(arg_core)),
                    _ => Type::Data(name.clone(), vec![Rc::new(arg_core)]),
                });
            }
            None
        }
        TypeKind::Record(fields) => {
            let mut field_map: BTreeMap<Label, Rc<Type>> = BTreeMap::new();
            for field in fields {
                let field_type = Rc::new(ast_type_to_core_type(&field.type_)?);
                field_map
                    .insert(Label::from(field.label.name.clone()), field_type);
            }
            Some(Type::Record(false, field_map))
        }
        _ => None,
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
                        attributes: Vec::new(),
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
    /// Fresh unification variables for type variables encountered in
    /// user-written type annotations that are not pre-registered in
    /// `type_variables` (e.g., `'a` in `fun f (x: 'a list) = x`).
    extra_type_vars: BTreeMap<String, Var>,
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
        v: &Var,
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
        v: &Var,
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
                        terms.push(Term::Variable(v2));
                        let arg2 = self.type_term(&arg, subst, &v2);
                        args2.push(arg2);
                    }
                    // Arity check: if the type constructor is known
                    // (built-in or previously declared), reject mismatched
                    // applications. Without this, e.g. `(bool, int) list`
                    // either panics in the unifier or silently drops the
                    // extra arg.
                    let expected_opt =
                        self.type_resolver.arity_of_type_ctor(name.as_str());
                    if let Some(expected) = expected_opt
                        && expected != terms.len()
                    {
                        let actual = terms.len();
                        self.type_resolver.field_errors.borrow_mut().push((
                            format!(
                                "type constructor {} given {} argument{}, \
                                 wants {}",
                                name,
                                actual,
                                if actual == 1 { "" } else { "s" },
                                expected,
                            ),
                            type_node.span.clone(),
                        ));
                        // Bind to a fresh variable so resolution can
                        // continue and the error is reported.
                        return self.type_resolver.reg_type(
                            &type_node.kind,
                            &type_node.span,
                            &v,
                        );
                    }
                    // Build a collection term for `t list` and `t bag`, so
                    // that they match collections from other sources.
                    if terms.len() == 1
                        && matches!(name.as_str(), "list" | "bag")
                    {
                        let term = terms[0].clone();
                        if name == "list" {
                            self.type_resolver.list_term(term, &v);
                        } else {
                            self.type_resolver.bag_term(term, &v);
                        }
                    } else {
                        let op = self
                            .type_resolver
                            .unifier
                            .op(name.as_str(), Some(terms.len()));
                        let apply =
                            self.type_resolver.unifier.apply(op, &terms);
                        self.type_resolver.equiv(&Term::Sequence(apply), &v);
                    }
                    let x = TypeKind::App(args2, t.clone());
                    self.type_resolver.reg_type(&x, &type_node.span, &v)
                } else {
                    panic!("{:?}", type_node.kind)
                }
            }
            TypeKind::Composite(_) => {
                // `(t1, ..., tn)` is only valid as the argument list of
                // a parameterized type, e.g. `(int, string) either`.
                // It is not valid by itself: a tuple type must be
                // written `t1 * ... * tn`, e.g. `int * string`.
                self.type_resolver.field_errors.borrow_mut().push((
                    "tuple types must be written 't1 * ... * tn', \
                     not '(t1, ..., tn)'"
                        .to_string(),
                    type_node.span.clone(),
                ));
                // Bind to a fresh variable so resolution can continue
                // and the error is reported.
                self.type_resolver.reg_type(
                    &type_node.kind,
                    &type_node.span,
                    &v,
                )
            }
            TypeKind::Expression(expr) => {
                // `typeof expr` — the type of this annotation is the type
                // of `expr`. Deduce `expr`'s type into a fresh variable and
                // unify it with `v`.
                let v_expr = self.type_resolver.variable();
                self.type_resolver
                    .deduce_expr_type(self.env, expr, &v_expr)
                    .unwrap_or_else(|e| panic!("typeof: {}", e));
                self.type_resolver.equiv(&Term::Variable(v_expr), v);
                self.type_resolver
                    .reg_type(&type_node.kind, &type_node.span, v)
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
                // First check user-defined type aliases ('type myInt = int').
                // If found, register the alias's underlying type term.
                if let Some(alias_type) =
                    self.type_resolver.type_aliases.get(name).cloned()
                {
                    self.type_resolver.type_term(&alias_type, subst, v);
                    // Record that this variable carries an alias, so
                    // that type reconstruction wraps the resolved type
                    // in Type::Alias.
                    self.type_resolver.var_alias_map.insert(*v, name.clone());
                    return self.type_resolver.reg_type(
                        &type_node.kind,
                        &type_node.span,
                        &v,
                    );
                }
                if let Some(p) = PrimitiveType::parse_name(name) {
                    self.type_resolver.primitive_term(&p, &v);
                } else {
                    // Treat as a nilary built-in datatype (e.g.
                    // 'order'). The runtime representation is
                    // Type::Data(name, vec![]).
                    let data_type = Type::Data(name.clone(), vec![]);
                    self.type_resolver.type_term(&data_type, subst, v);
                }
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
                    terms.push(Term::Variable(v2));
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
                // If the type variable is pre-registered (via
                // type_variables + subst), use the substitution. Otherwise
                // lazily create a fresh unification variable for it
                // (handles user-written `'a` in pattern annotations such as
                // `fun f (x: 'a list) = x`).
                let term = if let Some(type_variable) =
                    self.type_variables.get(name)
                {
                    subst.get(type_variable).unwrap()
                } else {
                    let fresh_var = self
                        .extra_type_vars
                        .entry(name.clone())
                        .or_insert_with(|| self.type_resolver.variable());
                    Term::Variable(*fresh_var)
                };
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

    /// Returns the source position to use when reporting errors about
    /// this field's label. Uses the label's span if it is explicit, or
    /// the expression's span when the label is derived implicitly.
    pub fn label_span(&self) -> &Span {
        self.label.as_ref().map_or(&self.expr.span, |l| &l.span)
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

/// Returns whether `op_name` names a functor that safe navigation `?.`
/// projects fields through.
///
/// Accepts both term operators (a collection term is `$collection`) and
/// type-constructor names (a bag/list type is `bag`/`list`).
fn is_safe_nav_functor(op_name: &str) -> bool {
    matches!(
        op_name,
        "list" | "bag" | "option" | "vector" | COLLECTION_OP_NAME
    )
}

/// Re-wraps `element` in a functor layer, preserving the layer's non-element
/// terms (e.g. a collection's orderedness).
fn rewrap(layer: &Sequence, element: Term) -> Sequence {
    let mut terms = layer.terms.to_vec();
    terms[0] = element;
    Sequence {
        op: layer.op,
        terms: Rc::from(terms),
    }
}

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
            Rc::new(Type::Tuple(vec![
                Rc::new(Type::Primitive(PrimitiveType::Int)),
                Rc::new(Type::Fn(
                    Rc::new(Type::Tuple(vec![
                        Rc::new(Type::Variable(tv.clone())),
                        Rc::new(Type::Variable(tv.clone())),
                    ])),
                    Rc::new(Type::Primitive(PrimitiveType::Bool)),
                )),
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

/// Returns the body of a chain of `let` expressions; `exp` itself if it
/// is not a `let`.
fn let_body(exp: &Expr) -> Expr {
    let mut e = exp.clone();
    while let ExprKind::Let(_, body) = e.kind {
        e = *body;
    }
    e
}

/// The labels a record's modifiers mention, in the order written. When
/// the base's fields are unknown these are the only ones we know it has,
/// and the error says so.
fn modifier_labels(modifiers: &[Modifier]) -> Vec<String> {
    let mut out = Vec::new();
    for m in modifiers {
        match m {
            Modifier::Assign(_, _, args) => {
                out.extend(args.iter().filter_map(|a| {
                    a.label
                        .as_ref()
                        .map(|l| l.name.clone())
                        .or_else(|| a.expr.implicit_label_opt())
                }))
            }
            Modifier::Remove(_, labels) => {
                out.extend(labels.iter().map(|l| l.name.clone()))
            }
            Modifier::Rename(args) => {
                out.extend(args.iter().map(|(_, from)| from.name.clone()))
            }
            Modifier::All(..) => {}
        }
    }
    out
}

/// Returns a name that is not one of `fields`.
fn free_name(fields: &[String], stem: &str) -> String {
    let mut name = stem.to_string();
    while fields.contains(&name) {
        name.push('_');
    }
    name
}

/// Returns the expression `<name>` — a reference to a bound field.
fn id(span: &Span, name: &str) -> Expr {
    ExprKind::Identifier(name.to_string()).spanned(span)
}

/// Whether `s` can be a variable name, and so was bound by the
/// destructuring pattern. A tuple's `1` cannot.
fn is_name(s: &str) -> bool {
    let mut cs = s.chars();
    cs.next().is_some_and(|c| c.is_alphabetic() || c == '_')
        && cs.all(|c| c.is_alphanumeric() || c == '_' || c == '\'')
}

/// Returns the expression that reads `field` of the record the previous
/// modifier produced: the variable the pattern bound it to, or a
/// selector on the whole record if the label is not a name.
fn field_ref(span: &Span, rec: &str, field: &str) -> Expr {
    if is_name(field) {
        id(span, field)
    } else {
        field_of(span, rec, field)
    }
}

/// Returns the expression `#field name`.
fn field_of(span: &Span, name: &str, field: &str) -> Expr {
    ExprKind::Apply(
        Box::new(ExprKind::RecordSelector(field.to_string()).spanned(span)),
        Box::new(id(span, name)),
    )
    .spanned(span)
}

/// Returns `e : typeof field`, so that the assigned expression must have
/// the type the field already has. `field` is in scope as the variable
/// the enclosing `let` destructured it into.
fn same_type(span: &Span, e: &Expr, field_ref: &Expr) -> Expr {
    ExprKind::Annotated(
        Box::new(e.clone()),
        Box::new(
            TypeKind::Expression(Box::new(field_ref.clone())).spanned(span),
        ),
    )
    .spanned(span)
}

fn field_not_found(field: &str, span: &Span) -> Error {
    Error::Compile(format!("field '{}' does not exist", field), span.clone())
}

fn field_exists(field: &str, span: &Span) -> Error {
    Error::Compile(format!("field '{}' already exists", field), span.clone())
}

fn duplicate_field(field: &str, span: &Span) -> Error {
    Error::Compile(
        format!("duplicate field '{}' in record", field),
        span.clone(),
    )
}

/// Applies an `extend` or `replace` modifier, in either case taking each
/// label to whichever of the verb's two cases it falls in: the record has
/// the label already, or it does not.
fn assign_fields(
    span: &Span,
    rec: &str,
    verb: ModifierVerb,
    lenient: bool,
    assignments: &[LabeledExpr],
    fields: &[String],
) -> Result<Vec<(String, Expr)>, Error> {
    let mut assigned: Vec<(String, &Expr)> = Vec::new();
    for a in assignments {
        // The label of `replace a = e` is written; that of `replace a`
        // is the expression's own name.
        let (name, label_span) = match &a.label {
            Some(l) => (l.name.clone(), l.span.clone()),
            None => (
                a.expr.implicit_label_opt().ok_or_else(|| {
                    Error::Compile(
                        format!(
                            "cannot derive label for expression {}",
                            a.expr
                        ),
                        a.expr.span.clone(),
                    )
                })?,
                a.expr.span.clone(),
            ),
        };
        if fields.contains(&name) {
            if verb.exists() == Exists::Error {
                return Err(field_exists(&name, &label_span));
            }
        } else if verb.absent() == Absent::Error {
            return Err(field_not_found(&name, &label_span));
        }
        if assigned.iter().any(|(n, _)| *n == name) {
            return Err(duplicate_field(&name, &label_span));
        }
        assigned.push((name, &a.expr));
    }

    let mut args: Vec<(String, Expr)> = Vec::new();
    // Fields the record has: assigned, or kept as they were.
    for field in fields {
        let e = assigned.iter().find(|(n, _)| n == field).map(|(_, e)| *e);
        match e {
            Some(e) if verb.exists() != Exists::Skip => {
                let e = if lenient {
                    e.clone()
                } else {
                    same_type(span, e, &field_ref(span, rec, field))
                };
                args.push((field.clone(), e));
            }
            _ => args.push((field.clone(), field_ref(span, rec, field))),
        }
    }
    // Labels the record does not have: added, or ignored.
    if verb.absent() == Absent::Add {
        for (name, e) in &assigned {
            if !fields.iter().any(|f| f == name) {
                args.push((name.clone(), (*e).clone()));
            }
        }
    }
    Ok(args)
}

/// Applies an `extend all` or `replace all` modifier: the same rules as
/// [`assign_fields`], for every field of the modifier's record-valued
/// argument, which the enclosing `let` has bound to `name`.
fn assign_all_fields(
    span: &Span,
    rec: &str,
    exp_span: &Span,
    verb: ModifierVerb,
    lenient: bool,
    fields: &[String],
    all_fields: &[String],
    name: &str,
) -> Result<Vec<(String, Expr)>, Error> {
    for field in all_fields {
        if fields.contains(field) {
            if verb.exists() == Exists::Error {
                return Err(field_exists(field, exp_span));
            }
        } else if verb.absent() == Absent::Error {
            return Err(field_not_found(field, exp_span));
        }
    }
    let mut args: Vec<(String, Expr)> = Vec::new();
    for field in fields {
        if !all_fields.iter().any(|f| f == field)
            || verb.exists() == Exists::Skip
        {
            args.push((field.clone(), field_ref(span, rec, field)));
        } else {
            let e = field_of(span, name, field);
            let e = if lenient {
                e
            } else {
                same_type(span, &e, &field_ref(span, rec, field))
            };
            args.push((field.clone(), e));
        }
    }
    if verb.absent() == Absent::Add {
        for field in all_fields {
            if !fields.iter().any(|f| f == field) {
                args.push((field.clone(), field_of(span, name, field)));
            }
        }
    }
    Ok(args)
}

/// Applies a `remove` modifier.
fn remove_fields(
    span: &Span,
    rec: &str,
    verb: ModifierVerb,
    labels: &[AstLabel],
    fields: &[String],
) -> Result<Vec<(String, Expr)>, Error> {
    let mut removed: Vec<&str> = Vec::new();
    for label in labels {
        if !fields.contains(&label.name) && verb.absent() == Absent::Error {
            return Err(field_not_found(&label.name, &label.span));
        }
        if removed.contains(&label.name.as_str()) {
            return Err(duplicate_field(&label.name, &label.span));
        }
        removed.push(&label.name);
    }
    Ok(fields
        .iter()
        .filter(|f| !removed.contains(&f.as_str()))
        .map(|f| (f.clone(), field_ref(span, rec, f)))
        .collect())
}

/// Applies a `rename` modifier. It takes the value of each label on the
/// right, which must exist, and gives it to the label on the left, which
/// must not survive the renaming.
fn rename_fields(
    span: &Span,
    rec: &str,
    renames: &[(AstLabel, AstLabel)],
    fields: &[String],
) -> Result<Vec<(String, Expr)>, Error> {
    let mut sources: Vec<&str> = Vec::new();
    for (_, source) in renames {
        if !fields.contains(&source.name) {
            return Err(field_not_found(&source.name, &source.span));
        }
        if sources.contains(&source.name.as_str()) {
            return Err(duplicate_field(&source.name, &source.span));
        }
        sources.push(&source.name);
    }
    let mut args: Vec<(String, Expr)> = fields
        .iter()
        .filter(|f| !sources.contains(&f.as_str()))
        .map(|f| (f.clone(), field_ref(span, rec, f)))
        .collect();
    for (target, source) in renames {
        if args.iter().any(|(f, _)| *f == target.name) {
            return Err(field_exists(&target.name, &target.span));
        }
        args.push((target.name.clone(), field_ref(span, rec, &source.name)));
    }
    Ok(args)
}
