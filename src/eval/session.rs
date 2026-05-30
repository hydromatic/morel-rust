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

use crate::compile::core::Decl;
use crate::compile::core::{Expr as CoreExpr, Pat as CorePat};
use crate::compile::inliner::Env;
use crate::compile::library;
use crate::compile::library::{
    BuiltInFunction, built_in_datatype_constructors,
};
use crate::compile::type_env::{
    BindType, EmptyTypeEnv, FunTypeEnv, SimpleTypeEnv, TypeEnv, TypeEnvBuilder,
};
use crate::compile::type_resolver::{BindingKind, Resolved, TypeResolver};
use crate::compile::types::Type;
use crate::eval::code::Code;
use crate::eval::file::{self, File, TypedValue};
use crate::eval::val::Val;
use crate::shell::error::Error;
use crate::shell::prop::{Configurable, Output, Prop, PropVal};
use crate::syntax::ast::Statement;
use crate::unify::unifier::Term;
use std::cell::{OnceCell, RefCell};
use std::collections::{BTreeMap, HashMap};
use std::path::PathBuf;
use std::rc::Rc;
use std::sync::Arc;

/// Shell implementation for use within scripts.
pub struct Session {
    pub config: Config,
    /// The plan of the previous command.
    pub code: Option<Arc<Code>>,
    /// Core declaration of the previous command, before inlining. Used by
    /// `Sys.planEx` to show the plan at the start of the optimizer.
    pub pre_inline_decl: Option<Decl>,
    /// Core declaration of the previous command, after inlining. Used by
    /// `Sys.planEx` to show the plan after all optimization passes.
    pub post_inline_decl: Option<Decl>,
    /// The accumulated type environment (bindings from previous statements).
    pub type_env: Rc<dyn TypeEnv>,
    /// Accumulated type bindings from all statements. When a name is
    /// redefined, HashMap::insert naturally overwrites the old binding.
    /// The bool indicates whether this is a constructor (true) or a
    /// regular value (false).
    pub type_bindings: HashMap<String, (Type, bool)>,
    /// Accumulated type aliases from `type` and `datatype` declarations
    /// across all statements. Each new `TypeResolver` is seeded with
    /// this map so that aliases defined in one statement are visible in
    /// later ones.
    pub type_aliases: HashMap<String, Type>,
    /// Accumulated constructor sets from `datatype` declarations.
    /// Each new `TypeMap` is seeded with this map so that the match
    /// coverage checker knows the constructor set of previously
    /// declared datatypes.
    pub datatype_constructors: HashMap<String, Vec<String>>,
    /// Accumulated parameter counts (arities) of user-declared
    /// datatypes. Seeded into each new `TypeResolver` so that
    /// `(t1, …, tn) name` is arity-checked even when the datatype
    /// was declared in a prior statement. Built-in arities are not
    /// kept here — they live as strum properties on
    /// `library::BuiltInDatatype` / `library::BuiltInEqtype`.
    pub user_datatype_arities: HashMap<String, usize>,
    /// Constructor argument types accumulated across statements.
    /// Used by the pretty printer to format record arguments.
    pub constructor_arg_types: HashMap<String, Type>,
    /// Accumulated overload instance types. Maps overloaded name
    /// to a list of instance types (one per `val inst` declaration).
    pub overloads: HashMap<String, Vec<Type>>,
    /// Core function bodies of single-arm `fn p => body` value
    /// bindings from earlier statements. Lets predicate inversion
    /// inline a function declared in a previous shell statement.
    pub fn_bindings: HashMap<String, (CorePat, CoreExpr)>,
    /// Pre-expander variant of [`Self::fn_bindings`]. Recursive
    /// predicate inversion reads bodies from this map so the
    /// original step predicates are still visible as conjuncts of
    /// the inner `where`.
    pub rec_fn_bindings: HashMap<String, (CorePat, CoreExpr)>,
    /// Cached inliner `Env` populated with all built-in functions
    /// and structures. Built lazily on first access and reused
    /// across statements; each statement clones it and layers
    /// session bindings on top.
    base_env: OnceCell<Env>,
    /// Per-session root [`File`] for the `Sys.file` built-in. Lazily
    /// initialised on first access from the `directory` property so
    /// every reference to `file` within a session shares the same
    /// `Rc<File>` and any progressive expansion accumulates there.
    /// Reset when the `directory` property is set (so a script can
    /// repoint the file root mid-session).
    file_root: RefCell<Option<Rc<File>>>,
}

// static SESSION_COUNTER: std::sync::atomic::AtomicUsize =
//     std::sync::atomic::AtomicUsize::new(0);

impl Default for Session {
    fn default() -> Self {
        Self::new()
    }
}

impl Session {
    /// Creates a session.
    pub fn new() -> Self {
        // Initialize type environment with built-in functions
        let empty_type_env = EmptyTypeEnv {};
        let type_env = FunTypeEnv {
            parent: Rc::new(empty_type_env) as Rc<dyn TypeEnv>,
        };
        // Seed built-in overloads for functions with both list and
        // bag forms (e.g. List.only / Bag.only, both global as "only").
        let mut overloads: HashMap<String, Vec<Type>> = HashMap::new();
        for f in &[BuiltInFunction::ListOnly, BuiltInFunction::BagOnly] {
            let name = f.overloaded_name().unwrap_or_else(|| f.name());
            overloads
                .entry(name.to_string())
                .or_default()
                .push((*f.get_type()).clone());
        }
        // Seed the datatype constructor map with the built-in datatypes
        // (`bool`, `either`, `list`, `option`, `order`, ...); user-
        // declared datatypes are added incrementally as their
        // declarations are resolved.
        let datatype_constructors = built_in_datatype_constructors();
        Session {
            config: Config::default(),
            code: None,
            pre_inline_decl: None,
            post_inline_decl: None,
            type_env: Rc::new(type_env) as Rc<dyn TypeEnv>,
            type_bindings: HashMap::new(),
            type_aliases: HashMap::new(),
            datatype_constructors,
            user_datatype_arities: HashMap::new(),
            constructor_arg_types: HashMap::new(),
            overloads,
            fn_bindings: HashMap::new(),
            rec_fn_bindings: HashMap::new(),
            base_env: OnceCell::new(),
            file_root: RefCell::new(None),
        }
    }

    /// Returns the session's root [`File`], creating it on first
    /// access from the `directory` property (or `.` when unset).
    /// Cached so subsequent calls return the same `Rc<File>`,
    /// preserving any expansion that has happened so far.
    pub fn file(&self) -> Rc<File> {
        if let Some(rc) = self.file_root.borrow().as_ref() {
            return Rc::clone(rc);
        }
        let rc = file::session_file(self);
        *self.file_root.borrow_mut() = Some(Rc::clone(&rc));
        rc
    }

    /// Returns the cached inliner `Env` populated with all built-in
    /// functions and structures. Built lazily on first call and
    /// reused thereafter; callers clone it before layering
    /// session-local bindings.
    pub fn base_env(&self) -> &Env {
        self.base_env.get_or_init(|| {
            let mut map: BTreeMap<&str, (Type, Option<Val>)> = BTreeMap::new();
            library::populate_env(&mut map);
            Env::empty().multi(&map)
        })
    }

    /// Deduces a statement's type. The statement is represented by an AST node.
    /// `runtime_bindings` is the map of top-level user val bindings from prior
    /// statements (`Shell::environment.bindings`). The wrapper env uses it to
    /// project runtime [`Val::File`] values into [`TypedValue`] registrations
    /// for the resolver's progressive-widening hook.
    pub fn deduce_type_inner(
        &mut self,
        node: &Statement,
        runtime_bindings: &HashMap<String, Val>,
    ) -> Result<Resolved, Error> {
        let mut type_resolver = TypeResolver::new();
        type_resolver.match_coverage_enabled =
            self.config.match_coverage_enabled.unwrap_or(true);
        // Seed with type aliases accumulated from previous statements,
        // so that 'type myInt = int' in one statement and 'val x: myInt = 5'
        // in the next can both refer to the alias.
        type_resolver.type_aliases = self.type_aliases.clone();
        // Same for user-declared datatype arities (built-ins live
        // in `library`, queried on demand).
        type_resolver.user_datatype_arities =
            self.user_datatype_arities.clone();
        type_resolver.prior_datatype_constructors =
            self.datatype_constructors.clone();
        type_resolver.prior_constructor_arg_types =
            self.constructor_arg_types.clone();
        type_resolver.seed_overloads = self.overloads.clone();

        // Use the accumulated type environment from previous statements,
        // wrapped in a session-aware layer that resolves the `file`
        // identifier against the session's progressive root file and
        // promotes any prior `Val::File` runtime binding to a
        // `TypedValue` registration for the resolver's progressive
        // widening hook.
        let env = SessionAwareEnv {
            parent: Rc::clone(&self.type_env),
            file: self.file(),
            runtime_bindings: runtime_bindings.clone(),
        };
        let resolved = type_resolver.deduce_type(&env, node)?;
        let new_overloads = std::mem::take(&mut type_resolver.new_overloads);

        // Capture new overload instances: convert candidate Vars
        // to Types using the resolved type_map.
        for (name, vars) in &new_overloads {
            let mut types = Vec::new();
            for v in vars {
                if let Some(t) = resolved.type_map.var_to_type(v) {
                    types.push(t);
                }
            }
            if !types.is_empty() {
                self.overloads
                    .entry(name.clone())
                    .or_default()
                    .extend(types);
            }
        }

        // Capture any new aliases introduced by this statement.
        for (name, t) in &type_resolver.type_aliases {
            self.type_aliases.insert(name.clone(), t.clone());
        }

        // Capture any new (or redeclared) user datatype arities.
        for (name, arity) in &type_resolver.user_datatype_arities {
            self.user_datatype_arities.insert(name.clone(), *arity);
        }

        // Capture any new constructor sets from datatype declarations.
        for (name, cons) in &resolved.type_map.datatype_constructors {
            self.datatype_constructors
                .insert(name.clone(), cons.clone());
        }
        for (name, t) in &resolved.type_map.constructor_arg_types {
            self.constructor_arg_types.insert(name.clone(), t.clone());
        }

        Ok(resolved)
    }

    /// Commits the bindings from a resolved statement into the
    /// persistent type environment. Call this AFTER evaluating the
    /// statement, so that `Sys.env()` during evaluation does not
    /// see the current statement's own bindings (e.g. `it`).
    pub fn commit_bindings(&mut self, resolved: &Resolved) {
        let mut has_new_bindings = false;
        for binding in &resolved.bindings {
            if binding.kind == BindingKind::Val
                || binding.kind == BindingKind::Constructor
            {
                let is_con = binding.kind == BindingKind::Constructor;
                self.type_bindings.insert(
                    binding.name.clone(),
                    (binding.resolved_type.clone(), is_con),
                );
                has_new_bindings = true;
            }
        }

        // Rebuild the type environment if there are new bindings.
        // We keep the FunTypeEnv (built-ins) as the base and create a single
        // ResolvedTypeEnv with all accumulated bindings.
        if has_new_bindings {
            let empty_type_env = EmptyTypeEnv {};
            let fun_type_env = FunTypeEnv {
                parent: Rc::new(empty_type_env) as Rc<dyn TypeEnv>,
            };
            self.type_env = Rc::new(ResolvedTypeEnv {
                parent: Rc::new(fun_type_env) as Rc<dyn TypeEnv>,
                bindings: self.type_bindings.clone(),
            }) as Rc<dyn TypeEnv>;
        }
    }
}

/// Configuration of a [Session].
pub struct Config {
    pub directory: Option<Rc<PathBuf>>,
    pub hybrid: Option<bool>,
    pub inline_pass_count: Option<i32>,
    pub now: Option<Rc<String>>,
    pub optional_int: Option<i32>,
    pub match_coverage_enabled: Option<bool>,
    pub output: Option<Output>,
    pub script_directory: Option<Rc<PathBuf>>,
    pub string_fold: Option<i32>,
    pub time_zone: Option<Rc<String>>,
}

impl Default for Config {
    fn default() -> Self {
        Self {
            directory: None,
            hybrid: Some(false),
            inline_pass_count: Some(5),
            now: None,
            optional_int: None,
            output: Some(Output::Classic),
            match_coverage_enabled: None,
            script_directory: None,
            string_fold: None,
            time_zone: None,
        }
    }
}

impl Config {
    /// Returns the value of an optional (non-required) property, or `None`
    /// if it has not been set.
    pub fn get_optional(&self, prop: Prop) -> Option<PropVal> {
        match prop {
            Prop::Now => self.now.clone().map(PropVal::String),
            Prop::OptionalInt => self.optional_int.map(PropVal::Int),
            Prop::StringFold => self.string_fold.map(PropVal::Int),
            Prop::TimeZone => self.time_zone.clone().map(PropVal::String),
            _ => None,
        }
    }
}

impl Configurable for Config {
    fn set(&mut self, prop: Prop, val: &PropVal) {
        match (prop, val) {
            // lint: sort until '#}' where '##\('
            (Prop::Directory, PropVal::PathBuf(b)) => {
                self.directory = Some(b.clone());
            }
            (Prop::Hybrid, PropVal::Bool(b)) => {
                self.hybrid = Some(*b);
            }
            (Prop::InlinePassCount, PropVal::Int(i)) => {
                self.inline_pass_count = Some(*i);
            }
            (Prop::MatchCoverageEnabled, PropVal::Bool(b)) => {
                self.match_coverage_enabled = Some(*b);
            }
            (Prop::Now, PropVal::String(s)) => {
                self.now = Some(s.clone());
            }
            (Prop::Output, PropVal::Output(x)) => {
                self.output = Some(*x);
            }
            (Prop::ScriptDirectory, PropVal::PathBuf(b)) => {
                self.script_directory = Some(b.clone());
            }
            (Prop::TimeZone, PropVal::String(s)) => {
                self.time_zone = Some(s.clone());
            }
            _ => todo!(),
        }
    }

    fn get(&self, prop: Prop) -> PropVal {
        match prop {
            // lint: sort until '#}' where '##Prop::'
            Prop::Directory => {
                if let Some(b) = &self.directory {
                    PropVal::PathBuf(b.clone())
                } else {
                    prop.default_value()
                }
            }
            Prop::Hybrid => {
                if let Some(b) = self.hybrid {
                    PropVal::Bool(b)
                } else {
                    prop.default_value()
                }
            }
            Prop::InlinePassCount => {
                if let Some(i) = self.inline_pass_count {
                    PropVal::Int(i)
                } else {
                    prop.default_value()
                }
            }
            Prop::MatchCoverageEnabled => {
                if let Some(b) = self.match_coverage_enabled {
                    PropVal::Bool(b)
                } else {
                    prop.default_value()
                }
            }
            Prop::Output => {
                if let Some(o) = &self.output {
                    PropVal::Output(*o)
                } else {
                    prop.default_value()
                }
            }
            Prop::ScriptDirectory => {
                if let Some(b) = &self.script_directory {
                    PropVal::PathBuf(b.clone())
                } else {
                    prop.default_value()
                }
            }
            // For read-only properties and properties not stored in this
            // Config, return the default value.
            _ => prop.default_value(),
        }
    }
}

/// Type environment that stores resolved types from previous statements
/// and converts them to terms on-demand.
pub struct ResolvedTypeEnv {
    pub parent: Rc<dyn TypeEnv>,
    /// `(type, is_constructor)`.
    pub bindings: HashMap<String, (Type, bool)>,
}

impl TypeEnv for ResolvedTypeEnv {
    fn get(&self, name: &str, t: &mut TypeResolver) -> Option<BindType> {
        if let Some((type_, is_con)) = self.bindings.get(name) {
            let term = t.type_to_term(type_);
            let term = Term::Variable(term);
            Some(if *is_con {
                BindType::Constructor(term)
            } else {
                BindType::Val(term)
            })
        } else {
            self.parent.get(name, t)
        }
    }

    fn bind(&self, name: String, term: Term) -> Rc<dyn TypeEnv> {
        // We can't directly store a Term, so just create a new SimpleTypeEnv.
        SimpleTypeEnv::with_parent_and_binding(
            Rc::new(self.clone()),
            name,
            term,
        )
    }

    fn bind_all(&self, bindings: &[(String, Term)]) -> Rc<dyn TypeEnv> {
        SimpleTypeEnv::with_parent_and_bindings(Rc::new(self.clone()), bindings)
    }

    fn builder(&self) -> TypeEnvBuilder {
        // We need to return a builder based on THIS environment, not the
        // parent. Since we can't directly create a TypeEnvBuilder (private
        // field), we create an empty SimpleTypeEnv with self as parent, then
        // get its builder.
        let self_rc: Rc<dyn TypeEnv> = Rc::new(self.clone());
        Rc::new(SimpleTypeEnv {
            parent: self_rc,
            bindings: HashMap::new(),
        })
        .builder()
    }
}

impl Clone for ResolvedTypeEnv {
    fn clone(&self) -> Self {
        ResolvedTypeEnv {
            parent: self.parent.clone(),
            bindings: self.bindings.clone(),
        }
    }
}

/// Type environment that intercepts the `file` identifier and binds
/// it to the type of the session's [`File`]. Wraps a regular parent
/// env so all other names fall through. Created fresh per
/// [`Session::deduce_type_inner`] call so the `file` type reflects
/// whatever expansion has happened during this round.
pub struct SessionAwareEnv {
    pub parent: Rc<dyn TypeEnv>,
    pub file: Rc<File>,
    /// Snapshot of [`crate::shell::main::Environment::bindings`] at
    /// the moment this env was built. Used to discover that a name
    /// from a previous statement is bound to a `Val::File`, which we
    /// then re-register as a [`TypedValue`] for the field-selector
    /// action's widening hook.
    pub runtime_bindings: HashMap<String, Val>,
}

impl TypeEnv for SessionAwareEnv {
    fn get(&self, name: &str, tr: &mut TypeResolver) -> Option<BindType> {
        if name == "file" {
            // Make sure the root is expanded so its type lists its
            // children (the first layer of progressive widening).
            self.file.expand();
            let v = tr.type_to_term(&self.file.type_());
            // Register the File as the TypedValue behind this var,
            // so the field-selector action can call discover_field
            // on it when a missing field is requested.
            tr.typed_values
                .borrow_mut()
                .insert(v, Rc::clone(&self.file) as Rc<dyn file::TypedValue>);
            return Some(BindType::Val(Term::Variable(v)));
        }
        // If a prior statement's val binding evaluated to a
        // `Val::File`, use the file's *current* type (which reflects
        // any expansion that's happened since the binding was
        // resolved) rather than the type that was frozen at binding
        // time. Also register the file as a [`TypedValue`] for the
        // field-selector action's progressive widening hook.
        if let Some(Val::File(f)) = self.runtime_bindings.get(name) {
            f.expand();
            let v = tr.type_to_term(&f.type_());
            tr.typed_values
                .borrow_mut()
                .insert(v, Rc::clone(f) as Rc<dyn file::TypedValue>);
            return Some(BindType::Val(Term::Variable(v)));
        }
        self.parent.get(name, tr)
    }

    fn bind(&self, name: String, term: Term) -> Rc<dyn TypeEnv> {
        SimpleTypeEnv::with_parent_and_binding(
            Rc::new(self.clone()),
            name,
            term,
        )
    }

    fn bind_all(&self, bindings: &[(String, Term)]) -> Rc<dyn TypeEnv> {
        SimpleTypeEnv::with_parent_and_bindings(Rc::new(self.clone()), bindings)
    }

    fn builder(&self) -> TypeEnvBuilder {
        let self_rc: Rc<dyn TypeEnv> = Rc::new(self.clone());
        Rc::new(SimpleTypeEnv {
            parent: self_rc,
            bindings: HashMap::new(),
        })
        .builder()
    }
}

impl Clone for SessionAwareEnv {
    fn clone(&self) -> Self {
        SessionAwareEnv {
            parent: self.parent.clone(),
            file: Rc::clone(&self.file),
            runtime_bindings: self.runtime_bindings.clone(),
        }
    }
}
