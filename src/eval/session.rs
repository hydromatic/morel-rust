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

use crate::compile::type_env::{
    BindType, EmptyTypeEnv, FunTypeEnv, SimpleTypeEnv, TypeEnv, TypeEnvBuilder,
};
use crate::compile::type_resolver::{BindingKind, Resolved, TypeResolver};
use crate::compile::types::Type;
use crate::eval::code::Code;
use crate::eval::val::Val;
use crate::shell::ShellResult;
use crate::shell::error::Error;
use crate::shell::main::MorelError;
use crate::shell::prop::{Configurable, Output, Prop, PropVal};
use crate::syntax::ast::Statement;
use crate::unify::unifier::Term;
use std::collections::HashMap;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::rc::Rc;
use std::sync::Arc;

/// Shell implementation for use within scripts.
pub struct Session {
    pub config: Config,
    /// The plan of the previous command.
    pub code: Option<Arc<Code>>,
    /// The output lines of the previous command.
    pub out: Option<Vec<String>>,
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
    /// Constructor argument types accumulated across statements.
    /// Used by the pretty printer to format record arguments.
    pub constructor_arg_types: HashMap<String, Type>,
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
        Session {
            config: Config::default(),
            code: None,
            out: None,
            type_env: Rc::new(type_env) as Rc<dyn TypeEnv>,
            type_bindings: HashMap::new(),
            type_aliases: HashMap::new(),
            datatype_constructors: HashMap::new(),
            constructor_arg_types: HashMap::new(),
        }
    }

    pub(crate) fn set_prop(
        &mut self,
        prop: &str,
        val: &Val,
    ) -> Result<(), Error> {
        match prop {
            "hybrid" => {
                self.config.hybrid = Some(val.expect_bool());
                Ok(())
            }
            _ => todo!(),
        }
    }

    pub(crate) fn handle_exception(&self, _p0: MorelError, _p1: &mut str) {
        todo!()
    }

    /// Executes a `use` command (load a file).
    pub fn use_file<P: AsRef<Path>, W: Write>(
        &mut self,
        file_path: P,
        silent: bool,
        _output: W,
    ) -> ShellResult<()> {
        let path = file_path.as_ref();

        if !silent {
            // TODO: Write opening message to output
        }

        // Check if file exists
        if !path.exists() {
            return Err(Error::FileNotFound(format!(
                "use failed: File not found: {}",
                path.display(),
            )));
        }

        // TODO: Run the file
        // For now, just write a placeholder
        todo!("Implement use_file without shell dependency")
    }

    /// Clears the environment.
    pub fn clear_env(&mut self) {
        // TODO: Implement clear_env without shell dependency
        todo!("Implement clear_env without shell dependency");
    }

    /// Deduces a statement's type. The statement is represented by an AST node.
    pub fn deduce_type_inner(
        &mut self,
        node: &Statement,
    ) -> Result<Resolved, Error> {
        let mut type_resolver = TypeResolver::new();
        type_resolver.match_coverage_enabled =
            self.config.match_coverage_enabled.unwrap_or(true);
        // Seed with type aliases accumulated from previous statements,
        // so that 'type myInt = int' in one statement and 'val x: myInt = 5'
        // in the next can both refer to the alias.
        type_resolver.type_aliases = self.type_aliases.clone();
        type_resolver.prior_datatype_constructors =
            self.datatype_constructors.clone();
        type_resolver.prior_constructor_arg_types =
            self.constructor_arg_types.clone();

        // Use the accumulated type environment from previous statements
        let resolved = type_resolver.deduce_type(&*self.type_env, node)?;

        // Capture any new aliases introduced by this statement.
        for (name, t) in &type_resolver.type_aliases {
            self.type_aliases.insert(name.clone(), t.clone());
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
    pub optional_int: Option<i32>,
    pub match_coverage_enabled: Option<bool>,
    pub output: Option<Output>,
    pub script_directory: Option<Rc<PathBuf>>,
}

impl Default for Config {
    fn default() -> Self {
        Self {
            directory: None,
            hybrid: Some(false),
            inline_pass_count: Some(5),
            optional_int: None,
            output: Some(Output::Classic),
            match_coverage_enabled: None,
            script_directory: None,
        }
    }
}

impl Config {
    /// Returns the value of an optional (non-required) property, or `None`
    /// if it has not been set.
    pub fn get_optional(&self, prop: Prop) -> Option<PropVal> {
        match prop {
            Prop::OptionalInt => self.optional_int.map(PropVal::Int),
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
            (Prop::Output, PropVal::Output(x)) => {
                self.output = Some(*x);
            }
            (Prop::ScriptDirectory, PropVal::PathBuf(b)) => {
                self.script_directory = Some(b.clone());
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
