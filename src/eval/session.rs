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
use crate::compile::type_resolver::{Resolved, TypeResolver};
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
    /// Accumulated type bindings from all statements. When a name is redefined,
    /// the HashMap::insert naturally overwrites the old binding.
    pub type_bindings: HashMap<String, Type>,
    // Debug ID to track session instances
    // pub debug_id: usize,
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
            // debug_id: id,
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

        // Use the accumulated type environment from previous statements
        let resolved = type_resolver.deduce_type(&*self.type_env, node)?;

        // Update the accumulated environment with new bindings from this
        // statement. We store bindings in a single HashMap; when a name is
        // redefined, HashMap::insert overwrites the old binding, preventing
        // memory growth from shadowed values.
        let mut has_new_bindings = false;
        for binding in &resolved.bindings {
            if binding.kind == crate::compile::type_resolver::BindingKind::Val {
                self.type_bindings.insert(
                    binding.name.clone(),
                    binding.resolved_type.clone(),
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

        Ok(resolved)
    }
}

/// Configuration of a [Session].
pub struct Config {
    pub directory: Option<Rc<PathBuf>>,
    pub hybrid: Option<bool>,
    pub inline_pass_count: Option<i32>,
    pub output: Option<Output>,
    pub script_directory: Option<Rc<PathBuf>>,
}

impl Default for Config {
    fn default() -> Self {
        Self {
            directory: None,
            hybrid: Some(false),
            output: Some(Output::Classic),
            inline_pass_count: Some(5),
            script_directory: None,
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
    pub bindings: HashMap<String, Type>,
}

impl TypeEnv for ResolvedTypeEnv {
    fn get(&self, name: &str, t: &mut TypeResolver) -> Option<BindType> {
        if let Some(type_) = self.bindings.get(name) {
            // Convert the type to a term using the current TypeResolver
            let term = t.type_to_term(type_);
            Some(BindType::Val(Term::Variable(term)))
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
