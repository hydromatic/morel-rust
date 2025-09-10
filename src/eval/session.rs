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
    EmptyTypeEnv, FunTypeEnv, TypeEnv, TypeSchemeResolver,
};
use crate::compile::type_resolver::{Resolved, TypeResolver};
use crate::compile::unifier::Term;
use crate::eval::code::Code;
use crate::eval::val::Val;
use crate::shell::ShellResult;
use crate::shell::error::Error;
use crate::shell::main::{BUILT_IN_TYPES, MorelError};
use crate::shell::prop::{Configurable, Output, Prop, PropVal};
use crate::syntax::ast::Statement;
use crate::syntax::parser::parse_type_scheme;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::rc::Rc;

/// Shell implementation for use within scripts.
pub struct Session {
    pub config: Config,
    /// The plan of the previous command.
    pub code: Option<Box<Code>>,
    /// The output lines of the previous command.
    pub out: Option<Vec<String>>,
}

impl Default for Session {
    fn default() -> Self {
        Self::new()
    }
}

impl Session {
    /// Creates a session.
    pub fn new() -> Self {
        Session {
            config: Config::default(),
            code: None,
            out: None,
        }
    }

    #[allow(clippy::needless_pass_by_value)] // Val is small
    pub(crate) fn set_prop(
        &mut self,
        prop: &str,
        val: Val,
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
    pub fn deduce_type_inner(&self, node: &Statement) -> Resolved {
        let mut type_resolver = TypeResolver::new();
        let empty_type_env = EmptyTypeEnv {};
        let resolve =
            |id: &str, t: &mut dyn TypeSchemeResolver| -> Option<Term> {
                if let Some(x) = BUILT_IN_TYPES.get(id) {
                    let type_scheme = parse_type_scheme(x).unwrap();
                    Some(Term::Variable(t.deduce_type_scheme(&type_scheme)))
                } else {
                    None
                }
            };
        let type_env = FunTypeEnv {
            parent: Rc::new(empty_type_env) as Rc<dyn TypeEnv>,
            resolve: Rc::new(resolve),
        };

        type_resolver.deduce_type(&type_env, node)
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
            _ => todo!("get: prop {}", prop.name()),
        }
    }
}
