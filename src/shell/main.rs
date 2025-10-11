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

#![allow(clippy::derivable_impls)]
#![allow(clippy::to_string_in_format_args)]
#![allow(clippy::unnecessary_unwrap)]
#![allow(clippy::useless_format)]
#![allow(clippy::redundant_closure)]

use crate::compile::inliner::Env;
use crate::compile::library::BuiltInExn;
use crate::compile::resolver;
use crate::compile::type_env::Binding;
use crate::compile::type_resolver::Resolved;
use crate::compile::types::Type;
use crate::compile::{compiler, inliner, library};
use crate::eval::code::{Effect, Span};
use crate::eval::session::Config as SessionConfig;
use crate::eval::session::Session;
use crate::eval::val::Val;
use crate::shell::ShellResult;
use crate::shell::config::Config;
use crate::shell::error::Error;
use crate::shell::prop::Mode;
use crate::shell::utils::{prefix_lines, strip_prefix};
use crate::syntax::ast::Statement;
use crate::syntax::parser;
use rustc_version::version;
use std::cell::RefCell;
use std::collections::{BTreeMap, HashMap};
use std::fmt::{Debug, Display, Formatter};
use std::fs;
use std::io::{BufRead, BufReader, BufWriter, Cursor, Read, Write};
use std::path::{Path, PathBuf};
use std::rc::Rc;

/// Main shell for Morel - Standard ML REPL.
pub struct Shell {
    pub(crate) config: Config,
    environment: Environment,
    session: Rc<RefCell<Session>>,
}

/// Simple environment for storing bindings.
#[derive(Debug, Clone)]
pub struct Environment {
    bindings: HashMap<String, Val>,
}

impl Default for Environment {
    fn default() -> Self {
        Self {
            bindings: HashMap::new(),
        }
    }
}

impl Environment {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn bind(&mut self, name: String, value: &Val) {
        self.bindings.insert(name, value.clone());
    }

    pub fn bind_all(&self, bindings: &[Binding]) -> Self {
        let mut env = Self::new();
        for b in bindings {
            if b.value.is_some() {
                env.bind(b.id.name.clone(), b.value.as_ref().unwrap());
            }
        }
        env
    }

    pub fn get(&self, name: &str) -> Option<&Val> {
        self.bindings.get(name)
    }

    pub fn clear(&mut self) {
        self.bindings.clear();
    }
}

impl Shell {
    pub(crate) fn set_prop(
        &mut self,
        prop: &str,
        val: &Val,
    ) -> Result<(), Error> {
        match prop {
            // lint: sort until '#}' where '##[^ }]'
            "hybrid" => {
                self.session.borrow_mut().config.hybrid =
                    Some(val.expect_bool());
                Ok(())
            }
            "lineWidth" => {
                self.config.line_width = Some(val.expect_int());
                Ok(())
            }
            "mode" => {
                self.config.mode = val.expect_string().parse().ok();
                Ok(())
            }
            "printDepth" => {
                self.config.print_depth = Some(val.expect_int());
                Ok(())
            }
            "printLength" => {
                self.config.print_length = Some(val.expect_int());
                Ok(())
            }
            "stringDepth" => {
                self.config.string_depth = Some(val.expect_int());
                Ok(())
            }
            _ => todo!("set_prop: {}", prop),
        }
    }

    pub(crate) fn unset_prop(&mut self, prop: &str) -> Result<(), Error> {
        match prop {
            // lint: sort until '#}' where '##[^ }]'
            "hybrid" => {
                self.session.borrow_mut().config.hybrid = None;
                Ok(())
            }
            "lineWidth" => {
                self.config.line_width = None;
                Ok(())
            }
            "mode" => {
                self.config.mode = None;
                Ok(())
            }
            "printDepth" => {
                self.config.print_depth = None;
                Ok(())
            }
            "printLength" => {
                self.config.print_length = None;
                Ok(())
            }
            "stringDepth" => {
                self.config.string_depth = None;
                Ok(())
            }
            _ => todo!("unset_prop: {}", prop),
        }
    }

    /// Creates a new Main shell with the given configuration.
    pub fn new(args: &[String]) -> Self {
        let mut config = Config::default();
        let mut session_config = SessionConfig::default();

        // Parse command line arguments
        for arg in args {
            match arg.as_str() {
                "--banner" => config.banner = Some(true),
                "--echo" => config.echo = Some(true),
                "--idempotent" => config.idempotent = Some(true),
                _ if arg.starts_with("--directory=") => {
                    let dir = arg.strip_prefix("--directory=").unwrap();
                    session_config.directory =
                        Some(Rc::new(PathBuf::from(dir)));
                }
                _ => {} // Ignore unknown arguments for now
            }
        }

        // Set default directory to current working directory
        if session_config.directory.is_none() {
            session_config.directory =
                Some(Rc::new(std::env::current_dir().ok().unwrap()));
        }

        Self::with_config(config)
    }

    /// Creates a Shell with a custom configuration.
    pub fn with_config(config: Config) -> Self {
        Self {
            config,
            environment: Environment::new(),
            session: Rc::new(RefCell::new(Session::new())),
        }
    }

    /// Runs the shell with given input/output streams.
    pub fn run<R: Read, W: Write>(
        &mut self,
        input: R,
        output: W,
    ) -> ShellResult<()> {
        let mut reader = BufReader::new(input);
        let mut writer = BufWriter::new(output);

        if self.config.banner.unwrap() {
            writeln!(writer, "{}", Self::banner().as_str())?;
            writer.flush()?;
        }

        let mut line_buffer = String::new();
        let mut line_buffer_ready = false;
        let mut statement_buffer = String::new();
        let mut expected_output_buffer = String::new();

        loop {
            if line_buffer_ready {
                line_buffer_ready = false;
            } else {
                if self.config.echo.unwrap() {
                    write!(writer, "- ")?;
                    writer.flush()?;
                }

                line_buffer.clear();
                let bytes_read = reader.read_line(&mut line_buffer)?;
                if bytes_read == 0 {
                    return Ok(()); // EOF reached
                }
            }

            write!(writer, "{}", line_buffer)?;
            writer.flush()?;

            let line = line_buffer.trim_end();
            if line.is_empty() {
                continue;
            }

            // Add a line to the statement buffer
            statement_buffer.push_str(line);

            // If we have a complete statement (the last line ends with a
            // semicolon and is not inside a comment), execute it.
            if statement_buffer.ends_with(';')
                && comment_depth(statement_buffer.as_str()) == 0
            {
                // In idempotent mode, look ahead for output lines.
                if self.config.idempotent.unwrap() {
                    // Strip out lines that are not part of the statement
                    expected_output_buffer.clear();
                    loop {
                        if line_buffer_ready {
                            line_buffer_ready = false;
                        } else {
                            line_buffer.clear();
                            let bytes_read =
                                reader.read_line(&mut line_buffer)?;
                            if bytes_read == 0 {
                                break; // EOF reached; no more expected output
                            }
                        }
                        if !line_buffer.starts_with('>') {
                            line_buffer_ready = true;
                            break;
                        } else {
                            expected_output_buffer.push_str(&line_buffer);
                        }
                    }
                }

                // Remove the semicolon, then parse/execute the statement
                statement_buffer.pop();
                let result = self.process_statement(
                    &statement_buffer,
                    Some(&expected_output_buffer),
                );
                write!(writer, "{}", result.unwrap())?;
                writer.flush()?;
                statement_buffer.clear();
            } else {
                statement_buffer.push('\n');
            }

            writer.flush()?;
        }
    }

    fn banner() -> String {
        let rustc_version = version().unwrap();
        format!(
            "morel-rust version {} (rust version {})",
            env!("CARGO_PKG_VERSION"),
            rustc_version.to_string()
        )
    }

    /// Processes a single statement.
    fn process_statement(
        &mut self,
        code: &str,
        expected_output: Option<&str>,
    ) -> ShellResult<String> {
        // Try to parse the statement
        let statement = match parser::parse_statement(code) {
            Err(e) => {
                let string = e.to_string();
                println!("Failed to parse: {}, err {}", code, string);
                return Err(Error::Parse(format!(
                    "Failed to parse: {}, err {}",
                    code, string,
                )));
            }
            Ok(statement) => statement,
        };

        // Mode for just this statement.
        let mut statement_mode = self.config.mode.unwrap();

        // When we're in parse or validate mode, how do we execute a statement
        // to change mode? This block solves the conundrum.
        if matches!(self.config.mode, Some(Mode::Parse) | Some(Mode::Validate))
            && format!("{}", statement.kind.clone())
                == r#"set ("mode", "evaluate")"#
        {
            statement_mode = Mode::Evaluate;
        }

        if matches!(statement_mode, Mode::Parse | Mode::Validate)
            && expected_output.is_some()
            && !expected_output.unwrap().starts_with(">type")
        {
            // We are running in idempotent mode,
            // and we cannot yet evaluate expressions.
            // So, just say the expression returned what we expected.
            return Ok(expected_output.unwrap().to_string());
        }

        if matches!(statement_mode, Mode::Validate | Mode::Evaluate)
            && expected_output.is_some()
            && expected_output.unwrap().starts_with(">type")
        {
            // We are running in idempotent mode,
            // and we cannot yet evaluate expressions,
            // but we can deduce their type.
            let _expected_type =
                strip_prefix(">type ", expected_output.unwrap()).trim();
            let output = self.deduce_type(&statement);
            return match &output {
                Ok(s) => Ok(prefix_lines(">type", s.as_str())),
                Err(_) => output,
            };
        }

        // Successfully parsed, now evaluate
        let resolved = self.session.borrow_mut().deduce_type_inner(&statement);
        let output = self.evaluate_node(&resolved);
        match &output {
            Ok(s) => Ok(prefix_lines(">", s.as_str())),
            Err(_) => output,
        }
    }

    fn deduce_type(&mut self, node: &Statement) -> ShellResult<String> {
        let resolved = self.session.borrow_mut().deduce_type_inner(node);

        // For now, just unparse the node back to a string. In a full
        // implementation, this would actually evaluate the expression.
        let mut type_string = String::new();
        {
            let type_map = &resolved.type_map;
            let closure = |id: i32, name: &str| {
                let s = match type_map.get_type(id) {
                    Some(x) => x,
                    None => {
                        panic!("no type for id {} in {}", id, name);
                    }
                }
                .to_string();
                type_string.push_str(&format!("{} : {}\n", name, s));
            };
            resolved.decl.for_each_id_pat(closure);
        }
        let result = format!("{}", type_string);
        Ok(result)
    }

    /// Evaluates a parsed AST node.
    fn evaluate_node(&mut self, resolved: &Resolved) -> ShellResult<String> {
        let decl = resolver::resolve(resolved);

        let env = Env::empty();
        let mut map: BTreeMap<&str, (Type, Option<Val>)> = BTreeMap::new();
        library::populate_env(&mut map);
        let env2 = env.multi(&map);
        let decl2 = inliner::inline_decl(&env2, &decl);

        let compiled_statement = compiler::compile_statement(
            &resolved.type_map,
            &self.environment,
            &decl2,
        );
        let mut result = String::new();
        let mut bindings = Vec::new();
        // Collect effects from evaluation
        let mut effects = Vec::new();
        let session = self.session.borrow();
        compiled_statement.eval(
            &session,
            self,
            &self.environment,
            &mut effects,
            &resolved.type_map,
        );
        drop(session); // Release the borrow before applying effects

        // Apply effects
        for effect in effects {
            match effect {
                // lint: sort until '#}' where '##Effect::'
                Effect::AddBinding(binding) => {
                    bindings.push(binding);
                }
                Effect::EmitCode(code) => {
                    self.session.borrow_mut().code = Some(code);
                }
                Effect::EmitLine(line) => {
                    result.push_str(&line);
                    result.push('\n');
                }
                Effect::SetSessionProp(prop, val) => {
                    let mut session = self.session.borrow_mut();
                    let _ = session.set_prop(&prop, &val);
                }
                Effect::SetShellProp(prop, val) => {
                    let _ = self.set_prop(&prop, &val);
                }
                Effect::UnsetShellProp(prop) => {
                    let _ = self.unset_prop(&prop);
                }
            }
        }
        Ok(result)
    }

    /// Runs a script file.
    pub fn run_file<P: AsRef<Path>, W: Write>(
        &mut self,
        file_path: P,
        output: W,
    ) -> ShellResult<()> {
        let content =
            fs::read_to_string(&file_path).map_err(|e| Error::Io(e))?;

        // Create a cursor from the string content
        let cursor = Cursor::new(content.as_bytes());
        self.run(cursor, output)
    }

    /// Returns the current environment.
    pub fn environment(&self) -> &Environment {
        &self.environment
    }

    /// Returns the environment, mutable.
    pub fn environment_mut(&mut self) -> &mut Environment {
        &mut self.environment
    }
}

/// Returns the level comment nesting the end of the string.
///
/// Examples:
/// * Depth 0: `(* comment *)`
/// * Depth 1: `(* comment (* nested *)`
/// * Depth 1: `(*) line comment`
/// * Depth 0: `(*) line comment\n`
/// * Depth -1: `code; *)`
fn comment_depth(code: &str) -> i32 {
    let mut depth = 0;
    let mut buf = [' '; 3]; // cyclic buffer
    let n = 3;
    let mut i = n;
    let mut in_line_comment = false;
    for c in code.chars() {
        if buf[i % n] == '(' && c == '*' {
            // We say "(*", which is a block comment.
            // (It may turn out to be "(*)", a line comment.)
            depth += 1;
        } else if buf[i % n] == '*' && c == ')' {
            if buf[(i - 1) % n] == '(' {
                // We saw "(*)", which is a line comment.
                // We already increased the depth when we saw "(*".
                // Now we set a flag to decrease the depth when we next see a
                // newline.
                in_line_comment = true;
            } else {
                // We saw "*)", which closes a block comment, except if we're
                // in a line comment.
                if !in_line_comment {
                    depth -= 1;
                }
            }
        } else if c == '\n' && in_line_comment {
            depth -= 1;
            in_line_comment = false;
        }
        i += 1;
        buf[i % n] = c;
    }
    depth
}

pub enum MorelError {
    Runtime(BuiltInExn, Span),
    Other,
    // "Bind [nonexhaustive binding failure]"
    Bind,
}

impl Display for MorelError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            MorelError::Runtime(exn, loc) => {
                write!(f, "uncaught exception {}", exn)?;
                if let Some(explanation) = exn.explain() {
                    write!(f, " [{}]", explanation)?;
                }
                write!(f, "\n  raised at: {}", loc)
            }
            MorelError::Other => write!(f, "Other error"),
            MorelError::Bind => write!(f, "Bind error"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Cursor;

    #[test]
    fn test_main_creation() {
        let args = vec!["--echo".to_string()];
        let main = Shell::new(&args);
        assert!(main.config.echo.unwrap());
    }

    #[test]
    fn test_simple_expression() {
        let args = Vec::new();
        let mut main = Shell::new(&args);
        let input = "42;";
        let mut output = Vec::new();

        let cursor = Cursor::new(input.as_bytes());
        main.run(cursor, &mut output).unwrap();

        let output_str = String::from_utf8(output).unwrap();
        assert!(output_str.contains("42"));
    }

    #[test]
    fn test_environment() {
        let mut env = Environment::new();
        let val = Val::String("42".to_string());
        env.bind("x".to_string(), &val);
        assert_eq!(env.get("x"), Some(&val));
    }

    #[test]
    fn test_comment_depth() {
        assert_eq!(comment_depth("(* comment *)"), 0);
        assert_eq!(comment_depth("(* comment (* nested *)"), 1);
        assert_eq!(comment_depth("code; *)"), -1);
        assert_eq!(comment_depth("(* (* nested (* deeper *) *) *)"), 0);
        assert_eq!(comment_depth("(*) line comment"), 1);
        assert_eq!(comment_depth("(*) line comment\n"), 0);
        let s = r#"(* If a block comment
   contains a (*) comment close *) in a line comment
   then it is ignored. *)
"#;
        assert_eq!(comment_depth(s), 0);
    }
}
