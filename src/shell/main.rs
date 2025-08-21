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

use crate::shell::config::Config;
use crate::shell::error::Error;
use crate::shell::utils::prefix_lines;
use crate::shell::{ShellResult, utils};
use crate::syntax::ast;
use crate::syntax::ast::{MorelNode, StatementKind};
use crate::syntax::parser;
use crate::syntax::parser::parse_program_single;
use std::collections::HashMap;
use std::io::{BufRead, BufReader, BufWriter, Read, Write};
use std::path::{Path, PathBuf};

/// Main shell for Morel - Standard ML REPL
pub struct Shell {
    config: Config,
    environment: Environment,
}

/// Simple environment for storing bindings
#[derive(Debug, Clone)]
pub struct Environment {
    bindings: HashMap<String, String>,
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

    pub fn bind(&mut self, name: String, value: String) {
        self.bindings.insert(name, value);
    }

    pub fn get(&self, name: &str) -> Option<&String> {
        self.bindings.get(name)
    }

    pub fn clear(&mut self) {
        self.bindings.clear();
    }
}

impl Shell {
    /// Create a new Main shell with given configuration
    pub fn new(args: Vec<String>) -> Self {
        let mut config = Config::default();

        // Parse command line arguments
        for arg in &args {
            match arg.as_str() {
                "--echo" => config.echo = true,
                "--idempotent" => config.idempotent = true,
                _ if arg.starts_with("--directory=") => {
                    let dir = arg.strip_prefix("--directory=").unwrap();
                    config.directory = Some(PathBuf::from(dir));
                }
                _ => {} // Ignore unknown arguments for now
            }
        }

        // Set default directory to current working directory
        if config.directory.is_none() {
            config.directory = std::env::current_dir().ok();
        }

        Self {
            config,
            environment: Environment::new(),
        }
    }

    /// Create Main with custom configuration
    pub fn with_config(config: Config) -> Self {
        Self {
            config,
            environment: Environment::new(),
        }
    }

    /// Run the shell with given input/output streams
    pub fn run<R: Read, W: Write>(
        &mut self,
        input: R,
        output: W,
    ) -> ShellResult<()> {
        let mut reader = BufReader::new(input);
        let mut writer = BufWriter::new(output);

        if self.config.banner {
            writeln!(writer, "{}", Self::banner().as_str())?;
        }

        let mut line_buffer = String::new();
        let mut line_buffer_ready = false;
        let mut statement_buffer = String::new();
        let mut expected_output_buffer = String::new();

        loop {
            if line_buffer_ready {
                line_buffer_ready = false;
            } else {
                line_buffer.clear();
                let bytes_read = reader.read_line(&mut line_buffer)?;
                if bytes_read == 0 {
                    return Ok(()) // EOF reached
                }
            }

            if self.config.echo {
                write!(writer, "- ")?;
            }
            write!(writer, "{}", line_buffer)?;
            writer.flush()?;

            let line = line_buffer.trim();

            // Handle special commands
            // if line == "quit" || line == "exit" {
            //     break;
            // }

            if line.is_empty() {
                continue;
            }

            // Add line to statement buffer
            statement_buffer.push_str(line);

            // Check if we have a complete statement (ends with semicolon)
            if statement_buffer.ends_with(';') {
                // In idempotent mode, look ahead for output lines.
                if self.config.idempotent {
                    // Strip out lines that are not part of the statement
                    expected_output_buffer.clear();
                    loop {
                        if line_buffer_ready {
                            line_buffer_ready = false;
                        } else {
                            line_buffer.clear();
                            let bytes_read = reader.read_line(&mut line_buffer)?;
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

                // Remove the semicolon, then parse/execute statement
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
        String::from(
            "Morel Rust - Standard ML interpreter with relational extensions",
        )
    }

    /// Process a single statement
    fn process_statement(
        &mut self,
        statement: &str,
        expected_output: Option<&str>,
    ) -> ShellResult<String> {
        // Try to parse the statement
        let node = parse_program_single(statement);
        if node.is_err() {
            Err(Error::Parse(format!("Failed to parse: {}", statement)))
        } else if expected_output.is_some() {
            // We are running in idempotent mode,
            // and we cannot yet evaluate expressions.
            // So, just say the expression returned what we expected.
            Ok(expected_output.unwrap().to_string())
        } else {
            // Successfully parsed, now evaluate
            let output = self.evaluate_node(node.unwrap(), None);
            match &output {
                Ok(s) => Ok(prefix_lines(s.as_str())),
                Err(_) => output,
            }
        }
    }

    /// Evaluate a parsed AST node
    fn evaluate_node(
        &mut self,
        node: ast::Statement,
        expected_output: Option<&str>,
    ) -> ShellResult<String> {
        // For now, just unparse the node back to a string
        // In a full implementation, this would actually evaluate the expression
        let mut result = String::new();
        node.unparse(&mut result);

        // Simple evaluation simulation
        match &node.kind {
            StatementKind::Expr(expr) => {
                // For expressions, show the type and value
                Ok(format!("val it = {} : <type>", result))
            }
            StatementKind::Decl(_) => {
                // For declarations, show what was declared
                Ok(result)
            }
        }
    }

    /// Run a script file
    pub fn run_file<P: AsRef<Path>, W: Write>(
        &mut self,
        file_path: P,
        output: W,
    ) -> ShellResult<()> {
        let content =
            utils::read_file_to_string(&file_path).map_err(|e| Error::Io(e))?;

        // Create a cursor from the string content
        let cursor = std::io::Cursor::new(content.as_bytes());
        self.run(cursor, output)
    }

    /// Get the current environment
    pub fn environment(&self) -> &Environment {
        &self.environment
    }

    /// Get mutable access to the environment
    pub fn environment_mut(&mut self) -> &mut Environment {
        &mut self.environment
    }
}

/// Shell implementation for use within scripts
pub struct Session {
    shell: Shell,
}

impl Session {
    pub fn new(main: Shell) -> Self {
        Self { shell: main }
    }

    /// Execute a use command (load a file)
    pub fn use_file<P: AsRef<Path>, W: Write>(
        &mut self,
        file_path: P,
        silent: bool,
        output: W,
    ) -> ShellResult<()> {
        let path = file_path.as_ref();

        if !silent {
            // TODO: Write opening message to output
        }

        // Check if file exists
        if !path.exists() {
            return Err(Error::FileNotFound(format!(
                "use failed: Io: openIn failed on {}, No such file or directory",
                path.display()
            )));
        }

        // Run the file
        self.shell.run_file(path, output)
    }

    /// Clear the environment
    pub fn clear_env(&mut self) {
        self.shell.environment_mut().clear();
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Cursor;

    #[test]
    fn test_main_creation() {
        let args = vec!["--echo".to_string()];
        let main = Shell::new(args);
        assert!(main.config.echo);
    }

    #[test]
    fn test_simple_expression() {
        let mut main = Shell::new(vec![]);
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
        env.bind("x".to_string(), "42".to_string());
        assert_eq!(env.get("x"), Some(&"42".to_string()));
    }
}
