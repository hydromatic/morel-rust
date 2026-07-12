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

//! The line-oriented driver for a [`Kernel`]: it reads a byte stream,
//! assembles statements, feeds each to the shell, and writes the
//! results. This is the path used for piped stdin, `.smli` scripts, and
//! `use`-file execution — everything except the interactive terminal.
//! Prompting, echo, and the idempotent `>`-lookahead / output-matching
//! live here; statement execution lives on the [`Kernel`].

use crate::shell::error::Error;
use crate::shell::kernel::Kernel;
use crate::shell::prop::create_banner;
use crate::shell::statement::{comment_depth, is_complete};
use crate::shell::utils::{prefix_lines, strip_prefix};
use crate::shell::{ShellResult, output_matcher};
use std::fs;
use std::io::{BufRead, BufReader, BufWriter, Cursor, Read, Write};
use std::path::Path;

/// Drives a [`Kernel`] over a stream of input lines, producing a
/// transcript of results. Borrows the shell for the duration of a run.
pub struct ScriptRunner<'a> {
    kernel: &'a mut Kernel,
}

impl<'a> ScriptRunner<'a> {
    /// Creates a runner that drives `kernel`.
    pub fn new(kernel: &'a mut Kernel) -> Self {
        Self { kernel }
    }

    /// Runs the shell with given input/output streams.
    pub fn run<R: Read, W: Write>(
        &mut self,
        input: R,
        output: W,
    ) -> ShellResult<()> {
        let mut reader = BufReader::new(input);
        let mut writer = BufWriter::new(output);

        if self.kernel.config.banner.unwrap() {
            writeln!(writer, "{}", create_banner().as_str())?;
            writer.flush()?;
        }

        let mut line_buffer = String::new();
        let mut line_buffer_ready = false;
        let mut statement_buffer = String::new();
        let mut expected_output_buffer = String::new();

        let prompt_enabled = self.kernel.config.prompt.unwrap_or(false);
        let echo_enabled = self.kernel.config.echo.unwrap_or(false);
        let idempotent = self.kernel.config.idempotent.unwrap_or(false);
        let stdin_is_tty = self.kernel.config.stdin_is_tty.unwrap_or(false);

        loop {
            if line_buffer_ready {
                line_buffer_ready = false;
            } else {
                if prompt_enabled {
                    // Prompt style matches SML-NJ:
                    //   tty + fresh statement: '- '
                    //   tty + continuation   : '= '
                    //   pipe + fresh statement: '- '
                    //   pipe + continuation  : (nothing; SML-NJ suppresses)
                    let continuation = !statement_buffer.is_empty()
                        || comment_depth(&statement_buffer) > 0;
                    if !continuation {
                        write!(writer, "- ")?;
                        writer.flush()?;
                    } else if stdin_is_tty {
                        write!(writer, "= ")?;
                        writer.flush()?;
                    }
                }

                line_buffer.clear();
                let bytes_read = reader.read_line(&mut line_buffer)?;
                if bytes_read == 0 {
                    // Terminate the dangling prompt so the caller's output
                    // (e.g. "Goodbye!") starts on a new line.
                    if prompt_enabled {
                        writeln!(writer)?;
                        writer.flush()?;
                    }
                    return Ok(()); // EOF reached
                }
            }

            if echo_enabled {
                write!(writer, "{}", line_buffer)?;
                writer.flush()?;
            }

            let line = line_buffer.trim_end();
            if line.is_empty() {
                continue;
            }

            // Add a line to the statement buffer
            statement_buffer.push_str(line);

            // If we have a complete statement (the last line ends with a
            // semicolon and is not inside a comment), execute it.
            if is_complete(&statement_buffer) {
                // In idempotent mode, look ahead for output lines.
                if idempotent {
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
                let raw = match self.kernel.process_statement(
                    &statement_buffer,
                    Some(&expected_output_buffer),
                ) {
                    Ok(s) => s,
                    Err(e) => format!("{}\n", e),
                };
                // In idempotent mode, if the actual output is
                // semantically equivalent to the expected output
                // (modulo whitespace and bag reordering), emit the
                // expected output verbatim so the .smli file stays
                // idempotent across runs where bag iteration order
                // or pretty-printer wrapping may differ. The
                // 'matchStrict' property disables this, so that exact
                // formatting (e.g. pretty-printing) can be tested.
                let match_strict =
                    self.kernel.config.match_strict.unwrap_or(false);
                let to_write = if idempotent
                    && !match_strict
                    && !expected_output_buffer.is_empty()
                    && !raw.is_empty()
                {
                    let expected_stripped =
                        strip_prefix("> ", &expected_output_buffer);
                    // The output line is "val ... : TYPE" but we
                    // have the actual result from process_statement
                    // already stripped of "> ". Compare as whole
                    // output lines.
                    let actual_line = raw.trim_end_matches('\n');
                    let expected_line =
                        expected_stripped.trim_end_matches('\n');
                    if output_matcher::equivalent(actual_line, expected_line) {
                        prefix_lines(">", &expected_stripped)
                    } else {
                        prefix_lines(">", &raw)
                    }
                } else if idempotent {
                    prefix_lines(">", &raw)
                } else {
                    raw
                };
                write!(writer, "{}", to_write)?;
                writer.flush()?;
                statement_buffer.clear();
            } else {
                statement_buffer.push('\n');
            }

            writer.flush()?;
        }
    }

    /// Reads a file and runs its contents through [`run`](Self::run).
    pub fn run_file<P: AsRef<Path>, W: Write>(
        &mut self,
        file_path: P,
        output: W,
    ) -> ShellResult<()> {
        let content = fs::read_to_string(&file_path).map_err(Error::Io)?;

        // Create a cursor from the string content
        let cursor = Cursor::new(content.as_bytes());
        self.run(cursor, output)
    }
}
