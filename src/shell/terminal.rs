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

//! The interactive terminal front end, built on [rustyline]. It gives
//! the user Emacs/vi key bindings, up-arrow history recall, and history
//! that persists across sessions, then feeds each complete statement to
//! a [`Kernel`]. Used only when standard input is a terminal; piped and
//! scripted input goes through the
//! [`ScriptRunner`](super::runner::ScriptRunner) instead.
//!
//! It reads one line at a time, accumulating a statement until it is
//! complete (ends with `;`, not inside a comment), in the style of
//! SML/NJ: a fresh statement is prompted with `- ` and a continuation
//! line with `= `. The whole statement — however many lines — is added
//! to history as a single entry, so up-arrow recalls it as a unit.
//!
//! [rustyline]: https://crates.io/crates/rustyline

use crate::shell::ShellResult;
use crate::shell::error::Error;
use crate::shell::kernel::Kernel;
use crate::shell::prop::create_banner;
use crate::shell::statement::is_complete;
use rustyline::Editor;
use rustyline::error::ReadlineError;
use rustyline::history::FileHistory;
use std::env;
use std::fs;
use std::mem;
use std::path::PathBuf;

/// The prompt for the next input line: `- ` when starting a fresh
/// statement (the buffer is empty) and `= ` when continuing an
/// incomplete one, matching SML/NJ.
fn prompt(buffer: &str) -> &'static str {
    if buffer.is_empty() { "- " } else { "= " }
}

/// The result of feeding one input line into a statement buffer.
enum Submit {
    /// A complete statement is ready. `statement` is the full text (for
    /// history); `code` is the same text without the trailing `;`, ready
    /// for the kernel.
    Ready { statement: String, code: String },
    /// Nothing to run yet: the line was blank, or the statement is still
    /// incomplete, so keep reading.
    Pending,
}

/// Feeds one input `line` into `buffer`. A blank line is ignored (the
/// statement in progress, if any, is untouched). Otherwise the line is
/// appended; if that completes the statement the buffer is taken and
/// returned, ready to run.
fn accept_line(buffer: &mut String, line: &str) -> Submit {
    let line = line.trim_end();
    if line.is_empty() {
        return Submit::Pending;
    }
    if !buffer.is_empty() {
        buffer.push('\n');
    }
    buffer.push_str(line);
    if is_complete(buffer) {
        let statement = mem::take(buffer);
        // is_complete guarantees a trailing ';'; strip it for the kernel.
        let code = statement
            .strip_suffix(';')
            .unwrap_or(&statement)
            .to_string();
        Submit::Ready { statement, code }
    } else {
        Submit::Pending
    }
}

/// The interactive terminal shell: a rustyline editor driving a
/// [`Kernel`].
pub struct Shell<'a> {
    kernel: &'a mut Kernel,
}

impl<'a> Shell<'a> {
    /// Creates a terminal shell that drives `kernel`.
    pub fn new(kernel: &'a mut Kernel) -> Self {
        Self { kernel }
    }

    /// Returns the path of the persistent history file
    /// (`~/.morel/history-rust`), or `None` if the home directory cannot be
    /// determined (in which case history is simply not persisted). The file
    /// name distinguishes it from Morel-Java's `~/.morel/history`, whose
    /// format differs.
    fn history_path() -> Option<PathBuf> {
        env::var_os("HOME")
            .map(|h| PathBuf::from(h).join(".morel").join("history-rust"))
    }

    /// Runs the read-eval-print loop until end-of-file (Ctrl-D).
    pub fn run(&mut self) -> ShellResult<()> {
        if self.kernel.config.banner.unwrap_or(false) {
            println!("{}", create_banner());
        }

        let mut editor: Editor<(), FileHistory> =
            Editor::new().map_err(|e| Error::Runtime(e.to_string()))?;

        let history_path = Self::history_path();
        if let Some(path) = &history_path {
            // Create the `~/.morel` directory; warn (rather than fail) if we
            // cannot, in which case history is not persisted this session.
            if let Some(dir) = path.parent()
                && let Err(e) = fs::create_dir_all(dir)
            {
                eprintln!("Warning: cannot create {}: {}", dir.display(), e);
            }
            // A missing history file on first run is not an error.
            let _ = editor.load_history(path);
        }

        // Accumulates the lines of the statement currently being entered.
        let mut buffer = String::new();
        loop {
            match editor.readline(prompt(&buffer)) {
                Ok(line) => match accept_line(&mut buffer, &line) {
                    Submit::Ready { statement, code } => {
                        // Record the whole (possibly multi-line) statement as
                        // one history entry so up-arrow recalls it as a unit.
                        let _ = editor.add_history_entry(statement);
                        let output =
                            match self.kernel.process_statement(&code, None) {
                                Ok(s) => s,
                                Err(e) => format!("{}\n", e),
                            };
                        print!("{}", output);
                        if !output.ends_with('\n') {
                            println!();
                        }
                    }
                    Submit::Pending => {}
                },
                // Ctrl-C: abandon the statement in progress and start over.
                Err(ReadlineError::Interrupted) => buffer.clear(),
                // Ctrl-D: end the session.
                Err(ReadlineError::Eof) => break,
                Err(e) => return Err(Error::Runtime(e.to_string())),
            }
        }

        if let Some(path) = &history_path {
            let _ = editor.save_history(path);
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_prompt_is_dash_when_fresh_and_equals_when_continuing() {
        // A fresh (empty) buffer prompts with '- '.
        assert_eq!(prompt(""), "- ");
        // An incomplete statement in the buffer prompts with '= '.
        assert_eq!(prompt("1 +"), "= ");
        assert_eq!(prompt("val x ="), "= ");
    }

    #[test]
    fn test_incomplete_line_continues_with_equals_prompt() {
        let mut buffer = String::new();
        assert_eq!(prompt(&buffer), "- ");

        // Typing "1 +" leaves the statement incomplete: keep reading, and
        // the next line is prompted with '= '.
        assert!(matches!(accept_line(&mut buffer, "1 +"), Submit::Pending));
        assert_eq!(prompt(&buffer), "= ");

        // The continuation line ends with ';', completing the statement.
        match accept_line(&mut buffer, "2;") {
            Submit::Ready { statement, code } => {
                assert_eq!(statement, "1 +\n2;");
                assert_eq!(code, "1 +\n2");
            }
            Submit::Pending => panic!("expected a complete statement"),
        }
        // The buffer is drained, so the next prompt is '- ' again.
        assert_eq!(prompt(&buffer), "- ");
    }

    #[test]
    fn test_empty_line_keeps_dash_prompt() {
        let mut buffer = String::new();
        // An empty line at a fresh prompt is ignored; the prompt stays '- '.
        assert!(matches!(accept_line(&mut buffer, ""), Submit::Pending));
        assert_eq!(prompt(&buffer), "- ");
        // Whitespace-only lines are treated the same.
        assert!(matches!(accept_line(&mut buffer, "   "), Submit::Pending));
        assert_eq!(prompt(&buffer), "- ");
    }

    #[test]
    fn test_single_line_statement_completes_immediately() {
        let mut buffer = String::new();
        match accept_line(&mut buffer, "1 + 2;") {
            Submit::Ready { statement, code } => {
                assert_eq!(statement, "1 + 2;");
                assert_eq!(code, "1 + 2");
            }
            Submit::Pending => panic!("expected a complete statement"),
        }
        assert_eq!(prompt(&buffer), "- ");
    }

    #[test]
    fn test_semicolon_inside_comment_is_not_complete() {
        let mut buffer = String::new();
        // The ';' is inside an unterminated block comment, so the statement
        // is not complete and continues with '= '.
        assert!(matches!(
            accept_line(&mut buffer, "(* a ;"),
            Submit::Pending
        ));
        assert_eq!(prompt(&buffer), "= ");
        // Closing the comment and terminating completes it.
        match accept_line(&mut buffer, "*) 1;") {
            Submit::Ready { code, .. } => assert_eq!(code, "(* a ;\n*) 1"),
            Submit::Pending => panic!("expected a complete statement"),
        }
    }
}
