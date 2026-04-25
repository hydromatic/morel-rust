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

use crate::compile::core::{Decl, Expr};
use crate::compile::inliner::Env;
use crate::compile::library::{BuiltInExn, BuiltInFunction};
use crate::compile::resolver;
use crate::compile::span::Span;
use crate::compile::type_env::{Binding, EmptyTypeEnv, FunTypeEnv, TypeEnv};
use crate::compile::type_resolver::Resolved;
use crate::compile::types::{PrimitiveType, Type};
use crate::compile::{compiler, inliner, library};
use crate::eval::code::Effect;
use crate::eval::link_table::LinkTable;
use crate::eval::session::Config as SessionConfig;
use crate::eval::session::Session;
use crate::eval::val::Val;
use crate::shell::ShellResult;
use crate::shell::config::Config;
use crate::shell::error::Error;
use crate::shell::output_matcher;
use crate::shell::prop::{Mode, Output, create_banner};
use crate::shell::utils::{prefix_lines, strip_prefix};
use crate::syntax::ast::Statement;
use crate::syntax::parser;
use std::cell::RefCell;
use std::collections::{BTreeMap, HashMap};
use std::env::current_dir;
use std::fmt::{self, Debug, Display, Formatter};
use std::fs;
use std::io::{BufRead, BufReader, BufWriter, Cursor, Read, Write};
use std::path::{Path, PathBuf};
use std::rc::Rc;

/// Counts the number of leading comment or blank lines in a Morel source
/// string.  Matches the line offset computed by morel-java's `parser.zero()`
/// (which sets `lineOffset = beginLine - 1` where `beginLine` is the line of
/// the first non-comment token).
///
/// Morel has two comment forms:
/// Returns true if `decl` is a top-level call to `Sys.plan` or
/// `Sys.planEx`. Used to skip storing the previous command's plan when
/// the user is asking about it; otherwise the stored plan would always
/// just be the most recent `Sys.plan*` call itself.
fn is_plan_or_plan_ex_call(decl: &Decl) -> bool {
    let Decl::NonRecVal(vb) = decl else {
        return false;
    };
    fn fn_is_plan(expr: &Expr) -> bool {
        if let Expr::Literal(_, Val::Fn(f)) = expr {
            matches!(f, BuiltInFunction::SysPlan | BuiltInFunction::SysPlanEx)
        } else {
            false
        }
    }
    if let Expr::Apply(_, fn_expr, _, _) = &vb.expr {
        fn_is_plan(fn_expr)
    } else {
        fn_is_plan(&vb.expr)
    }
}

/// * Line comment: `(*) text...` — starts with `(*)`, runs to end of line.
/// * Block comment: `(* text... *)` — may span lines and nest.
fn leading_comment_lines(code: &str) -> usize {
    let mut count = 0usize;
    let mut depth = 0usize; // nesting depth of block comments
    for line in code.lines() {
        let trimmed = line.trim();
        if depth > 0 {
            // Inside a block comment: scan for `*)` or `(*`.
            let mut s = trimmed;
            loop {
                if let Some(pos) = s.find("*)") {
                    depth -= 1;
                    s = &s[pos + 2..];
                    if depth == 0 {
                        // Comment closed mid-line. If the rest of the line is
                        // blank, count it; otherwise stop.
                        if s.trim().is_empty() {
                            count += 1;
                        }
                        break;
                    }
                } else if let Some(pos) = s.find("(*") {
                    depth += 1;
                    s = &s[pos + 2..];
                } else {
                    // Entire line is inside block comment.
                    count += 1;
                    break;
                }
            }
        } else if trimmed.is_empty() {
            count += 1;
        } else if trimmed.starts_with("(*)") {
            // Line comment — consumes whole line.
            count += 1;
        } else if trimmed.starts_with("(*") {
            // Block comment starting at depth 0. Scan the whole line to handle
            // inline comments like `(* foo *)` that open and close on the same
            // line.
            depth += 1;
            let mut s = trimmed.strip_prefix("(*").unwrap_or("");
            loop {
                if let Some(pos) = s.find("*)") {
                    depth -= 1;
                    s = &s[pos + 2..];
                    if depth == 0 {
                        // Comment closed on the same line. Count only if the
                        // remainder is blank (pure comment line).
                        if s.trim().is_empty() {
                            count += 1;
                        }
                        break;
                    }
                } else if let Some(pos) = s.find("(*") {
                    depth += 1;
                    s = &s[pos + 2..];
                } else {
                    // Comment continues onto subsequent lines.
                    count += 1;
                    break;
                }
            }
        } else {
            break;
        }
    }
    count
}

/// Main shell for Morel - Standard ML REPL.
pub struct Shell {
    pub(crate) config: Config,
    environment: Environment,
    session: Rc<RefCell<Session>>,
    /// Persistent table of compiled `Code` values referenced
    /// indirectly by recursive `fun` / `val rec` bindings. See
    /// [`crate::eval::link_table::LinkTable`] for the full
    /// rationale; in short, this table outlives any single
    /// statement so that recursive functions defined in one
    /// statement can still resolve their self-references when
    /// they are invoked from a later statement.
    pub(crate) link_table: RefCell<LinkTable>,
}

/// Simple environment for storing bindings.
#[derive(Clone, Debug)]
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

    /// Returns a new environment with the given bindings merged on top
    /// of `self`. New bindings shadow existing ones with the same name;
    /// any existing binding whose name is not mentioned in `bindings`
    /// is preserved. (Previously, `bind_all` returned an environment
    /// containing only the new bindings — silently dropping every
    /// outer binding — which broke any compilation step that walks
    /// into a let body or function body, since the recursive name
    /// would no longer be visible.)
    pub fn bind_all(&self, bindings: &[Binding]) -> Self {
        let mut env = self.clone();
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
                    Some(val.maybe_bool().ok_or_else(|| {
                        Error::Runtime(
                            "value for property must have type 'bool'"
                                .to_string(),
                        )
                    })?);
                Ok(())
            }
            "lineWidth" => {
                self.config.line_width =
                    Some(val.maybe_int().ok_or_else(|| {
                        Error::Runtime(
                            "value for property must have type 'int'"
                                .to_string(),
                        )
                    })?);
                Ok(())
            }
            "matchCoverageEnabled" => {
                self.session.borrow_mut().config.match_coverage_enabled =
                    Some(val.expect_bool());
                Ok(())
            }
            "mode" => {
                let s = val.maybe_string().ok_or_else(|| {
                    Error::Runtime(
                        "value for property must have type 'string'"
                            .to_string(),
                    )
                })?;
                self.config.mode =
                    Some(s.parse::<Mode>().map_err(Error::Runtime)?);
                Ok(())
            }
            "optionalInt" => {
                let v = val.maybe_int().ok_or_else(|| {
                    Error::Runtime(
                        "value for property must have type 'int'".to_string(),
                    )
                })?;
                self.config.optional_int = Some(v);
                self.session.borrow_mut().config.optional_int = Some(v);
                Ok(())
            }
            "output" => {
                let s = val.maybe_string().ok_or_else(|| {
                    Error::Runtime(
                        "value for property must have type 'string'"
                            .to_string(),
                    )
                })?;
                self.config.output =
                    Some(s.parse::<Output>().map_err(Error::Runtime)?);
                Ok(())
            }
            "printDepth" => {
                self.config.print_depth =
                    Some(val.maybe_int().ok_or_else(|| {
                        Error::Runtime(
                            "value for property must have type 'int'"
                                .to_string(),
                        )
                    })?);
                Ok(())
            }
            "printLength" => {
                self.config.print_length =
                    Some(val.maybe_int().ok_or_else(|| {
                        Error::Runtime(
                            "value for property must have type 'int'"
                                .to_string(),
                        )
                    })?);
                Ok(())
            }
            "stringDepth" => {
                self.config.string_depth =
                    Some(val.maybe_int().ok_or_else(|| {
                        Error::Runtime(
                            "value for property must have type 'int'"
                                .to_string(),
                        )
                    })?);
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
            "matchCoverageEnabled" => {
                self.session.borrow_mut().config.match_coverage_enabled = None;
                Ok(())
            }
            "mode" => {
                self.config.mode = None;
                Ok(())
            }
            "optionalInt" => {
                self.config.optional_int = None;
                self.session.borrow_mut().config.optional_int = None;
                Ok(())
            }
            "output" => {
                self.config.output = None;
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
                "--prompt" => config.prompt = Some(true),
                "--tty" => config.stdin_is_tty = Some(true),
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
                Some(Rc::new(current_dir().ok().unwrap()));
        }

        Self::with_config(config)
    }

    /// Creates a Shell with a custom configuration.
    pub fn with_config(config: Config) -> Self {
        Self {
            config,
            environment: Environment::new(),
            session: Rc::new(RefCell::new(Session::new())),
            link_table: RefCell::new(LinkTable::new()),
        }
    }

    /// Applies session configuration settings (script directory, etc.).
    pub fn apply_session_config(&mut self, config: &SessionConfig) {
        let mut session = self.session.borrow_mut();
        if let Some(dir) = &config.script_directory {
            session.config.script_directory = Some(dir.clone());
        }
        if let Some(dir) = &config.directory {
            session.config.directory = Some(dir.clone());
        }
    }

    /// Returns the value of a binding in the environment, if it exists.
    pub(crate) fn get_val(&self, name: &str) -> Option<&Val> {
        self.environment.get(name)
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
            writeln!(writer, "{}", create_banner().as_str())?;
            writer.flush()?;
        }

        let mut line_buffer = String::new();
        let mut line_buffer_ready = false;
        let mut statement_buffer = String::new();
        let mut expected_output_buffer = String::new();

        let prompt_enabled = self.config.prompt.unwrap_or(false);
        let echo_enabled = self.config.echo.unwrap_or(false);
        let idempotent = self.config.idempotent.unwrap_or(false);
        let stdin_is_tty = self.config.stdin_is_tty.unwrap_or(false);

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
            if statement_buffer.ends_with(';')
                && comment_depth(statement_buffer.as_str()) == 0
            {
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
                let raw = match self.process_statement(
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
                // or pretty-printer wrapping may differ.
                let to_write = if idempotent
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

    /// Processes a single statement.
    pub fn process_statement(
        &mut self,
        code: &str,
        expected_output: Option<&str>,
    ) -> ShellResult<String> {
        // Check if the statement contains ':t' on any line (type-only mode)
        // :t can appear on any line of a multi-line expression
        let (type_only, actual_code) = {
            let mut type_only_flag = false;
            let mut result = String::new();

            for line in code.lines() {
                let trimmed_line = line.trim_start();
                if trimmed_line.starts_with(":t") {
                    type_only_flag = true;
                    // Remove the :t prefix and any whitespace after it
                    let stripped =
                        trimmed_line.strip_prefix(":t").unwrap().trim_start();
                    result.push_str(stripped);
                } else {
                    result.push_str(line);
                }
                result.push('\n');
            }

            // Remove the trailing newline that we added
            if result.ends_with('\n') {
                result.pop();
            }

            (type_only_flag, result)
        };

        // Try to parse the statement
        let statement = match parser::parse_statement(&actual_code) {
            Err(e) => {
                let span = Span::from_line_col(&e.line_col);
                return Ok(format!(
                    "{} Error: syntax error\n  raised at: {}\n",
                    span, span
                ));
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
            && !type_only
        {
            // We are running in idempotent mode,
            // and we cannot yet evaluate expressions.
            // So, just say the expression returned what we expected.
            // Strip the "> " prefix; the run loop re-adds it in
            // idempotent mode.
            return Ok(strip_prefix("> ", expected_output.unwrap()));
        }

        let base_line = leading_comment_lines(&actual_code);

        if type_only {
            // We are running in type-only mode (via :t prefix).
            // Deduce the type without evaluating.
            let output = self.deduce_type(&statement);
            return match &output {
                Ok(s) => Ok(s.clone()),
                Err(Error::Compile(msg, span)) => {
                    let pest_span = span.to_pest_span();
                    let span2 = Span::from_pest_span(&pest_span, base_line);
                    Ok(format!(
                        "{} Error: {}\n  raised at: {}\n",
                        span2, msg, span2
                    ))
                }
                Err(_) => output,
            };
        }

        // Successfully parsed, now validate.
        let resolved =
            match self.session.borrow_mut().deduce_type_inner(&statement) {
                Ok(resolved) => resolved,
                Err(Error::Compile(message, span)) => {
                    let pest_span = span.to_pest_span();
                    let span2 = Span::from_pest_span(&pest_span, base_line);
                    let s = format!(
                        "{} Error: {}\n  raised at: {}\n",
                        span2.to_string(),
                        message,
                        span2.to_string()
                    );
                    return Ok(s);
                }
                Err(e) => return Err(e),
            };

        // Collect any type-checker warnings (e.g. non-alphabetical record
        // field order in 'order' expressions).
        let mut warning_prefix = String::new();
        for warning in &resolved.warnings {
            let pest_span = warning.span.to_pest_span();
            let span2 = Span::from_pest_span(&pest_span, resolved.base_line);
            warning_prefix.push_str(&format!(
                "{} Warning: {}\n  raised at: {}\n",
                span2, warning.message, span2
            ));
        }

        // Resolution succeeded but pattern coverage detected errors
        // (e.g. "match redundant"). Record the declaration for
        // `Sys.planEx` and return the error message; do not run the
        // case at runtime.
        if let Some((message, span)) = resolved.errors.first() {
            self.record_decls_for_planex(&resolved);
            let pest_span = span.to_pest_span();
            let span2 = Span::from_pest_span(&pest_span, resolved.base_line);
            let s = format!(
                "{} Error: {}\n  raised at: {}\n",
                span2, message, span2
            );
            return Ok(format!("{}{}", warning_prefix, s));
        }

        // Successfully parsed, now evaluate
        let output = self.evaluate_node(&resolved);
        match &output {
            Ok(s) => Ok(format!("{}{}", warning_prefix, s)),
            Err(_) => output,
        }
    }

    /// Stores the current command's pre- and post-inlining declarations
    /// in the session so that `Sys.planEx` can re-print them. Mirrors
    /// the storage logic in `evaluate_node`, but is a separate entry
    /// point used when evaluation is skipped due to a compile error.
    fn record_decls_for_planex(&mut self, resolved: &Resolved) {
        let (decl, resolve_errors) = resolver::resolve(resolved);
        if !resolve_errors.is_empty() {
            return;
        }
        let env = Env::empty();
        let mut map: BTreeMap<&str, (Type, Option<Val>)> = BTreeMap::new();
        self.environment.bindings.iter().for_each(|(k, v)| {
            map.insert(
                k,
                (Type::Primitive(PrimitiveType::Unit), Some(v.clone())),
            );
        });
        library::populate_env(&mut map);
        let env2 = env.multi(&map);
        let decl2 = inliner::inline_decl(&env2, &decl);
        if !is_plan_or_plan_ex_call(&decl2) {
            let mut session = self.session.borrow_mut();
            session.pre_inline_decl = Some(decl);
            session.post_inline_decl = Some(decl2);
        }
    }

    fn deduce_type(&mut self, node: &Statement) -> ShellResult<String> {
        let resolved = self.session.borrow_mut().deduce_type_inner(node)?;

        // For now, just unparse the node back to a string. In a full
        // implementation, this would actually evaluate the expression.
        let mut type_string = String::new();

        // Output warnings first.
        for warning in &resolved.warnings {
            let pest_span = warning.span.to_pest_span();
            let span2 = Span::from_pest_span(&pest_span, resolved.base_line);
            type_string.push_str(&format!(
                "{} Warning: {}\n  raised at: {}\n",
                span2, warning.message, span2
            ));
        }

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
                type_string.push_str(&format!("val {} : {}\n", name, s));
            };
            resolved.decl.for_each_id_pat(closure);
        }
        let result = format!("{}", type_string);
        Ok(result)
    }

    /// Evaluates a parsed AST node.
    fn evaluate_node(&mut self, resolved: &Resolved) -> ShellResult<String> {
        let (decl, resolve_errors) = resolver::resolve(resolved);
        if let Some((msg, span)) = resolve_errors.first() {
            return Ok(format!(
                "{} Error: {}\n  raised at: {}\n",
                span, msg, span
            ));
        }

        let env = Env::empty();
        let mut map: BTreeMap<&str, (Type, Option<Val>)> = BTreeMap::new();
        self.environment.bindings.iter().for_each(|(k, v)| {
            map.insert(
                k,
                (Type::Primitive(PrimitiveType::Unit), Some(v.clone())),
            );
        });
        library::populate_env(&mut map);
        let env2 = env.multi(&map);
        let decl2 = inliner::inline_decl(&env2, &decl);

        // Save the pre- and post-inlining declarations so that
        // `Sys.planEx` can re-print the previous command's plan at the
        // requested optimizer phase. Skip when the current command is
        // itself a `Sys.plan` or `Sys.planEx` call so it operates on the
        // user's last real command rather than on itself.
        if !is_plan_or_plan_ex_call(&decl2) {
            let mut session = self.session.borrow_mut();
            session.pre_inline_decl = Some(decl.clone());
            session.post_inline_decl = Some(decl2.clone());
        }

        let compiled_statement = {
            let mut link_table = self.link_table.borrow_mut();
            compiler::compile_statement(
                &resolved.type_map,
                &self.environment,
                &decl2,
                &mut link_table,
            )
        };
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
                Effect::ClearEnv => {
                    // Clear all user-defined bindings.
                    bindings.clear();
                    let mut session = self.session.borrow_mut();
                    session.type_bindings.clear();

                    // Reset type_env to initial state (FunTypeEnv).
                    let empty_type_env = EmptyTypeEnv {};
                    let type_env = FunTypeEnv {
                        parent: Rc::new(empty_type_env) as Rc<dyn TypeEnv>,
                    };
                    session.type_env = Rc::new(type_env) as Rc<dyn TypeEnv>;
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
                    if let Err(e) = self.set_prop(&prop, &val) {
                        return Ok(format!("{}\n", e));
                    }
                }
                Effect::UnsetShellProp(prop) => {
                    let _ = self.unset_prop(&prop);
                }
                Effect::UseFile(path, silent) => {
                    // Resolve the file path relative to the script
                    // directory.
                    let file_path = self.resolve_use_path(&path);
                    match self.execute_use_file(&file_path, silent) {
                        Ok(output) => {
                            if !silent {
                                result.push_str(&output);
                            }
                        }
                        Err(e) => {
                            if !silent {
                                result.push_str(&format!("{}\n", e));
                            }
                        }
                    }
                }
            }
        }

        // Add bindings to the runtime environment
        for binding in bindings {
            if let Some(value) = &binding.value {
                self.environment.bind(binding.id.name.clone(), value);
            }
        }

        // Commit type bindings AFTER evaluation, so that Sys.env()
        // during evaluation does not see the current statement's own
        // bindings (e.g. the implicit `it`).
        self.session.borrow_mut().commit_bindings(resolved);

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

    /// Executes a single command and writes the output.
    pub fn run_command<W: Write>(
        &mut self,
        command: &str,
        mut output: W,
    ) -> ShellResult<()> {
        // Remove trailing semicolon if present (process_statement
        // expects input without the semicolon).
        let command_without_semicolon = command
            .trim_end()
            .strip_suffix(';')
            .unwrap_or(command.trim_end());

        let result = self.process_statement(command_without_semicolon, None)?;

        write!(output, "{}", result)?;
        if !result.ends_with('\n') {
            writeln!(output)?;
        }
        Ok(())
    }

    /// Resolves a path from a `use` command relative to the script
    /// directory (if set), otherwise relative to the working directory.
    fn resolve_use_path(&self, path: &str) -> PathBuf {
        let session = self.session.borrow();
        if let Some(script_dir) = &session.config.script_directory {
            script_dir.join(path)
        } else if let Some(dir) = &session.config.directory {
            dir.join(path)
        } else {
            PathBuf::from(path)
        }
    }

    /// Reads a file and executes each statement in the current
    /// shell context, returning the combined output.
    fn execute_use_file(
        &mut self,
        file_path: &Path,
        silent: bool,
    ) -> ShellResult<String> {
        let content = fs::read_to_string(file_path).map_err(|_| {
            Error::FileNotFound(format!(
                "use failed: File not found: {}",
                file_path.display(),
            ))
        })?;
        // Save shell mode — the loaded file might change it (e.g.
        // set("mode", "validate")) but we don't want that to persist
        // after the use returns.
        let saved_mode = self.config.mode;
        let mut output = String::new();
        let mut statement_buffer = String::new();
        for line in content.lines() {
            // Skip expected-output lines (from .smli idempotent
            // format).
            if line.starts_with('>') {
                continue;
            }

            if !silent {
                // Echo the line (including comments).
                output.push_str(line);
                output.push('\n');
            }

            let trimmed = line.trim_end();
            if trimmed.is_empty() {
                continue;
            }
            statement_buffer.push_str(trimmed);
            if statement_buffer.ends_with(';')
                && comment_depth(&statement_buffer) == 0
            {
                // Remove the trailing semicolon.
                statement_buffer.pop();
                match self.process_statement(&statement_buffer, None) {
                    Ok(stmt_output) => {
                        if !silent {
                            output.push_str(&stmt_output);
                        }
                    }
                    Err(e) => {
                        if !silent {
                            output.push_str(&format!("{}\n", e));
                        }
                    }
                }
                statement_buffer.clear();
            } else {
                statement_buffer.push('\n');
            }
        }
        // Restore shell mode.
        self.config.mode = saved_mode;
        Ok(output)
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
/// * Depth 0: `"(*)" ^ "(*)"`  (parentheses inside strings are not comments)
fn comment_depth(code: &str) -> i32 {
    let mut depth = 0;
    let mut buf = [' '; 3]; // cyclic buffer
    let n = 3;
    let mut i = n;
    let mut in_line_comment = false;
    let mut in_string = false;
    let mut in_string_escape = false;
    for c in code.chars() {
        if in_string {
            // Inside a string literal: track escape sequences and closing
            // quote; do not interpret comment syntax.
            if in_string_escape {
                in_string_escape = false;
            } else if c == '\\' {
                in_string_escape = true;
            } else if c == '"' {
                in_string = false;
                buf = [' '; 3]; // reset look-back to avoid false positives
            }
            continue;
        }

        // Opening a string literal (only when not inside any comment).
        if c == '"' && depth == 0 && !in_line_comment {
            in_string = true;
            continue;
        }

        if buf[i % n] == '(' && c == '*' && !in_line_comment {
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

#[derive(Clone, PartialEq, Debug)]
pub enum MorelError {
    Runtime(BuiltInExn, Span),

    /// Surfaces a caller error with a custom message (e.g. "not a
    /// discrete type: real" raised by `Range.discreteSetOf`).
    /// Analogous to Java's `IllegalArgumentException`.
    IllegalArgument(String, Span),

    /// Advisory signal that a row sink has completed early and does not
    /// need more rows. Producers may honor this for performance or safely
    /// ignore it. Sinks returning EarlyReturn must be idempotent.
    EarlyReturn,

    Other,
}

impl Display for MorelError {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            MorelError::Runtime(exn, loc) => {
                write!(f, "uncaught exception {}", exn)?;
                if let Some(explanation) = exn.explain() {
                    write!(f, " [{}]", explanation)?;
                }
                write!(f, "\n  raised at: {}", loc)
            }
            MorelError::IllegalArgument(msg, loc) => {
                write!(f, "java.lang.IllegalArgumentException: {}", msg)?;
                write!(f, "\n  raised at: {}", loc)
            }
            MorelError::EarlyReturn => {
                write!(f, "EarlyReturn (internal signal)")
            }
            MorelError::Other => write!(f, "Other error"),
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

    /// Runs a simulated interactive session (no tty) and returns body lines
    /// (everything after the version banner line).
    fn run_interactive_piped(input: &str) -> Vec<String> {
        let args = vec!["--banner".to_string(), "--prompt".to_string()];
        let mut shell = Shell::new(&args);
        let mut output = Vec::new();
        shell
            .run(Cursor::new(input.as_bytes()), &mut output)
            .unwrap();
        let out = String::from_utf8(output).unwrap();
        let mut lines: Vec<String> =
            out.split('\n').map(|s| s.to_string()).collect();
        assert!(
            lines.first().map(|s| s.starts_with("morel-rust version"))
                == Some(true),
            "expected banner line, got: {:?}",
            lines.first()
        );
        lines.remove(0);
        lines
    }

    #[test]
    fn test_interactive_single_stmt() {
        let body = run_interactive_piped("val x = 1;\n");
        assert_eq!(body, vec!["- val x = 1 : int", "- ", ""]);
    }

    #[test]
    fn test_interactive_multi_stmt() {
        let body = run_interactive_piped("val x = 1;\nval y = 2;\n");
        // Each statement gets a '- ' prompt; no input echo; trailing '- '
        // before EOF.
        assert_eq!(
            body,
            vec!["- val x = 1 : int", "- val y = 2 : int", "- ", ""]
        );
    }

    #[test]
    fn test_interactive_multiline_expr() {
        // Multi-line expression in piped mode: SML-NJ shows no '= ' prompt
        // between continuation lines.
        let body = run_interactive_piped("1 +\n  2;\n");
        assert_eq!(body, vec!["- val it = 3 : int", "- ", ""]);
    }

    #[test]
    fn test_interactive_comment_only() {
        // Comment-only input is swallowed; only prompts remain.
        let body = run_interactive_piped("(* hi *)\n");
        // In piped mode, once statement buffer is non-empty we suppress
        // the continuation prompt, so we see a single '- ' prefix plus the
        // EOF-terminating newline.
        assert_eq!(body, vec!["- ", ""]);
    }

    #[test]
    fn test_interactive_no_bare_echo() {
        // The input line must NOT appear echoed back in the output:
        // the terminal (in real tty use) echoes, and piped mode matches
        // SML-NJ by not echoing either. This is the core fix for issue #36.
        let input = "val x = 42;\n";
        let body_joined = run_interactive_piped(input).join("\n");
        assert!(
            !body_joined.contains("val x = 42;"),
            "input line should not be echoed back, got: {}",
            body_joined
        );
        // But the evaluated result should still be present.
        assert!(body_joined.contains("val x = 42 : int"));
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
        // Parentheses inside string literals are not comments.
        assert_eq!(comment_depth(r#""(*)" ^ "(*)""#), 0);
        assert_eq!(comment_depth(r#""(*)" ^ "(*)""#), 0);
        assert_eq!(comment_depth(r#"val x = "(*) not a comment""#), 0);
        // Escaped quote inside a string does not end the string.
        assert_eq!(comment_depth(r#""a\"(*) not a comment\"b""#), 0);
        // A (*) line comment with (*fake block*) inside it:
        // the fake (*) should NOT increment depth; only the \n matters.
        assert_eq!(comment_depth("(*) line comment with (* fake\n"), 0);
        // Multi-line: expression ^ (*) line comment with fake (* \n ^ rest;
        assert_eq!(
            comment_depth("\"a\" ^ (*) line comment (* fake\n\"b\";\n"),
            0
        );
    }

    #[test]
    fn test_line_mode() {
        let mut shell = Shell::new(&[]);
        let mut result;

        let in_1 = "val x = 5\n\
            and y = 6\n";
        let out_1 = "val x = 5 : int\n\
            val y = 6 : int\n";
        result = shell.process_statement(in_1, None).unwrap();
        assert_eq!(result, out_1);

        let in_2 = "x + y\n";
        let out_2 = "val it = 11 : int\n";
        result = shell.process_statement(in_2, None).unwrap();
        assert_eq!(result, out_2);
    }
}
