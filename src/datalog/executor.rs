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

//! Orchestrator for `Datalog.execute`. Mirrors morel-java's
//! `DatalogEvaluator`.
//!
//! Pipeline: parse → analyze → translate → run translated Morel source
//! in a fresh `Shell` → wrap last binding's value as `Val::Variant`.
//!
//! A fresh `Shell` is used per call so the inner program's bindings,
//! type bindings, and overload state stay isolated from the outer
//! session that triggered the `Datalog.execute` call. The morel-java
//! implementation calls back into the same compile pipeline; in
//! morel-rust the borrow chain through `RefCell<Session>` makes
//! re-entry impractical, so we run in a sibling shell instead.

use std::collections::HashMap;
use std::fs;
use std::path::{Path, PathBuf};

use crate::compile::types::{PrimitiveType, Type};
use crate::datalog::ast::{
    Atom, DatalogType, Declaration, Fact, Program, Statement, Term,
};
use crate::datalog::error::DatalogError;
use crate::datalog::{analyze, parse, translate};
use crate::eval::val::Val;
use crate::eval::variant::variant_of;
use crate::shell::main::Shell;

/// Runs a Datalog program and returns its output wrapped as a
/// `Val::Variant`. On parse, analysis, or runtime failure, returns a
/// variant of type `string` whose value is the error message.
///
/// `base_dir` is the directory used to resolve `.input` file paths
/// (typically the outer session's working directory).
pub fn execute(source: &str, base_dir: Option<&Path>) -> Val {
    match compile_and_run(source, base_dir) {
        Ok((ty, val)) => variant_of(ty, val),
        Err(msg) => error_variant(&msg),
    }
}

/// Validates a Datalog program. Returns a Morel-style rendering of
/// the result type on success (e.g. `"{edge:{x:int, y:int} list}"`),
/// or an error message starting with `"Parse error: "` /
/// `"Compilation error: "` on failure. Mirrors morel-java's
/// `Datalog.validate : string -> string`.
pub fn validate(source: &str, base_dir: Option<&Path>) -> String {
    match compile_and_run(source, base_dir) {
        Ok((ty, _)) => format!("{}", ty),
        Err(msg) => msg,
    }
}

/// Shared pipeline for `execute` and `validate`: parse → load input
/// files → analyze → translate → run translated Morel in a fresh
/// shell → return the last binding's `(type, value)`.
fn compile_and_run(
    source: &str,
    base_dir: Option<&Path>,
) -> Result<(Type, Val), String> {
    let mut ast = match parse(source) {
        Ok(a) => a,
        Err(DatalogError::Parse(msg)) => {
            return Err(format!("Parse error: {}", msg));
        }
        Err(e) => return Err(format!("Compilation error: {}", e)),
    };
    if let Err(e) = load_input_files(&mut ast, base_dir) {
        let msg = match e {
            DatalogError::Analysis(m) => m,
            other => format!("{}", other),
        };
        return Err(format!("Compilation error: {}", msg));
    }
    if let Err(e) = analyze(&ast) {
        let msg = match e {
            DatalogError::Analysis(m) => m,
            other => format!("{}", other),
        };
        return Err(format!("Compilation error: {}", msg));
    }
    let morel_source = translate(&ast);

    let mut shell = Shell::new(&[]);
    if let Err(e) = shell.process_statement(&morel_source, None) {
        return Err(format!(
            "Error executing Morel translation: {:?}\n\
             Generated Morel code:\n{}",
            e, morel_source
        ));
    }

    // Pull the last binding (`it` for an expression). The Datalog
    // translator always emits a `let ... in <expr> end` whose top-level
    // value lands in `it`; an empty program (no facts/rules and no
    // .output) emits `()` which still binds `it`.
    let value = shell.get_val("it").cloned().unwrap_or(Val::Unit);
    let result_type = shell
        .session_borrow()
        .type_bindings
        .get("it")
        .map_or(Type::Primitive(PrimitiveType::Unit), |(t, _)| t.clone());
    Ok((result_type, value))
}

fn error_variant(msg: &str) -> Val {
    variant_of(
        Type::Primitive(PrimitiveType::String),
        Val::String(msg.to_string()),
    )
}

/// For each `.input` directive whose relation has a declaration,
/// reads the corresponding CSV file and injects synthetic `Fact`
/// statements into the program. Mirrors morel-java's
/// `DatalogEvaluator.loadInputFiles`.
///
/// Each row of the CSV becomes one fact; column types are taken from
/// the declaration's parameters. The first row is treated as a header
/// when its column count matches the declaration arity AND every
/// column name matches a parameter name (case-sensitive). Otherwise
/// the file is treated as headerless and every row produces a fact.
fn load_input_files(
    ast: &mut Program,
    base_dir: Option<&Path>,
) -> Result<(), DatalogError> {
    let inputs = ast.inputs();
    if inputs.is_empty() {
        return Ok(());
    }

    // Snapshot declarations so we can drop the borrow on `ast`.
    let decl_map: HashMap<String, Declaration> = ast
        .declarations()
        .iter()
        .map(|(k, v)| ((*k).to_string(), (*v).clone()))
        .collect();

    let mut new_facts: Vec<Statement> = Vec::new();
    for input in &inputs {
        let Some(decl) = decl_map.get(&input.relation) else {
            // Caught later by analyze(); skip here so we surface the
            // canonical "Relation 'X' used in .input but not declared"
            // message rather than a file-not-found.
            continue;
        };

        let file_name = input.effective_file_name();
        let path: PathBuf = match base_dir {
            Some(dir) => dir.join(&file_name),
            None => PathBuf::from(&file_name),
        };
        let content = fs::read_to_string(&path).map_err(|_| {
            DatalogError::Analysis(format!(
                "Input file not found: {} (resolved to {})",
                file_name,
                path.display()
            ))
        })?;

        for fact in csv_rows_to_facts(&content, decl)? {
            new_facts.push(Statement::Fact(fact));
        }
    }

    ast.statements.extend(new_facts);
    Ok(())
}

/// Parses CSV text and turns each row into a `Fact` for `decl`.
/// Skips a leading header row when the column count matches and every
/// column matches a declaration parameter name.
fn csv_rows_to_facts(
    content: &str,
    decl: &Declaration,
) -> Result<Vec<Fact>, DatalogError> {
    let arity = decl.arity();
    let mut rows: Vec<Vec<String>> = Vec::new();
    for line in content.lines() {
        if line.is_empty() {
            continue;
        }
        rows.push(parse_csv_line(line));
    }
    if rows.is_empty() {
        return Ok(Vec::new());
    }

    // Detect a header row: column count matches arity and each entry
    // is the name of a declaration parameter (optionally suffixed with
    // `:type`, as morel-java's CSV files use, e.g. `deptno:int`).
    let header_present = rows[0].len() == arity
        && rows[0].iter().all(|cell| {
            let bare = cell.split(':').next().unwrap_or(cell);
            decl.params.iter().any(|p| p.name == bare)
        });
    let data_rows = if header_present {
        &rows[1..]
    } else {
        &rows[..]
    };

    let mut facts = Vec::with_capacity(data_rows.len());
    for (i, row) in data_rows.iter().enumerate() {
        if row.len() != arity {
            return Err(DatalogError::Analysis(format!(
                "Row {} of input file for '{}' has {} columns, expected {}",
                i + if header_present { 2 } else { 1 },
                decl.name,
                row.len(),
                arity
            )));
        }
        let mut terms: Vec<Term> = Vec::with_capacity(arity);
        for (j, cell) in row.iter().enumerate() {
            terms.push(match decl.params[j].ty {
                DatalogType::Int => {
                    let n: i64 = cell.parse().map_err(|_| {
                        DatalogError::Analysis(format!(
                            "Cannot parse '{}' as int for column '{}' of '{}'",
                            cell, decl.params[j].name, decl.name
                        ))
                    })?;
                    Term::IntConst(n)
                }
                DatalogType::String => {
                    Term::StringConst(strip_csv_quotes(cell))
                }
            });
        }
        facts.push(Fact {
            atom: Atom {
                name: decl.name.clone(),
                terms,
            },
        });
    }
    Ok(facts)
}

/// Strips matching surrounding `'…'` (morel-java CSV convention) or
/// `"…"` quotes from a cell. Leaves unquoted cells unchanged.
fn strip_csv_quotes(cell: &str) -> String {
    let bytes = cell.as_bytes();
    if bytes.len() >= 2
        && ((bytes[0] == b'\'' && bytes[bytes.len() - 1] == b'\'')
            || (bytes[0] == b'"' && bytes[bytes.len() - 1] == b'"'))
    {
        cell[1..cell.len() - 1].to_string()
    } else {
        cell.to_string()
    }
}

/// Minimal CSV line splitter. Handles double-quoted fields with `""`
/// escaping for an embedded quote. Does not handle embedded newlines
/// inside quoted fields (the `.input` files we ship never use them).
fn parse_csv_line(line: &str) -> Vec<String> {
    let mut out = Vec::new();
    let mut cur = String::new();
    let mut chars = line.chars().peekable();
    let mut in_quotes = false;
    while let Some(c) = chars.next() {
        match (c, in_quotes) {
            ('"', true) => {
                if chars.peek() == Some(&'"') {
                    cur.push('"');
                    chars.next();
                } else {
                    in_quotes = false;
                }
            }
            ('"', false) if cur.is_empty() => {
                in_quotes = true;
            }
            (',', false) => {
                out.push(std::mem::take(&mut cur));
            }
            _ => cur.push(c),
        }
    }
    out.push(cur);
    out
}
