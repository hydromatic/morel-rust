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

//! End-to-end CLI tests: run the `morel` binary as a subprocess and
//! check stdout / exit status. Cargo populates `CARGO_BIN_EXE_morel`
//! with the path to the binary built for the current target.

use std::io::Write;
use std::process::{Command, Stdio};

/// Feeds `input` to the shell on stdin and returns its stdout.
fn pipe(input: &str) -> String {
    let bin = env!("CARGO_BIN_EXE_morel");
    let mut child = Command::new(bin)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::null())
        .spawn()
        .expect("failed to execute morel");
    child
        .stdin
        .take()
        .expect("no stdin")
        .write_all(input.as_bytes())
        .expect("failed to write stdin");
    let out = child.wait_with_output().expect("failed to wait");
    String::from_utf8(out.stdout).expect("non-utf8 stdout")
}

fn run(args: &[&str]) -> (String, i32) {
    let bin = env!("CARGO_BIN_EXE_morel");
    let out = Command::new(bin)
        .args(args)
        .output()
        .expect("failed to execute morel");
    let stdout = String::from_utf8(out.stdout).expect("non-utf8 stdout");
    let code = out.status.code().expect("no exit code");
    (stdout, code)
}

#[test]
fn dash_e_evaluates_expression() {
    let (out, code) = run(&["-e", "1 + 2"]);
    assert_eq!(code, 0, "expected exit 0, got {}: {}", code, out);
    assert!(
        out.contains("3 : int"),
        "expected '3 : int' in output, got: {}",
        out
    );
}

#[test]
fn long_eval_evaluates_expression() {
    let (out, code) = run(&["--eval", "5 * 6"]);
    assert_eq!(code, 0);
    assert!(
        out.contains("30 : int"),
        "expected '30 : int' in output, got: {}",
        out
    );
}

#[test]
fn long_eval_equals_evaluates_expression() {
    let (out, code) = run(&["--eval=10 - 4"]);
    assert_eq!(code, 0);
    assert!(
        out.contains("6 : int"),
        "expected '6 : int' in output, got: {}",
        out
    );
}

#[test]
fn dash_e_query_expression() {
    let (out, code) = run(&["-e", "from x in [1, 2, 3] yield x * 2"]);
    assert_eq!(code, 0);
    assert!(
        out.contains("[2,4,6]"),
        "expected '[2,4,6]' in output, got: {}",
        out
    );
}

#[test]
fn dash_e_without_argument_is_error() {
    let (_out, code) = run(&["-e"]);
    assert_ne!(code, 0, "expected non-zero exit code");
}

#[test]
fn long_eval_without_argument_is_error() {
    let (_out, code) = run(&["--eval"]);
    assert_ne!(code, 0, "expected non-zero exit code");
}

#[test]
fn help_mentions_eval_option() {
    let (out, code) = run(&["--help"]);
    assert_eq!(code, 0);
    assert!(
        out.contains("--eval"),
        "expected --help to mention --eval, got: {}",
        out
    );
    assert!(
        out.contains("-e"),
        "expected --help to mention -e, got: {}",
        out
    );
}

/// A line that holds a statement and then a comment holds a whole
/// statement: the comment must not swallow the line that follows.
#[test]
fn statement_followed_by_comment_does_not_lose_the_next_line() {
    let out = pipe("val a = 1; (* a comment *)\nval b = 2;\nb;\n");
    assert!(out.contains("val a = 1 : int"), "{}", out);
    assert!(out.contains("val b = 2 : int"), "{}", out);
    assert!(out.contains("val it = 2 : int"), "{}", out);
}

/// Two statements on one line are two statements.
#[test]
fn two_statements_on_one_line_both_run() {
    let out = pipe("val a = 1; val b = 2;\na + b;\n");
    assert!(out.contains("val a = 1 : int"), "{}", out);
    assert!(out.contains("val b = 2 : int"), "{}", out);
    assert!(out.contains("val it = 3 : int"), "{}", out);
}

/// ... but a semicolon inside a `let` does not end the statement.
#[test]
fn semicolons_inside_a_let_do_not_split_it() {
    let out = pipe("let val i = 0; val j = 1; in i + j end;\n");
    assert!(out.contains("val it = 1 : int"), "{}", out);
}

/// A statement may still span lines.
#[test]
fn statement_may_span_lines() {
    let out = pipe("let\n  val i = 0;\nin\n  i + 1\nend;\n");
    assert!(out.contains("val it = 1 : int"), "{}", out);
}

/// Input that never forms a statement is reported when it runs out,
/// rather than being silently dropped.
#[test]
fn unterminated_statement_is_reported_at_end_of_input() {
    let out = pipe("let val i = 0;\n");
    assert!(out.contains("Error"), "{}", out);
}

/// A trailing comment is not an unterminated statement.
#[test]
fn trailing_comment_is_not_an_error() {
    let out = pipe("1 + 1;\n(*) done\n");
    assert!(out.contains("val it = 2 : int"), "{}", out);
    assert!(!out.contains("Error"), "{}", out);
}
