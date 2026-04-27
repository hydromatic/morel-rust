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
//! check stdout / exit status. Cargo populates `CARGO_BIN_EXE_main`
//! with the path to the binary built for the current target.

use std::process::Command;

fn run(args: &[&str]) -> (String, i32) {
    let bin = env!("CARGO_BIN_EXE_main");
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
