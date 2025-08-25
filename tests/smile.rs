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

use morel::shell::ScriptTest;

/// Runs an idempotent script as a test.
fn run_script(file_name: &str) {
    let shell = ScriptTest::default();
    let result = shell.run(file_name);
    result.expect("should work");
}

#[test]
fn bag() {
    run_script("tests/script/bag.smli");
}

#[test]
fn blog() {
    run_script("tests/script/blog.smli");
}

#[test]
fn built_in() {
    run_script("tests/script/builtIn.smli");
}

#[test]
fn closure() {
    run_script("tests/script/closure.smli");
}

#[test]
fn datatype() {
    run_script("tests/script/datatype.smli");
}

#[test]
fn dummy() {
    run_script("tests/script/dummy.smli");
}

#[test]
fn file() {
    run_script("tests/script/file.smli");
}

#[test]
fn fixed_point() {
    run_script("tests/script/fixedPoint.smli");
}

#[test]
fn foreign() {
    run_script("tests/script/foreign.smli");
}

#[test]
fn hybrid() {
    run_script("tests/script/hybrid.smli");
}

#[test]
fn idempotent() {
    run_script("tests/script/idempotent.smli");
}

#[test]
fn logic() {
    run_script("tests/script/logic.smli");
}

#[test]
fn match_test() {
    run_script("tests/script/match.smli");
}

#[test]
fn misc() {
    run_script("tests/script/misc.smli");
}

#[test]
fn overload() {
    run_script("tests/script/overload.smli");
}

#[test]
fn pretty() {
    run_script("tests/script/pretty.smli");
}

#[test]
fn regex_example() {
    run_script("tests/script/regex-example.smli");
}

#[test]
fn relational() {
    run_script("tests/script/relational.smli");
}

#[test]
fn scott() {
    run_script("tests/script/scott.smli");
}

#[test]
fn simple() {
    run_script("tests/script/simple.smli");
}

#[test]
fn such_that() {
    run_script("tests/script/suchThat.smli");
}

#[test]
fn type_alias() {
    run_script("tests/script/type-alias.smli");
}

#[test]
fn type_() {
    run_script("tests/script/type.smli");
}

#[test]
fn wordle() {
    run_script("tests/script/wordle.smli");
}
