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

// lint: sort until 'End smile.rs' where '^fn '

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
    run_script("tests/script/built-in.smli");
}

#[test]
fn built_in_bag() {
    run_script("tests/script/built-in/bag.smli");
}

#[test]
fn built_in_bool() {
    run_script("tests/script/built-in/bool.smli");
}

#[test]
fn built_in_char() {
    run_script("tests/script/built-in/char.smli");
}

#[test]
fn built_in_date() {
    run_script("tests/script/built-in/date.smli");
}

#[test]
fn built_in_either() {
    run_script("tests/script/built-in/either.smli");
}

#[test]
fn built_in_fn() {
    run_script("tests/script/built-in/fn.smli");
}

#[test]
fn built_in_general() {
    run_script("tests/script/built-in/general.smli");
}

#[test]
fn built_in_int() {
    run_script("tests/script/built-in/int.smli");
}

#[test]
fn built_in_interact() {
    run_script("tests/script/built-in/interact.smli");
}

#[test]
fn built_in_list() {
    run_script("tests/script/built-in/list.smli");
}

#[test]
fn built_in_list_pair() {
    run_script("tests/script/built-in/list-pair.smli");
}

#[test]
fn built_in_math() {
    run_script("tests/script/built-in/math.smli");
}

#[test]
fn built_in_option() {
    run_script("tests/script/built-in/option.smli");
}

#[test]
fn built_in_order() {
    run_script("tests/script/built-in/order.smli");
}

#[test]
fn built_in_real() {
    run_script("tests/script/built-in/real.smli");
}

#[test]
fn built_in_relational() {
    run_script("tests/script/built-in/relational.smli");
}

#[test]
fn built_in_string() {
    run_script("tests/script/built-in/string.smli");
}

#[test]
fn built_in_sys() {
    run_script("tests/script/built-in/sys.smli");
}

#[test]
fn built_in_time() {
    run_script("tests/script/built-in/time.smli");
}

#[test]
fn built_in_vector() {
    run_script("tests/script/built-in/vector.smli");
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
    run_script("tests/script/fixed-point.smli");
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
fn optimize() {
    run_script("tests/script/optimize.smli");
}

#[test]
fn overload() {
    run_script("tests/script/overload.smli");
}

/// Postfix method-call syntax (hydromatic/morel#346).
#[test]
fn postfix() {
    run_script("tests/script/postfix.smli");
}

#[test]
fn pretty() {
    run_script("tests/script/pretty.smli");
}

#[test]
fn range() {
    run_script("tests/script/range.smli");
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
fn signature() {
    run_script("tests/script/signature.smli");
}

#[test]
fn simple() {
    run_script("tests/script/simple.smli");
}

#[test]
fn such_that() {
    run_script("tests/script/such-that.smli");
}

#[test]
fn tail_recursion() {
    run_script("tests/script/tail-recursion.smli");
}

#[test]
fn type_() {
    run_script("tests/script/type.smli");
}

#[test]
fn type_alias() {
    run_script("tests/script/type-alias.smli");
}

#[test]
fn type_inference() {
    run_script("tests/script/type-inference.smli");
}

#[test]
fn use_() {
    run_script("tests/script/use.smli");
}

#[test]
fn variant() {
    run_script("tests/script/variant.smli");
}

#[test]
fn wordle() {
    run_script("tests/script/wordle.smli");
}

// End smile.rs
