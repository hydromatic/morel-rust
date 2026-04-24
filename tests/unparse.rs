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

//! Round-trip tests for AST pretty-printing: parse an expression, unparse
//! it, and check that the result matches the expected string. These verify
//! that the unparser uses parentheses iff they are required by the
//! precedence of surrounding operators.

use morel::syntax::ast::{Expr, StatementKind};
use morel::syntax::parser::parse_unadorned_statement;

/// Parses `input` as a single expression statement and returns the
/// expression.
fn parse_expr(input: &str) -> Expr {
    let stmt = parse_unadorned_statement(input).expect("parse should succeed");
    match stmt.kind {
        StatementKind::Expr(kind) => Expr {
            kind,
            span: stmt.span,
            id: stmt.id,
        },
        other => panic!("expected an expression, got {:?}", other),
    }
}

/// Parses `input` as a single expression statement and returns its unparsed
/// form.
fn unparse(input: &str) -> String {
    format!("{}", parse_expr(input).kind)
}

/// Asserts that `input` parses and unparses to `expected`.
#[track_caller]
fn check(input: &str, expected: &str) {
    let actual = unparse(input);
    assert_eq!(
        actual, expected,
        "\n  input    = {:?}\n  expected = {:?}\n  actual   = {:?}",
        input, expected, actual
    );
}

use morel::syntax::ast::ExprKindTag;
use std::collections::HashSet;
use strum::IntoEnumIterator;

/// Coverage tracker for `ExprKind` variants. Seeded with every variant
/// via `ExprKindTag::iter()` (generated from `ExprKind` by
/// `strum::EnumDiscriminants`). [`Self::check_kind`] removes the parsed
/// variant's tag as each canonical input is exercised;
/// [`Self::assert_complete`] fails the test if anything remains.
struct KindCoverage {
    remaining: HashSet<ExprKindTag>,
}

impl KindCoverage {
    fn new() -> Self {
        Self {
            remaining: ExprKindTag::iter().collect(),
        }
    }

    /// Round-trips `input` (must be canonical) and marks the parsed
    /// variant as covered.
    #[track_caller]
    fn check_kind(&mut self, input: &str) {
        self.check_kind_as(input, input);
    }

    /// Round-trips a possibly non-canonical `input` to the canonical
    /// `expected` form, and marks the parsed variant as covered.
    #[track_caller]
    fn check_kind_as(&mut self, input: &str, expected: &str) {
        check(input, expected);
        let expr = parse_expr(input);
        self.remaining.remove(&ExprKindTag::from(&expr.kind));
    }

    /// Fails the test if any declared variant is still uncovered.
    #[track_caller]
    fn assert_complete(&self) {
        assert!(
            self.remaining.is_empty(),
            "ExprKind variants not exercised by any check_kind call: {:?}",
            self.remaining
        );
    }
}

/// Round-trip tests, grouped by operator family. Exercises every
/// `ExprKind` variant at least once, plus a handful of ad-hoc
/// precedence / associativity / normalization checks per group.
///
/// `ExprKindTag` (auto-derived by `strum::EnumDiscriminants` from
/// `ExprKind`) tracks coverage. Adding a new variant to `ExprKind`
/// automatically adds it to `ExprKindTag::iter()`, so a canonical input
/// for it is required for this test to pass; the failure message names
/// any variant that was never exercised.
#[test]
fn test_each_expr_kind() {
    let mut k = KindCoverage::new();

    // Atoms: literal, identifier, op section, record selector, current,
    // ordinal, elements.
    k.check_kind("1");
    k.check_kind("x");
    k.check_kind("op +");
    k.check_kind("#name");
    k.check_kind("current");
    k.check_kind("ordinal");
    k.check_kind("elements");

    // Arithmetic ops: +, -, *, /, div, mod, ~.
    k.check_kind("1 + 2");
    k.check_kind("1 - 2");
    k.check_kind("1 * 2");
    k.check_kind("1 / 2.0");
    k.check_kind("1 div 2");
    k.check_kind("1 mod 2");
    k.check_kind("~x");
    // `*` binds tighter than `+`; left-associative chains stay flat.
    k.check_kind("1 + 2 * 3");
    k.check_kind("1 * 2 + 3");
    k.check_kind("(1 + 2) * 3");
    k.check_kind("(1 + 2) * (3 + 4)");
    k.check_kind("1 + 2 + 3");
    k.check_kind("1 - 2 - 3");
    k.check_kind("1 * 2 * 3");
    // Redundant outer parens are stripped.
    k.check_kind_as("((1 + 2)) * 3", "(1 + 2) * 3");
    k.check_kind_as("((1 * 2)) + 3", "1 * 2 + 3");

    // String concat: ^.
    k.check_kind("\"a\" ^ \"b\"");

    // Comparison ops: =, <>, <, <=, >, >=, elem, notelem.
    k.check_kind("1 = 2");
    k.check_kind("1 <> 2");
    k.check_kind("1 < 2");
    k.check_kind("1 <= 2");
    k.check_kind("1 > 2");
    k.check_kind("1 >= 2");
    k.check_kind("1 elem [1, 2]");
    k.check_kind("1 notelem [1, 2]");
    // `+` binds tighter than `=`.
    k.check_kind("1 + 2 = 3");
    k.check_kind("1 = 2 + 3");
    k.check_kind_as("(1 + 2) = 3", "1 + 2 = 3");

    // Boolean ops: andalso, orelse, implies.
    k.check_kind("true andalso false");
    k.check_kind("true orelse false");
    k.check_kind("true implies false");
    // `andalso` binds tighter than `orelse`.
    k.check_kind("true andalso false orelse true");
    k.check_kind("true orelse false andalso true");
    k.check_kind("(true orelse false) andalso true");

    // Function: apply, compose.
    k.check_kind("f x");
    k.check_kind("f o g");

    // List ops: ::, @. `::` is right-associative.
    k.check_kind("1 :: [2]");
    k.check_kind("[1] @ [2]");
    k.check_kind("1 :: 2 :: [3]");
    k.check_kind("(1 :: [2]) :: [[3]]");

    // Data constructors: [...], (...), {...}. All three are atomic when
    // used as a function argument.
    k.check_kind("[1, 2]");
    k.check_kind("(1, 2)");
    k.check_kind("{a = 1}");
    k.check_kind("hd [1, 2, 3]");
    k.check_kind_as("hd ([1, 2, 3])", "hd [1, 2, 3]");
    k.check_kind("length [1, 2, 3]");
    k.check_kind("f (1, 2)");
    k.check_kind("f {a = 1, b = 2}");
    k.check_kind("{r with a = 1}");

    // Type annotation: `:`.
    k.check_kind("1 : int");

    // Control flow: if, case, let, fn.
    k.check_kind("if x then 1 else 2");
    k.check_kind("case x of 1 => \"a\" | _ => \"b\"");
    k.check_kind("let val x = 1 in x end");
    k.check_kind("fn x => x");
    k.check_kind("if x > 0 then y + 1 else y - 1");
    k.check_kind("let val x = 1 in x + 2 end");
    k.check_kind("fn x => x + 1");
    k.check_kind("fn x => fn y => x + y");

    // Queries: from, exists, forall, over (aggregate).
    k.check_kind("from x in xs");
    k.check_kind("exists x in xs where true");
    k.check_kind("forall x in xs require true");
    k.check_kind("count over xs");
    k.check_kind("from e in emps");
    k.check_kind("from i in [1, 2, 3] where i > 1");
    k.check_kind("from i in [1, 2, 3] where i > 1 yield i");
    // Consecutive scans are separated by comma (canonical); an explicit
    // `join` between adjacent scans is canonicalized to comma.
    k.check_kind("from x in xs, y in ys");
    k.check_kind_as(
        "from x in xs join y in ys on x = y",
        "from x in xs, y in ys on x = y",
    );
    // After a non-scan step, a subsequent scan must use `join`.
    k.check_kind("from x in xs where x > 0 join y in ys on x = y");
    k.check_kind("from i in [3, 1, 2] order i");
    k.check_kind_as(
        "from e in emps group e.deptno compute count",
        "from e in emps group #deptno e compute count",
    );
    k.check_kind("from i in [1, 2, 3] distinct");
    k.check_kind("from i in [1, 2, 3, 4, 5] skip 1 take 3");
    k.check_kind("from i in [1, 2, 3] union [4, 5]");
    k.check_kind("from i in [1, 2, 3] union distinct [4, 5]");
    k.check_kind("from i in [1, 2, 3] intersect [2, 3]");
    k.check_kind("from i in [1, 2, 3] except [2]");
    k.check_kind_as(
        "exists e in emps where e.name = \"X\"",
        "exists e in emps where #name e = \"X\"",
    );
    k.check_kind_as(
        "forall e in emps require e.age > 0",
        "forall e in emps require #age e > 0",
    );
    // A `from` appearing as the source of another `from` must be
    // parenthesized; otherwise the inner query's steps would be
    // attributed to the outer query.
    k.check_kind("from e in (from x in xs yield x)");

    k.assert_complete();
}
