<!--
{% comment %}
Licensed to Julian Hyde under one or more contributor license
agreements.  See the NOTICE file distributed with this work
for additional information regarding copyright ownership.
Julian Hyde licenses this file to you under the Apache
License, Version 2.0 (the "License"); you may not use this
file except in compliance with the License.  You may obtain a
copy of the License at

http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing,
software distributed under the License is distributed on an
"AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND,
either express or implied.  See the License for the specific
language governing permissions and limitations under the
License.
{% endcomment %}
-->
# Morel release history and change log

For a full list of releases, see
<a href="https://github.com/hydromatic/morel-rust/releases">GitHub</a>.

<!--
## <a id="0.x.0" href="https://github.com/hydromatic/morel-rust/releases/tag/v0.x.0">0.x.0</a> / xxxx-xx-xx

Release 0.x.0 ...

Contributors:

### Features

### Bug-fixes and internal improvements

### Build and tests

### Component upgrades

### Site and documentation

* Release 0.x.0
  ([#xxx](https://github.com/hydromatic/morel-rust/issues/xxx))
-->

## <a id="0.9.0" href="https://github.com/hydromatic/morel-rust/releases/tag/v0.9.0">0.9.0</a> / 2026-08-25

Morel Rust's second release. Release 0.2.0 could parse the whole
language but evaluate only a fraction of it; this release adds query
expressions, user-defined types, and Datalog support, doubles the size
of the standard library, and now runs in the browser via WebAssembly.

The version number matches that of
[Morel Java](https://github.com/hydromatic/morel) version 0.9.0, released
[two weeks](https://github.com/hydromatic/morel/blob/main/HISTORY.md#0.9.0)
before this release, with which this release is
feature-compatible. Our goal is to be compatible with the Morel
language as implemented by Morel Java, and our strategy is to copy the
`.smli` test scripts from that project and get them to
pass. Compatibility is therefore measured by how much of Morel Java's
script corpus Morel Rust reproduces line for line; at this release, it
is 91%, about 28,000 lines over 64 files. Much of the difference is
Morel Java's ability, provided by
[Apache Calcite](https://calcite.apache.org) and missing in Morel
Rust, to translate expressions to SQL and execute them via JDBC.

Contributors:
Julian Hyde,
Will Noble

Key features:
 * Query expressions are evaluated, not merely parsed: `from`, `join`
   (including outer joins), `where`, `group`, `compute`, `order`,
   `take`, `skip`, `yield`, `yieldAll`, `into`, `through`, `exists`,
   `forall`, and the set operations `union`, `except` and `intersect`.
 * A query may scan an unbounded variable, if a step bounds it: the
   compiler inverts predicates, tightens ranges, and materializes the
   extent of any finite type.
 * User-defined types: `datatype` (including polymorphic and
   recursive), `type` aliases, records and record modifiers.
 * Overloading (`over`, `val inst`), let-polymorphism, and qualified
   types.
 * The standard library has 450 functions and values in 27 structures,
   up from 256 in 14 in release 0.2.0.
 * The shell has command-line editing, persistent history, syntax
   highlighting, tabular output, and a `-e` option that evaluates a
   single expression.
 * Morel Rust runs in the browser, compiled to WebAssembly.
 * Morel Rust builds with Rust 1.93.1 or later.

### Features

* Materialize the extent of any finite type
* Allow an unbounded scan to have any pattern, and report one that cannot be
  enumerated ([morel#440](https://github.com/hydromatic/morel/issues/440))
* `scan` for `Bool`, `Char`, `Date`, `Int`, `Real`, `String`, `Time` and
  `Word`, and the conversions defined by them
  ([morel#371](https://github.com/hydromatic/morel/issues/371), continued)
* `StringCvt` structure
  ([morel#371](https://github.com/hydromatic/morel/issues/371))
* Extend tabular mode to render enum values as scalars
  ([morel#441](https://github.com/hydromatic/morel/issues/441))
* Add `extend`, `remove` and `rename` record modifiers, and replace `with`
  with `replace` ([morel#432](https://github.com/hydromatic/morel/issues/432))
* Change implementation of `ordinal` from a slot to a row field
  ([morel#434](https://github.com/hydromatic/morel/issues/434))
* Qualified types for overloaded identifiers
  ([morel#426](https://github.com/hydromatic/morel/issues/426))
* Let-polymorphism: generalize values bound in a local `let`
  ([morel#427](https://github.com/hydromatic/morel/issues/427))
* Add `PP.pack`, and make the pretty-printer's fit test affordable and exact
  ([morel#453](https://github.com/hydromatic/morel/issues/453))
* Syntax highlighting in the shell
  ([morel#413](https://github.com/hydromatic/morel/issues/413))
* Add command-line editing to the shell using Rustyline
  ([#45](https://github.com/hydromatic/morel-rust/issues/45),
  [morel#414](https://github.com/hydromatic/morel/issues/414))
* Rename binary to `morel`
  ([#46](https://github.com/hydromatic/morel-rust/issues/46))
* Syntax that allows `yield`, `yieldAll` and `group` to produce a single
  "binder" variable
  ([morel#387](https://github.com/hydromatic/morel/issues/387))
* Add `type_string` operator
  ([morel#406](https://github.com/hydromatic/morel/issues/406))
* Add the `Test` structure and collection-kind dispatch (completes
  [morel#271](https://github.com/hydromatic/morel/issues/271))
* Add `PP` structure (pretty-printer), and use it to print values
  ([#398](https://github.com/hydromatic/morel-rust/issues/398),
  [#339](https://github.com/hydromatic/morel-rust/issues/339))
* Add a `matchStrict` property, and move pretty-printing tests into
  `pretty.smli` ([morel#398](https://github.com/hydromatic/morel/issues/398),
  part 1)
* Add the `word` type and `Word` structure
  ([#396](https://github.com/hydromatic/morel-rust/issues/396))
* Align the top-level environment with Standard ML
  ([morel#395](https://github.com/hydromatic/morel/issues/395))
* Extend tabular mode to render nested records and record options (continues
  [morel#376](https://github.com/hydromatic/morel/issues/376))
* Outer joins ([morel#75](https://github.com/hydromatic/morel/issues/75))
* Add safe navigation operator `?.`
  ([morel#378](https://github.com/hydromatic/morel/issues/378))
* Extend tabular mode to render `option` values
  ([morel#382](https://github.com/hydromatic/morel/issues/382))
* Add `yieldAll` step, a flatMap for `from` expressions
  ([morel#257](https://github.com/hydromatic/morel/issues/257))
* Extend tabular mode to fold strings and display nested collections
  ([morel#376](https://github.com/hydromatic/morel/issues/376))
* Extend list constructor to allow ranges, e.g. `where i elem [0..^10, 20,
  100..]` ([morel#372](https://github.com/hydromatic/morel/issues/372))
* Expose `Range.complement` and `Range.ranges`, and add `built-in/range.smli`
  (continues [morel#361](https://github.com/hydromatic/morel/issues/361))
* File reader, and progressive types
  ([morel#209](https://github.com/hydromatic/morel/issues/209))
* Implement functions `Real.fmt` and `Int.fmt`, and parts of the `StringCvt`
  structure ([morel#371](https://github.com/hydromatic/morel/issues/371))
* Signature files as the primary definition of built-in functions and types
  ([morel#368](https://github.com/hydromatic/morel/issues/368))
* Add attributes and doc comments
  ([morel#369](https://github.com/hydromatic/morel/issues/369))
* Add `Sys.parseTree` built-in function for AST inspection
* Add `raise` command
  ([morel#364](https://github.com/hydromatic/morel/issues/364))
* Datalog ([morel#323](https://github.com/hydromatic/morel/issues/323))
* Implement queries with unbounded variables by inverting predicates
  ([morel#217](https://github.com/hydromatic/morel/issues/217))
* Add `Relational.iterate` function, which allows "recursive queries" such as
  transitive closure
* Tail-call optimization via trampolining
  ([morel#151](https://github.com/hydromatic/morel/issues/151))
* `Date` structure
  ([morel#278](https://github.com/hydromatic/morel/issues/278))
* `Time` structure
  ([morel#351](https://github.com/hydromatic/morel/issues/351))
* Add `now` and `timeZone` properties
  ([morel#352](https://github.com/hydromatic/morel/issues/352))
* Add `-e`/`--eval` option to the `morel` script, to execute a single command
  ([morel#333](https://github.com/hydromatic/morel/issues/333))
* Add `variant` datatype and `Variant` structure
  ([morel#324](https://github.com/hydromatic/morel/issues/324))
* `Range` structure
  ([morel#338](https://github.com/hydromatic/morel/issues/338))
* Postfix method-call syntax `x.f ()` and `x.f (a, b)`
  ([morel#346](https://github.com/hydromatic/morel/issues/346))
* Unparse expressions
  ([#41](https://github.com/hydromatic/morel-rust/issues/41))
* Replace `Relational.only` with overloaded `Bag.only` and `List.only`
* Ordinal-based constructors and type-directed comparators
* Make `elem` and `notelem` work with bags, in addition to lists
* Ordered and unordered queries
  ([morel#273](https://github.com/hydromatic/morel/issues/273))
* Operator overloading
  ([morel#237](https://github.com/hydromatic/morel/issues/237))
* Implement `through` clause in query expressions
  ([morel#171](https://github.com/hydromatic/morel/issues/171))
* Add function `Sys.clearEnv ()`
  ([morel#251](https://github.com/hydromatic/morel/issues/251))
* Add structure `Interactive`, with functions `use` and `useSilently`
  ([morel#198](https://github.com/hydromatic/morel/issues/198))
* Add built-in datatype `Descending`, and method `Relational.compare`, for
  type-based orderings
  ([morel#282](https://github.com/hydromatic/morel/issues/282))
* Polymorphic datatype
  ([morel#70](https://github.com/hydromatic/morel/issues/70))
* Implement `op ::` (cons operator section)
* Type abbreviations, also known as alias types, declared using the `type`
  keyword ([morel#285](https://github.com/hydromatic/morel/issues/285))
* `Fn` structure ([morel#301](https://github.com/hydromatic/morel/issues/301))
* Layered patterns (`as`), and composite `val`
  ([morel#103](https://github.com/hydromatic/morel/issues/103))
* Allow `from` clause that defines 0 sources
  ([morel#17](https://github.com/hydromatic/morel/issues/17))
* Allow recursive functions defined in one statement to be called from later
  statements ([morel#7](https://github.com/hydromatic/morel/issues/7))
* Analyze match coverage, detecting redundant and exhaustive matches
  ([morel#55](https://github.com/hydromatic/morel/issues/55))
* Satisfiability prover
* Execute `current`, `ordinal`, and `unorder` in queries
  ([morel#265](https://github.com/hydromatic/morel/issues/265),
  [morel#276](https://github.com/hydromatic/morel/issues/276),
  [morel#277](https://github.com/hydromatic/morel/issues/277))
* Add `with` operator (functional update notation for record values)
  ([morel#249](https://github.com/hydromatic/morel/issues/249))
* Execution of queries with group, compute, elements
* Tabular output mode in the shell
  ([morel#259](https://github.com/hydromatic/morel/issues/259))
* Add `typeof` operator, to extract the type of an expression
  ([morel#291](https://github.com/hydromatic/morel/issues/291))
* Access tuple fields using dot syntax, e.g. `tuple.1`
  ([morel#332](https://github.com/hydromatic/morel/issues/332))
* Allow nested block comments
  ([morel#306](https://github.com/hydromatic/morel/issues/306))
* Add `banner`, `productName`, `productVersion` properties
  ([#30](https://github.com/hydromatic/morel-rust/issues/30))
* `Sys` structure (part of
  [#16](https://github.com/hydromatic/morel-rust/issues/16))
* Morel in the browser, via WebAssembly
  ([#13](https://github.com/hydromatic/morel-rust/issues/13))
* Optimize `exists` and `forall` queries with short-circuit evaluation
  ([#25](https://github.com/hydromatic/morel-rust/issues/25))
* Evaluate `exists`, `forall` and `into` query expressions
  ([#26](https://github.com/hydromatic/morel-rust/issues/26))
* Execute query expressions
  ([#15](https://github.com/hydromatic/morel-rust/issues/15))
* Translate queries from AST to Core; add `struct FromBuilder`
* Derive types for query expressions
  ([#14](https://github.com/hydromatic/morel-rust/issues/14))
* Add `Relational` structure
  ([#24](https://github.com/hydromatic/morel-rust/issues/24))
* Add `-c` (command) and `-h` (help) command-line flags
  ([#23](https://github.com/hydromatic/morel-rust/issues/23))
* Add signatures for standard library
* Parse `signature`
  ([#20](https://github.com/hydromatic/morel-rust/issues/20))
* Support `op` keyword (operator sections)
  ([morel#311](https://github.com/hydromatic/morel/issues/311))

### Bug-fixes and internal improvements

* Add `BigInt`, an integer of arbitrary size
* Property error messages should specify the property name and its type
  ([morel#455](https://github.com/hydromatic/morel/issues/455))
* Enumerating `unit` yields a value that prints as `{}` and is not `()`
  ([morel#454](https://github.com/hydromatic/morel/issues/454))
* Change the argument of `Relational.count` and other commutative aggregate
  functions from bag to generic collection
  ([morel#452](https://github.com/hydromatic/morel/issues/452))
* `Range.flatten` raises `Size` for a bounded domain, and runs out of memory
  for a large one
  ([morel#450](https://github.com/hydromatic/morel/issues/450))
* An unbound name in a type is accepted, or crashes
  ([morel#448](https://github.com/hydromatic/morel/issues/448))
* Unbounded scans should be ordered and distinct
  ([morel#443](https://github.com/hydromatic/morel/issues/443))
* Inlining a subquery that ends with `yield`, and a one-field record in a set
  operation
* Type annotation containing `typeof` throws `AssertionError`
  ([morel#445](https://github.com/hydromatic/morel/issues/445))
* Shell highlighter should color a keyword inside backticks as an identifier
  ([morel#437](https://github.com/hydromatic/morel/issues/437))
* Inlining a `val` captured a name the destination rebinds
* Two block comments opened by the
  [#399](https://github.com/hydromatic/morel-rust/issues/399) reformat were
  never closed
* A `let` did not bind its declarations sequentially
* A malformed statement swallowed the rest of the input
* `ordinal` in a join's `on` condition should be the ordinal of the candidate
  pair ([morel#435](https://github.com/hydromatic/morel/issues/435))
* A singleton subquery in a `yield` had the wrong type
* Source span of a function application omits the parentheses around a grouped
  argument ([morel#422](https://github.com/hydromatic/morel/issues/422))
* Shell loses input when a line holds a comment or more than one statement
  ([morel#439](https://github.com/hydromatic/morel/issues/439))
* Script test harness does not check a warning that precedes a value
* Backswing from morel-go
  ([morel#428](https://github.com/hydromatic/morel/issues/428))
* Redefining a type name with `type` or `datatype` breaks the new type and
  values of the old one
  ([morel#429](https://github.com/hydromatic/morel/issues/429))
* When printing nested values, treat constructor's argument as one level of
  `printDepth` ([morel#456](https://github.com/hydromatic/morel/issues/456))
* Row binder gives wrong result or crashes when the binder name equals the
  record's only field name
  ([morel#416](https://github.com/hydromatic/morel/issues/416))
* Don't assume that `NaN` is positive
  ([morel#425](https://github.com/hydromatic/morel/issues/425))
* Unify `list` and `bag` in type resolution via an orderedness atom
  ([morel#407](https://github.com/hydromatic/morel/issues/407))
* Shell highlighter crashes when typing a string escape
  ([morel#415](https://github.com/hydromatic/morel/issues/415))
* Evaluation deep-copies values and compiled code
  ([#47](https://github.com/hydromatic/morel-rust/issues/47))
* `Real.floor`, `Real.ceil`, and `Real.trunc` give wrong results when applied
  to `NaN` ([morel#423](https://github.com/hydromatic/morel/issues/423))
* `max` and `min` give wrong answers or crash for `word`, `real`, and
  composite typed arguments
  ([morel#421](https://github.com/hydromatic/morel/issues/421))
* `max` and `min` over an empty collection should raise `Empty`
  ([morel#419](https://github.com/hydromatic/morel/issues/419))
* Character constant that is not exactly one character crashes the shell
  ([morel#420](https://github.com/hydromatic/morel/issues/420))
* Separate the kernel from the script runner
  ([#45](https://github.com/hydromatic/morel-rust/issues/45), part 2)
* Extract statement-completeness logic into `shell/statement.rs`
  ([#45](https://github.com/hydromatic/morel-rust/issues/45), part 1)
* `Math` functions should compute in `f64`, to match Morel Java
  ([#44](https://github.com/hydromatic/morel-rust/issues/44))
* Invert a recursive predicate applied to a constant
  ([morel#217](https://github.com/hydromatic/morel/issues/217))
* A bare qualified-member aggregate in a `group` panics in the pretty-printer
* `Real.fmt (FIX n)` and `Real.minPos` print incorrectly
  ([morel#371](https://github.com/hydromatic/morel/issues/371))
* Report `unresolved flex record` for a bare record selector
* Pretty-print lists and types compactly, like SML/NJ
  ([morel#398](https://github.com/hydromatic/morel/issues/398), part 2)
* Referencing an atom row by its implicit label fails in `order`/`compute`
* A built-in shadows a same-named `group`/`compute` field in a later step
* Type resolver for `into` should infer the parameter type of a kind-agnostic
  function
* `Relational.sum` should be `'a bag -> 'a`, not `int bag -> int`
* The group key should be in scope inside a `compute` aggregate's `over`
* Wrong results for `except`/`intersect distinct` and for a set operation
  before `group`
* `group` by an anonymous expression, a record-valued binding, or a tuple
  gives wrong results or crashes
* `over` outside `compute` reports the wrong error, and nested `over` is
  accepted
* Set operations (`except`, `intersect`, `union`) crash after `distinct` and
  over records
* Ground an unbounded variable bounded by `elem` over a range
* Parenthesize a constructor application that is a constructor's argument
* Make the built-in structures consistent in Java and Rust implementations
  ([morel#385](https://github.com/hydromatic/morel/issues/385))
* Lexical error should not crash the shell
  ([morel#383](https://github.com/hydromatic/morel/issues/383))
* Unparser should quote reserved-word identifiers (e.g. `left`, `o`,
  `ordinal`)
* Use feasibility-based bound tightening (FBBT) to deduce and strengthen
  variable bounds
  ([morel#373](https://github.com/hydromatic/morel/issues/373))
* `Fn.repeat` with a negative count should raise `Domain` immediately
  ([morel#354](https://github.com/hydromatic/morel/issues/354))
* You're going to need a bigger SAT Solver
  ([morel#367](https://github.com/hydromatic/morel/issues/367))
* Include source position in interactive compile-error messages
* Intern types in library
  ([#34](https://github.com/hydromatic/morel-rust/issues/34), part 3)
* Migrate `Box<Type>` to `Rc<Type>`
  ([#34](https://github.com/hydromatic/morel-rust/issues/34), part 2)
* Tune unifier, inliner, type-resolver
  ([#34](https://github.com/hydromatic/morel-rust/issues/34) part 1)
* Drop the recursive-reentry shortcut in `capture_bound_vals`
* Reject standalone tuple type and fix nested tuple printing
  ([morel#360](https://github.com/hydromatic/morel/issues/360))
* The `intersect` and `except` steps should count, and preserve order
  ([morel#321](https://github.com/hydromatic/morel/issues/321))
* Composite value declarations should not assign `it`
  ([morel#355](https://github.com/hydromatic/morel/issues/355))
* In `OutputMatcher`, handle polymorphism and unordered tables (continues
  [morel#334](https://github.com/hydromatic/morel/issues/334))
* Capture closure-bound recursive fns lexically
  ([#42](https://github.com/hydromatic/morel-rust/issues/42))
* Improve `OutputMatcher` (continues
  [morel#334](https://github.com/hydromatic/morel/issues/334))
* Make postfix dispatch metadata-driven via type-signature inference
* Inline functions (and other expressions) that are not in the same compile
  unit ([morel#223](https://github.com/hydromatic/morel/issues/223))
* Inline `case x` when `x` is constant
  ([morel#330](https://github.com/hydromatic/morel/issues/330))
* Disallow `0` and integer literals starting with `0` as record labels
* The built-in `abs` function should be overloaded, and can apply to both
  `int` and `real`
  ([morel#318](https://github.com/hydromatic/morel/issues/318))
* In a zero-field relation, `distinct` should give a different result from
  `group {}` ([morel#328](https://github.com/hydromatic/morel/issues/328))
* Display whole `real` values without trailing `.0`
  ([morel#358](https://github.com/hydromatic/morel/issues/358))
* Match SML-NJ output format in interactive shell
  ([#36](https://github.com/hydromatic/morel-rust/issues/36))
* Aggregate functions should adapt to list or bag input
  ([morel#271](https://github.com/hydromatic/morel/issues/271))
* Use `GroupRowSink` for `distinct` queries, and obsolete `DistinctRowSink`
* Local bindings should shadow built-in functions
* Resolve various evaluation issues
* Convert various panics to exceptions that can be caught
* Improve how datatype values are stored
* Print single-character spans without end position
* Non-trivial expression in `over`
* Each `val` should be able to see previous declarations in the same `let`
  block
* Preserve type alias names through type resolution and display
* Persistent `LinkTable` for cross-statement recursive references
* Default overloaded +, -, *, ~ to int when unconstrained
  ([morel#29](https://github.com/hydromatic/morel/issues/29))
* In the `scott` sample database, map the `EMP` table to `emps` (and pluralize
  other table names)
  ([morel#255](https://github.com/hydromatic/morel/issues/255))
* Distinguish `Bind` and `Match` exceptions, and report span
* Record pattern in `from` mixes up fields if not in alphabetical order
  ([morel#35](https://github.com/hydromatic/morel/issues/35))
* Warn when record fields in `order` are not in alphabetical order
  ([morel#244](https://github.com/hydromatic/morel/issues/244))
* Always print `real` values with a decimal point, even whole numbers like
  `1.0`
* Correct signature of `List.except`, `List.intersect`, `Sys.unset` functions,
  and remove `Bag.collate`
* Tune `Unifier` ([#18](https://github.com/hydromatic/morel-rust/issues/18))
* Tune `Inliner`
* Span of `+` expression is too short
* When encoding record types in unifier, quote field names if necessary

### Build and tests

* Declare a minimum Rust version of 1.93.1, and test it in CI
* Enable more `.smli` tests by removing or narrowing `set(mode, validate)`
  brackets
* Lint should ensure that block comment continuation lines have a '*' prefix
  ([morel#442](https://github.com/hydromatic/morel/issues/442))
* Enable calls to `Sys.plan ()` and `Sys.planEx ()` in tests
  ([#48](https://github.com/hydromatic/morel-rust/issues/48))
* Enable disabled script sections
* Add a test, `dual.smli`, that runs each query locally and in Calcite
  ([morel#412](https://github.com/hydromatic/morel/issues/412))
* Lint: flag consecutive `(*)` line comments that should be a block comment
  ([#399](https://github.com/hydromatic/morel-rust/issues/399))
* Use a larger stack for certain tests in debug builds
* Remove dead code, and treat dead-code warnings as errors from now on
* Lint: synchronize `.smli` and `.md` rules with morel-java
  ([morel#335](https://github.com/hydromatic/morel/issues/335))
* Split `built-in.smli` into one file per structure
  ([morel#361](https://github.com/hydromatic/morel/issues/361))
* Lint: Ban fully-qualified paths
* Make test scripts resilient to changes in the order of `bag` values
  ([morel#334](https://github.com/hydromatic/morel/issues/334))
* In CI, run tests in release mode (in addition to debug mode)
* Suppress `clippy::result_large_err` in parser files
* Lint: Prevent redundant `set("mode", "evaluate")` and `set("mode",
  "validate")` statements
* Add a utility to re-enable sections of test scripts that already work
* Make sure that every `.smli` file is called from a test in `smile.rs`

### Component upgrades

* Bump pest from 2.1 to 2.8
* Move minimum supported Rust version (MSRV) down from 1.95.0 to
  1.93.1 (while still supporting all later versions including
  `stable`)

### Site and documentation

* In release notes, add release name (e.g. `0.9.0`) as an anchor
* Release 0.9.0 ([#49](https://github.com/hydromatic/morel-rust/issues/49))
* Document and test various recursion patterns
  ([#39](https://github.com/hydromatic/morel-rust/issues/39))

## <a id="0.2.0" href="https://github.com/hydromatic/morel-rust/releases/tag/v0.2.0">0.2.0</a> / 2025-10-23

Initial release.

There are too many changes to list here. Suffice it to say, much has
been done, and much more is left to do. Our goal is to be compatible
with the Morel language as implemented by
[Morel Java](https://github.com/hydromatic/morel), and our strategy is
to copy the `.smli` test scripts from that project and get them to
pass. Large sections of those scripts currently run under `set
("mode", "validate")`, which parses expressions but does not resolve
types of execute, and we are gradually converting sections to `set
("mode", "evaluate")`.

Key features:
 * The parser is complete.
 * Type resolution (via the Hindley-Milner algorithm and unification)
   is complete for expressions, function declarations, and built-in
   types including `list`, `option`, `either`.
 * Evaluation is complete (but not very efficient) for simple
   expressions including lists, lambdas and closures.
 * There are 256 built-in functions in 14 structures.
   [`Bool`](https://smlfamily.github.io/Basis/bool.html),
   [`Char`](https://smlfamily.github.io/Basis/char.html),
   [`General`](https://smlfamily.github.io/Basis/general.html),
   [`Int`](https://smlfamily.github.io/Basis/int.html),
   [`List`](https://smlfamily.github.io/Basis/list.html),
   [`ListPair`](https://smlfamily.github.io/Basis/list.html),
   [`Math`](https://smlfamily.github.io/Basis/math.html),
   [`Option`](https://smlfamily.github.io/Basis/option.html),
   [`Real`](https://smlfamily.github.io/Basis/real.html),
   [`String`](https://smlfamily.github.io/Basis/string.html), and
   [`Vector`](https://smlfamily.github.io/Basis/vector.html)
   are based on the Standard ML Basis Library;
   [`Either`](https://github.com/SMLFamily/BasisLibrary/wiki/2015-002-Addition-of-Either-module)
   is a proposed extension to the Standard ML Basis Library; and
   `Bag` and
   `Sys`
   are Morel-specific.

Among the many remaining tasks to achieve parity with Morel Java are
type-resolution and execution of query expressions (`from`, `forall`,
`exists`), external data (from the file system or from a database via
ODBC or JDBC), and user-defined types.
