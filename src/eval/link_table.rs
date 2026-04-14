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

//! Persistent table of compiled `Code` values referenced by
//! recursive function bindings.
//!
//! See [`LinkTable`] for the architectural rationale.

use crate::eval::code::Code;
use std::sync::Arc;

/// A persistent registry of compiled [`Code`] values referenced
/// indirectly by recursive function bindings.
///
/// # Why this exists
///
/// In Standard ML, recursive functions like
///
/// ```sml
/// fun fact 0 = 1
///   | fact n = n * fact (n - 1)
/// ```
///
/// are tricky to compile, because the body of `fact` references
/// `fact` itself, but at the moment we are compiling `fact`'s body
/// we do not yet have a `Code` value for `fact` to plug in. The
/// compiler resolves this with an indirection: every recursive
/// reference is compiled as `Code::Link(slot, name)`, and after
/// the body has been compiled the [`LinkEntry`] at `slot` is
/// filled in with the just-compiled [`Code`]. At evaluation time,
/// `Code::Link` follows the slot to find the real code and
/// continues from there.
///
/// # The cross-statement problem
///
/// In a single statement this is straightforward: each statement
/// builds its own short-lived link vector and the recursive
/// references resolve while the statement is running. The
/// complication is that **functions can outlive the statement
/// that defined them**. Consider:
///
/// ```sml
/// fun baz f =
///   let
///     fun fact 0 = 1
///       | fact n = n * fact (f n)
///   in
///     fact 5
///   end;
/// baz (fn i => i - 1);    (* a separate statement *)
/// ```
///
/// The second statement applies `baz`, which in turn invokes the
/// inner `fact`, whose body still contains a `Code::Link`
/// pointing into the first statement's link vector. If that
/// vector were dropped at the end of the first statement, the
/// `Link` would dangle and evaluation would panic with "link
/// 'fact' not found in environment".
///
/// The fix is to make the link table **persistent across
/// statements**: every `Code::Link(slot, _)` ever produced
/// references a slot in a single, append-only `LinkTable` owned
/// by the [`Shell`](crate::shell::main::Shell). Older slots are
/// never reused or freed, so any `Code` that captured a slot
/// index in the past can still resolve it later.
///
/// Slot indices are therefore **absolute** — they index directly
/// into the shell-wide table, not into a per-statement window.
///
/// # Lifecycle
///
/// **Compile, recursive binding seen.** [`reserve`](Self::reserve)
/// is called once per recursive name. It returns the absolute
/// slot the new binding will live at. The slot starts empty
/// (`code = None`).
///
/// **Compile, recursive body finished.** [`fill`](Self::fill)
/// writes the compiled `Code` into the reserved slot. After this
/// point any runtime path that follows a `Code::Link` to this
/// slot will succeed.
///
/// **Statement evaluate.** `Code::Link(slot, _)` looks up the
/// slot via [`get`](Self::get) and dispatches into the resolved
/// `Code`.
///
/// **Cross-statement evaluate.** A function compiled in
/// statement *N* runs in statement *M*. Its `Code::Link` slots
/// still resolve because the same `LinkTable` is in scope on
/// the shell.
///
/// **Session end.** The table is dropped together with the
/// shell.
///
/// Outside of the brief window between [`reserve`](Self::reserve)
/// and [`fill`](Self::fill), every slot is filled. A `None` slot
/// observed at runtime is a compiler bug.
///
/// # Memory characteristics
///
/// This is a deliberate space–correctness tradeoff. Slots are
/// **never reclaimed**, so a long REPL session that defines many
/// recursive functions will accumulate their compiled `Code` in
/// the `LinkTable` indefinitely. In practice this is bounded by
/// the number of distinct `fun` / `val rec` declarations the
/// user types, which is small. Heavier alternatives that reclaim
/// memory (carrying a per-function link table on `Val::Code`,
/// substituting `Link`s with their resolved `Code` at storage
/// time, etc.) are described in the design notes for issue
/// hydromatic/morel#301; revisit if memory growth becomes a
/// problem.
///
/// # Concurrency
///
/// Morel-rust is single-threaded. The `LinkTable` is stored on
/// the shell behind a `RefCell` so that compilation (which
/// mutates the table) and evaluation (which reads it) can both
/// borrow it briefly. Recursive function calls re-borrow the
/// table immutably and must not be entered while a mutable borrow
/// is held.
#[derive(Debug, Default)]
pub struct LinkTable {
    entries: Vec<LinkEntry>,
}

/// One slot in a [`LinkTable`].
///
/// `code` is `None` only during the brief window between
/// [`LinkTable::reserve`] and [`LinkTable::fill`]. Outside of
/// that window — i.e. for any slot that has ever been observed
/// by a runtime `Code::Link` lookup — it is always `Some`.
#[derive(Debug)]
pub struct LinkEntry {
    /// The bound name. Carried for diagnostics and for the
    /// shell-name fallback in `Code::GetLocal`. The slot index
    /// is what the runtime actually uses to dispatch.
    pub name: String,
    /// The compiled body of the recursive binding. `None` only
    /// during the reserve/fill window.
    pub code: Option<Arc<Code>>,
}

impl LinkTable {
    /// Creates a new, empty link table. The first slot reserved
    /// in this table will have index `0`.
    pub fn new() -> Self {
        Self::default()
    }

    /// Reserves a fresh slot for a recursive binding named
    /// `name` and returns its absolute slot index.
    ///
    /// The slot starts with `code = None`. The compiler **must**
    /// call [`fill`](Self::fill) on this slot before any code
    /// path that can be evaluated at runtime references it; a
    /// `None` slot observed at evaluation time is a compiler bug.
    pub fn reserve(&mut self, name: &str) -> usize {
        let i = self.entries.len();
        self.entries.push(LinkEntry {
            name: name.to_string(),
            code: None,
        });
        i
    }

    /// Fills the previously-reserved slot with the compiled
    /// `Code` for the recursive binding's body.
    ///
    /// Panics if `slot` is out of range. Overwriting a slot that
    /// already has code is allowed but should not normally
    /// happen — each reservation is filled exactly once.
    pub fn fill(&mut self, slot: usize, code: Arc<Code>) {
        self.entries[slot].code = Some(code);
    }

    /// Looks up the `Code` at `slot`. Returns `None` if `slot`
    /// is out of range or has not yet been filled (which is a
    /// compiler bug if it ever happens at runtime).
    pub fn get(&self, slot: usize) -> Option<Arc<Code>> {
        self.entries.get(slot).and_then(|e| e.code.clone())
    }

    /// Returns the binding name recorded for `slot`, if the slot
    /// is in range. Used for diagnostics.
    pub fn name(&self, slot: usize) -> Option<&str> {
        self.entries.get(slot).map(|e| e.name.as_str())
    }

    /// Number of slots in the table. Mainly useful for
    /// diagnostics. User code should not depend on slot indices
    /// being contiguous between statements.
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    /// Returns whether the table is empty.
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }
}
