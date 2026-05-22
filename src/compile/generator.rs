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

//! Generator data type for predicate inversion.
//!
//! A `Generator` is an expression that produces all values satisfying
//! some predicate, attached to the pattern that consumes them. The
//! `Expander` derives one or more generators per unbounded pattern
//! and stores them in a `Cache`; the strongest (most-recently
//! inserted) generator wins.
//!
//! Mirrors morel-java's `compile.Generator` plus the `Cache`
//! abstraction from `compile.Generators`.

use crate::compile::core::{Expr, Pat};
use std::collections::BTreeSet;
use std::collections::HashMap;

/// How many values per binding of the generator's free variables
/// the generator produces.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum Cardinality {
    /// Exactly one value (e.g. `x = 5`).
    Single,
    /// A bounded number of values (e.g. `x elem [1, 2, 3]`).
    Finite,
    /// Unbounded — the generator hasn't (yet) been derived. We carry
    /// this only as a placeholder for in-progress derivations; a
    /// generator with `Cardinality::Infinite` is not usable.
    Infinite,
}

/// A generator expression bound to an unbounded pattern.
#[derive(Clone, Debug)]
pub struct Generator {
    /// Pattern this generator scans into.
    pub pat: Pat,
    /// Expression to scan — a list, bag, or other collection.
    pub exp: Expr,
    /// Cardinality bucket.
    pub cardinality: Cardinality,
    /// Names of patterns the generator depends on. Drives ordering
    /// of scans in the rewritten `from`.
    pub free_pats: BTreeSet<String>,
    /// Whether the generator's values are unique. If false, the
    /// rewritten query needs a `distinct` after the scan.
    pub unique: bool,
    /// Whether *every* value produced by this generator satisfies
    /// every constraint in `provenance`. Only sealed generators'
    /// provenance can be safely removed from the surrounding
    /// `where` clause. Phase 1 marks all leaf generators as sealed;
    /// composite generators added in later phases set this to
    /// `false`.
    pub sealed: bool,
    /// Original `where` conjuncts this generator subsumes.
    pub provenance: Vec<Expr>,
    /// Extra per-row predicate(s) the generator must apply but
    /// can't fold into `exp`. Used when function inlining brings
    /// in conjuncts that are not consumed by the chosen leaf
    /// strategy (e.g. `fun isClerk e = e elem coll andalso
    /// e.job = "CLERK"` — the elem-strategy consumes the first
    /// conjunct, the second becomes a row filter on the scan).
    pub extra_filter: Option<Expr>,
}

impl Generator {
    pub fn new(
        pat: Pat,
        exp: Expr,
        cardinality: Cardinality,
        free_pats: BTreeSet<String>,
        unique: bool,
        sealed: bool,
        provenance: Vec<Expr>,
    ) -> Self {
        Generator {
            pat,
            exp,
            cardinality,
            free_pats,
            unique,
            sealed,
            provenance,
            extra_filter: None,
        }
    }
}

/// Multimap of pattern-name → list of generators.
///
/// Append-only: refinements add a new generator without removing
/// the old. `best(pat)` returns the most-recent entry.
#[derive(Debug, Default)]
pub struct Cache {
    by_pat: HashMap<String, Vec<Generator>>,
}

impl Cache {
    pub fn new() -> Self {
        Self::default()
    }

    /// Inserts a generator. Multiple generators may be associated
    /// with the same pattern; `best` returns the one inserted last.
    pub fn add(&mut self, name: String, generator: Generator) {
        self.by_pat.entry(name).or_default().push(generator);
    }

    /// Returns the most-recent generator for the pattern, or
    /// `None` if none has been added.
    pub fn best(&self, name: &str) -> Option<&Generator> {
        self.by_pat.get(name).and_then(|v| v.last())
    }

    /// Returns `true` if any generator has been added for `name`.
    pub fn has(&self, name: &str) -> bool {
        self.by_pat.get(name).is_some_and(|v| !v.is_empty())
    }

    /// Returns the names of all patterns with at least one generator.
    pub fn pat_names(&self) -> impl Iterator<Item = &str> {
        self.by_pat.keys().map(String::as_str)
    }

    /// Returns every generator's provenance combined. Used by the
    /// Expander to filter conjuncts out of the rewritten `where`.
    pub fn sealed_provenance(&self) -> Vec<&Expr> {
        let mut out = Vec::new();
        for gens in self.by_pat.values() {
            if let Some(g) = gens.last()
                && g.sealed
            {
                out.extend(g.provenance.iter());
            }
        }
        out
    }
}
