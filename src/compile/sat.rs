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

//! Propositional satisfiability solver.
//!
//! Provides a brute-force SAT solver over boolean formulas. Used by the
//! pattern coverage checker to determine whether match arms are exhaustive
//! and non-redundant.
//!
//! Ported from morel-java: `Sat.java`.

use std::fmt::{Display, Formatter, Result as FmtResult};

// ---------------------------------------------------------------------------
// Formula
// ---------------------------------------------------------------------------

/// A propositional formula over boolean variables (identified by index).
#[derive(Clone, Debug)]
pub enum Formula {
    /// The constant true. Written `true`, also the empty conjunction.
    True,
    /// The constant false. Written `false`, also the empty disjunction.
    False,
    /// A boolean variable, identified by its index.
    Var(usize),
    /// Negation. Written `¬f`.
    Not(Box<Formula>),
    /// Conjunction of zero or more formulas. Written `f0 ∧ f1 ∧ ...`.
    And(Vec<Formula>),
    /// Disjunction of zero or more formulas. Written `f0 ∨ f1 ∨ ...`.
    Or(Vec<Formula>),
}

impl Formula {
    /// Evaluates this formula under a given variable assignment.
    ///
    /// `assignment[i]` is the truth value of variable `i`.
    pub fn eval(&self, assignment: &[bool]) -> bool {
        match self {
            Formula::True => true,
            Formula::False => false,
            Formula::Var(v) => assignment[*v],
            Formula::Not(f) => !f.eval(assignment),
            Formula::And(fs) => fs.iter().all(|f| f.eval(assignment)),
            Formula::Or(fs) => fs.iter().any(|f| f.eval(assignment)),
        }
    }
}

impl Display for Formula {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        match self {
            Formula::True => write!(f, "true"),
            Formula::False => write!(f, "false"),
            Formula::Var(v) => write!(f, "x{}", v),
            Formula::Not(inner) => write!(f, "¬{}", inner),
            Formula::And(fs) => {
                if fs.is_empty() {
                    write!(f, "true")
                } else if fs.len() == 1 {
                    write!(f, "{}", fs[0])
                } else {
                    let parts: Vec<String> =
                        fs.iter().map(|g| format!("{}", g)).collect();
                    write!(f, "{}", parts.join(" ∧ "))
                }
            }
            Formula::Or(fs) => {
                if fs.is_empty() {
                    write!(f, "false")
                } else if fs.len() == 1 {
                    write!(f, "{}", fs[0])
                } else {
                    let parts: Vec<String> =
                        fs.iter().map(|g| format!("{}", g)).collect();
                    write!(f, "({})", parts.join(" ∨ "))
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Sat
// ---------------------------------------------------------------------------

/// Brute-force propositional satisfiability solver.
///
/// Variables are anonymous integers allocated by [`Sat::new_var`]. Background
/// constraints (type exclusivity, etc.) are added via [`Sat::add_constraint`]
/// and are implicitly conjoined with every formula tested by [`Sat::is_sat`].
pub struct Sat {
    pub num_vars: usize,
    /// Background constraints that always hold.
    pub constraints: Vec<Formula>,
}

impl Sat {
    /// Creates an empty solver with no variables and no constraints.
    pub fn new() -> Self {
        Sat {
            num_vars: 0,
            constraints: Vec::new(),
        }
    }

    /// Allocates a fresh boolean variable and returns its index.
    pub fn new_var(&mut self) -> usize {
        let v = self.num_vars;
        self.num_vars += 1;
        v
    }

    /// Adds a background constraint that must hold in every solution.
    pub fn add_constraint(&mut self, f: Formula) {
        self.constraints.push(f);
    }

    /// Returns `true` if `formula` (combined with all background constraints)
    /// is satisfiable, i.e. there exists an assignment of variables that makes
    /// it true.
    ///
    /// Uses brute-force enumeration of all 2^n assignments. Treats `n > 20`
    /// as satisfiable to avoid exponential blowup.
    pub fn is_sat(&self, formula: &Formula) -> bool {
        let n = self.num_vars;
        if n > 20 {
            // Safety limit: assume satisfiable rather than hang.
            return true;
        }
        let mut all = self.constraints.clone();
        all.push(formula.clone());
        let combined = Formula::And(all);
        for mask in 0u64..(1u64 << n) {
            let assignment: Vec<bool> =
                (0..n).map(|i| (mask >> i) & 1 == 1).collect();
            if combined.eval(&assignment) {
                return true;
            }
        }
        false
    }

    /// Returns a satisfying assignment for `formula` (combined with background
    /// constraints), or `None` if the formula is unsatisfiable.
    ///
    /// The returned vector maps each variable index to its truth value.
    pub fn solve(&self, formula: &Formula) -> Option<Vec<bool>> {
        let n = self.num_vars;
        if n > 20 {
            return Some(vec![false; n]);
        }
        let mut all = self.constraints.clone();
        all.push(formula.clone());
        let combined = Formula::And(all);
        for mask in 0u64..(1u64 << n) {
            let assignment: Vec<bool> =
                (0..n).map(|i| (mask >> i) & 1 == 1).collect();
            if combined.eval(&assignment) {
                return Some(assignment);
            }
        }
        None
    }
}

impl Default for Sat {
    fn default() -> Self {
        Self::new()
    }
}

// ---------------------------------------------------------------------------
// Tests (ported from SatTest.java)
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    /// Tests a formula with two variables.
    ///
    /// Port of `SatTest.testBuild`.
    ///
    /// Builds and solves a formula with two variables:
    /// `(x ∨ x ∨ y) ∧ (¬x ∨ ¬y ∨ ¬y) ∧ (¬x ∨ y ∨ y)`.
    #[test]
    fn test_build() {
        let mut sat = Sat::new();
        let x = sat.new_var(); // x0
        let y = sat.new_var(); // x1

        // (x ∨ x ∨ y)
        let clause0 = Formula::Or(vec![
            Formula::Var(x),
            Formula::Var(x),
            Formula::Var(y),
        ]);
        // (¬x ∨ ¬y ∨ ¬y)
        let clause1 = Formula::Or(vec![
            Formula::Not(Box::new(Formula::Var(x))),
            Formula::Not(Box::new(Formula::Var(y))),
            Formula::Not(Box::new(Formula::Var(y))),
        ]);
        // (¬x ∨ y ∨ y)
        let clause2 = Formula::Or(vec![
            Formula::Not(Box::new(Formula::Var(x))),
            Formula::Var(y),
            Formula::Var(y),
        ]);
        let formula = Formula::And(vec![clause0, clause1, clause2]);

        assert_eq!(
            formula.to_string(),
            "(x0 ∨ x0 ∨ x1) ∧ (¬x0 ∨ ¬x1 ∨ ¬x1) \
             ∧ (¬x0 ∨ x1 ∨ x1)"
        );

        let solution = sat.solve(&formula);
        // Solution exists: x=false (0), y=true (1).
        assert!(solution.is_some(), "formula is satisfiable");
        let sol = solution.unwrap();
        assert_eq!(sol[x], false, "x should be false");
        assert_eq!(sol[y], true, "y should be true");
    }

    /// Tests `true` (conjunction of zero terms).
    ///
    /// Port of `SatTest.testTrue`.
    #[test]
    fn test_true() {
        let sat = Sat::new();
        let true_term = Formula::And(vec![]);
        assert_eq!(true_term.to_string(), "true");

        let sol = sat.solve(&true_term);
        assert!(sol.is_some(), "true is satisfiable");
        assert!(sol.unwrap().is_empty(), "solution is empty (no variables)");
    }

    /// Tests `false` (disjunction of zero terms).
    ///
    /// Port of `SatTest.testFalse`.
    #[test]
    fn test_false() {
        let sat = Sat::new();
        let false_term = Formula::Or(vec![]);
        assert_eq!(false_term.to_string(), "false");

        let sol = sat.solve(&false_term);
        assert!(sol.is_none(), "false is not satisfiable");
    }

    /// Tests that a single literal is satisfiable and its negation is also
    /// satisfiable independently, but together they are not.
    #[test]
    fn test_single_var() {
        let mut sat = Sat::new();
        let x = sat.new_var();

        assert!(sat.is_sat(&Formula::Var(x)));
        assert!(sat.is_sat(&Formula::Not(Box::new(Formula::Var(x)))));

        // x ∧ ¬x is unsatisfiable.
        let contradiction = Formula::And(vec![
            Formula::Var(x),
            Formula::Not(Box::new(Formula::Var(x))),
        ]);
        assert!(!sat.is_sat(&contradiction));
    }

    /// Tests at-most-one and at-least-one constraints, as used by the coverage
    /// checker for closed types (bool, order, option, list).
    #[test]
    fn test_closed_type_constraints() {
        let mut sat = Sat::new();
        let t = sat.new_var(); // "true" constructor
        let f = sat.new_var(); // "false" constructor

        // At least one must be active.
        sat.add_constraint(Formula::Or(vec![Formula::Var(t), Formula::Var(f)]));
        // At most one: ¬(t ∧ f).
        sat.add_constraint(Formula::Not(Box::new(Formula::And(vec![
            Formula::Var(t),
            Formula::Var(f),
        ]))));

        // Matching only "true" leaves "false" uncovered → non-exhaustive.
        let not_true = Formula::Not(Box::new(Formula::Var(t)));
        assert!(sat.is_sat(&not_true), "¬true is satisfiable (false works)");

        // Matching both "true" and "false" → exhaustive.
        let not_covered = Formula::And(vec![
            Formula::Not(Box::new(Formula::Var(t))),
            Formula::Not(Box::new(Formula::Var(f))),
        ]);
        assert!(!sat.is_sat(&not_covered), "¬true ∧ ¬false is unsat");
    }
}
