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
    /// A boolean variable, identified by its index.
    Var(usize),
    /// Negation. Written `¬f`.
    Not(Box<Formula>),
    /// Conjunction of zero or more formulas. Written `f0 ∧ f1 ∧ ...`.
    And(Vec<Formula>),
}

impl Formula {
    /// Evaluates this formula under a given variable assignment.
    ///
    /// `assignment[i]` is the truth value of variable `i`.
    pub fn eval(&self, assignment: &[bool]) -> bool {
        match self {
            Formula::True => true,
            Formula::Var(v) => assignment[*v],
            Formula::Not(f) => !f.eval(assignment),
            Formula::And(fs) => fs.iter().all(|f| f.eval(assignment)),
        }
    }
}

impl Display for Formula {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        match self {
            Formula::True => write!(f, "true"),
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
        }
    }
}

// ---------------------------------------------------------------------------
// Sat
// ---------------------------------------------------------------------------

/// Brute-force propositional satisfiability solver.
///
/// Variables are anonymous integers allocated by [`Sat::new_var`]. A *slot*
/// (declared via [`Sat::slot`]) is a group of variables of which exactly
/// one is true. Slots let the solver enumerate `N` one-hot assignments per
/// slot rather than `2^N`, which is essential for datatypes with many
/// constructors (the pattern-coverage check uses one boolean per
/// constructor). Variables not in any slot are searched by brute force.
pub struct Sat {
    pub num_vars: usize,
    /// Groups of variables of which exactly one is true. Disjoint by
    /// construction.
    slots: Vec<Vec<usize>>,
}

impl Sat {
    /// Creates an empty solver with no variables.
    pub fn new() -> Self {
        Sat {
            num_vars: 0,
            slots: Vec::new(),
        }
    }

    /// Allocates a fresh boolean variable and returns its index.
    pub fn new_var(&mut self) -> usize {
        let v = self.num_vars;
        self.num_vars += 1;
        v
    }

    /// Declares that `vars` is a slot: exactly one of them is true in any
    /// satisfying assignment. Allows [`Self::solve`] to enumerate `N`
    /// candidates (one per variable in the slot) rather than `2^N`.
    pub fn slot(&mut self, vars: Vec<usize>) {
        self.slots.push(vars);
    }

    /// Returns `true` if `formula` is satisfiable, i.e. there exists an
    /// assignment of variables that makes it true.
    pub fn is_sat(&self, formula: &Formula) -> bool {
        self.solve(formula).is_some()
    }

    /// Returns a satisfying assignment for `formula`, or `None` if the
    /// formula is unsatisfiable.
    ///
    /// Enumerates candidates as the Cartesian product of `2^F` settings of
    /// the `F` "free" variables (those not in any slot) and `N_i` one-hot
    /// settings per slot of size `N_i`. To avoid pathological blow-up when
    /// many free variables are present, treats `F > 20` as satisfiable.
    pub fn solve(&self, formula: &Formula) -> Option<Vec<bool>> {
        let n = self.num_vars;

        let mut in_slot = vec![false; n];
        for slot in &self.slots {
            for &v in slot {
                in_slot[v] = true;
            }
        }
        let free_vars: Vec<usize> = (0..n).filter(|&i| !in_slot[i]).collect();

        if free_vars.len() > 20 {
            // Safety limit on the brute-force portion.
            return Some(vec![false; n]);
        }

        let mut env = vec![false; n];
        if Self::enumerate_free(&mut env, &free_vars, 0, &self.slots, formula) {
            Some(env)
        } else {
            None
        }
    }

    fn enumerate_free(
        env: &mut [bool],
        free_vars: &[usize],
        free_idx: usize,
        slots: &[Vec<usize>],
        formula: &Formula,
    ) -> bool {
        if free_idx < free_vars.len() {
            let v = free_vars[free_idx];
            for value in [false, true] {
                env[v] = value;
                if Self::enumerate_free(
                    env,
                    free_vars,
                    free_idx + 1,
                    slots,
                    formula,
                ) {
                    return true;
                }
            }
            return false;
        }
        Self::enumerate_slots(env, slots, 0, formula)
    }

    fn enumerate_slots(
        env: &mut [bool],
        slots: &[Vec<usize>],
        slot_idx: usize,
        formula: &Formula,
    ) -> bool {
        if slot_idx == slots.len() {
            return formula.eval(env);
        }
        let slot = &slots[slot_idx];
        for &v in slot {
            env[v] = false;
        }
        for &true_var in slot {
            env[true_var] = true;
            if Self::enumerate_slots(env, slots, slot_idx + 1, formula) {
                return true;
            }
            env[true_var] = false;
        }
        false
    }
}

impl Default for Sat {
    fn default() -> Self {
        Self::new()
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    /// Tests `true` (conjunction of zero terms).
    #[test]
    fn test_true() {
        let sat = Sat::new();
        let true_term = Formula::And(vec![]);
        assert_eq!(true_term.to_string(), "true");

        let sol = sat.solve(&true_term);
        assert!(sol.is_some(), "true is satisfiable");
        assert!(sol.unwrap().is_empty(), "solution is empty (no variables)");
    }

    /// Tests that an unsatisfiable formula (`x ∧ ¬x`) returns `None`.
    #[test]
    fn test_unsatisfiable() {
        let mut sat = Sat::new();
        let x = sat.new_var();
        let contradiction = Formula::And(vec![
            Formula::Var(x),
            Formula::Not(Box::new(Formula::Var(x))),
        ]);
        assert!(sat.solve(&contradiction).is_none());
    }

    /// Tests that a single literal is satisfiable and its negation is also
    /// satisfiable independently.
    #[test]
    fn test_single_var() {
        let mut sat = Sat::new();
        let x = sat.new_var();

        assert!(sat.is_sat(&Formula::Var(x)));
        assert!(sat.is_sat(&Formula::Not(Box::new(Formula::Var(x)))));
    }

    /// Mirrors the workload the pattern-coverage checker generates for a
    /// datatype with 35 constructors: one boolean variable per constructor,
    /// declared as a single one-hot slot. The previous brute-force solver
    /// could not solve this without the slot, because 2^35 exceeds the
    /// safety cap.
    #[test]
    fn test_big_datatype() {
        let mut sat = Sat::new();
        let n = 35;
        let cs: Vec<usize> = (0..n).map(|_| sat.new_var()).collect();
        sat.slot(cs.clone());

        // "Is there a value not caught by C01?" — yes, any of C02..C35.
        let not_c01 = Formula::Not(Box::new(Formula::Var(cs[0])));
        let solution = sat.solve(&not_c01).expect("satisfiable");

        let true_count = solution.iter().filter(|&&b| b).count();
        assert_eq!(true_count, 1, "exactly one is true");
        assert!(!solution[cs[0]], "C01 is false");
    }
}
