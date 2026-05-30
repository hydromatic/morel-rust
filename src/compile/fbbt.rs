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

//! Feasibility-based bound tightening (FBBT).
//!
//! Given the conjuncts of a `where` clause, FBBT tightens the
//! per-variable feasible interval by propagating each constraint,
//! iterating to a fixed point. Newly deduced constant bounds are
//! returned as extra conjuncts; the existing range extractor in
//! [`crate::compile::generators`] then turns them into finite
//! generators.
//!
//! Current scope (matching morel-java's `Fbbt`): int-valued patterns over
//! (a) linear constraints `(varA + kA) OP (varB + kB)` for `OP` in
//! `<, <=, >, >=, =`; (b) `abs x OP c` for the connected-interval cases
//! (`<`, `<=`, `= 0`); and (c) `(a * b) OP c` on the non-negative
//! quadrant. Real-valued patterns are not tracked: real extents are
//! uncountable, so the downstream "not grounded" check fires for them
//! regardless.
//!
//! See <https://github.com/hydromatic/morel/issues/373>.

use crate::compile::core::Expr;
use crate::compile::library::BuiltInFunction;
use crate::compile::span::Span;
use crate::compile::types::{PrimitiveType, Type};
use crate::eval::val::Val;
use std::cmp::Ordering;
use std::collections::HashMap;
use std::rc::Rc;

/// Maximum number of fixed-point iterations (a safety cap; FBBT
/// typically converges in a small number of rounds).
const MAX_ROUNDS: usize = 8;

/// Tightens the bounds of each pattern in `unbounded` by propagating the
/// `conjuncts` of a `where` clause to a fixed point. Returns the
/// newly-deduced constant-bound conjuncts (e.g. `x < 10`), to be
/// *prepended* to the constraint list so the range extractor picks them
/// up before any cross-variable bound.
///
/// `unbounded` lists the name and type of each pattern to deduce bounds
/// for (typically the extent patterns of a `from`).
pub fn strengthen(
    unbounded: &[(String, Rc<Type>)],
    conjuncts: &[Expr],
) -> Vec<Expr> {
    let mut state = State::new(unbounded);
    if state.is_empty() {
        return Vec::new();
    }
    // Snapshot the input-implied intervals (constant bounds only) so we
    // can tell which deductions are *newly produced* by cross-variable
    // propagation versus already-expressed by an input conjunct.
    state.capture_inputs(conjuncts);
    iterate_to_fixed_point(&mut state, conjuncts);
    state.deduced_bounds()
}

/// Runs propagators on each conjunct, iterating until no bound tightens.
fn iterate_to_fixed_point(state: &mut State, conjuncts: &[Expr]) {
    for _ in 0..MAX_ROUNDS {
        let mut changed = false;
        for conjunct in conjuncts {
            changed |= propagate_linear(conjunct, state);
            changed |= propagate_abs(conjunct, state);
            changed |= propagate_multiply(conjunct, state);
        }
        if !changed {
            return;
        }
    }
}

// ---------------------------------------------------------------------------
// Rational arithmetic
// ---------------------------------------------------------------------------

/// An exact rational `num / den` with `den > 0`, always in lowest terms.
/// Division (from the multiply propagator) can produce fractions, so the
/// interval engine works in rationals rather than integers or floats.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
struct Rat {
    num: i128,
    den: i128,
}

fn gcd(a: i128, b: i128) -> i128 {
    let (mut a, mut b) = (a.abs(), b.abs());
    while b != 0 {
        let t = a % b;
        a = b;
        b = t;
    }
    a.max(1)
}

impl Rat {
    fn new(num: i128, den: i128) -> Rat {
        debug_assert!(den != 0);
        let (num, den) = if den < 0 { (-num, -den) } else { (num, den) };
        let g = gcd(num, den);
        Rat {
            num: num / g,
            den: den / g,
        }
    }

    fn int(n: i128) -> Rat {
        Rat { num: n, den: 1 }
    }

    fn add(self, o: Rat) -> Rat {
        Rat::new(self.num * o.den + o.num * self.den, self.den * o.den)
    }

    fn sub(self, o: Rat) -> Rat {
        Rat::new(self.num * o.den - o.num * self.den, self.den * o.den)
    }

    fn neg(self) -> Rat {
        Rat {
            num: -self.num,
            den: self.den,
        }
    }

    fn div(self, o: Rat) -> Rat {
        Rat::new(self.num * o.den, self.den * o.num)
    }

    fn signum(self) -> i32 {
        self.num.signum() as i32
    }

    fn is_int(self) -> bool {
        self.den == 1
    }

    /// Largest integer `<= self`.
    fn floor(self) -> i128 {
        if self.num >= 0 {
            self.num / self.den
        } else {
            -((-self.num + self.den - 1) / self.den)
        }
    }

    /// Smallest integer `>= self`.
    fn ceil(self) -> i128 {
        -(self.neg().floor())
    }
}

impl PartialOrd for Rat {
    fn partial_cmp(&self, o: &Rat) -> Option<Ordering> {
        Some(self.cmp(o))
    }
}

impl Ord for Rat {
    fn cmp(&self, o: &Rat) -> Ordering {
        (self.num * o.den).cmp(&(o.num * self.den))
    }
}

// ---------------------------------------------------------------------------
// Connected intervals
// ---------------------------------------------------------------------------

/// One endpoint of an interval.
#[derive(Copy, Clone, PartialEq, Debug)]
enum End {
    /// Unbounded (−∞ for a lower endpoint, +∞ for an upper one).
    Inf,
    /// A finite endpoint at `value`; `open` is true for a strict bound.
    At { value: Rat, open: bool },
}

/// A single connected interval, or `Empty` (infeasible). FBBT's
/// propagators only ever produce connected ranges (disjoint cases such
/// as `abs x > c` are skipped), so intersections stay connected and a
/// full range-set is unnecessary.
#[derive(Copy, Clone, Debug)]
enum Interval {
    Empty,
    Range { lo: End, hi: End },
}

impl Interval {
    fn all() -> Interval {
        Interval::Range {
            lo: End::Inf,
            hi: End::Inf,
        }
    }

    fn less_than(c: Rat) -> Interval {
        Interval::Range {
            lo: End::Inf,
            hi: End::At {
                value: c,
                open: true,
            },
        }
    }

    fn at_most(c: Rat) -> Interval {
        Interval::Range {
            lo: End::Inf,
            hi: End::At {
                value: c,
                open: false,
            },
        }
    }

    fn greater_than(c: Rat) -> Interval {
        Interval::Range {
            lo: End::At {
                value: c,
                open: true,
            },
            hi: End::Inf,
        }
    }

    fn at_least(c: Rat) -> Interval {
        Interval::Range {
            lo: End::At {
                value: c,
                open: false,
            },
            hi: End::Inf,
        }
    }

    fn singleton(c: Rat) -> Interval {
        Interval::Range {
            lo: End::At {
                value: c,
                open: false,
            },
            hi: End::At {
                value: c,
                open: false,
            },
        }
    }

    fn from_op(op: Cmp, c: Rat) -> Interval {
        match op {
            Cmp::Lt => Interval::less_than(c),
            Cmp::Le => Interval::at_most(c),
            Cmp::Gt => Interval::greater_than(c),
            Cmp::Ge => Interval::at_least(c),
            Cmp::Eq => Interval::singleton(c),
        }
    }

    /// Intersects two connected intervals. Picks the tighter (greater)
    /// lower endpoint and the tighter (lesser) upper endpoint, then
    /// collapses to `Empty` if they cross.
    fn intersect(self, o: Interval) -> Interval {
        let (lo1, hi1) = match self {
            Interval::Empty => return Interval::Empty,
            Interval::Range { lo, hi } => (lo, hi),
        };
        let (lo2, hi2) = match o {
            Interval::Empty => return Interval::Empty,
            Interval::Range { lo, hi } => (lo, hi),
        };
        let lo = tighter_lower(lo1, lo2);
        let hi = tighter_upper(hi1, hi2);
        normalize(lo, hi)
    }

    fn is_empty(self) -> bool {
        matches!(self, Interval::Empty)
    }

    fn lower(self) -> End {
        match self {
            Interval::Range { lo, .. } => lo,
            Interval::Empty => End::Inf,
        }
    }

    fn upper(self) -> End {
        match self {
            Interval::Range { hi, .. } => hi,
            Interval::Empty => End::Inf,
        }
    }

    /// Translates this interval by `delta` along the number line.
    fn shift(self, delta: Rat) -> Interval {
        let shift_end = |e: End| match e {
            End::Inf => End::Inf,
            End::At { value, open } => End::At {
                value: value.add(delta),
                open,
            },
        };
        match self {
            Interval::Empty => Interval::Empty,
            Interval::Range { lo, hi } => Interval::Range {
                lo: shift_end(lo),
                hi: shift_end(hi),
            },
        }
    }
}

/// Returns the tighter (greater) of two lower endpoints.
fn tighter_lower(a: End, b: End) -> End {
    match (a, b) {
        (End::Inf, x) | (x, End::Inf) => x,
        (
            End::At {
                value: va,
                open: oa,
            },
            End::At {
                value: vb,
                open: ob,
            },
        ) => match va.cmp(&vb) {
            Ordering::Greater => a,
            Ordering::Less => b,
            Ordering::Equal => End::At {
                value: va,
                open: oa || ob,
            },
        },
    }
}

/// Returns the tighter (lesser) of two upper endpoints.
fn tighter_upper(a: End, b: End) -> End {
    match (a, b) {
        (End::Inf, x) | (x, End::Inf) => x,
        (
            End::At {
                value: va,
                open: oa,
            },
            End::At {
                value: vb,
                open: ob,
            },
        ) => match va.cmp(&vb) {
            Ordering::Less => a,
            Ordering::Greater => b,
            Ordering::Equal => End::At {
                value: va,
                open: oa || ob,
            },
        },
    }
}

/// Builds an interval from a lower and upper endpoint, collapsing to
/// `Empty` when they cross or meet at an excluded point.
fn normalize(lo: End, hi: End) -> Interval {
    if let (
        End::At {
            value: lv,
            open: lo_open,
        },
        End::At {
            value: hv,
            open: hi_open,
        },
    ) = (lo, hi)
    {
        match lv.cmp(&hv) {
            Ordering::Greater => return Interval::Empty,
            Ordering::Equal => {
                if lo_open || hi_open {
                    return Interval::Empty;
                }
            }
            Ordering::Less => {}
        }
    }
    Interval::Range { lo, hi }
}

// ---------------------------------------------------------------------------
// Propagation state
// ---------------------------------------------------------------------------

/// Per-pattern feasible interval. Keyed by pattern name (within a single
/// `from` scope names are unique).
struct State {
    /// The int-typed patterns FBBT tracks, and their order-of-discovery
    /// types (used when materializing deduced bounds).
    pats: HashMap<String, Rc<Type>>,
    intervals: HashMap<String, Interval>,
    /// Snapshot of intervals after only the constant-bound conjuncts of
    /// the original where clause, to identify newly-deduced bounds.
    inputs: HashMap<String, Interval>,
}

impl State {
    fn new(unbounded: &[(String, Rc<Type>)]) -> State {
        let mut pats = HashMap::new();
        for (name, t) in unbounded {
            if is_int(t) {
                pats.insert(name.clone(), t.clone());
            }
        }
        State {
            pats,
            intervals: HashMap::new(),
            inputs: HashMap::new(),
        }
    }

    fn is_empty(&self) -> bool {
        self.pats.is_empty()
    }

    fn knows(&self, name: &str) -> bool {
        self.pats.contains_key(name)
    }

    fn get(&self, name: &str) -> Interval {
        *self.intervals.get(name).unwrap_or(&Interval::all())
    }

    /// Intersects `name`'s current interval with `rs`; returns whether it
    /// actually tightened.
    fn tighten(&mut self, name: &str, rs: Interval) -> bool {
        if !self.knows(name) {
            return false;
        }
        let current = self.get(name);
        let next = current.intersect(rs);
        if interval_eq(next, current) {
            return false;
        }
        self.intervals.insert(name.to_string(), next);
        true
    }

    /// Initializes `inputs` by applying only the constant-side bounds of
    /// the original conjuncts, then snapshotting.
    fn capture_inputs(&mut self, conjuncts: &[Expr]) {
        for c in conjuncts {
            apply_constant_bound(c, self);
        }
        self.inputs = self.intervals.clone();
    }

    /// Emits the newly-deduced constant-bound conjuncts. Patterns are
    /// visited in name order so output is deterministic; lower before
    /// upper for the same pattern.
    fn deduced_bounds(&self) -> Vec<Expr> {
        let mut names: Vec<&String> = self.intervals.keys().collect();
        names.sort();
        let mut out = Vec::new();
        for name in names {
            let final_iv = self.get(name);
            if final_iv.is_empty() {
                continue;
            }
            let input_iv = *self.inputs.get(name).unwrap_or(&Interval::all());
            let t = &self.pats[name];
            if let End::At { value, open } = final_iv.lower()
                && lower_tighter(final_iv.lower(), input_iv.lower())
            {
                out.push(bound_conjunct(name, t, true, value, open));
            }
            if let End::At { value, open } = final_iv.upper()
                && upper_tighter(final_iv.upper(), input_iv.upper())
            {
                out.push(bound_conjunct(name, t, false, value, open));
            }
        }
        out
    }
}

fn interval_eq(a: Interval, b: Interval) -> bool {
    match (a, b) {
        (Interval::Empty, Interval::Empty) => true,
        (
            Interval::Range { lo: l1, hi: h1 },
            Interval::Range { lo: l2, hi: h2 },
        ) => l1 == l2 && h1 == h2,
        _ => false,
    }
}

/// Returns whether `final_lo` is a strictly tighter lower endpoint than
/// `input_lo`.
fn lower_tighter(final_lo: End, input_lo: End) -> bool {
    match (final_lo, input_lo) {
        (_, End::Inf) => matches!(final_lo, End::At { .. }),
        (End::Inf, _) => false,
        (
            End::At {
                value: fv,
                open: fo,
            },
            End::At {
                value: iv,
                open: io,
            },
        ) => match fv.cmp(&iv) {
            Ordering::Greater => true,
            Ordering::Less => false,
            Ordering::Equal => fo && !io,
        },
    }
}

fn upper_tighter(final_hi: End, input_hi: End) -> bool {
    match (final_hi, input_hi) {
        (_, End::Inf) => matches!(final_hi, End::At { .. }),
        (End::Inf, _) => false,
        (
            End::At {
                value: fv,
                open: fo,
            },
            End::At {
                value: iv,
                open: io,
            },
        ) => match fv.cmp(&iv) {
            Ordering::Less => true,
            Ordering::Greater => false,
            Ordering::Equal => fo && !io,
        },
    }
}

// ---------------------------------------------------------------------------
// Linear-term decomposition
// ---------------------------------------------------------------------------

/// A linear term `(var + offset)`, or a pure constant when `var` is None.
struct Term {
    var: Option<String>,
    offset: Rat,
}

/// Decomposes `exp` into a linear term `(var?, offset)`, or `None` if it
/// is not a linear combination of one variable and integer constants.
fn linear_term(exp: &Expr) -> Option<Term> {
    match exp {
        Expr::Identifier(_, name) => Some(Term {
            var: Some(name.clone()),
            offset: Rat::int(0),
        }),
        Expr::Literal(_, Val::Int(n)) => Some(Term {
            var: None,
            offset: Rat::int(*n as i128),
        }),
        Expr::Apply(_, f, arg, _) => {
            let op = builtin_of(f)?;
            let minus = matches!(op, BuiltInFunction::IntMinus);
            if !minus && !matches!(op, BuiltInFunction::IntPlus) {
                return None;
            }
            let (a_e, b_e) = match arg.as_ref() {
                Expr::Tuple(_, args) if args.len() == 2 => (&args[0], &args[1]),
                _ => return None,
            };
            let a = linear_term(a_e)?;
            let b = linear_term(b_e)?;
            let other_offset = if minus { b.offset.neg() } else { b.offset };
            match (&a.var, &b.var) {
                (Some(_), Some(_)) => None, // two distinct variables
                (None, None) => Some(Term {
                    var: None,
                    offset: a.offset.add(other_offset),
                }),
                (Some(_), None) => Some(Term {
                    var: a.var,
                    offset: a.offset.add(other_offset),
                }),
                (None, Some(_)) => {
                    // `const - var` would introduce a -1 coefficient.
                    if minus {
                        None
                    } else {
                        Some(Term {
                            var: b.var,
                            offset: a.offset.add(b.offset),
                        })
                    }
                }
            }
        }
        _ => None,
    }
}

/// If `exp` is an int literal, returns its value.
fn numeric_literal(exp: &Expr) -> Option<Rat> {
    match exp {
        Expr::Literal(_, Val::Int(n)) => Some(Rat::int(*n as i128)),
        _ => None,
    }
}

// ---------------------------------------------------------------------------
// Comparison-op helpers
// ---------------------------------------------------------------------------

#[derive(Copy, Clone, PartialEq)]
enum Cmp {
    Lt,
    Le,
    Gt,
    Ge,
    Eq,
}

impl Cmp {
    /// The operator with its operands swapped (`a < b` ⇔ `b > a`).
    fn reverse(self) -> Cmp {
        match self {
            Cmp::Lt => Cmp::Gt,
            Cmp::Le => Cmp::Ge,
            Cmp::Gt => Cmp::Lt,
            Cmp::Ge => Cmp::Le,
            Cmp::Eq => Cmp::Eq,
        }
    }
}

fn cmp_of(op: BuiltInFunction) -> Option<Cmp> {
    match op {
        BuiltInFunction::IntLt => Some(Cmp::Lt),
        BuiltInFunction::IntLe => Some(Cmp::Le),
        BuiltInFunction::IntGt => Some(Cmp::Gt),
        BuiltInFunction::IntGe => Some(Cmp::Ge),
        BuiltInFunction::IntEq => Some(Cmp::Eq),
        _ => None,
    }
}

/// If `exp` is `Apply(Literal(Fn(op)), Tuple([a, b]))`, returns
/// `(a, b, op)`.
fn binary_call(exp: &Expr) -> Option<(&Expr, &Expr, BuiltInFunction)> {
    if let Expr::Apply(_, f, arg, _) = exp
        && let Some(op) = builtin_of(f)
        && let Expr::Tuple(_, args) = arg.as_ref()
        && args.len() == 2
    {
        return Some((&args[0], &args[1], op));
    }
    None
}

/// Returns the comparison `(lhs, rhs, op)` if `exp` is a comparison.
fn comparison(exp: &Expr) -> Option<(&Expr, &Expr, Cmp)> {
    let (a, b, op) = binary_call(exp)?;
    Some((a, b, cmp_of(op)?))
}

/// Resolves `f` (an inlined `Literal(Fn(_))`) to its built-in function.
fn builtin_of(f: &Expr) -> Option<BuiltInFunction> {
    match f {
        Expr::Literal(_, Val::Fn(b)) => Some(*b),
        _ => None,
    }
}

// ---------------------------------------------------------------------------
// Propagators
// ---------------------------------------------------------------------------

/// Propagator for linear constraints `(varA + kA) OP (varB + kB)`.
fn propagate_linear(constraint: &Expr, state: &mut State) -> bool {
    let (lhs_e, rhs_e, op) = match comparison(constraint) {
        Some(t) => t,
        None => return false,
    };
    let lhs = match linear_term(lhs_e) {
        Some(t) => t,
        None => return false,
    };
    let rhs = match linear_term(rhs_e) {
        Some(t) => t,
        None => return false,
    };
    match (&lhs.var, &rhs.var) {
        (None, None) => false,
        (None, Some(rv)) => {
            // const OP (rv + k)  ⇒  rv reverse(OP) (const - k)
            tighten_from_constant(
                state,
                rv,
                op.reverse(),
                lhs.offset.sub(rhs.offset),
            )
        }
        (Some(lv), None) => {
            tighten_from_constant(state, lv, op, rhs.offset.sub(lhs.offset))
        }
        (Some(lv), Some(rv)) => {
            // varA + kA OP varB + kB  ⇒  varA OP varB + (kB - kA)
            let delta = rhs.offset.sub(lhs.offset);
            let mut changed = false;
            changed |= tighten_from_other(state, lv, op, rv, delta);
            changed |=
                tighten_from_other(state, rv, op.reverse(), lv, delta.neg());
            changed
        }
    }
}

/// Applies a `var op constant` tightening (used by `capture_inputs`).
fn apply_constant_bound(constraint: &Expr, state: &mut State) -> bool {
    let (lhs_e, rhs_e, op) = match comparison(constraint) {
        Some(t) => t,
        None => return false,
    };
    let lhs = match linear_term(lhs_e) {
        Some(t) => t,
        None => return false,
    };
    let rhs = match linear_term(rhs_e) {
        Some(t) => t,
        None => return false,
    };
    match (&lhs.var, &rhs.var) {
        (Some(lv), None) => {
            tighten_from_constant(state, lv, op, rhs.offset.sub(lhs.offset))
        }
        (None, Some(rv)) => tighten_from_constant(
            state,
            rv,
            op.reverse(),
            lhs.offset.sub(rhs.offset),
        ),
        _ => false,
    }
}

fn tighten_from_constant(
    state: &mut State,
    name: &str,
    op: Cmp,
    c: Rat,
) -> bool {
    if !state.knows(name) {
        return false;
    }
    state.tighten(name, Interval::from_op(op, c))
}

/// Tightens `target`'s interval by `target OP (other + delta)`, using
/// `other`'s current interval.
fn tighten_from_other(
    state: &mut State,
    target: &str,
    op: Cmp,
    other: &str,
    delta: Rat,
) -> bool {
    if !state.knows(target) {
        return false;
    }
    let other_iv = state.get(other);
    if other_iv.is_empty() {
        return false;
    }
    let bound = match range_from_other(op, other_iv, delta) {
        Some(b) => b,
        None => return false,
    };
    state.tighten(target, bound)
}

/// Given `v OP (other + delta)` and `other`'s interval, returns the
/// interval `v` must lie in, or `None` if the relevant side is unbounded.
fn range_from_other(op: Cmp, other: Interval, delta: Rat) -> Option<Interval> {
    match op {
        Cmp::Lt => match other.upper() {
            End::Inf => None,
            End::At { value, .. } => {
                Some(Interval::less_than(value.add(delta)))
            }
        },
        Cmp::Le => match other.upper() {
            End::Inf => None,
            End::At { value, open } => Some(if open {
                Interval::less_than(value.add(delta))
            } else {
                Interval::at_most(value.add(delta))
            }),
        },
        Cmp::Gt => match other.lower() {
            End::Inf => None,
            End::At { value, .. } => {
                Some(Interval::greater_than(value.add(delta)))
            }
        },
        Cmp::Ge => match other.lower() {
            End::Inf => None,
            End::At { value, open } => Some(if open {
                Interval::greater_than(value.add(delta))
            } else {
                Interval::at_least(value.add(delta))
            }),
        },
        Cmp::Eq => {
            if matches!(other.lower(), End::Inf)
                && matches!(other.upper(), End::Inf)
            {
                None
            } else {
                Some(other.shift(delta))
            }
        }
    }
}

/// Propagator for `abs x OP c` (or `c OP abs x`), handling the
/// connected-interval cases (`<`, `<=`, `= 0`).
fn propagate_abs(constraint: &Expr, state: &mut State) -> bool {
    let (lhs, rhs, op) = match comparison(constraint) {
        Some(t) => t,
        None => return false,
    };
    let (arg, constant, op) = match extract_abs_arg(lhs) {
        Some(a) => match numeric_literal(rhs) {
            Some(c) => (a, c, op),
            None => return false,
        },
        None => match extract_abs_arg(rhs) {
            Some(a) => match numeric_literal(lhs) {
                Some(c) => (a, c, op.reverse()),
                None => return false,
            },
            None => return false,
        },
    };
    if !state.knows(&arg) {
        return false;
    }
    match op {
        Cmp::Lt => {
            // abs x < c: x in (-c, c). c <= 0 is infeasible.
            if constant.signum() <= 0 {
                return state.tighten(&arg, Interval::Empty);
            }
            state.tighten(
                &arg,
                normalize(
                    End::At {
                        value: constant.neg(),
                        open: true,
                    },
                    End::At {
                        value: constant,
                        open: true,
                    },
                ),
            )
        }
        Cmp::Le => {
            // abs x <= c: x in [-c, c]. c < 0 is infeasible.
            if constant.signum() < 0 {
                return state.tighten(&arg, Interval::Empty);
            }
            state.tighten(
                &arg,
                normalize(
                    End::At {
                        value: constant.neg(),
                        open: false,
                    },
                    End::At {
                        value: constant,
                        open: false,
                    },
                ),
            )
        }
        Cmp::Eq => {
            // abs x = 0: x = 0. Non-zero gives two disjoint points, which
            // we don't materialize per-side.
            if constant.signum() == 0 {
                state.tighten(&arg, Interval::singleton(Rat::int(0)))
            } else {
                false
            }
        }
        // Disjoint cases (>, >=, = c) — skip; constraint stays a filter.
        Cmp::Gt | Cmp::Ge => false,
    }
}

/// If `exp` is `abs <id>` (the global `abs` or `Int.abs`), returns the
/// argument variable name.
fn extract_abs_arg(exp: &Expr) -> Option<String> {
    if let Expr::Apply(_, f, arg, _) = exp
        && let Some(b) = builtin_of(f)
        && matches!(b, BuiltInFunction::GAbs | BuiltInFunction::IntAbs)
        && let Expr::Identifier(_, name) = arg.as_ref()
    {
        return Some(name.clone());
    }
    None
}

/// Propagator for `A * B OP c` (or `c OP A * B`) on the non-negative
/// quadrant, where `A`, `B` are each linear in a single variable.
fn propagate_multiply(constraint: &Expr, state: &mut State) -> bool {
    let (lhs, rhs, op) = match comparison(constraint) {
        Some(t) => t,
        None => return false,
    };
    if matches!(op, Cmp::Eq) {
        return false;
    }
    let (product, constant, op) = if let Some(p) = as_multiply(lhs) {
        match numeric_literal(rhs) {
            Some(c) => (p, c, op),
            None => return false,
        }
    } else if let Some(p) = as_multiply(rhs) {
        match numeric_literal(lhs) {
            Some(c) => (p, c, op.reverse()),
            None => return false,
        }
    } else {
        return false;
    };
    let a = match linear_term(product.0) {
        Some(t) => t,
        None => return false,
    };
    let b = match linear_term(product.1) {
        Some(t) => t,
        None => return false,
    };
    let (av, bv) = match (&a.var, &b.var) {
        (Some(av), Some(bv)) => (av.clone(), bv.clone()),
        _ => return false,
    };
    if !state.knows(&av) || !state.knows(&bv) {
        return false;
    }
    let mut changed = false;
    changed |= tighten_multiply_side(state, &a, &b, op, constant);
    changed |= tighten_multiply_side(state, &b, &a, op, constant);
    changed
}

/// Tightens `self.var`'s interval given `self * other OP c`, using
/// `other`'s interval shifted by its offset.
fn tighten_multiply_side(
    state: &mut State,
    self_t: &Term,
    other_t: &Term,
    op: Cmp,
    c: Rat,
) -> bool {
    let self_var = match &self_t.var {
        Some(v) => v,
        None => return false,
    };
    let other_span = state
        .get(other_t.var.as_ref().unwrap())
        .shift(other_t.offset);
    match op {
        Cmp::Lt | Cmp::Le => {
            // need other.lo > 0 to divide.
            let lo = match other_span.lower() {
                End::At { value, .. } if value.signum() > 0 => value,
                _ => return false,
            };
            let self_upper = c.div(lo);
            let var_upper = self_upper.sub(self_t.offset);
            state.tighten(self_var, Interval::less_than(var_upper))
        }
        Cmp::Gt | Cmp::Ge => {
            let hi = match other_span.upper() {
                End::At { value, .. } if value.signum() > 0 => value,
                _ => return false,
            };
            let self_lower = c.div(hi);
            let var_lower = self_lower.sub(self_t.offset);
            state.tighten(self_var, Interval::greater_than(var_lower))
        }
        Cmp::Eq => false,
    }
}

/// If `exp` is `A * B`, returns the two operand expressions.
fn as_multiply(exp: &Expr) -> Option<(&Expr, &Expr)> {
    if let Expr::Apply(_, f, arg, _) = exp
        && let Some(BuiltInFunction::IntTimes) = builtin_of(f)
        && let Expr::Tuple(_, args) = arg.as_ref()
        && args.len() == 2
    {
        return Some((&args[0], &args[1]));
    }
    None
}

// ---------------------------------------------------------------------------
// Materializing deduced bounds
// ---------------------------------------------------------------------------

/// Builds a conjunct expressing one deduced bound, e.g. `x >= 1`. For an
/// int-typed pattern, a fractional value is snapped to the tightest
/// integer endpoint (`x > 7.5` ⇒ `x >= 8`, `x < 7.5` ⇒ `x <= 7`).
fn bound_conjunct(
    name: &str,
    t: &Rc<Type>,
    lower: bool,
    value: Rat,
    strict: bool,
) -> Expr {
    let (int_val, strict) = if value.is_int() {
        (value.num, strict)
    } else if lower {
        (value.ceil(), false)
    } else {
        (value.floor(), false)
    };
    let id = Expr::Identifier(t.clone(), name.to_string());
    let lit = Expr::Literal(t.clone(), Val::Int(int_val as i32));
    let op = match (lower, strict) {
        (true, true) => BuiltInFunction::IntGt,
        (true, false) => BuiltInFunction::IntGe,
        (false, true) => BuiltInFunction::IntLt,
        (false, false) => BuiltInFunction::IntLe,
    };
    compare(op, id, lit)
}

/// Builds `Apply(Literal(Fn(op)), (a, b))` for a boolean comparison.
fn compare(op: BuiltInFunction, a: Expr, b: Expr) -> Expr {
    let int_t = Rc::new(Type::Primitive(PrimitiveType::Int));
    let bool_t = Rc::new(Type::Primitive(PrimitiveType::Bool));
    let pair_t = Rc::new(Type::Tuple(vec![int_t.clone(), int_t.clone()]));
    let fn_t = Rc::new(Type::Fn(pair_t.clone(), bool_t.clone()));
    let fn_expr = Expr::Literal(fn_t, Val::Fn(op));
    let arg = Expr::Tuple(pair_t, vec![a, b]);
    Expr::Apply(bool_t, Box::new(fn_expr), Box::new(arg), Span::new(""))
}

fn is_int(t: &Type) -> bool {
    matches!(t, Type::Primitive(PrimitiveType::Int))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rat_floor_ceil() {
        // 30 / 4 = 7.5
        let v = Rat::int(30).div(Rat::int(4));
        assert_eq!(v.floor(), 7);
        assert_eq!(v.ceil(), 8);
        assert!(!v.is_int());
        // Integer-valued division stays exact.
        let w = Rat::int(30).div(Rat::int(3));
        assert!(w.is_int());
        assert_eq!(w.floor(), 10);
        assert_eq!(w.ceil(), 10);
        // Negative fraction: -7.5
        let n = v.neg();
        assert_eq!(n.floor(), -8);
        assert_eq!(n.ceil(), -7);
    }

    #[test]
    fn rat_arithmetic_and_order() {
        assert_eq!(Rat::int(1).add(Rat::int(2)), Rat::int(3));
        assert_eq!(Rat::int(5).sub(Rat::int(8)), Rat::int(-3));
        assert!(Rat::int(1).div(Rat::int(2)) < Rat::int(1));
        assert_eq!(Rat::int(2).div(Rat::int(4)), Rat::int(1).div(Rat::int(2)));
        assert_eq!(Rat::int(0).signum(), 0);
        assert_eq!(Rat::int(-3).signum(), -1);
    }

    fn lo_val(iv: Interval) -> Option<(i128, bool)> {
        match iv.lower() {
            End::At { value, open } if value.is_int() => {
                Some((value.num, open))
            }
            _ => None,
        }
    }

    fn hi_val(iv: Interval) -> Option<(i128, bool)> {
        match iv.upper() {
            End::At { value, open } if value.is_int() => {
                Some((value.num, open))
            }
            _ => None,
        }
    }

    #[test]
    fn interval_intersection() {
        // (0, ∞) ∩ (−∞, 10) = (0, 10)
        let iv = Interval::greater_than(Rat::int(0))
            .intersect(Interval::less_than(Rat::int(10)));
        assert_eq!(lo_val(iv), Some((0, true)));
        assert_eq!(hi_val(iv), Some((10, true)));
        // Same-value endpoints: open wins over closed.
        let iv2 = Interval::at_least(Rat::int(5))
            .intersect(Interval::greater_than(Rat::int(5)));
        assert_eq!(lo_val(iv2), Some((5, true)));
    }

    #[test]
    fn interval_empty() {
        // (10, ∞) ∩ (−∞, 5) is empty.
        assert!(
            Interval::greater_than(Rat::int(10))
                .intersect(Interval::less_than(Rat::int(5)))
                .is_empty()
        );
        // [5, 5] is a singleton, not empty.
        assert!(!Interval::singleton(Rat::int(5)).is_empty());
        // (5, 5] collapses to empty.
        assert!(
            Interval::greater_than(Rat::int(5))
                .intersect(Interval::at_most(Rat::int(5)))
                .is_empty()
        );
    }

    #[test]
    fn abs_lt_interval() {
        // abs x < 5  ⇒  x in (−5, 5).
        let iv = normalize(
            End::At {
                value: Rat::int(-5),
                open: true,
            },
            End::At {
                value: Rat::int(5),
                open: true,
            },
        );
        assert_eq!(lo_val(iv), Some((-5, true)));
        assert_eq!(hi_val(iv), Some((5, true)));
    }
}
