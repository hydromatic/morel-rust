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
            changed |= propagate_sum(conjunct, state);
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

    fn mul(self, o: Rat) -> Rat {
        Rat::new(self.num * o.num, self.den * o.den)
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
        // Track any numeric variable, not only the ones whose bounds we
        // are deducing: a variable that a scan bound, such as `z` in
        // `from z in [1, 2, 3], x where x < z`, tells us about its
        // neighbours even though it needs no bounds itself.
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
        // First, the bounds that the range extractor can already use,
        // such as `x > 0`. Re-emitting those would be noise, so they are
        // the baseline.
        for c in conjuncts {
            apply_constant_bound(c, self, true);
        }
        self.inputs = self.intervals.clone();
        // Then the bounds that take arithmetic to see, such as the
        // `x = 2` implied by `x + 1 = 3`. They constrain propagation, but
        // the extractor cannot use them as they stand, so if they survive
        // to the end they are worth emitting in a form that it can.
        for c in conjuncts {
            apply_constant_bound(c, self, false);
        }
    }

    /// Emits the newly-deduced constant-bound conjuncts. Patterns are
    /// visited in name order so output is deterministic; lower before
    /// upper for the same pattern.
    fn deduced_bounds(&self) -> Vec<Expr> {
        let mut names: Vec<&String> = self.intervals.keys().collect();
        names.sort();
        let mut out = Vec::new();
        for name in names {
            if !self.pats.contains_key(name) {
                // A variable that a scan bound. It needs no bounds of
                // its own.
                continue;
            }
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

// ---------------------------------------------------------------------------
// Linear forms
// ---------------------------------------------------------------------------

/// An atom of a linear form: a variable, or an `abs` term.
///
/// An `abs` term is a quantity that the arithmetic cannot see into but
/// whose value lies in a known interval, `[0, inf)` -- which is exactly
/// what a variable is, to FBBT.
#[derive(Clone)]
enum Atom {
    Var(String),
    Abs(Expr),
}

impl Atom {
    /// A key that tells atoms apart, as morel-java's structural equality
    /// on expressions does.
    fn key(&self) -> String {
        match self {
            Atom::Var(name) => format!("v{}", name),
            Atom::Abs(e) => format!("a{}", e),
        }
    }
}

/// A linear combination of atoms, `c1 * a1 + ... + cn * an + k`.
#[derive(Clone)]
struct LinearForm {
    /// Coefficients, keyed by atom. No coefficient is zero. In the order
    /// the atoms were met, so that deductions are deterministic.
    terms: Vec<(Atom, Rat)>,
    constant: Rat,
}

impl LinearForm {
    /// Creates a form with no atoms.
    fn constant(constant: Rat) -> LinearForm {
        LinearForm {
            terms: Vec::new(),
            constant,
        }
    }

    /// Creates the form `atom`, with coefficient 1.
    fn atom(atom: Atom) -> LinearForm {
        LinearForm {
            terms: vec![(atom, Rat::int(1))],
            constant: Rat::int(0),
        }
    }

    /// Returns whether this form has no atoms.
    fn is_constant(&self) -> bool {
        self.terms.is_empty()
    }

    /// Returns the sum of this form and `that`.
    fn plus(&self, that: &LinearForm) -> LinearForm {
        self.combine(that, Rat::int(1))
    }

    /// Returns the difference of this form and `that`.
    fn minus(&self, that: &LinearForm) -> LinearForm {
        self.combine(that, Rat::int(-1))
    }

    fn combine(&self, that: &LinearForm, scale: Rat) -> LinearForm {
        let mut terms = self.terms.clone();
        for (atom, c) in &that.terms {
            let c = c.mul(scale);
            let key = atom.key();
            match terms.iter().position(|(a, _)| a.key() == key) {
                Some(i) => {
                    let sum = terms[i].1.add(c);
                    if sum.signum() == 0 {
                        // An atom whose coefficients cancel (as `x` does
                        // in `x + y - x`) drops out of the form.
                        terms.remove(i);
                    } else {
                        terms[i].1 = sum;
                    }
                }
                None => terms.push((atom.clone(), c)),
            }
        }
        LinearForm {
            terms,
            constant: self.constant.add(that.constant.mul(scale)),
        }
    }

    /// Returns this form with every coefficient and the constant scaled.
    fn times(&self, scale: Rat) -> LinearForm {
        if scale.signum() == 0 {
            return LinearForm::constant(Rat::int(0));
        }
        LinearForm {
            terms: self
                .terms
                .iter()
                .map(|(a, c)| (a.clone(), c.mul(scale)))
                .collect(),
            constant: self.constant.mul(scale),
        }
    }
}

/// Decomposes `exp` into a [`LinearForm`], or `None` if `exp` is not
/// linear.
///
/// Handles addition, subtraction, negation, and multiplication where one
/// side is constant. A product of two variables (say `x * y`) is not
/// linear, and gives `None`.
///
/// Examples: `2 * x + 3` gives `2x + 3`; `x - y` gives `x - y`;
/// `abs (x - 2) + abs (y - 3)` gives a sum of two atoms; `x * y` gives
/// `None`.
fn linear_form(exp: &Expr) -> Option<LinearForm> {
    if let Expr::Identifier(t, name) = exp {
        // A variable of another type is not arithmetic we can follow.
        return is_int(t).then(|| LinearForm::atom(Atom::Var(name.clone())));
    }
    if is_abs(exp) {
        return Some(LinearForm::atom(Atom::Abs(exp.clone())));
    }
    if let Some(c) = numeric_literal(exp) {
        return Some(LinearForm::constant(c));
    }
    let Expr::Apply(_, f, arg, _) = exp else {
        return None;
    };
    let op = builtin_of(f)?;
    if matches!(op, BuiltInFunction::GNegate | BuiltInFunction::IntNegate) {
        return Some(linear_form(arg)?.times(Rat::int(-1)));
    }
    if !matches!(
        op,
        BuiltInFunction::GPlus
            | BuiltInFunction::IntPlus
            | BuiltInFunction::GMinus
            | BuiltInFunction::IntMinus
            | BuiltInFunction::GTimes
            | BuiltInFunction::IntTimes
    ) {
        return None;
    }
    let Expr::Tuple(_, args) = arg.as_ref() else {
        return None;
    };
    if args.len() != 2 {
        return None;
    }
    let a = linear_form(&args[0])?;
    let b = linear_form(&args[1])?;
    match op {
        BuiltInFunction::GPlus | BuiltInFunction::IntPlus => Some(a.plus(&b)),
        BuiltInFunction::GMinus | BuiltInFunction::IntMinus => {
            Some(a.minus(&b))
        }
        // Multiplication is linear only if one side is constant.
        _ if a.is_constant() => Some(b.times(a.constant)),
        _ if b.is_constant() => Some(a.times(b.constant)),
        _ => None,
    }
}

/// Returns whether `exp` is a call to `abs`.
fn is_abs(exp: &Expr) -> bool {
    match exp {
        Expr::Apply(_, f, _, _) => matches!(
            builtin_of(f),
            Some(BuiltInFunction::GAbs | BuiltInFunction::IntAbs)
        ),
        _ => false,
    }
}

/// Returns the argument of an `abs` term.
fn abs_arg(exp: &Expr) -> &Expr {
    match exp {
        Expr::Apply(_, _, arg, _) => arg,
        _ => panic!("not abs: {}", exp),
    }
}

/// Propagator for a linear constraint over any number of atoms, with any
/// coefficients: `c1 * a1 + ... + cn * an OP k`.
///
/// This is FBBT proper. Moving everything to the left gives `sum OP 0`.
/// To bound one atom, substitute the extreme values that the others'
/// current intervals allow, and solve. For example, `25q + 10d + 5n + p
/// = 100` with `q, d, n, p >= 0` gives `25q <= 100`, that is `q <= 4`;
/// and likewise `d <= 10`, `n <= 20`, `p <= 100`.
///
/// An `abs` term is an atom whose interval is `[0, inf)`, and so it
/// takes part on the same terms as a variable. In
/// `abs (x - 2) + abs (y - 3) < 5` -- the Manhattan distance from a
/// point -- each `abs` is bounded by what the other leaves over, and
/// bounding an `abs` bounds the variable inside it: `~3 < x < 7` and
/// `~2 < y < 8`.
///
/// An atom whose siblings are unbounded on the side that matters yields
/// nothing this round; a later round may bound it, once a sibling has a
/// bound. That is why [`iterate_to_fixed_point`] iterates.
///
/// What this propagator cannot do is combine two constraints, which is
/// what Fourier-Motzkin elimination does. Constraints such as
/// `x + y >= 0 andalso x - y >= ~3`, where no single constraint bounds a
/// variable, remain ungrounded.
fn propagate_sum(constraint: &Expr, state: &mut State) -> bool {
    let Some((lhs_e, rhs_e, op)) = comparison(constraint) else {
        return false;
    };
    let Some(lhs) = linear_form(lhs_e) else {
        return false;
    };
    let Some(rhs) = linear_form(rhs_e) else {
        return false;
    };
    // Rewrite `lhs OP rhs` as `sum OP 0`.
    let sum = lhs.minus(&rhs);
    if sum.is_constant() {
        // Both sides constant; nothing to deduce.
        return false;
    }
    let mut changed = false;
    for (atom, coefficient) in sum.terms.clone() {
        changed |= tighten_one(state, &sum, &atom, coefficient, op);
    }
    changed
}

/// Bounds one atom of `sum OP 0`, given the intervals of the others.
fn tighten_one(
    state: &mut State,
    sum: &LinearForm,
    atom: &Atom,
    coefficient: Rat,
    op: Cmp,
) -> bool {
    if !can_tighten(state, atom) {
        return false;
    }
    // The rest of the sum, `sum - coefficient * atom`, lies in
    // `[rest_min, rest_max]`; either may be absent, if some atom is
    // unbounded on that side.
    let key = atom.key();
    let mut rest_min = Some(sum.constant);
    let mut rest_max = Some(sum.constant);
    for (other, c) in &sum.terms {
        if other.key() == key {
            continue;
        }
        let interval = atom_interval(state, other);
        if interval.is_empty() {
            // Constraints that contradict each other leave an atom with
            // an empty interval. The query has no rows, and there is
            // nothing more to deduce.
            return false;
        }
        // A positive coefficient takes its minimum at the atom's lower
        // endpoint, a negative one at its upper endpoint.
        let (min_end, max_end) = if c.signum() > 0 {
            (interval.lower(), interval.upper())
        } else {
            (interval.upper(), interval.lower())
        };
        rest_min = add_endpoint(rest_min, min_end, *c);
        rest_max = add_endpoint(rest_max, max_end, *c);
    }

    // `coefficient * atom OP -rest`. An upper bound on the atom needs the
    // largest that `-rest` can be, that is the smallest rest; and the
    // other way about.
    match op {
        Cmp::Lt | Cmp::Le => {
            bound_atom(state, atom, coefficient, rest_min, false, op)
        }
        Cmp::Gt | Cmp::Ge => {
            bound_atom(state, atom, coefficient, rest_max, true, op)
        }
        Cmp::Eq => {
            let lower =
                bound_atom(state, atom, coefficient, rest_min, false, Cmp::Le);
            let upper =
                bound_atom(state, atom, coefficient, rest_max, true, Cmp::Ge);
            lower || upper
        }
    }
}

/// Adds `c` times one endpoint to a running total, or gives `None` if
/// the endpoint is unbounded. Whether the endpoint is open does not
/// matter: treating a strict bound as non-strict only weakens the
/// result.
fn add_endpoint(total: Option<Rat>, end: End, c: Rat) -> Option<Rat> {
    match end {
        End::Inf => None,
        End::At { value, .. } => Some(total?.add(value.mul(c))),
    }
}

/// Applies one side of a bound: `coefficient * atom OP -rest`, where
/// `rest` is `None` if that side is unbounded.
fn bound_atom(
    state: &mut State,
    atom: &Atom,
    coefficient: Rat,
    rest: Option<Rat>,
    lower: bool,
    op: Cmp,
) -> bool {
    let Some(rest) = rest else {
        return false;
    };
    // Dividing by a negative coefficient turns an upper bound into a
    // lower bound, and the other way about.
    let flip = coefficient.signum() < 0;
    let result_lower = flip != lower;
    // The arithmetic is exact, so the bound is the true one; for an
    // integer variable `bound_conjunct` snaps it to the tightest integer.
    let value = rest.neg().div(coefficient);
    let strict = matches!(op, Cmp::Lt | Cmp::Gt);
    let range = match (result_lower, strict) {
        (true, true) => Interval::greater_than(value),
        (true, false) => Interval::at_least(value),
        (false, true) => Interval::less_than(value),
        (false, false) => Interval::at_most(value),
    };
    tighten_atom(state, atom, range)
}

/// Returns whether we can put an atom's deduced bounds to use.
fn can_tighten(state: &State, atom: &Atom) -> bool {
    match atom {
        Atom::Var(name) => state.knows(name),
        Atom::Abs(e) => inner_variable(e, state).is_some(),
    }
}

/// Returns the interval that an atom is known to lie in.
fn atom_interval(state: &State, atom: &Atom) -> Interval {
    match atom {
        Atom::Var(name) => state.get(name),
        // An absolute value is never negative. (We do not track how much
        // more than zero it is; the variable inside it is what we are
        // after.)
        Atom::Abs(_) => Interval::at_least(Rat::int(0)),
    }
}

/// Tightens an atom to `range`. For a variable that is direct; for
/// `abs e`, whose upper bound `b` says that `e` lies in `[~b, b]`, it is
/// the variable inside `e` that tightens.
fn tighten_atom(state: &mut State, atom: &Atom, range: Interval) -> bool {
    let e = match atom {
        Atom::Var(name) => return state.tighten(name, range),
        Atom::Abs(e) => e,
    };
    let Some((name, c)) = inner_variable(e, state) else {
        return false;
    };
    let End::At {
        value: b,
        open: strict,
    } = range.upper()
    else {
        return false;
    };
    if b.signum() < 0 || b.signum() == 0 && strict {
        // `abs e < 0` cannot be satisfied.
        return state.tighten(&name, Interval::Empty);
    }
    // `abs (c * x + k) OP b` is `(~b - k) / c OP x OP (b - k) / c`, with
    // the ends swapped if `c` is negative.
    let form = match linear_form(abs_arg(e)) {
        Some(f) => f,
        None => return false,
    };
    let k = form.constant;
    let end1 = b.neg().sub(k);
    let end2 = b.sub(k);
    let (lower, upper) = if c.signum() > 0 {
        (end1.div(c), end2.div(c))
    } else {
        (end2.div(c), end1.div(c))
    };
    if strict && lower >= upper {
        // The ends have met; no value satisfies the constraint.
        return state.tighten(&name, Interval::Empty);
    }
    state.tighten(
        &name,
        normalize(
            End::At {
                value: lower,
                open: strict,
            },
            End::At {
                value: upper,
                open: strict,
            },
        ),
    )
}

/// If `e` is `abs (f)` and `f` is linear in one variable that `state` is
/// deducing bounds for, returns that variable and its coefficient;
/// otherwise `None`.
fn inner_variable(e: &Expr, state: &State) -> Option<(String, Rat)> {
    let form = linear_form(abs_arg(e))?;
    if form.terms.len() != 1 {
        return None;
    }
    let (atom, c) = &form.terms[0];
    // `abs (abs (x - 2) - 1)`, say. One layer is enough.
    let Atom::Var(name) = atom else {
        return None;
    };
    state.knows(name).then(|| (name.clone(), *c))
}

/// Applies a `var op constant` tightening to `state`.
///
/// If `direct_only`, considers only a constraint that the range
/// extractor could itself use, namely one whose variable side has no
/// offset: `x <= 3`, but not `x + 1 = 3`.
///
/// This is morel-java's `ConstantBounds`. It is not a propagator:
/// `propagate_sum` deduces everything that propagating such a
/// constraint would; `capture_inputs` uses it to record what the query
/// already says, before propagation begins.
fn apply_constant_bound(
    constraint: &Expr,
    state: &mut State,
    direct_only: bool,
) -> bool {
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
            if direct_only && lhs.offset.signum() != 0 {
                return false;
            }
            tighten_from_constant(state, lv, op, rhs.offset.sub(lhs.offset))
        }
        (None, Some(rv)) => {
            if direct_only && rhs.offset.signum() != 0 {
                return false;
            }
            tighten_from_constant(
                state,
                rv,
                op.reverse(),
                lhs.offset.sub(rhs.offset),
            )
        }
        _ => false,
    }
}

fn tighten_from_constant(
    state: &mut State,
    name: &str,
    op: Cmp,
    c: Rat,
) -> bool {
    state.tighten(name, Interval::from_op(op, c))
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
    let other_interval = state.get(other_t.var.as_ref().unwrap());
    if other_interval.is_empty() {
        // An empty interval means the query has no rows, and there is
        // nothing more to deduce.
        return false;
    }
    let other_span = other_interval.shift(other_t.offset);
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

    fn int_t() -> Rc<Type> {
        Rc::new(Type::Primitive(PrimitiveType::Int))
    }

    fn id(name: &str) -> Expr {
        Expr::Identifier(int_t(), name.to_string())
    }

    fn i(n: i32) -> Expr {
        Expr::Literal(int_t(), Val::Int(n))
    }

    /// Builds an arithmetic call, `a op b`.
    fn arith(op: BuiltInFunction, a: Expr, b: Expr) -> Expr {
        let pair_t = Rc::new(Type::Tuple(vec![int_t(), int_t()]));
        let fn_t = Rc::new(Type::Fn(pair_t.clone(), int_t()));
        Expr::Apply(
            int_t(),
            Box::new(Expr::Literal(fn_t, Val::Fn(op))),
            Box::new(Expr::Tuple(pair_t, vec![a, b])),
            Span::new(""),
        )
    }

    /// Returns `n * exp`.
    fn times(n: i32, exp: Expr) -> Expr {
        arith(BuiltInFunction::IntTimes, i(n), exp)
    }

    /// Returns `a + b`.
    fn plus(a: Expr, b: Expr) -> Expr {
        arith(BuiltInFunction::IntPlus, a, b)
    }

    /// Returns `a - b`.
    fn minus(a: Expr, b: Expr) -> Expr {
        arith(BuiltInFunction::IntMinus, a, b)
    }

    /// Returns `abs exp`.
    fn abs(exp: Expr) -> Expr {
        let fn_t = Rc::new(Type::Fn(int_t(), int_t()));
        Expr::Apply(
            int_t(),
            Box::new(Expr::Literal(fn_t, Val::Fn(BuiltInFunction::IntAbs))),
            Box::new(exp),
            Span::new(""),
        )
    }

    /// Runs FBBT over `conjuncts`, deducing bounds for `names`, and
    /// renders the conjuncts it deduces.
    fn deduced(names: &[&str], conjuncts: &[Expr]) -> Vec<String> {
        let pats: Vec<(String, Rc<Type>)> =
            names.iter().map(|n| (n.to_string(), int_t())).collect();
        strengthen(&pats, conjuncts)
            .iter()
            .map(|e| format!("{}", e))
            .collect()
    }

    /// `x > 0 andalso x < 10` says all there is to say about `x`, so
    /// there is nothing to add.
    #[test]
    fn constant_bounds_deduce_nothing_new() {
        let conjuncts = [
            compare(BuiltInFunction::IntGt, id("x"), i(0)),
            compare(BuiltInFunction::IntLt, id("x"), i(10)),
        ];
        assert!(deduced(&["x"], &conjuncts).is_empty());
    }

    /// The issue's cyclic-bound example: `x > 0 andalso x < y andalso
    /// y < 10` bounds `x` above and `y` below, by combining conjuncts.
    #[test]
    fn cyclic_bound_deduction() {
        let conjuncts = [
            compare(BuiltInFunction::IntGt, id("x"), i(0)),
            compare(BuiltInFunction::IntLt, id("x"), id("y")),
            compare(BuiltInFunction::IntLt, id("y"), i(10)),
        ];
        assert_eq!(deduced(&["x", "y"], &conjuncts), ["x < 10", "y > 0"]);
    }

    /// A constraint with coefficients over two variables: `3t + 5f = 30`
    /// with `t, f >= 0` gives `t <= 10` and `f <= 6`.
    #[test]
    fn coefficients() {
        let conjuncts = [
            compare(BuiltInFunction::IntGe, id("t"), i(0)),
            compare(BuiltInFunction::IntGe, id("f"), i(0)),
            compare(
                BuiltInFunction::IntEq,
                plus(times(3, id("t")), times(5, id("f"))),
                i(30),
            ),
        ];
        assert_eq!(deduced(&["t", "f"], &conjuncts), ["f <= 6", "t <= 10"]);
    }

    /// An upper bound that does not divide exactly rounds down, and a
    /// lower bound rounds up. `3x <= 10` gives `x <= 3`, not `x <= 4`;
    /// rounding the wrong way would admit a value that does not satisfy
    /// the constraint, or exclude one that does.
    #[test]
    fn bound_rounds_towards_the_truth() {
        let upper = [compare(BuiltInFunction::IntLe, times(3, id("x")), i(10))];
        assert_eq!(deduced(&["x"], &upper), ["x <= 3"]);
        let lower = [compare(BuiltInFunction::IntGe, times(3, id("x")), i(10))];
        assert_eq!(deduced(&["x"], &lower), ["x >= 4"]);
    }

    /// A negative coefficient bounds a variable from the other side:
    /// `x - y <= 5` with `0 <= y <= 2` gives `x <= 7`.
    #[test]
    fn negative_coefficient() {
        let conjuncts = [
            compare(BuiltInFunction::IntGe, id("y"), i(0)),
            compare(BuiltInFunction::IntLe, id("y"), i(2)),
            compare(BuiltInFunction::IntLe, minus(id("x"), id("y")), i(5)),
        ];
        assert_eq!(deduced(&["x", "y"], &conjuncts), ["x <= 7"]);
    }

    /// `abs x < 5` bounds `x` on both sides, open because `<` is strict.
    #[test]
    fn abs_less_than() {
        let conjuncts = [compare(BuiltInFunction::IntLt, abs(id("x")), i(5))];
        assert_eq!(deduced(&["x"], &conjuncts), ["x > ~5", "x < 5"]);
    }

    /// Two `abs` terms bound each other: the Manhattan distance from a
    /// point, `abs (x - 2) + abs (y - 3) < 5`.
    #[test]
    fn abs_atoms_bound_each_other() {
        let conjuncts = [compare(
            BuiltInFunction::IntLt,
            plus(abs(minus(id("x"), i(2))), abs(minus(id("y"), i(3)))),
            i(5),
        )];
        assert_eq!(
            deduced(&["x", "y"], &conjuncts),
            ["x > ~3", "x < 7", "y > ~2", "y < 8"]
        );
    }

    /// In `abs (c * x + k) OP b` the ends swap when `c` is negative. If
    /// the rounding followed the formula rather than the endpoint, both
    /// ends would round inwards and the interval would be tighter than
    /// the truth.
    #[test]
    fn abs_with_negative_coefficient() {
        // abs (~1 * x + 2) <= 3, that is ~1 <= x <= 5.
        let conjuncts = [compare(
            BuiltInFunction::IntLe,
            abs(plus(times(-1, id("x")), i(2))),
            i(3),
        )];
        assert_eq!(deduced(&["x"], &conjuncts), ["x >= ~1", "x <= 5"]);
    }

    /// Constraints that contradict each other leave an empty interval.
    /// There is nothing to deduce, and nothing to throw: an empty
    /// interval has no endpoints to read.
    #[test]
    fn contradiction_deduces_nothing() {
        let conjuncts = [
            compare(BuiltInFunction::IntGe, id("x"), i(0)),
            compare(BuiltInFunction::IntGe, id("y"), i(0)),
            compare(BuiltInFunction::IntEq, plus(id("x"), id("y")), i(-1)),
        ];
        assert!(deduced(&["x", "y"], &conjuncts).is_empty());
        let direct = [
            compare(BuiltInFunction::IntGt, id("x"), i(5)),
            compare(BuiltInFunction::IntLt, id("x"), i(3)),
            compare(BuiltInFunction::IntLt, id("y"), id("x")),
            compare(BuiltInFunction::IntGt, id("y"), i(0)),
        ];
        assert!(deduced(&["x", "y"], &direct).is_empty());
    }

    /// FBBT deduces `x = 2` from `x + 1 = 3`. The range extractor cannot
    /// use that equation as it stands, so the bounds are worth emitting.
    #[test]
    fn bound_the_extractor_cannot_see() {
        let conjuncts =
            [compare(BuiltInFunction::IntEq, plus(id("x"), i(1)), i(3))];
        assert_eq!(deduced(&["x"], &conjuncts), ["x >= 2", "x <= 2"]);
    }

    /// A variable that a scan bound constrains its neighbours and gets
    /// no bounds of its own: `z` is not one of the patterns we deduce
    /// for, so `x < z` with `z <= 3` bounds only `x`.
    #[test]
    fn scan_bound_variable_gets_no_bounds() {
        let conjuncts = [
            compare(BuiltInFunction::IntGe, id("z"), i(1)),
            compare(BuiltInFunction::IntLe, id("z"), i(3)),
            compare(BuiltInFunction::IntLt, id("x"), id("z")),
        ];
        assert_eq!(deduced(&["x"], &conjuncts), ["x < 3"]);
    }

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
