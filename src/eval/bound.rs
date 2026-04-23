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

//! Bound endpoints for ranges, and merging logic used by
//! `Range.continuousSetOf` / `Range.discreteSetOf`.
//!
//! Port of `Bound.java` from morel-java commit b4a0c4b1. Discrete-step
//! support (the `Discrete` interface) is not yet wired up; it lands in
//! a later commit with `Range.discreteSetOf`.

use crate::eval::comparator::Comparator;
use crate::eval::discrete::Discrete;
use crate::eval::val::{self, Val};
use std::cmp::Ordering;

/// One endpoint of a range: either unbounded (representing −∞ or +∞)
/// or a specific value with inclusivity.
#[derive(Clone, Debug)]
pub struct Bound {
    /// The endpoint value, or `None` if unbounded.
    pub value: Option<Val>,
    /// Whether the endpoint is inclusive (`>=` or `<=`). Only meaningful
    /// when `value` is `Some`.
    pub inclusive: bool,
}

impl Bound {
    /// Sentinel representing an unbounded endpoint.
    pub const UNBOUNDED: Self = Self {
        value: None,
        inclusive: false,
    };

    /// Returns an inclusive bound at `v`.
    pub fn inclusive(v: Val) -> Self {
        Self {
            value: Some(v),
            inclusive: true,
        }
    }

    /// Returns an exclusive bound at `v`.
    pub fn exclusive(v: Val) -> Self {
        Self {
            value: Some(v),
            inclusive: false,
        }
    }

    /// Extracts the lower `Bound` from a runtime range value.
    pub fn lower(range: &Val) -> Self {
        let (ord, inner) = match range {
            Val::Constructor(ord, inner) => (*ord, inner.as_ref()),
            _ => panic!("Bound::lower: not a range value"),
        };
        match ord {
            val::RANGE_ALL_ORDINAL
            | val::RANGE_AT_MOST_ORDINAL
            | val::RANGE_LESS_THAN_ORDINAL => Self::UNBOUNDED,
            val::RANGE_POINT_ORDINAL | val::RANGE_AT_LEAST_ORDINAL => {
                Self::inclusive(inner.clone())
            }
            val::RANGE_CLOSED_ORDINAL | val::RANGE_CLOSED_OPEN_ORDINAL => {
                Self::inclusive(inner.expect_list()[0].clone())
            }
            val::RANGE_GREATER_THAN_ORDINAL => Self::exclusive(inner.clone()),
            val::RANGE_OPEN_ORDINAL | val::RANGE_OPEN_CLOSED_ORDINAL => {
                Self::exclusive(inner.expect_list()[0].clone())
            }
            _ => panic!("Bound::lower: unknown range constructor {}", ord),
        }
    }

    /// Extracts the upper `Bound` from a runtime range value.
    pub fn upper(range: &Val) -> Self {
        let (ord, inner) = match range {
            Val::Constructor(ord, inner) => (*ord, inner.as_ref()),
            _ => panic!("Bound::upper: not a range value"),
        };
        match ord {
            val::RANGE_ALL_ORDINAL
            | val::RANGE_AT_LEAST_ORDINAL
            | val::RANGE_GREATER_THAN_ORDINAL => Self::UNBOUNDED,
            val::RANGE_POINT_ORDINAL | val::RANGE_AT_MOST_ORDINAL => {
                Self::inclusive(inner.clone())
            }
            val::RANGE_CLOSED_ORDINAL | val::RANGE_OPEN_CLOSED_ORDINAL => {
                Self::inclusive(inner.expect_list()[1].clone())
            }
            val::RANGE_LESS_THAN_ORDINAL => Self::exclusive(inner.clone()),
            val::RANGE_OPEN_ORDINAL | val::RANGE_CLOSED_OPEN_ORDINAL => {
                Self::exclusive(inner.expect_list()[1].clone())
            }
            _ => panic!("Bound::upper: unknown range constructor {}", ord),
        }
    }

    /// Converts a lower-upper `Bound` pair to a runtime range value.
    pub fn to_range(lo: &Self, hi: &Self) -> Val {
        match (&lo.value, &hi.value) {
            (None, None) => {
                Val::Constructor(val::RANGE_ALL_ORDINAL, Box::new(Val::Unit))
            }
            (None, Some(h)) => {
                let ord = if hi.inclusive {
                    val::RANGE_AT_MOST_ORDINAL
                } else {
                    val::RANGE_LESS_THAN_ORDINAL
                };
                Val::Constructor(ord, Box::new(h.clone()))
            }
            (Some(l), None) => {
                let ord = if lo.inclusive {
                    val::RANGE_AT_LEAST_ORDINAL
                } else {
                    val::RANGE_GREATER_THAN_ORDINAL
                };
                Val::Constructor(ord, Box::new(l.clone()))
            }
            (Some(l), Some(h)) => {
                if lo.inclusive && hi.inclusive && l == h {
                    return Val::Constructor(
                        val::RANGE_POINT_ORDINAL,
                        Box::new(l.clone()),
                    );
                }
                let ord = match (lo.inclusive, hi.inclusive) {
                    (true, true) => val::RANGE_CLOSED_ORDINAL,
                    (true, false) => val::RANGE_CLOSED_OPEN_ORDINAL,
                    (false, true) => val::RANGE_OPEN_CLOSED_ORDINAL,
                    (false, false) => val::RANGE_OPEN_ORDINAL,
                };
                Val::Constructor(
                    ord,
                    Box::new(Val::List(vec![l.clone(), h.clone()])),
                )
            }
        }
    }

    /// Compares this lower bound with `other` (earlier/smaller first).
    /// An unbounded lower bound sorts before all finite bounds. Among
    /// bounds with the same value, inclusive sorts before exclusive.
    pub fn compare_lower(
        &self,
        other: &Self,
        cmp: &dyn Comparator,
    ) -> Ordering {
        match (&self.value, &other.value) {
            (None, None) => Ordering::Equal,
            (None, Some(_)) => Ordering::Less,
            (Some(_), None) => Ordering::Greater,
            (Some(a), Some(b)) => match cmp.compare(a, b) {
                Ordering::Equal => match (self.inclusive, other.inclusive) {
                    (true, false) => Ordering::Less,
                    (false, true) => Ordering::Greater,
                    _ => Ordering::Equal,
                },
                other => other,
            },
        }
    }

    /// Returns whether this upper bound reaches or exceeds `next` (the
    /// lower bound of the next range), meaning the two ranges overlap or
    /// touch.
    pub fn can_merge(&self, next: &Self, cmp: &dyn Comparator) -> bool {
        match (&self.value, &next.value) {
            (None, _) | (_, None) => true,
            (Some(a), Some(b)) => match cmp.compare(a, b) {
                Ordering::Greater => true,
                Ordering::Less => false,
                Ordering::Equal => self.inclusive || next.inclusive,
            },
        }
    }

    /// Returns whether this upper bound and `next` are adjacent in
    /// discrete order (e.g. `CLOSED(1,3)` and `CLOSED(4,6)` for `int`).
    pub fn can_merge_discrete(
        &self,
        next: &Self,
        discrete: &dyn Discrete,
        cmp: &dyn Comparator,
    ) -> bool {
        let (a, b) = match (&self.value, &next.value) {
            (Some(a), Some(b)) => (a, b),
            _ => return true, // one side is unbounded
        };
        // Effective last-included value of this upper bound.
        let hi_eff = if self.inclusive {
            Some(a.clone())
        } else {
            discrete.prev(a)
        };
        // Effective first-included value of the next lower bound.
        let lo_eff = if next.inclusive {
            Some(b.clone())
        } else {
            discrete.next(b)
        };
        let (hi_eff, lo_eff) = match (hi_eff, lo_eff) {
            (Some(h), Some(l)) => (h, l),
            _ => return false,
        };
        let Some(next_after_hi) = discrete.next(&hi_eff) else {
            return false;
        };
        // Ranges touch iff step-past-hi reaches or exceeds lo.
        cmp.compare(&next_after_hi, &lo_eff).is_ge()
    }

    /// Compares `x` against this lower bound. Positive if `x`
    /// satisfies the bound (is at or past the lower endpoint), zero
    /// if `x` exactly equals an inclusive bound, -1 if `x` equals an
    /// exclusive lower bound (not satisfied). Unbounded always
    /// returns positive.
    pub fn compare_value(&self, x: &Val, cmp: &dyn Comparator) -> Ordering {
        let Some(v) = &self.value else {
            return Ordering::Greater;
        };
        match cmp.compare(x, v) {
            Ordering::Equal if !self.inclusive => Ordering::Less,
            other => other,
        }
    }

    /// Returns the greater of this upper bound and `other`.
    pub fn max(&self, other: &Self, cmp: &dyn Comparator) -> Self {
        match (&self.value, &other.value) {
            (None, _) | (_, None) => Self::UNBOUNDED,
            (Some(a), Some(b)) => match cmp.compare(a, b) {
                Ordering::Greater => self.clone(),
                Ordering::Less => other.clone(),
                Ordering::Equal => {
                    if self.inclusive {
                        self.clone()
                    } else {
                        other.clone()
                    }
                }
            },
        }
    }
}

/// Tests whether `x` is contained in any of the (normalized) ranges.
/// Binary-searches for the range whose lower bound is satisfied, then
/// checks the upper bound.
pub fn set_contains(ranges: &[Val], x: &Val, cmp: &dyn Comparator) -> bool {
    if ranges.is_empty() {
        return false;
    }
    let bounds: Vec<(Bound, Bound)> = ranges
        .iter()
        .map(|r| (Bound::lower(r), Bound::upper(r)))
        .collect();
    let mut lo: i32 = 0;
    let mut hi: i32 = bounds.len() as i32 - 1;
    let mut candidate: i32 = -1;
    while lo <= hi {
        let mid = (lo + hi) / 2;
        if bounds[mid as usize].0.compare_value(x, cmp).is_ge() {
            candidate = mid;
            lo = mid + 1;
        } else {
            hi = mid - 1;
        }
    }
    if candidate >= 0 {
        let hi_b = &bounds[candidate as usize].1;
        let Some(hi_val) = &hi_b.value else {
            return true; // unbounded above
        };
        match cmp.compare(x, hi_val) {
            Ordering::Less => return true,
            Ordering::Equal if hi_b.inclusive => return true,
            _ => return false,
        }
    }
    false
}

/// Returns the complement of a normalized list of ranges: the set of
/// values *not* covered by any range. For continuous sets (`discrete =
/// None`), bounds are flipped (inclusive ↔ exclusive). For discrete
/// sets (`Some(d)`), adjacent discrete values are used so the result
/// contains only `CLOSED` and unbounded constructors.
pub fn complement(ranges: &[Val], discrete: Option<&dyn Discrete>) -> Vec<Val> {
    let mut result: Vec<Val> = Vec::new();
    let mut lo = Bound::UNBOUNDED;
    for r in ranges {
        let range_lo = Bound::lower(r);
        let range_hi = Bound::upper(r);
        if range_lo.value.is_some()
            && let Some(hi) = complement_hi(&range_lo, discrete)
        {
            result.push(Bound::to_range(&lo, &hi));
        }
        if range_hi.value.is_none() {
            // Range extends to +∞; no complement after this.
            return result;
        }
        match complement_lo(&range_hi, discrete) {
            Some(next_lo) => lo = next_lo,
            None => return result,
        }
    }
    result.push(Bound::to_range(&lo, &Bound::UNBOUNDED));
    result
}

/// Upper bound of the complement range that ends just before `lo`.
/// Returns `None` if that complement is empty (only possible when
/// `discrete` is supplied and `lo` is at the discrete minimum).
fn complement_hi(lo: &Bound, discrete: Option<&dyn Discrete>) -> Option<Bound> {
    let lo_value = lo.value.as_ref()?;
    if let Some(d) = discrete {
        if lo.inclusive {
            d.prev(lo_value).map(Bound::inclusive)
        } else {
            Some(Bound::inclusive(lo_value.clone()))
        }
    } else if lo.inclusive {
        Some(Bound::exclusive(lo_value.clone()))
    } else {
        Some(Bound::inclusive(lo_value.clone()))
    }
}

/// Lower bound of the complement range that starts just after `hi`.
/// Returns `None` if no value remains past `hi` in the discrete
/// domain.
fn complement_lo(hi: &Bound, discrete: Option<&dyn Discrete>) -> Option<Bound> {
    let hi_value = hi.value.as_ref()?;
    if let Some(d) = discrete {
        if hi.inclusive {
            d.next(hi_value).map(Bound::inclusive)
        } else {
            Some(Bound::inclusive(hi_value.clone()))
        }
    } else if hi.inclusive {
        Some(Bound::exclusive(hi_value.clone()))
    } else {
        Some(Bound::inclusive(hi_value.clone()))
    }
}

/// Appends all discrete values in the range `[lo..hi]` to `out`, using
/// `discrete` for stepping and `cmp` for the upper-bound check. Panics
/// on an unbounded upper side or an empty exclusive lower bound at the
/// discrete maximum — morel-java raises `Size` in those cases, but the
/// runtime-error plumbing for `discrete_set` isn't wired yet.
pub fn enumerate(
    lo: &Bound,
    hi: &Bound,
    discrete: &dyn Discrete,
    cmp: &dyn Comparator,
    out: &mut Vec<Val>,
) {
    let hi_val = match &hi.value {
        Some(v) => v,
        None => panic!("Range.toList/toBag: range is unbounded above"),
    };
    let start = match &lo.value {
        None => match discrete.min_value() {
            Some(v) => v,
            None => panic!("Range.toList/toBag: element type has no minimum"),
        },
        Some(v) => {
            if lo.inclusive {
                v.clone()
            } else {
                match discrete.next(v) {
                    Some(n) => n,
                    None => {
                        panic!("Range.toList/toBag: empty open range at max")
                    }
                }
            }
        }
    };
    let mut v = start;
    loop {
        let c = cmp.compare(&v, hi_val);
        if c == Ordering::Greater || (c == Ordering::Equal && !hi.inclusive) {
            break;
        }
        out.push(v.clone());
        match discrete.next(&v) {
            Some(n) => v = n,
            None => break,
        }
    }
}

/// Enumerates every value covered by the given (normalized) list of
/// ranges, in ascending order.
pub fn enumerate_ranges(
    ranges: &[Val],
    discrete: &dyn Discrete,
    cmp: &dyn Comparator,
) -> Vec<Val> {
    let mut out = Vec::new();
    for r in ranges {
        let lo = Bound::lower(r);
        let hi = Bound::upper(r);
        enumerate(&lo, &hi, discrete, cmp, &mut out);
    }
    out
}

/// Converts a list of runtime range values into a normalized list:
/// sorts by lower bound, then merges overlapping or touching ranges.
/// Returns the merged ranges as `Val::List` of range constructors.
///
/// If `discrete` is provided, also merges ranges that are adjacent in
/// the discrete domain (e.g. `[1,3] ∪ [4,7] → [1,7]` for `int`).
pub fn from_ranges(
    ranges: &[Val],
    cmp: &dyn Comparator,
    discrete: Option<&dyn Discrete>,
) -> Vec<Val> {
    let mut pairs: Vec<(Bound, Bound)> = ranges
        .iter()
        .map(|r| (Bound::lower(r), Bound::upper(r)))
        .collect();
    if pairs.len() < 2 {
        return pairs
            .iter()
            .map(|(lo, hi)| Bound::to_range(lo, hi))
            .collect();
    }
    pairs.sort_by(|a, b| a.0.compare_lower(&b.0, cmp));

    let mut result: Vec<(Bound, Bound)> = Vec::new();
    let (mut lo, mut hi) = pairs[0].clone();
    for (next_lo, next_hi) in pairs.into_iter().skip(1) {
        let merge = match discrete {
            Some(d) => hi.can_merge_discrete(&next_lo, d, cmp),
            None => hi.can_merge(&next_lo, cmp),
        };
        if merge {
            hi = hi.max(&next_hi, cmp);
        } else {
            result.push((lo, hi));
            lo = next_lo;
            hi = next_hi;
        }
    }
    result.push((lo, hi));
    result
        .iter()
        .map(|(lo, hi)| Bound::to_range(lo, hi))
        .collect()
}
