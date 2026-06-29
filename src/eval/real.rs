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

use crate::compile::library::BuiltInExn;
use crate::compile::span::Span;
use crate::eval::order::Order;
use crate::eval::val::{
    REALFMT_EXACT, REALFMT_FIX, REALFMT_GEN, REALFMT_SCI, Val,
};
use crate::shell::main::MorelError;
use std::cmp::Ordering;

/// Support for the `real` built-in type and the `Real` structure.
pub struct Real;

impl Real {
    // lint: sort until '#}' where '##pub'

    /// Computes the Morel expression `Real.abs r`.
    ///
    /// Returns the absolute value of `r`.
    pub(crate) fn abs(r: f32) -> f32 {
        r.abs()
    }

    /// Computes the Morel expression `Real.ceil r`.
    ///
    /// Produces ceil(r), the smallest int not less than `r`.
    #[allow(clippy::if_same_then_else)]
    pub(crate) fn ceil(r: f32, span: &Span) -> Result<Val, MorelError> {
        let result = r.ceil();
        if result.is_infinite() || result.is_nan() {
            Err(MorelError::Runtime(BuiltInExn::Overflow, span.clone()))
        } else if result < i32::MIN as f32 || result > i32::MAX as f32 {
            Err(MorelError::Runtime(BuiltInExn::Overflow, span.clone()))
        } else {
            Ok(Val::Int(result as i32))
        }
    }

    /// Computes the Morel expression `Real.checkFloat x`.
    ///
    /// Raises `Overflow` if x is an infinity, and raises `Div` if x is NaN.
    /// Otherwise, it returns its argument.
    pub(crate) fn check_float(x: f32, span: &Span) -> Result<Val, MorelError> {
        if x.is_infinite() {
            Err(MorelError::Runtime(BuiltInExn::Overflow, span.clone()))
        } else if x.is_nan() {
            Err(MorelError::Runtime(BuiltInExn::Div, span.clone()))
        } else {
            Ok(Val::Real(x))
        }
    }

    /// Computes the Morel expression `Real.compare (x, y)`.
    ///
    /// Returns `LESS`, `EQUAL`, or `GREATER` according to whether its first
    /// argument is less than, equal to, or greater than the second.
    /// It raises `IEEEReal.Unordered` on unordered arguments.
    pub(crate) fn compare(
        x: f32,
        y: f32,
        span: &Span,
    ) -> Result<Val, MorelError> {
        if x.is_nan() || y.is_nan() {
            Err(MorelError::Runtime(BuiltInExn::Unordered, span.clone()))
        } else {
            Ok(Val::Order(Order(if x < y {
                Ordering::Less
            } else if x > y {
                Ordering::Greater
            } else {
                Ordering::Equal
            })))
        }
    }

    /// Computes the Morel expression `Real.copySign (x, y)`.
    ///
    /// Returns `x` with the sign of `y`, even if `y` is NaN.
    pub(crate) fn copy_sign(x: f32, y: f32) -> f32 {
        x.copysign(y)
    }

    /// Computes the Morel expression `Real.floor r`.
    ///
    /// Produces floor(r), the largest int not larger than `r`.
    #[allow(clippy::if_same_then_else)]
    pub(crate) fn floor(r: f32, span: &Span) -> Result<Val, MorelError> {
        let result = r.floor();
        if result.is_infinite() || result.is_nan() {
            Err(MorelError::Runtime(BuiltInExn::Overflow, span.clone()))
        } else if result < i32::MIN as f32 || result > i32::MAX as f32 {
            Err(MorelError::Runtime(BuiltInExn::Overflow, span.clone()))
        } else {
            Ok(Val::Int(result as i32))
        }
    }

    /// Computes the Morel expression `Real.fmt spec r`. The spec is a
    /// `StringCvt.realfmt` constructor (`SCI | FIX | GEN | EXACT`).
    /// Special values render as `"nan"`, `"inf"`, and `"~inf"`. The
    /// spec is assumed to have already been validated by
    /// [`Self::validate_fmt_spec`] at partial-application time.
    pub(crate) fn fmt(spec: &Val, r: f32) -> String {
        let (kind, n) = parse_fmt_spec(spec);
        if r.is_nan() {
            return "nan".to_string();
        }
        if r.is_infinite() {
            return if r.is_sign_negative() { "~inf" } else { "inf" }
                .to_string();
        }
        let neg_sign = r.is_sign_negative();
        let abs = r.abs();
        let body = match kind {
            FmtKind::Sci => format_sci(abs, n),
            FmtKind::Fix => format_fix(abs, n),
            FmtKind::Gen => format_gen(abs, n),
            FmtKind::Exact => format_exact(abs),
        };
        if neg_sign { format!("~{}", body) } else { body }
    }

    /// Computes the Morel expression `Real.fromInt i`.
    ///
    /// Converts the integer `i` to a `real` value.
    pub(crate) fn from_int(i: i32) -> f32 {
        i as f32
    }

    /// Computes the Morel expression `Real.fromManExp {exp, man}`.
    ///
    /// Returns the real value constructed from mantissa and exponent.
    pub(crate) fn from_man_exp(man: f32, exp: i32) -> f32 {
        man * 2_f32.powi(exp)
    }

    /// Computes the Morel expression `Real.fromString s`.
    ///
    /// Scans a `real` value from a string.
    pub(crate) fn from_string(s: &str) -> Val {
        let trimmed = s.trim_start();

        // Handle special values.
        if trimmed.starts_with("inf") {
            return Val::Some(Box::new(Val::Real(f32::INFINITY)));
        } else if trimmed.starts_with("~inf") || trimmed.starts_with("-inf") {
            return Val::Some(Box::new(Val::Real(f32::NEG_INFINITY)));
        } else if trimmed.starts_with("nan")
            || trimmed.starts_with("~nan")
            || trimmed.starts_with("-nan")
        {
            return Val::Some(Box::new(Val::Real(f32::NAN)));
        }

        // Replace ~ with - for parsing.
        // (Standard ML uses ~ for negation.)
        let normalized = trimmed.replace('~', "-");

        // Try to parse the entire string first.
        if let Ok(r) = normalized.parse::<f32>() {
            return Val::Some(Box::new(Val::Real(r)));
        }

        // If that fails, try to parse as much as possible.
        // This handles cases like "1.5e2e" -> parse "1.5e2".
        let mut end_idx = 0;
        // Last index where we had a valid number.
        let mut last_valid_idx = 0;
        let mut seen_dot = false;
        let mut seen_e = false;
        let mut seen_sign_after_e = false;
        let mut seen_digit_after_e = false;
        let chars: Vec<char> = normalized.chars().collect();

        for (i, &ch) in chars.iter().enumerate() {
            match ch {
                '0'..='9' => {
                    end_idx = i + 1;
                    last_valid_idx = i + 1;
                    if seen_e {
                        seen_digit_after_e = true;
                        seen_sign_after_e = false;
                    }
                }
                '.' => {
                    if seen_dot || seen_e {
                        break; // Second dot or dot after 'e' is invalid.
                    }
                    seen_dot = true;
                    end_idx = i + 1;
                    last_valid_idx = i + 1;
                }
                'e' | 'E' => {
                    if seen_e || end_idx == 0 {
                        break; // Second 'e' or 'e' at start is invalid.
                    }
                    seen_e = true;
                    // Don't update last_valid_idx yet.
                    // Wait for digits after 'e'.
                    end_idx = i + 1;
                }
                '-' | '+' => {
                    if i == 0 {
                        // Sign at start is OK, but needs digit after.
                        continue;
                    } else if seen_e && !seen_sign_after_e && i == end_idx {
                        // Sign right after 'e' is OK.
                        seen_sign_after_e = true;
                        continue;
                    } else {
                        break; // Otherwise, stop parsing.
                    }
                }
                _ => break, // Any other character stops parsing.
            }
        }

        // If 'e' was seen but no digits after it, use last_valid_idx
        // before 'e'.
        if seen_e && !seen_digit_after_e {
            end_idx = last_valid_idx;
        }

        // If we found a valid prefix, try to parse it.
        if end_idx > 0 {
            let prefix = &normalized[..end_idx];
            if let Ok(r) = prefix.parse::<f32>() {
                return Val::Some(Box::new(Val::Real(r)));
            }
        }

        Val::Unit // NONE
    }

    /// Computes the Morel expression `Real.isFinite x`.
    ///
    /// Returns true if x is neither NaN nor an infinity.
    pub(crate) fn is_finite(x: f32) -> bool {
        x.is_finite()
    }

    /// Computes the Morel expression `Real.isNan x`.
    ///
    /// Returns true if x is NaN.
    pub(crate) fn is_nan(x: f32) -> bool {
        x.is_nan()
    }

    /// Computes the Morel expression `Real.isNormal x`.
    ///
    /// Returns true if x is normal, i.e., neither zero, subnormal,
    /// infinite nor NaN.
    pub(crate) fn is_normal(x: f32) -> bool {
        x.is_normal()
    }

    /// Computes the Morel expression `Real.max (x, y)`.
    ///
    /// Returns the larger of the arguments. If exactly one argument is NaN,
    /// returns the other argument. If both arguments are NaN, returns NaN.
    pub(crate) fn max(x: f32, y: f32) -> f32 {
        if x.is_nan() {
            if y.is_nan() { f32::NAN } else { y }
        } else if y.is_nan() {
            x
        } else {
            x.max(y)
        }
    }

    /// Computes the Morel expression `Real.min (x, y)`.
    ///
    /// Returns the smaller of the arguments. If exactly one argument is NaN,
    /// returns the other argument. If both arguments are NaN, returns NaN.
    pub(crate) fn min(x: f32, y: f32) -> f32 {
        if x.is_nan() {
            if y.is_nan() { f32::NAN } else { y }
        } else if y.is_nan() {
            x
        } else {
            x.min(y)
        }
    }

    /// Computes the Morel expression `Real.realCeil r`.
    ///
    /// Produces ceil(r), the smallest integer not less than `r`.
    pub(crate) fn real_ceil(r: f32) -> f32 {
        r.ceil()
    }

    /// Computes the Morel expression `Real.realFloor r`.
    ///
    /// Produces floor(r), the largest integer not larger than `r`.
    pub(crate) fn real_floor(r: f32) -> f32 {
        r.floor()
    }

    /// Computes the Morel expression `Real.realMod r`.
    ///
    /// Returns the fractional part of `r`.
    pub(crate) fn real_mod(r: f32) -> f32 {
        if r == 0.0 || r.is_nan() {
            r // 0 -> 0, ~0 -> ~0, nan -> nan
        } else if r.is_infinite() {
            0_f32.copysign(r) // +inf -> 0, -inf -> ~0
        } else {
            r.fract()
        }
    }

    /// Computes the Morel expression `Real.realRound r`.
    ///
    /// Rounds to the integer-valued real value that is nearest to `r`.
    /// In the case of a tie, it rounds to the nearest even integer.
    pub(crate) fn real_round(r: f32) -> f32 {
        r.round_ties_even()
    }

    /// Computes the Morel expression `Real.realTrunc r`.
    ///
    /// Rounds `r` towards zero.
    pub(crate) fn real_trunc(r: f32) -> f32 {
        r.trunc()
    }

    /// Computes the Morel expression `Real.rem (x, y)`.
    ///
    /// Returns the remainder `x - n * y`, where `n` = `trunc (x / y)`.
    pub(crate) fn rem(x: f32, y: f32) -> f32 {
        if x.is_infinite() || y == 0.0 {
            f32::NAN
        } else if y.is_infinite() {
            x
        } else {
            let n = (x / y).trunc();
            x - n * y
        }
    }

    /// Computes the Morel expression `Real.round r`.
    ///
    /// Yields the integer nearest to `r`. In the case of a tie, it rounds
    /// to the nearest even integer.
    #[allow(clippy::if_same_then_else)]
    pub(crate) fn round(r: f32, span: &Span) -> Result<Val, MorelError> {
        // Check for NaN first to return Domain exception
        if r.is_nan() {
            return Err(MorelError::Runtime(BuiltInExn::Domain, span.clone()));
        }
        let result = r.round_ties_even();
        if result.is_infinite() {
            Err(MorelError::Runtime(BuiltInExn::Overflow, span.clone()))
        } else if result < i32::MIN as f32 || result > i32::MAX as f32 {
            Err(MorelError::Runtime(BuiltInExn::Overflow, span.clone()))
        } else {
            Ok(Val::Int(result as i32))
        }
    }

    /// Computes the Morel expression `Real.sameSign (r1, r2)`.
    ///
    /// Returns true if and only if `signBit r1` equals `signBit r2`.
    pub(crate) fn same_sign(r1: f32, r2: f32) -> bool {
        r1.is_sign_positive() == r2.is_sign_positive()
    }

    /// Computes the Morel expression `Real.sign r`.
    ///
    /// Returns ~1 if r is negative, 0 if r is zero, or 1 if r is positive.
    /// An infinity returns its sign; a zero returns 0 regardless of its sign.
    /// It raises `Domain` on NaN.
    pub(crate) fn sign(r: f32, span: &Span) -> Result<Val, MorelError> {
        if r.is_nan() {
            Err(MorelError::Runtime(BuiltInExn::Domain, span.clone()))
        } else if r == 0.0 {
            Ok(Val::Int(0))
        } else if r > 0.0 {
            Ok(Val::Int(1))
        } else {
            Ok(Val::Int(-1))
        }
    }

    /// Computes the Morel expression `Real.signBit r`.
    ///
    /// Returns true if and only if the sign of `r` (infinities, zeros,
    /// and NaN, included) is negative.
    pub(crate) fn sign_bit(r: f32) -> bool {
        r.is_sign_negative()
    }

    /// Computes the Morel expression `Real.split r`.
    ///
    /// Returns `{frac, whole}`, where `frac` and `whole` are the fractional
    /// and integral parts of `r`, respectively.
    pub(crate) fn split(r: f32) -> Val {
        let (frac, whole) = if r == 0.0 {
            // split ~0.0 -> (~0.0, ~0.0)
            // split 0.0 -> (0.0, 0.0)
            (r, r)
        } else if r.is_infinite() {
            // split posInf -> (0.0, inf)
            // split negInf -> (~0.0, ~inf)
            (if r.is_sign_positive() { 0_f32 } else { -0_f32 }, r)
        } else if r.is_nan() {
            // split nan -> (nan, nan)
            (r, r)
        } else {
            // split 2.75 -> (.75, 2.0)
            // split ~2.75 -> (~.75, ~2.0)
            let w = r.trunc();
            (r - w, w)
        };
        Val::List(vec![Val::Real(frac), Val::Real(whole)])
    }

    /// Computes the Morel expression `Real.toManExp r`.
    ///
    /// Returns `{man, exp}`, where `man` and `exp` are the mantissa
    /// and exponent of r, respectively.
    /// Satisfies: r = man * 2^exp, where man is in [0.5, 1.0) or (-1.0, -0.5]
    #[allow(clippy::wrong_self_convention)]
    pub(crate) fn to_man_exp(r: f32) -> Val {
        if r.is_nan() || r.is_infinite() {
            // Special cases: NaN, infinity use exp = 129
            Val::List(vec![Val::Int(129), Val::Real(r)])
        } else if r == 0.0 {
            // Zero uses exp = -126
            Val::List(vec![Val::Int(-126), Val::Real(r)])
        } else if !r.is_normal() {
            // Subnormal numbers: use exp = -126 and compute mantissa
            // accordingly. For subnormal: r = man * 2^(-126).
            let man = r * 2_f32.powi(126);
            Val::List(vec![Val::Int(-126), Val::Real(man)])
        } else {
            // Normal numbers: use frexp-like calculation.
            // Satisfies: r = man * 2^exp, where man is in [0.5, 1.0) or
            // (-1.0, -0.5].
            let abs = r.abs();
            let exp = abs.log2().floor() as i32 + 1;
            let man = r / 2_f32.powi(exp);
            Val::List(vec![Val::Int(exp), Val::Real(man)])
        }
    }

    /// Computes the Morel expression `Real.toString r`.
    ///
    /// Converts a `real` into a `string`.
    /// Returns a string suitable for parsing back as a real number.
    /// Uses `~` for negative numbers but `-` for negative exponents.
    ///
    /// Matches Standard ML's `Real.toString`, which drops a trailing
    /// ".0" from whole-number reals (so `1.0` prints as "1" and
    /// `1.0e10` prints as "1E10").
    #[allow(clippy::wrong_self_convention)]
    pub(crate) fn to_string(r: f32) -> String {
        if r.is_nan() {
            "nan".to_string()
        } else if r.is_infinite() {
            if r > 0.0 {
                "inf".to_string()
            } else {
                "~inf".to_string()
            }
        } else if r == 0.0 {
            if r.is_sign_negative() {
                "~0".to_string()
            } else {
                "0".to_string()
            }
        } else {
            // Use scientific notation for very large or very small numbers.
            let abs = r.abs();
            let s = if !(1e-3..1e7).contains(&abs) {
                // Format in scientific notation with uppercase E.
                // Rust's default precision for '{:E}' already strips
                // trailing zeros ("1E10" rather than "1.0E10").
                format!("{:E}", r).replace("-", "~")
            } else if r.fract() == 0.0 && abs < i64::MAX as f32 {
                // Whole numbers display without any fractional part,
                // matching SML's Real.toString ("1" rather than "1.0").
                format!("{}", r.trunc() as i64).replace("-", "~")
            } else {
                // For non-whole numbers, use default formatting.
                format!("{}", r).replace('-', "~")
            };
            // `Real.minPos`: SML reports 1.4e-45, not the shorter "1E~45".
            match s.as_str() {
                "1E~45" => "1.4E~45".to_string(),
                "~1E~45" => "~1.4E~45".to_string(),
                _ => s,
            }
        }
    }

    /// Computes the Morel expression `Real.trunc r`.
    ///
    /// Rounds r towards zero.
    #[allow(clippy::if_same_then_else)]
    pub(crate) fn trunc(r: f32, span: &Span) -> Result<Val, MorelError> {
        let result = r.trunc();
        if result.is_infinite() || result.is_nan() {
            Err(MorelError::Runtime(BuiltInExn::Overflow, span.clone()))
        } else if result < i32::MIN as f32 || result > i32::MAX as f32 {
            Err(MorelError::Runtime(BuiltInExn::Overflow, span.clone()))
        } else {
            Ok(Val::Int(result as i32))
        }
    }

    /// Computes the Morel expression `Real.unordered (x, y)`.
    ///
    /// Returns true if x and y are unordered, i.e., at least one of
    /// x and y is NaN.
    pub(crate) fn unordered(x: f32, y: f32) -> bool {
        x.is_nan() || y.is_nan()
    }

    /// Validates a `StringCvt.realfmt` spec; raises `Size` if invalid.
    /// `SCI` and `FIX` reject `SOME n` with `n < 0`; `GEN` rejects
    /// `SOME n` with `n < 1`; `EXACT` is always valid.
    pub(crate) fn validate_fmt_spec(
        spec: &Val,
        span: &Span,
    ) -> Result<(), MorelError> {
        let bad = match spec {
            Val::Constructor(REALFMT_SCI, inner)
            | Val::Constructor(REALFMT_FIX, inner) => {
                option_int(inner).is_some_and(|n| n < 0)
            }
            Val::Constructor(REALFMT_GEN, inner) => {
                option_int(inner).is_some_and(|n| n < 1)
            }
            Val::Constructor(REALFMT_EXACT, _) => false,
            other => panic!("expected realfmt constructor, got {:?}", other),
        };
        if bad {
            return Err(MorelError::Runtime(BuiltInExn::Size, span.clone()));
        }
        Ok(())
    }
}

/// Extracts the inner `int` from a `Val::Some(Val::Int(_))`; returns
/// `None` for `Val::Unit` (i.e. `NONE`).
fn option_int(v: &Val) -> Option<i32> {
    match v {
        Val::Some(inner) => Some(inner.expect_int()),
        Val::Unit => None,
        _ => None,
    }
}

#[derive(Copy, Clone)]
enum FmtKind {
    Sci,
    Fix,
    Gen,
    Exact,
}

/// Returns the (kind, n) pair for a validated `StringCvt.realfmt`. `n`
/// defaults to 6 for `SCI`/`FIX`, 12 for `GEN`, and 0 for `EXACT`.
fn parse_fmt_spec(spec: &Val) -> (FmtKind, usize) {
    let (kind, default, inner) = match spec {
        Val::Constructor(REALFMT_EXACT, _) => return (FmtKind::Exact, 0),
        Val::Constructor(REALFMT_SCI, inner) => (FmtKind::Sci, 6, inner),
        Val::Constructor(REALFMT_FIX, inner) => (FmtKind::Fix, 6, inner),
        Val::Constructor(REALFMT_GEN, inner) => (FmtKind::Gen, 12, inner),
        other => panic!("expected realfmt constructor, got {:?}", other),
    };
    let n = option_int(inner).map_or(default, |n| n as usize);
    (kind, n)
}

/// `D.dddE±exp` with `n` digits after the decimal.
fn format_sci(abs: f32, n: usize) -> String {
    if abs == 0.0 {
        return if n == 0 {
            "0E0".to_string()
        } else {
            format!("0.{}E0", "0".repeat(n))
        };
    }
    let (digits, exp) = canonical(abs);
    // Round `digits` to `n + 1` significant digits.
    let (rounded, exp_adj) = round_half_down_digits(&digits, n + 1);
    let exp = exp + exp_adj;
    if n == 0 {
        format!("{}E{}", &rounded[..1], sml_exp(exp))
    } else {
        format!("{}.{}E{}", &rounded[..1], &rounded[1..], sml_exp(exp))
    }
}

/// Fixed-point with `n` digits after the decimal.
fn format_fix(abs: f32, n: usize) -> String {
    if abs == 0.0 {
        return if n == 0 {
            "0".to_string()
        } else {
            format!("0.{}", "0".repeat(n))
        };
    }
    let (digits, exp) = canonical(abs);
    // The number is `digits.0 * 10^exp` (where `digits.0` is the
    // mantissa with the implicit decimal after the first character).
    // For FIX with `n` decimals, we round `digits` so that its implied
    // position relative to the decimal point keeps exactly `n` fractional
    // digits. The count of significant digits from the leading digit down
    // to the n-th decimal place is `exp + 1 + n`.
    let total_sig = exp + 1 + n as i32;
    if total_sig <= 0 {
        // The most significant digit lies at or below the n-th decimal
        // place, so the value rounds to 0.000…0 — unless `total_sig == 0`
        // and the leading digit rounds the n-th decimal up to 1 (e.g.
        // `FIX 3` of 0.0006 is "0.001").
        let round_up = total_sig == 0 && {
            let first = digits.as_bytes()[0];
            first > b'5'
                || (first == b'5' && digits[1..].bytes().any(|b| b != b'0'))
        };
        if n == 0 {
            return if round_up {
                "1".to_string()
            } else {
                "0".to_string()
            };
        }
        let mut frac = vec![b'0'; n];
        if round_up {
            frac[n - 1] = b'1';
        }
        return format!("0.{}", String::from_utf8(frac).unwrap());
    }
    let (rounded, exp_adj) =
        round_half_down_digits(&digits, total_sig as usize);
    let exp = exp + exp_adj;
    place_decimal(&rounded, exp, n, false)
}

/// At most `n` significant digits, using fixed when exp in `[-3, n)`,
/// scientific otherwise. Trailing zeros are stripped.
fn format_gen(abs: f32, n: usize) -> String {
    if abs == 0.0 {
        return "0".to_string();
    }
    let (digits, exp) = canonical(abs);
    let (rounded, exp_adj) = round_half_down_digits(&digits, n);
    let exp = exp + exp_adj;
    // Strip trailing zeros from the rounded significant digits.
    let stripped = rounded.trim_end_matches('0');
    let stripped = if stripped.is_empty() { "0" } else { stripped };
    if exp <= -3 || exp >= n as i32 {
        // Scientific form: `D.dddE±exp`. Mantissa is the stripped
        // significant digits; if length 1, no decimal point.
        if stripped.len() == 1 {
            format!("{}E{}", stripped, sml_exp(exp))
        } else {
            format!("{}.{}E{}", &stripped[..1], &stripped[1..], sml_exp(exp))
        }
    } else {
        // Fixed form: place decimal point per `exp`, drop trailing zeros.
        place_decimal(stripped, exp, 0, true)
    }
}

/// `0.dddE<exp>` form with no trailing zeros.
fn format_exact(abs: f32) -> String {
    if abs == 0.0 {
        return "0.0".to_string();
    }
    let (digits, exp) = canonical(abs);
    // EXACT prints as `0.<digits>E<exp+1>`. (Decimal point moves one
    // place left vs. standard scientific form.) Strip trailing zeros.
    let stripped = digits.trim_end_matches('0');
    let stripped = if stripped.is_empty() { "0" } else { stripped };
    let exp = exp + 1;
    if exp == 0 {
        format!("0.{}", stripped)
    } else {
        format!("0.{}E{}", stripped, sml_exp(exp))
    }
}

/// Format `exp` using SML's `~` for negatives.
fn sml_exp(exp: i32) -> String {
    if exp < 0 {
        format!("~{}", (exp as i64).unsigned_abs())
    } else {
        exp.to_string()
    }
}

/// Returns `abs`'s canonical decimal: a string of significant digits
/// (no leading zeros, no decimal point) and the standard scientific
/// exponent `e` such that `digits.0 * 10^e == abs` (decimal point
/// implicit after the first digit). Uses Rust's `{:e}` form, which
/// emits the shortest round-tripping representation for `f32`.
fn canonical(abs: f32) -> (String, i32) {
    // The smallest positive subnormal, `Real.minPos`, round-trips from the
    // one-digit "1e-45", so Rust's shortest `{:e}` reports it as "1E~45".
    // SML's `Real.toString`/`Real.fmt` instead report it as 1.4e-45.
    if abs == f32::from_bits(1) {
        return ("14".to_string(), -45);
    }
    let s = format!("{:e}", abs);
    let (mantissa, exp_str) = match s.find('e') {
        Some(i) => (&s[..i], &s[i + 1..]),
        None => (s.as_str(), "0"),
    };
    let exp_base: i32 = exp_str.parse().unwrap_or(0);
    let (int_part, frac_part) = match mantissa.find('.') {
        Some(d) => (&mantissa[..d], &mantissa[d + 1..]),
        None => (mantissa, ""),
    };
    let mut digits = format!("{}{}", int_part, frac_part);
    if digits.is_empty() {
        digits.push('0');
    }
    let exp = exp_base + (int_part.len() as i32 - 1);
    (digits, exp)
}

/// Rounds the digit string `digits` to `target` significant digits
/// using half-down (ties round toward zero). Returns the rounded
/// digit string and an exponent adjustment (1 if rounding carried
/// past the leading position, e.g. "999" -> "1000"; else 0).
fn round_half_down_digits(digits: &str, target: usize) -> (String, i32) {
    if target == 0 {
        // No significant digits requested. Treat as "0", exp_adj=0.
        return ("0".to_string(), 0);
    }
    if digits.len() <= target {
        let mut s = digits.to_string();
        while s.len() < target {
            s.push('0');
        }
        return (s, 0);
    }
    let kept = &digits[..target];
    let dropped = &digits[target..];
    let first_dropped = dropped.as_bytes()[0];
    let rest_dropped = &dropped[1..];
    // Round up iff first_dropped > '5', or first_dropped == '5' and any
    // remaining dropped digit is non-zero (half-down: exact .5 stays).
    let round_up = first_dropped > b'5'
        || (first_dropped == b'5' && rest_dropped.bytes().any(|b| b != b'0'));
    if !round_up {
        return (kept.to_string(), 0);
    }
    // Increment `kept` as if it were a big integer.
    let mut bytes: Vec<u8> = kept.bytes().collect();
    let mut carry = 1u8;
    for b in bytes.iter_mut().rev() {
        if carry == 0 {
            break;
        }
        let v = *b - b'0' + carry;
        if v >= 10 {
            *b = b'0';
            carry = 1;
        } else {
            *b = b'0' + v;
            carry = 0;
        }
    }
    if carry == 1 {
        // Carry past the front: "999" -> "1000". Truncate the trailing
        // zero and bump the exponent.
        let mut out = String::with_capacity(target);
        out.push('1');
        for _ in 1..target {
            out.push('0');
        }
        (out, 1)
    } else {
        (String::from_utf8(bytes).unwrap(), 0)
    }
}

/// Places a decimal point in `digits` so the result is `digits.0 *
/// 10^exp` with `min_frac` digits after the point. If `strip` is
/// true, trailing zeros (and a trailing `.`) are removed.
fn place_decimal(
    digits: &str,
    exp: i32,
    min_frac: usize,
    strip: bool,
) -> String {
    // Number of integer digits in the result.
    let int_len_signed = exp + 1;
    let body = if int_len_signed <= 0 {
        // Result is `0.<zeros><digits>`; need `-exp` zeros (1 for
        // exp=-1, 2 for exp=-2, etc., before the digits themselves).
        let lead = (-int_len_signed) as usize;
        format!("0.{}{}", "0".repeat(lead), digits)
    } else {
        let int_len = int_len_signed as usize;
        if int_len >= digits.len() {
            // Need to right-pad with zeros to reach int_len.
            let mut out = String::from(digits);
            for _ in digits.len()..int_len {
                out.push('0');
            }
            if min_frac > 0 {
                out.push('.');
                for _ in 0..min_frac {
                    out.push('0');
                }
            }
            return if strip { trim_decimal(&out) } else { out };
        }
        format!("{}.{}", &digits[..int_len], &digits[int_len..])
    };
    // Ensure min_frac digits after the decimal point.
    let mut body = body;
    if let Some(dot) = body.find('.') {
        let frac_len = body.len() - dot - 1;
        if frac_len < min_frac {
            for _ in frac_len..min_frac {
                body.push('0');
            }
        }
    } else if min_frac > 0 {
        body.push('.');
        for _ in 0..min_frac {
            body.push('0');
        }
    }
    if strip { trim_decimal(&body) } else { body }
}

/// Removes trailing zeros after a decimal point, then a trailing `.`.
fn trim_decimal(s: &str) -> String {
    if !s.contains('.') {
        return s.to_string();
    }
    let trimmed = s.trim_end_matches('0').trim_end_matches('.');
    if trimmed.is_empty() {
        "0".to_string()
    } else {
        trimmed.to_string()
    }
}
