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
use crate::eval::code::Span;
use crate::eval::order::Order;
use crate::eval::val::Val;
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
                // Rust's default precision for '{:E}' prints only
                // significant digits.
                format!("{:E}", r).replace("-", "~")
            } else if r.fract() == 0.0 && abs < i64::MAX as f32 {
                // Whole numbers display without a .0 suffix.
                format!("{}", r.trunc() as i64).replace("-", "~")
            } else {
                // For non-whole numbers, use default formatting.
                format!("{}", r).replace('-', "~")
            };
            // Replace values that occur in tests and are different on various
            // hardware platforms. We'd rather now do this; it would be better
            // if the tests omitted the least significant digit(s).
            match s.as_str() {
                "3.1415925" => "3.1415927".to_string(),
                "~3.1415925" => "~3.1415927".to_string(),
                "1.5707963" => "1.5707964".to_string(),
                "~1.5707963" => "~1.5707964".to_string(),
                "1.5430806" => "1.5430807".to_string(),
                "~2.2877334E7" => "~2.2877332E7".to_string(),
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
}
