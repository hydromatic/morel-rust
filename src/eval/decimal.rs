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

//! The `Decimal` structure.
//!
//! A `decimal` value is exact decimal floating point in the IEEE
//! 754-2008 decimal128 format: 34 significant digits, radix 10,
//! rounding half-even.
//!
//! Arithmetic is done on the decimal digits themselves rather than
//! through [crate::eval::big_int::BigInt], which has no division. A
//! decimal is a string of digits and a power of ten, so aligning,
//! rounding and scaling are string operations, and the one operation
//! that needs more, division, is schoolbook long division in base 10.

use crate::eval::real::{
    FmtKind, ZERO_DIGITS, format_exact, format_fix, format_gen, format_sci,
    round_digits,
};
use std::cmp::Ordering;
use std::fmt;

/// The number of significant digits, 34.
pub const PRECISION: usize = 34;

/// The largest adjusted exponent, 6144.
const E_MAX: i32 = 6144;

/// The largest scale, 6176: the least significant digit of a value is
/// never smaller than 10^-6176.
const MAX_SCALE: i32 = 6176;

/// Bounds the exponent read from a string. Any exponent this large
/// overflows or underflows, so clamping it loses nothing and keeps the
/// arithmetic small.
const MAX_PARSED_EXPONENT: i32 = 100_000;

/// A value of the `decimal` type, in canonical form: the value is
/// `digits * 10^exp`, negated if `neg`.
///
/// Canonical form means one representation per value, so two decimals
/// are numerically equal exactly when the structs are equal. It
/// requires that `digits` has no leading zero and no trailing zero,
/// that it is at most [PRECISION] long, and that zero is the single
/// value with empty digits, exponent 0 and `neg` false.
#[derive(Clone, Eq, PartialEq, Hash, Debug)]
pub struct Decimal {
    neg: bool,
    digits: String,
    exp: i32,
}

impl fmt::Display for Decimal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.to_string_with('~'))
    }
}

impl PartialOrd for Decimal {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Decimal {
    /// Compares two decimals. Canonical form makes this exact without
    /// any arithmetic: the sign decides, then the exponent in
    /// scientific notation, then the digits.
    fn cmp(&self, other: &Self) -> Ordering {
        match (self.is_zero(), other.is_zero()) {
            (true, true) => return Ordering::Equal,
            (true, false) => {
                return if other.neg {
                    Ordering::Greater
                } else {
                    Ordering::Less
                };
            }
            (false, true) => {
                return if self.neg {
                    Ordering::Less
                } else {
                    Ordering::Greater
                };
            }
            (false, false) => {}
        }
        if self.neg != other.neg {
            return if self.neg {
                Ordering::Less
            } else {
                Ordering::Greater
            };
        }
        let c = self.cmp_mag(other);
        if self.neg { c.reverse() } else { c }
    }
}

impl Decimal {
    /// The value zero.
    pub fn zero() -> Self {
        Decimal {
            neg: false,
            digits: String::new(),
            exp: 0,
        }
    }

    /// `Decimal.maxFinite`, 9.999999999999999999999999999999999E6144.
    pub fn max_finite() -> Self {
        Decimal {
            neg: false,
            digits: "9".repeat(PRECISION),
            exp: E_MAX - PRECISION as i32 + 1,
        }
    }

    /// `Decimal.minPos`, 1E~6176.
    pub fn min_pos() -> Self {
        Decimal {
            neg: false,
            digits: "1".to_string(),
            exp: -MAX_SCALE,
        }
    }

    /// Whether the value is zero.
    pub fn is_zero(&self) -> bool {
        self.digits.is_empty()
    }

    /// The exponent the value has in scientific notation: 0 for
    /// [1, 10), 1 for [10, 100), -1 for [0.1, 1).
    pub fn adj_exp(&self) -> i32 {
        self.digits.len() as i32 - 1 + self.exp
    }

    /// Renders the value with `~` for a negative value or exponent.
    /// Uses plain notation if the adjusted exponent is in [~7, 34),
    /// scientific notation otherwise; for example "12.3", "1200",
    /// "1E100", "1E~8".
    pub fn to_string_with(&self, negation: char) -> String {
        if self.is_zero() {
            return "0".to_string();
        }
        let mut s = String::new();
        if self.neg {
            s.push(negation);
        }
        const MIN_PLAIN_EXP: i32 = -7;
        let adjusted = self.adj_exp();
        if adjusted < MIN_PLAIN_EXP || adjusted >= PRECISION as i32 {
            s.push_str(&self.digits[..1]);
            if self.digits.len() > 1 {
                s.push('.');
                s.push_str(&self.digits[1..]);
            }
            s.push('E');
            if adjusted < 0 {
                s.push(negation);
            }
            s.push_str(&adjusted.abs().to_string());
            return s;
        }
        let k = -self.exp;
        let len = self.digits.len() as i32;
        if k <= 0 {
            s.push_str(&self.digits);
            s.push_str(&"0".repeat((-k) as usize));
        } else if k < len {
            let split = (len - k) as usize;
            s.push_str(&self.digits[..split]);
            s.push('.');
            s.push_str(&self.digits[split..]);
        } else {
            s.push_str("0.");
            s.push_str(&"0".repeat((k - len) as usize));
            s.push_str(&self.digits);
        }
        s
    }

    /// Compares the magnitudes of two non-zero decimals.
    fn cmp_mag(&self, other: &Self) -> Ordering {
        match self.adj_exp().cmp(&other.adj_exp()) {
            Ordering::Equal => {}
            other_order => return other_order,
        }
        // Equal scientific exponents, so the digit strings decide, the
        // shorter padded with the zeros canonical form removed.
        let (x, y) = (&self.digits, &other.digits);
        let n = x.len().max(y.len());
        let pad = |s: &String| {
            let mut t = s.clone();
            t.push_str(&"0".repeat(n - s.len()));
            t
        };
        pad(x).cmp(&pad(y))
    }

    /// The magnitude scaled so that its last digit is at 10^exp, which
    /// must be no greater than the decimal's own exponent.
    fn mag_at(&self, exp: i32) -> String {
        if self.is_zero() {
            return ZERO.to_string();
        }
        let mut s = self.digits.clone();
        s.push_str(&"0".repeat((self.exp - exp) as usize));
        s
    }

    /// Returns the value with the opposite sign. Zero negates to
    /// itself, because there is no negative zero.
    pub fn negate(&self) -> Self {
        if self.is_zero() {
            return self.clone();
        }
        Decimal {
            neg: !self.neg,
            ..self.clone()
        }
    }

    /// Returns the magnitude.
    pub fn abs(&self) -> Self {
        Decimal {
            neg: false,
            ..self.clone()
        }
    }

    /// The sign: -1, 0 or 1.
    pub fn signum(&self) -> i32 {
        if self.is_zero() {
            0
        } else if self.neg {
            -1
        } else {
            1
        }
    }
    /// Rounds to an integral decimal.
    pub fn round_to_int(&self, mode: RoundMode) -> Decimal {
        if self.exp >= 0 {
            // Already integral.
            return self.clone();
        }
        let k = (-self.exp) as usize;
        let (whole, frac) = if k >= self.digits.len() {
            (ZERO.to_string(), self.digits.clone())
        } else {
            let split = self.digits.len() - k;
            (
                self.digits[..split].to_string(),
                self.digits[split..].to_string(),
            )
        };
        let mut mag = whole;
        if round_up(mode, self.neg, &mag, &frac, k) {
            mag = add_mag(&mag, "1");
        }
        // An integral value always fits, so canonical cannot fail.
        canonical(self.neg, &mag, 0).unwrap()
    }

    /// The decimal equal to an int.
    pub fn from_i32(n: i32) -> Self {
        let neg = n < 0;
        let mag = i64::from(n).abs().to_string();
        canonical(neg, &mag, 0).unwrap()
    }

    /// Converts to an int, or `None` if it does not fit. The value must
    /// be integral.
    pub fn to_i32(&self) -> Option<i32> {
        if self.is_zero() {
            return Some(0);
        }
        let mut mag = self.digits.clone();
        if self.exp > 0 {
            mag.push_str(&"0".repeat(self.exp as usize));
        }
        // i32::MIN has 10 digits, so anything longer cannot fit.
        if mag.len() > 10 {
            return None;
        }
        let n: i64 = mag.parse().ok()?;
        let n = if self.neg { -n } else { n };
        i32::try_from(n).ok()
    }

    /// The nearest real, which is an infinity if the value is too
    /// large.
    pub fn to_f32(&self) -> f32 {
        if self.is_zero() {
            return 0.0;
        }
        let text = format!(
            "{}{}E{}",
            if self.neg { "-" } else { "" },
            self.digits,
            self.exp
        );
        // A value out of range parses as an infinity, with an error
        // that says so; that is the answer we want.
        text.parse::<f32>().unwrap_or(if self.neg {
            f32::NEG_INFINITY
        } else {
            f32::INFINITY
        })
    }

    /// Renders in the given `StringCvt.realfmt` style. Ties round
    /// half-even, as decimal arithmetic does.
    pub fn fmt_style(&self, kind: FmtKind, n: usize) -> String {
        let (digits, exp) = if self.is_zero() {
            (ZERO_DIGITS.to_string(), 0)
        } else {
            (self.digits.clone(), self.adj_exp())
        };
        let body = match kind {
            FmtKind::Sci => format_sci(&digits, exp, n, true),
            FmtKind::Fix => format_fix(&digits, exp, n, true),
            FmtKind::Gen => format_gen(&digits, exp, n, true),
            FmtKind::Exact => format_exact(&digits, exp),
        };
        if self.neg { format!("~{}", body) } else { body }
    }
}

/// The digit string of zero, where a magnitude needs one.
const ZERO: &str = "0";

// --- Base-10 arithmetic on magnitudes ------------------------------
//
// A magnitude is a non-empty string of decimal digits with no leading
// zero, except that zero is "0".

/// Strips leading zeros, leaving "0" if nothing is left.
fn trim_mag(s: &str) -> String {
    let t = s.trim_start_matches('0');
    if t.is_empty() {
        ZERO.to_string()
    } else {
        t.to_string()
    }
}

/// Compares two magnitudes.
fn cmp_mag(a: &str, b: &str) -> Ordering {
    a.len().cmp(&b.len()).then_with(|| a.cmp(b))
}

/// Adds two magnitudes.
fn add_mag(a: &str, b: &str) -> String {
    let (x, y) = (a.as_bytes(), b.as_bytes());
    let mut out = Vec::with_capacity(x.len().max(y.len()) + 1);
    let mut carry = 0u8;
    for i in 0..x.len().max(y.len()) {
        let dx = digit_from_end(x, i);
        let dy = digit_from_end(y, i);
        let sum = dx + dy + carry;
        out.push(b'0' + sum % 10);
        carry = sum / 10;
    }
    if carry > 0 {
        out.push(b'0' + carry);
    }
    out.reverse();
    String::from_utf8(out).unwrap()
}

/// Subtracts `b` from `a`, which must be no smaller.
fn sub_mag(a: &str, b: &str) -> String {
    let (x, y) = (a.as_bytes(), b.as_bytes());
    let mut out = Vec::with_capacity(x.len());
    let mut borrow = 0i8;
    for i in 0..x.len() {
        let mut d =
            digit_from_end(x, i) as i8 - digit_from_end(y, i) as i8 - borrow;
        if d < 0 {
            d += 10;
            borrow = 1;
        } else {
            borrow = 0;
        }
        out.push(b'0' + d as u8);
    }
    out.reverse();
    trim_mag(&String::from_utf8(out).unwrap())
}

/// The digit `i` places from the end of `s`, or 0 beyond its start.
fn digit_from_end(s: &[u8], i: usize) -> u8 {
    if i < s.len() {
        s[s.len() - 1 - i] - b'0'
    } else {
        0
    }
}

/// Multiplies two magnitudes.
fn mul_mag(a: &str, b: &str) -> String {
    if a == ZERO || b == ZERO {
        return ZERO.to_string();
    }
    let (x, y) = (a.as_bytes(), b.as_bytes());
    let mut acc = vec![0u32; x.len() + y.len()];
    for i in 0..x.len() {
        let dx = u32::from(x[x.len() - 1 - i] - b'0');
        if dx == 0 {
            continue;
        }
        let mut carry = 0u32;
        for j in 0..y.len() {
            let dy = u32::from(y[y.len() - 1 - j] - b'0');
            let k = i + j;
            let t = acc[k] + dx * dy + carry;
            acc[k] = t % 10;
            carry = t / 10;
        }
        let mut k = i + y.len();
        while carry > 0 {
            let t = acc[k] + carry;
            acc[k] = t % 10;
            carry = t / 10;
            k += 1;
        }
    }
    // `acc` is little-endian, so read it back to front.
    let out: Vec<u8> = acc.iter().rev().map(|d| b'0' + *d as u8).collect();
    trim_mag(&String::from_utf8(out).unwrap())
}

/// Multiplies a magnitude by a single digit.
fn mul_digit(a: &str, d: u8) -> String {
    if d == 0 || a == ZERO {
        return ZERO.to_string();
    }
    let x = a.as_bytes();
    let mut out = Vec::with_capacity(x.len() + 1);
    let mut carry = 0u8;
    for i in 0..x.len() {
        let t = digit_from_end(x, i) * d + carry;
        out.push(b'0' + t % 10);
        carry = t / 10;
    }
    while carry > 0 {
        out.push(b'0' + carry % 10);
        carry /= 10;
    }
    out.reverse();
    String::from_utf8(out).unwrap()
}

/// Divides one magnitude by another, returning the integer quotient
/// and whether the remainder is non-zero. Schoolbook long division:
/// one quotient digit at a time, found by trying the nine multiples of
/// the divisor.
fn divmod_mag(a: &str, b: &str) -> (String, bool) {
    let mut quotient = String::with_capacity(a.len());
    let mut rem = ZERO.to_string();
    for ch in a.chars() {
        if rem == ZERO {
            rem.clear();
        }
        rem.push(ch);
        rem = trim_mag(&rem);
        let mut d = 0u8;
        while d < 9 {
            if cmp_mag(&mul_digit(b, d + 1), &rem) == Ordering::Greater {
                break;
            }
            d += 1;
        }
        if d > 0 {
            rem = sub_mag(&rem, &mul_digit(b, d));
        }
        quotient.push((b'0' + d) as char);
    }
    (trim_mag(&quotient), rem != ZERO)
}

/// The remainder of one magnitude divided by another.
fn rem_mag(a: &str, b: &str) -> String {
    let (q, _) = divmod_mag(a, b);
    sub_mag(a, &mul_mag(b, &q))
}

// --- Canonical form and arithmetic ---------------------------------

/// Converts `mag * 10^exp`, negated if `neg`, to canonical form.
/// Returns `None` if the magnitude is too large to represent. Rounds
/// half-even to [PRECISION] significant digits, truncates toward zero
/// a value too small to represent, and strips trailing zeros.
fn canonical(neg: bool, mag: &str, exp: i32) -> Option<Decimal> {
    let mut digits = trim_mag(mag);
    if digits == ZERO {
        return Some(Decimal::zero());
    }
    let mut exp = exp;
    let adjusted = digits.len() as i32 - 1 + exp;
    if adjusted > E_MAX {
        return None;
    }
    if adjusted < -MAX_SCALE {
        // Too small for even the smallest subnormal.
        return Some(Decimal::zero());
    }
    if -exp > MAX_SCALE {
        // Truncate toward zero to the smallest representable digit.
        let drop = (-exp - MAX_SCALE) as usize;
        if drop >= digits.len() {
            return Some(Decimal::zero());
        }
        digits.truncate(digits.len() - drop);
        exp = -MAX_SCALE;
    }
    if digits.len() > PRECISION {
        let drop = (digits.len() - PRECISION) as i32;
        let (rounded, adj) = round_digits(&digits, PRECISION, true);
        digits = rounded;
        exp += drop + adj;
    }
    while digits.len() > 1 && digits.ends_with('0') {
        digits.pop();
        exp += 1;
    }
    if digits == ZERO {
        return Some(Decimal::zero());
    }
    // Rounding up may have raised the exponent, as 9.99...9E6144 to
    // 1E6145.
    if digits.len() as i32 - 1 + exp > E_MAX {
        return None;
    }
    Some(Decimal { neg, digits, exp })
}

/// Adds two decimals, or `None` on overflow.
pub fn add(a: &Decimal, b: &Decimal) -> Option<Decimal> {
    if a.is_zero() {
        return Some(b.clone());
    }
    if b.is_zero() {
        return Some(a.clone());
    }
    let exp = a.exp.min(b.exp);
    let (x, y) = (a.mag_at(exp), b.mag_at(exp));
    if a.neg == b.neg {
        return canonical(a.neg, &add_mag(&x, &y), exp);
    }
    match cmp_mag(&x, &y) {
        Ordering::Equal => Some(Decimal::zero()),
        Ordering::Greater => canonical(a.neg, &sub_mag(&x, &y), exp),
        Ordering::Less => canonical(b.neg, &sub_mag(&y, &x), exp),
    }
}

/// Subtracts one decimal from another, or `None` on overflow.
pub fn sub(a: &Decimal, b: &Decimal) -> Option<Decimal> {
    add(a, &b.negate())
}

/// Multiplies two decimals, or `None` on overflow.
pub fn mul(a: &Decimal, b: &Decimal) -> Option<Decimal> {
    if a.is_zero() || b.is_zero() {
        return Some(Decimal::zero());
    }
    canonical(
        a.neg != b.neg,
        &mul_mag(&a.digits, &b.digits),
        a.exp + b.exp,
    )
}

/// Divides one decimal by another, rounding half-even to [PRECISION]
/// significant digits. `Err(())` means the divisor is zero; `Ok(None)`
/// means the result overflows.
#[allow(clippy::result_unit_err)]
pub fn div(a: &Decimal, b: &Decimal) -> Result<Option<Decimal>, ()> {
    if b.is_zero() {
        return Err(());
    }
    if a.is_zero() {
        return Ok(Some(Decimal::zero()));
    }
    // Compute two digits more than the precision, so that rounding has
    // a digit to inspect and one to spare.
    const EXTRA: usize = 2;
    let scale = PRECISION + EXTRA + b.digits.len() - a.digits.len();
    let mut num = a.digits.clone();
    num.push_str(&"0".repeat(scale));
    let (mut quotient, inexact) = divmod_mag(&num, &b.digits);
    if inexact && quotient.ends_with('0') {
        // The quotient is inexact. A tie at the rounding place must
        // break upward rather than to even, and the only way a tie can
        // arise is a dropped tail of zeros, so it is enough to make the
        // last digit non-zero.
        quotient.pop();
        quotient.push('1');
    }
    Ok(canonical(
        a.neg != b.neg,
        &quotient,
        a.exp - b.exp - scale as i32,
    ))
}

/// The remainder of a division truncated toward zero, so it has the
/// sign of the dividend. `Err(())` means the divisor is zero.
#[allow(clippy::result_unit_err)]
pub fn rem(a: &Decimal, b: &Decimal) -> Result<Option<Decimal>, ()> {
    if b.is_zero() {
        return Err(());
    }
    if a.is_zero() {
        return Ok(Some(Decimal::zero()));
    }
    let exp = a.exp.min(b.exp);
    let (x, y) = (a.mag_at(exp), b.mag_at(exp));
    Ok(canonical(a.neg, &rem_mag(&x, &y), exp))
}

/// How a decimal is rounded to an integer.
#[derive(Copy, Clone)]
pub enum RoundMode {
    Trunc,
    Floor,
    Ceil,
    HalfEven,
}

/// Whether rounding a magnitude `whole` with dropped digits `frac`, of
/// the given sign, increases the magnitude. `k` is the number of
/// dropped digits.
fn round_up(
    mode: RoundMode,
    neg: bool,
    whole: &str,
    frac: &str,
    k: usize,
) -> bool {
    if frac.bytes().all(|b| b == b'0') {
        return false;
    }
    match mode {
        RoundMode::Trunc => false,
        RoundMode::Floor => neg,
        RoundMode::Ceil => !neg,
        RoundMode::HalfEven => {
            // Compare the dropped digits with half, which is a 5
            // followed by zeros.
            let mut half = String::from("5");
            half.push_str(&"0".repeat(k - 1));
            match cmp_mag(&trim_mag(frac), &trim_mag(&half)) {
                Ordering::Greater => true,
                Ordering::Equal => {
                    (whole.as_bytes()[whole.len() - 1] - b'0') & 1 == 1
                }
                Ordering::Less => false,
            }
        }
    }
}

// --- Parsing and conversion ----------------------------------------

/// A parsed decimal literal: sign, magnitude, and exponent, before
/// canonical form.
struct Parsed {
    neg: bool,
    mag: String,
    exp: i32,
}

/// Parses a decimal from the start of `s`: an optional sign, digits
/// with an optional decimal point, and an optional exponent. Returns
/// the value and how many bytes it consumed.
fn parse_at(s: &str) -> Option<(Parsed, usize)> {
    let b = s.as_bytes();
    let mut i = 0;
    let mut neg = false;
    if i < b.len() && matches!(b[i], b'~' | b'+' | b'-') {
        neg = b[i] != b'+';
        i += 1;
    }
    let int_start = i;
    while i < b.len() && b[i].is_ascii_digit() {
        i += 1;
    }
    let int_part = &s[int_start..i];
    let mut frac_part = "";
    if i < b.len() && b[i] == b'.' {
        i += 1;
        let frac_start = i;
        while i < b.len() && b[i].is_ascii_digit() {
            i += 1;
        }
        frac_part = &s[frac_start..i];
    }
    if int_part.is_empty() && frac_part.is_empty() {
        return None;
    }
    let mut exp = -(frac_part.len() as i32);
    // An exponent counts only if it is complete: "1e" is a decimal
    // followed by the letter e, not a malformed exponent.
    if i < b.len() && matches!(b[i], b'e' | b'E') {
        let mut j = i + 1;
        let mut exp_neg = false;
        if j < b.len() && matches!(b[j], b'~' | b'+' | b'-') {
            exp_neg = b[j] != b'+';
            j += 1;
        }
        let digit_start = j;
        while j < b.len() && b[j].is_ascii_digit() {
            j += 1;
        }
        if j > digit_start {
            let text = &s[digit_start..j];
            const MAX_EXPONENT_DIGITS: usize = 6;
            let e = if text.len() > MAX_EXPONENT_DIGITS {
                MAX_PARSED_EXPONENT
            } else {
                text.parse::<i32>().unwrap().min(MAX_PARSED_EXPONENT)
            };
            exp += if exp_neg { -e } else { e };
            i = j;
        }
    }
    let mut mag = String::with_capacity(int_part.len() + frac_part.len());
    mag.push_str(int_part);
    mag.push_str(frac_part);
    Some((
        Parsed {
            neg,
            mag: trim_mag(&mag),
            exp,
        },
        i,
    ))
}

/// Parses a string that is exactly a decimal and whose value is
/// exactly representable, which is what the `decimal` function
/// requires. Returns `None` if the string is malformed, has more than
/// [PRECISION] significant digits, or is out of range.
pub fn parse_exact(s: &str) -> Option<Decimal> {
    let (p, used) = parse_at(s)?;
    if used != s.len() {
        return None;
    }
    if p.mag == ZERO {
        return Some(Decimal::zero());
    }
    let mut digits = p.mag;
    let mut exp = p.exp;
    while digits.len() > 1 && digits.ends_with('0') {
        digits.pop();
        exp += 1;
    }
    if digits.len() > PRECISION
        || digits.len() as i32 - 1 + exp > E_MAX
        || exp < -MAX_SCALE
    {
        return None;
    }
    Some(Decimal {
        neg: p.neg,
        digits,
        exp,
    })
}

/// Parses a decimal from a prefix of a string, after skipping leading
/// whitespace, rounding to [PRECISION] digits. This is the semantics
/// of `Decimal.fromString`. `None` means there is no decimal;
/// `Some(None)` means the value is too large to represent.
pub fn parse_prefix(s: &str) -> Option<Option<Decimal>> {
    let rest = s.trim_start();
    let (p, _) = parse_at(rest)?;
    Some(canonical(p.neg, &p.mag, p.exp))
}

/// Adds a list of decimals exactly, then rounds once. `None` on
/// overflow.
pub fn sum(values: &[Decimal]) -> Option<Decimal> {
    let mut exp = 0i32;
    let mut first = true;
    for d in values {
        if d.is_zero() {
            continue;
        }
        if first || d.exp < exp {
            exp = d.exp;
            first = false;
        }
    }
    if first {
        // Every term is zero, so no exponent was chosen.
        return Some(Decimal::zero());
    }
    // Accumulate positive and negative magnitudes separately, so that
    // the addition is exact and nothing is rounded until the end.
    let mut pos = ZERO.to_string();
    let mut neg = ZERO.to_string();
    for d in values {
        if d.is_zero() {
            continue;
        }
        let m = d.mag_at(exp);
        if d.signum() < 0 {
            neg = add_mag(&neg, &m);
        } else {
            pos = add_mag(&pos, &m);
        }
    }
    let total = match cmp_mag(&pos, &neg) {
        Ordering::Equal => Decimal::zero(),
        Ordering::Greater => canonical(false, &sub_mag(&pos, &neg), exp)?,
        Ordering::Less => canonical(true, &sub_mag(&neg, &pos), exp)?,
    };
    Some(total)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Parses a literal the way the `decimal` function does, panicking
    /// on one the tests got wrong.
    fn d(s: &str) -> Decimal {
        parse_exact(s).unwrap_or_else(|| panic!("bad literal {:?}", s))
    }

    fn show(x: &Decimal) -> String {
        x.to_string_with('~')
    }

    #[test]
    fn parses_and_prints() {
        assert_eq!(show(&d("12.30")), "12.3");
        assert_eq!(show(&d("0.000")), "0");
        assert_eq!(show(&d("~0")), "0");
        assert_eq!(show(&d("-0.0")), "0");
        assert_eq!(show(&d("~12.3")), "~12.3");
        assert_eq!(show(&d("+12.3")), "12.3");
        assert_eq!(show(&d(".5")), "0.5");
        assert_eq!(show(&d("5.")), "5");
        assert_eq!(show(&d("1.5e3")), "1500");
        assert_eq!(show(&d("1.5E~3")), "0.0015");
        assert_eq!(show(&d("1.5e-3")), "0.0015");
        assert_eq!(show(&d("0.0000001")), "0.0000001");
        assert_eq!(show(&d("0.00000001")), "1E~8");
        assert_eq!(show(&d("~0.000000012")), "~1.2E~8");
        assert_eq!(show(&d("1200")), "1200");
        assert_eq!(show(&d("1E34")), "1E34");
        assert_eq!(show(&d("1.5E100")), "1.5E100");
        assert_eq!(
            show(&Decimal::max_finite()),
            "9.999999999999999999999999999999999E6144"
        );
        assert_eq!(show(&Decimal::min_pos()), "1E~6176");
    }

    #[test]
    fn rejects_bad_literals() {
        for s in [
            "12.x",
            "",
            " 1",
            "1e",
            "abc",
            "12345678901234567890123456789012345",
            "1E6145",
            "1E~6177",
        ] {
            assert!(parse_exact(s).is_none(), "should reject {:?}", s);
        }
        assert!(
            parse_exact("1.000000000000000000000000000000000000000").is_some()
        );
    }

    #[test]
    fn arithmetic() {
        assert_eq!(add(&d("0.1"), &d("0.2")).unwrap(), d("0.3"));
        assert_eq!(
            show(&add(&d("1E30"), &d("1E~5")).unwrap()),
            "1000000000000000000000000000000"
        );
        assert_eq!(show(&add(&d("1E34"), &d("1")).unwrap()), "1E34");
        assert_eq!(show(&sub(&d("5"), &d("7.5")).unwrap()), "~2.5");
        assert_eq!(show(&sub(&d("1.1"), &d("1.1")).unwrap()), "0");
        assert_eq!(show(&mul(&d("12"), &d("100")).unwrap()), "1200");
        assert_eq!(show(&mul(&d("1.5"), &d("~2")).unwrap()), "~3");
        assert!(mul(&Decimal::max_finite(), &d("10")).is_none());
        assert!(add(&Decimal::max_finite(), &Decimal::max_finite()).is_none());
        assert_eq!(show(&mul(&Decimal::min_pos(), &d("0.5")).unwrap()), "0");
    }

    #[test]
    fn division() {
        assert_eq!(
            show(&div(&d("1"), &d("3")).unwrap().unwrap()),
            "0.3333333333333333333333333333333333"
        );
        assert_eq!(
            show(&div(&d("2"), &d("3")).unwrap().unwrap()),
            "0.6666666666666666666666666666666667"
        );
        assert_eq!(show(&div(&d("10"), &d("4")).unwrap().unwrap()), "2.5");
        assert!(div(&d("1"), &d("0")).is_err());
        assert_eq!(
            show(&div(&Decimal::min_pos(), &d("3")).unwrap().unwrap()),
            "0"
        );
        assert_eq!(show(&rem(&d("10"), &d("3")).unwrap().unwrap()), "1");
        assert_eq!(show(&rem(&d("~10"), &d("3")).unwrap().unwrap()), "~1");
        assert_eq!(show(&rem(&d("10.5"), &d("~3")).unwrap().unwrap()), "1.5");
    }

    #[test]
    fn rounding() {
        let cases = [
            (RoundMode::Floor, ["2", "~3", "3"]),
            (RoundMode::Ceil, ["3", "~2", "3"]),
            (RoundMode::Trunc, ["2", "~2", "3"]),
        ];
        for (mode, want) in cases {
            for (i, s) in ["2.5", "~2.5", "3"].iter().enumerate() {
                assert_eq!(
                    show(&d(s).round_to_int(mode)),
                    want[i],
                    "{:?} of {}",
                    want,
                    s
                );
            }
        }
        for (s, want) in [
            ("2.5", "2"),
            ("3.5", "4"),
            ("~2.5", "~2"),
            ("2.51", "3"),
            ("1E100", "1E100"),
            ("0.4", "0"),
        ] {
            assert_eq!(
                show(&d(s).round_to_int(RoundMode::HalfEven)),
                want,
                "halfEven of {}",
                s
            );
        }
    }

    #[test]
    fn to_int_and_real() {
        assert_eq!(d("2.5").round_to_int(RoundMode::Floor).to_i32(), Some(2));
        assert_eq!(
            d("2147483647.9").round_to_int(RoundMode::Floor).to_i32(),
            Some(2147483647)
        );
        assert_eq!(
            d("2147483647.1").round_to_int(RoundMode::Ceil).to_i32(),
            None
        );
        assert_eq!(
            d("~2147483648.5").round_to_int(RoundMode::Floor).to_i32(),
            None
        );
        assert_eq!(d("1E100").round_to_int(RoundMode::HalfEven).to_i32(), None);
        assert_eq!(show(&Decimal::from_i32(-2147483648)), "~2147483648");
        assert_eq!(show(&Decimal::from_i32(1200)), "1200");
        assert_eq!(d("0.1").to_f32(), 0.1f32);
        assert_eq!(d("~12.5").to_f32(), -12.5f32);
        assert!(Decimal::max_finite().to_f32().is_infinite());
    }

    #[test]
    fn from_string_rounds() {
        assert_eq!(
            show(&parse_prefix("  ~12.3xyz").unwrap().unwrap()),
            "~12.3"
        );
        assert!(parse_prefix("abc").is_none());
        assert!(parse_prefix("").is_none());
        assert_eq!(
            show(
                &parse_prefix("12345678901234567890123456789012345")
                    .unwrap()
                    .unwrap()
            ),
            "1.234567890123456789012345678901234E34"
        );
        assert!(parse_prefix("1E6145").unwrap().is_none());
        assert_eq!(show(&parse_prefix("1E~7000").unwrap().unwrap()), "0");
        assert!(parse_prefix("1E999999999999").unwrap().is_none());
    }

    #[test]
    fn sums_exactly() {
        let xs = [d("0.1"), d("0.2"), d("12.30")];
        assert_eq!(show(&sum(&xs).unwrap()), "12.6");
        assert!(sum(&[Decimal::max_finite(), Decimal::max_finite()]).is_none());
        assert_eq!(show(&sum(&[]).unwrap()), "0");
    }

    #[test]
    fn compares() {
        assert_eq!(d("1.10"), d("1.1"));
        assert!(d("~1") < d("1"));
        assert!(d("2") > d("1"));
        assert!(d("1.5") < d("2"));
        assert_eq!(d("1"), d("1.0"));
        assert!(d("1") != d("1.01"));
    }
}
