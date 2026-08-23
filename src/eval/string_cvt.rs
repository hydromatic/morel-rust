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

//! The `StringCvt` functions that take a reader.
//!
//! A reader is a function `'b -> (char * 'b) option`: it reads one
//! character from a stream and returns it with the rest of the stream,
//! or `NONE` at the end. Only the reader knows what the stream is; the
//! functions here pass it back unexamined.

use crate::compile::library::BuiltInExn;
use crate::compile::span::Span;
use crate::eval::code::{EvalEnv, Frame};
use crate::eval::date::date_of;
use crate::eval::int::radix_base;
use crate::eval::val::{NativeFn, Val};
use crate::shell::kernel::MorelError;
use std::iter::repeat;
use std::rc::Rc;

/// Reads from `src` the longest prefix of characters satisfying `p`,
/// and returns it with the rest of the stream. `splitl`, `takel` and
/// `dropl` return the pair, its first component and its second.
pub(crate) fn splitl(
    r: &mut EvalEnv,
    f: &mut Frame,
    p: &Val,
    rdr: &Val,
    src: &Val,
) -> Result<(String, Val), MorelError> {
    let mut prefix = String::new();
    let mut s = src.clone();
    loop {
        let Val::Some(pair) = rdr.apply_f1(r, f, &s)? else {
            break; // NONE: end of stream
        };
        let pair = pair.expect_list();
        let c = pair[0].expect_char();
        if !p.apply_f1(r, f, &pair[0])?.expect_bool() {
            break;
        }
        prefix.push(c);
        s = pair[1].clone();
    }
    Ok((prefix, s))
}

/// Drops any leading whitespace from `src`.
pub(crate) fn skip_ws(
    r: &mut EvalEnv,
    f: &mut Frame,
    rdr: &Val,
    src: &Val,
) -> Result<Val, MorelError> {
    let mut s = src.clone();
    loop {
        let Val::Some(pair) = rdr.apply_f1(r, f, &s)? else {
            break;
        };
        let pair = pair.expect_list();
        if !pair[0].expect_char().is_whitespace() {
            break;
        }
        s = pair[1].clone();
    }
    Ok(s)
}

/// Scans `s` with the scanner `scan`, giving it a reader over the
/// characters of `s`. The stream is a position in `s`, but the
/// scanner's type does not say so, and the reader is the only thing
/// that can make sense of it.
pub(crate) fn scan_string(
    r: &mut EvalEnv,
    f: &mut Frame,
    scan: &Val,
    s: &str,
) -> Result<Val, MorelError> {
    let reader = string_reader(s);
    let scanner = scan.apply_f1(r, f, &reader)?;
    match scanner.apply_f1(r, f, &Val::Int(0))? {
        Val::Some(pair) => {
            Ok(Val::Some(Box::new(pair.expect_list()[0].clone())))
        }
        _ => Ok(Val::Unit),
    }
}

/// Reads `word` from `src`, character by character, and returns the
/// stream that follows it; `None` if the stream does not begin with it.
pub(crate) fn expect_word(
    r: &mut EvalEnv,
    f: &mut Frame,
    rdr: &Val,
    src: &Val,
    word: &str,
) -> Result<Option<Val>, MorelError> {
    let mut s = src.clone();
    for want in word.chars() {
        let Val::Some(pair) = rdr.apply_f1(r, f, &s)? else {
            return Ok(None);
        };
        let pair = pair.expect_list();
        if pair[0].expect_char() != want {
            return Ok(None);
        }
        s = pair[1].clone();
    }
    Ok(Some(s))
}

/// `SOME (value, rest)`, the result of a scanner that read something.
pub(crate) fn scanned(value: Val, rest: Val) -> Val {
    Val::Some(Box::new(Val::List(Rc::new(vec![value, rest]))))
}

/// Scans `true` or `false`, after skipping whitespace.
pub(crate) fn bool_scan(
    r: &mut EvalEnv,
    f: &mut Frame,
    rdr: &Val,
    src: &Val,
) -> Result<Val, MorelError> {
    let s = skip_ws(r, f, rdr, src)?;
    for (word, value) in [("true", true), ("false", false)] {
        if let Some(rest) = expect_word(r, f, rdr, &s, word)? {
            return Ok(scanned(Val::Bool(value), rest));
        }
    }
    Ok(Val::Unit)
}

/// Scans a value from a prefix of `s` with a scanner written in Rust,
/// as `StringCvt.scanString` does for one written in Morel. `Bool
/// .fromString` and its like are defined that way, so whitespace is
/// skipped and characters after the value are ignored.
pub(crate) fn scan_str(
    r: &mut EvalEnv,
    f: &mut Frame,
    scan: impl Fn(&mut EvalEnv, &mut Frame, &Val, &Val) -> Result<Val, MorelError>,
    s: &str,
) -> Result<Val, MorelError> {
    let reader = string_reader(s);
    match scan(r, f, &reader, &Val::Int(0))? {
        Val::Some(pair) => {
            Ok(Val::Some(Box::new(pair.expect_list()[0].clone())))
        }
        _ => Ok(Val::Unit),
    }
}

/// A reader over the characters of `s`. The stream is a position in `s`.
pub(crate) fn string_reader(s: &str) -> Val {
    let chars: Rc<Vec<char>> = Rc::new(s.chars().collect());
    Val::NativeFn(Rc::new(NativeFn::new(
        "StringCvt.scanString.reader",
        move |v| match usize::try_from(v.expect_int())
            .ok()
            .and_then(|i| chars.get(i).map(|c| (i, *c)))
        {
            Some((i, c)) => Val::Some(Box::new(Val::List(Rc::new(vec![
                Val::Char(c),
                Val::Int(i as i32 + 1),
            ])))),
            // NONE: the end of the string, or a position beyond it.
            None => Val::Unit,
        },
    )))
}

/// Reads the characters of `src` while `p` holds, and returns them with
/// the rest of the stream. Unlike [`splitl`] the predicate is a Rust
/// function, for the scanners that recognise a token themselves.
fn take_while(
    r: &mut EvalEnv,
    f: &mut Frame,
    rdr: &Val,
    src: &Val,
    p: impl Fn(char) -> bool,
) -> Result<(String, Val), MorelError> {
    let mut prefix = String::new();
    let mut s = src.clone();
    loop {
        let Val::Some(pair) = rdr.apply_f1(r, f, &s)? else {
            break;
        };
        let pair = pair.expect_list();
        let c = pair[0].expect_char();
        if !p(c) {
            break;
        }
        prefix.push(c);
        s = pair[1].clone();
    }
    Ok((prefix, s))
}

/// A radix's base, and which characters are its digits.
fn radix_of(radix: &Val) -> (u32, fn(char) -> bool) {
    match radix_base(radix) {
        2 => (2, |c: char| matches!(c, '0'..='1')),
        8 => (8, |c: char| matches!(c, '0'..='7')),
        16 => (16, |c: char| c.is_ascii_hexdigit()),
        base => (base, |c: char| c.is_ascii_digit()),
    }
}

/// Reads the digits of a number in `radix`, after an optional prefix
/// that says what the radix is (`0x` for hexadecimal, `0w`/`0wx` for a
/// word), and returns them with the rest of the stream. The prefix is
/// only taken if digits follow it; `0xzz` reads as the digit `0` and
/// stops at the `x`, because `0` is itself a hexadecimal digit.
fn digits(
    r: &mut EvalEnv,
    f: &mut Frame,
    rdr: &Val,
    src: &Val,
    radix: u32,
    is_digit: fn(char) -> bool,
    word: bool,
) -> Result<Option<(String, Val)>, MorelError> {
    let mut s = src.clone();
    for prefix in prefixes(radix, word) {
        if let Some(after) = expect_word(r, f, rdr, &s, prefix)? {
            let (ds, rest) = take_while(r, f, rdr, &after, is_digit)?;
            if !ds.is_empty() {
                return Ok(Some((ds, rest)));
            }
        }
    }
    let (ds, rest) = take_while(r, f, rdr, &s, is_digit)?;
    s = rest;
    if ds.is_empty() {
        return Ok(None);
    }
    Ok(Some((ds, s)))
}

/// The radix prefixes to try, longest first.
fn prefixes(radix: u32, word: bool) -> &'static [&'static str] {
    match (radix, word) {
        (16, true) => &["0wx", "0x"],
        (16, false) => &["0x"],
        (_, true) => &["0w"],
        _ => &[],
    }
}

/// Reads a sign, if there is one: `~` or `+`, and `-` too where
/// `minus` says so. Returns whether the value is negative, and the
/// stream that follows the sign.
fn signed(
    r: &mut EvalEnv,
    f: &mut Frame,
    rdr: &Val,
    src: &Val,
    minus: bool,
) -> Result<(bool, Val), MorelError> {
    let negatives: &[&str] = if minus { &["~", "-"] } else { &["~"] };
    for sign in negatives {
        if let Some(rest) = expect_word(r, f, rdr, src, sign)? {
            return Ok((true, rest));
        }
    }
    match expect_word(r, f, rdr, src, "+")? {
        Some(rest) => Ok((false, rest)),
        None => Ok((false, src.clone())),
    }
}

/// Scans an integer in `radix`, after skipping whitespace. A leading
/// `~` or `+` gives the sign.
pub(crate) fn int_scan(
    r: &mut EvalEnv,
    f: &mut Frame,
    radix: &Val,
    rdr: &Val,
    src: &Val,
) -> Result<Val, MorelError> {
    let (base, is_digit) = radix_of(radix);
    let s = skip_ws(r, f, rdr, src)?;
    let (negative, s) = signed(r, f, rdr, &s, false)?;
    let Some((ds, rest)) = digits(r, f, rdr, &s, base, is_digit, false)? else {
        return Ok(Val::Unit);
    };
    let Ok(magnitude) = i64::from_str_radix(&ds, base) else {
        return Ok(Val::Unit);
    };
    let value = if negative { -magnitude } else { magnitude };
    let Ok(value) = i32::try_from(value) else {
        return Ok(Val::Unit);
    };
    Ok(scanned(Val::Int(value), rest))
}

/// Scans a word in `radix`, after skipping whitespace. A word has no
/// sign.
pub(crate) fn word_scan(
    r: &mut EvalEnv,
    f: &mut Frame,
    radix: &Val,
    rdr: &Val,
    src: &Val,
) -> Result<Val, MorelError> {
    let (base, is_digit) = radix_of(radix);
    let s = skip_ws(r, f, rdr, src)?;
    let Some((ds, rest)) = digits(r, f, rdr, &s, base, is_digit, true)? else {
        return Ok(Val::Unit);
    };
    let Ok(value) = u64::from_str_radix(&ds, base) else {
        return Ok(Val::Unit);
    };
    Ok(scanned(Val::Word(value), rest))
}

/// Scans a real, after skipping whitespace: an optional sign, then
/// `inf`, `infinity` or `nan`, or digits with an optional fraction and
/// exponent.
pub(crate) fn real_scan(
    r: &mut EvalEnv,
    f: &mut Frame,
    rdr: &Val,
    src: &Val,
) -> Result<Val, MorelError> {
    let s = skip_ws(r, f, rdr, src)?;
    // A real may be signed with `-` as well as Standard ML's `~`, and
    // its exponent likewise, because `Real.fromString` reads what other
    // languages write.
    let (negative, s) = signed(r, f, rdr, &s, true)?;
    let sign = if negative { -1.0 } else { 1.0 };
    for (word, value) in [
        ("infinity", f32::INFINITY),
        ("inf", f32::INFINITY),
        ("nan", f32::NAN),
    ] {
        if let Some(rest) = expect_word(r, f, rdr, &s, word)? {
            let value = if word == "nan" { value } else { sign * value };
            return Ok(scanned(Val::Real(value), rest));
        }
    }
    let (whole, s) = take_while(r, f, rdr, &s, |c| c.is_ascii_digit())?;
    if whole.is_empty() {
        return Ok(Val::Unit);
    }
    let mut text = whole;
    let mut rest = s;
    // A fraction, only if a digit follows the point.
    if let Some(after) = expect_word(r, f, rdr, &rest, ".")? {
        let (frac, after2) =
            take_while(r, f, rdr, &after, |c| c.is_ascii_digit())?;
        if !frac.is_empty() {
            text.push('.');
            text.push_str(&frac);
            rest = after2;
        }
    }
    // An exponent, only if a digit follows `e` (or `E`) and its
    // optional sign.
    let exponent = match expect_word(r, f, rdr, &rest, "e")? {
        Some(after) => Some(after),
        None => expect_word(r, f, rdr, &rest, "E")?,
    };
    if let Some(after) = exponent {
        let (exp_neg, after) = signed(r, f, rdr, &after, true)?;
        let (exp, after2) =
            take_while(r, f, rdr, &after, |c| c.is_ascii_digit())?;
        if !exp.is_empty() {
            text.push('e');
            if exp_neg {
                text.push('-');
            }
            text.push_str(&exp);
            rest = after2;
        }
    }
    let Ok(value) = text.parse::<f32>() else {
        return Ok(Val::Unit);
    };
    Ok(scanned(Val::Real(sign * value), rest))
}

/// Reads one character from `src`, or `None` at the end of the stream.
fn read(
    r: &mut EvalEnv,
    f: &mut Frame,
    rdr: &Val,
    src: &Val,
) -> Result<Option<(char, Val)>, MorelError> {
    match rdr.apply_f1(r, f, src)? {
        Val::Some(pair) => {
            let pair = pair.expect_list();
            Ok(Some((pair[0].expect_char(), pair[1].clone())))
        }
        _ => Ok(None),
    }
}

/// Reads `n` digits in `radix` and returns their value, or `None` if
/// there are fewer than `n`, or the value is not a character.
fn code(
    r: &mut EvalEnv,
    f: &mut Frame,
    rdr: &Val,
    src: &Val,
    n: usize,
    radix: u32,
) -> Result<Option<(char, Val)>, MorelError> {
    let mut value: u32 = 0;
    let mut s = src.clone();
    for _ in 0..n {
        let Some((c, rest)) = read(r, f, rdr, &s)? else {
            return Ok(None);
        };
        let Some(d) = c.to_digit(radix) else {
            return Ok(None);
        };
        value = value * radix + d;
        s = rest;
    }
    // A character is a byte, as `Char.maxOrd` says; and a surrogate is
    // not a character at all.
    match u8::try_from(value) {
        Ok(b) => Ok(Some((b as char, s))),
        Err(_) => Ok(None),
    }
}

/// What reading one character in Standard ML source form produced.
enum Scanned {
    /// A character, and the stream after it.
    Char(char, Val),
    /// An escaped formatting sequence -- a backslash, whitespace and a
    /// backslash -- which stands for nothing; and the stream after it.
    Nothing(Val),
    /// Nothing that can be read: the end of the stream, an ill-formed
    /// escape, or a raw character that has to be escaped. The stream is
    /// left where it was.
    None,
}

/// Reads one character in Standard ML source form: itself, or an escape
/// sequence. Whitespace is not skipped -- a space is a character like
/// any other. `quote` says whether a raw double-quote is a character,
/// which it is in a string but not in a character constant.
fn scan_char(
    r: &mut EvalEnv,
    f: &mut Frame,
    rdr: &Val,
    src: &Val,
    quote: bool,
) -> Result<Scanned, MorelError> {
    let Some((c, rest)) = read(r, f, rdr, src)? else {
        return Ok(Scanned::None);
    };
    if c != '\\' {
        // A printable character stands for itself.
        return Ok(if (' '..='~').contains(&c) && (quote || c != '"') {
            Scanned::Char(c, rest)
        } else {
            Scanned::None
        });
    }
    let Some((e, after)) = read(r, f, rdr, &rest)? else {
        return Ok(Scanned::None);
    };
    let simple = match e {
        'a' => Some('\x07'),
        'b' => Some('\x08'),
        't' => Some('\t'),
        'n' => Some('\n'),
        'v' => Some('\x0B'),
        'f' => Some('\x0C'),
        'r' => Some('\r'),
        '"' => Some('"'),
        '\\' => Some('\\'),
        _ => None,
    };
    if let Some(c) = simple {
        return Ok(Scanned::Char(c, after));
    }
    match e {
        // `\^c` is the control character `c` minus 64.
        '^' => {
            let Some((c, after2)) = read(r, f, rdr, &after)? else {
                return Ok(Scanned::None);
            };
            Ok(if ('@'..='_').contains(&c) {
                Scanned::Char((c as u8 - 64) as char, after2)
            } else {
                Scanned::None
            })
        }
        // `\uxxxx` is four hexadecimal digits.
        'u' => Ok(match code(r, f, rdr, &after, 4, 16)? {
            Some((c, after2)) => Scanned::Char(c, after2),
            None => Scanned::None,
        }),
        // `\ddd` is exactly three decimal digits.
        '0'..='9' => Ok(match code(r, f, rdr, &rest, 3, 10)? {
            Some((c, after2)) => Scanned::Char(c, after2),
            None => Scanned::None,
        }),
        // A formatting sequence: a backslash, whitespace, a backslash.
        ' ' | '\t' | '\n' | '\r' | '\x0B' | '\x0C' => {
            let (_, after2) =
                take_while(r, f, rdr, &after, char::is_whitespace)?;
            Ok(match expect_word(r, f, rdr, &after2, "\\")? {
                Some(after3) => Scanned::Nothing(after3),
                None => Scanned::None,
            })
        }
        _ => Ok(Scanned::None),
    }
}

/// Scans one character constant. A formatting sequence stands for
/// nothing, so the scan goes on with what follows it.
pub(crate) fn char_scan(
    r: &mut EvalEnv,
    f: &mut Frame,
    rdr: &Val,
    src: &Val,
) -> Result<Val, MorelError> {
    let mut s = src.clone();
    loop {
        match scan_char(r, f, rdr, &s, false)? {
            Scanned::Char(c, rest) => return Ok(scanned(Val::Char(c), rest)),
            Scanned::Nothing(rest) => s = rest,
            Scanned::None => return Ok(Val::Unit),
        }
    }
}

/// Scans a run of characters in Standard ML source form, stopping at the
/// first thing that is not one -- a raw non-printable character, or an
/// ill-formed escape -- and returning what it has read so far. Unlike a
/// character constant, a raw double-quote is a character, and the empty
/// stream yields the empty string rather than nothing.
pub(crate) fn string_scan(
    r: &mut EvalEnv,
    f: &mut Frame,
    rdr: &Val,
    src: &Val,
) -> Result<Val, MorelError> {
    let mut out = String::new();
    let mut s = src.clone();
    loop {
        match scan_char(r, f, rdr, &s, true)? {
            Scanned::Char(c, rest) => {
                out.push(c);
                s = rest;
            }
            Scanned::Nothing(rest) => s = rest,
            Scanned::None => break,
        }
    }
    // Nothing read, and something there that could not be read: the
    // stream does not start with a string. (An empty stream does yield
    // the empty string.)
    if out.is_empty() && read(r, f, rdr, &s)?.is_some() {
        return Ok(Val::Unit);
    }
    Ok(scanned(Val::String(out.into()), s))
}

/// Scans a time: a decimal number of seconds, after skipping
/// whitespace. There is no exponent -- `1.5e3` is 1.5 seconds and stops
/// at the `e` -- and either the whole part or the fraction may be
/// missing, but not both, so `1.` and `.` are nothing.
///
/// Morel's `time` counts nanoseconds, so digits beyond a nanosecond are
/// discarded, and a number of seconds too large to count raises `Time`.
pub(crate) fn time_scan(
    r: &mut EvalEnv,
    f: &mut Frame,
    rdr: &Val,
    src: &Val,
    span: &Span,
) -> Result<Val, MorelError> {
    const NANOS: i64 = 1_000_000_000;
    let s = skip_ws(r, f, rdr, src)?;
    let (negative, s) = signed(r, f, rdr, &s, true)?;
    let (whole, s) = take_while(r, f, rdr, &s, |c| c.is_ascii_digit())?;
    let (frac, rest) = match expect_word(r, f, rdr, &s, ".")? {
        Some(after) => {
            let (frac, after2) =
                take_while(r, f, rdr, &after, |c| c.is_ascii_digit())?;
            // A point must have a digit after it: `1.` is not a time.
            if frac.is_empty() {
                return Ok(Val::Unit);
            }
            (frac, after2)
        }
        None => (String::new(), s),
    };
    if whole.is_empty() && frac.is_empty() {
        return Ok(Val::Unit);
    }
    // Nine digits of fraction, truncated or padded with zeros.
    let mut nanos: i64 = frac
        .chars()
        .chain(repeat('0'))
        .take(9)
        .fold(0, |acc, c| acc * 10 + c.to_digit(10).unwrap_or(0) as i64);
    // A number may be all fraction: `.5` is half a second.
    let seconds = if whole.is_empty() {
        Some(0)
    } else {
        whole.parse::<i64>().ok()
    };
    let total = seconds
        .and_then(|s| s.checked_mul(NANOS))
        .and_then(|s| s.checked_add(nanos));
    let Some(total) = total else {
        return Err(MorelError::Runtime(BuiltInExn::Time, span.clone()));
    };
    nanos = if negative { -total } else { total };
    Ok(scanned(Val::Time(nanos), rest))
}

/// Reads exactly `n` digits, and returns their value.
fn fixed_digits(
    r: &mut EvalEnv,
    f: &mut Frame,
    rdr: &Val,
    src: &Val,
    n: usize,
) -> Result<Option<(i32, Val)>, MorelError> {
    let mut value = 0i32;
    let mut s = src.clone();
    for _ in 0..n {
        let Some((c, rest)) = read(r, f, rdr, &s)? else {
            return Ok(None);
        };
        let Some(d) = c.to_digit(10) else {
            return Ok(None);
        };
        value = value * 10 + d as i32;
        s = rest;
    }
    Ok(Some((value, s)))
}

/// Reads a word of `n` letters, and returns its position in `words`.
fn word_of(
    r: &mut EvalEnv,
    f: &mut Frame,
    rdr: &Val,
    src: &Val,
    words: &[&str],
) -> Result<Option<(usize, Val)>, MorelError> {
    let mut text = String::new();
    let mut s = src.clone();
    for _ in 0..3 {
        let Some((c, rest)) = read(r, f, rdr, &s)? else {
            return Ok(None);
        };
        text.push(c);
        s = rest;
    }
    Ok(words.iter().position(|w| *w == text).map(|i| (i, s)))
}

/// Scans a date in the form `Date.toString` writes -- `Wed Mar 08
/// 19:06:45 2023` -- which is what SML/NJ documents. Whitespace is not
/// skipped: a space is part of the form, and the day may be written
/// with a leading space instead of a leading zero. The weekday is read
/// but not checked against the date.
pub(crate) fn date_scan(
    r: &mut EvalEnv,
    f: &mut Frame,
    rdr: &Val,
    src: &Val,
) -> Result<Val, MorelError> {
    const DAYS: [&str; 7] = ["Sun", "Mon", "Tue", "Wed", "Thu", "Fri", "Sat"];
    const MONTHS: [&str; 12] = [
        "Jan", "Feb", "Mar", "Apr", "May", "Jun", "Jul", "Aug", "Sep", "Oct",
        "Nov", "Dec",
    ];
    let Some((_, s)) = word_of(r, f, rdr, src, &DAYS)? else {
        return Ok(Val::Unit);
    };
    let Some(s) = expect_word(r, f, rdr, &s, " ")? else {
        return Ok(Val::Unit);
    };
    let Some((month, s)) = word_of(r, f, rdr, &s, &MONTHS)? else {
        return Ok(Val::Unit);
    };
    let Some(s) = expect_word(r, f, rdr, &s, " ")? else {
        return Ok(Val::Unit);
    };
    // Two columns for the day: `08`, or ` 8` as `Date.fmt` writes it,
    // in which case the space stands where the leading zero would.
    let (width, s) = match expect_word(r, f, rdr, &s, " ")? {
        Some(after) => (1, after),
        None => (2, s),
    };
    let Some((day, s)) = fixed_digits(r, f, rdr, &s, width)? else {
        return Ok(Val::Unit);
    };
    let Some(s) = expect_word(r, f, rdr, &s, " ")? else {
        return Ok(Val::Unit);
    };
    let Some((hour, s)) = fixed_digits(r, f, rdr, &s, 2)? else {
        return Ok(Val::Unit);
    };
    let Some(s) = expect_word(r, f, rdr, &s, ":")? else {
        return Ok(Val::Unit);
    };
    let Some((minute, s)) = fixed_digits(r, f, rdr, &s, 2)? else {
        return Ok(Val::Unit);
    };
    let Some(s) = expect_word(r, f, rdr, &s, ":")? else {
        return Ok(Val::Unit);
    };
    let Some((second, s)) = fixed_digits(r, f, rdr, &s, 2)? else {
        return Ok(Val::Unit);
    };
    let Some(s) = expect_word(r, f, rdr, &s, " ")? else {
        return Ok(Val::Unit);
    };
    // The year is as many digits as there are, not four: a date may
    // fall outside four digits.
    let (year, rest) = take_while(r, f, rdr, &s, |c| c.is_ascii_digit())?;
    let Ok(year) = year.parse::<i32>() else {
        return Ok(Val::Unit);
    };
    match date_of(year, month as u32 + 1, day, hour, minute, second) {
        Some(date) => Ok(scanned(date, rest)),
        None => Ok(Val::Unit),
    }
}
