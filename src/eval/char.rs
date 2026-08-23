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
use crate::eval::val::Val;
use crate::shell::kernel::MorelError;

/// Support for the `char` primitive type and the `Char` structure.
pub struct Char;

impl Char {
    // lint: sort until '#}' where '##pub'

    // Constants
    pub(crate) const MAX_CHAR: char = '\u{00FF}';
    pub(crate) const MAX_ORD: i32 = 255;
    pub(crate) const MIN_CHAR: char = '\u{0000}';

    /// How many characters the C escape sequence at the head of `s`
    /// occupies. `from_c_string` reads that sequence; this says how far
    /// to advance to read the next one.
    pub(crate) fn c_escape_len(s: &str) -> usize {
        let b = s.as_bytes();
        if b.is_empty() {
            return 0;
        }
        if b[0] != b'\\' {
            return 1;
        }
        if b.len() < 2 {
            return 1;
        }
        if b[1].is_ascii_digit() && b[1] < b'8' {
            return (2..b.len().min(4))
                .take_while(|&i| b[i].is_ascii_digit() && b[i] < b'8')
                .last()
                .map_or(2, |i| i + 1);
        }
        if b[1] == b'x' {
            return (2..b.len())
                .take_while(|&i| b[i].is_ascii_hexdigit())
                .last()
                .map_or(2, |i| i + 1);
        }
        2
    }

    /// Implements Morel `Char.chr i`. May throw [BuiltInExn::Chr].
    pub(crate) fn chr(i: i32, span: &Span) -> Result<Val, MorelError> {
        if !(0..=Self::MAX_ORD).contains(&i) {
            Err(MorelError::Runtime(BuiltInExn::Chr, span.clone()))
        } else {
            Ok(Val::Char(i as u8 as char))
        }
    }

    /// Computes the Morel expression `Char.compare (c1, c2)`.
    ///
    /// Returns `LESS`, `EQUAL`, or `GREATER` according to whether its first
    /// argument is less than, equal to, or greater than the second.
    pub(crate) fn compare(c1: char, c2: char) -> Order {
        Order(c1.cmp(&c2))
    }

    /// Computes the Morel expression `Char.contains s c`.
    ///
    /// Returns true if the character `c` occurs in the string `s`; false
    /// otherwise.
    pub(crate) fn contains(s: &str, c: char) -> bool {
        s.contains(c)
    }

    /// Computes the Morel expression `Char.fromCString s`.
    ///
    /// Scans a char value from a string, skipping leading whitespace.
    pub(crate) fn from_c_string(s: &str) -> Val {
        let b = s.as_bytes();
        if b.is_empty() {
            return Val::Unit;
        }
        if b[0] != b'\\' {
            // Any printable character stands for itself, a space and a
            // double-quote included; C does not require a quote to be
            // escaped, where Standard ML does. A raw non-printable
            // character is not a constant.
            return if (0x20..0x7F).contains(&b[0]) {
                Val::Some(Box::new(Val::Char(b[0] as char)))
            } else {
                Val::Unit
            };
        }
        if b.len() < 2 {
            return Val::Unit;
        }
        let simple = match b[1] {
            b'a' => Some('\x07'),
            b'b' => Some('\x08'),
            b'f' => Some('\x0C'),
            b'n' => Some('\n'),
            b'r' => Some('\r'),
            b't' => Some('\t'),
            b'v' => Some('\x0B'),
            b'\\' => Some('\\'),
            b'"' => Some('"'),
            b'\'' => Some('\''),
            // C escapes a question mark, where Standard ML has no such
            // escape.
            b'?' => Some('?'),
            _ => None,
        };
        if let Some(c) = simple {
            return Val::Some(Box::new(Val::Char(c)));
        }
        // One to three octal digits, stopping at the first character
        // that is not one -- so "\778" is "\77" followed by "8".
        if b[1].is_ascii_digit() && b[1] < b'8' {
            let end = (2..b.len().min(4))
                .take_while(|&i| b[i].is_ascii_digit() && b[i] < b'8')
                .last()
                .map_or(2, |i| i + 1);
            return Self::code(&s[1..end], 8);
        }
        // "x" and as many hexadecimal digits as follow it; there must
        // be at least one.
        if b[1] == b'x' {
            let end = (2..b.len())
                .take_while(|&i| b[i].is_ascii_hexdigit())
                .last()
                .map_or(2, |i| i + 1);
            if end == 2 {
                return Val::Unit;
            }
            return Self::code(&s[2..end], 16);
        }
        Val::Unit
    }

    /// The character whose code `digits` gives in `radix`, or `NONE` if
    /// it is above `maxOrd`.
    fn code(digits: &str, radix: u32) -> Val {
        match u32::from_str_radix(digits, radix) {
            Ok(v) if v <= Self::MAX_ORD as u32 => {
                Val::Some(Box::new(Val::Char(v as u8 as char)))
            }
            _ => Val::Unit,
        }
    }

    /// Computes the Morel expression `Char.fromInt i`.
    ///
    /// Converts an `int` into a `char`. Returns SOME(c) if successful,
    /// NONE otherwise.
    pub(crate) fn from_int(i: i32) -> Val {
        if (0..=Self::MAX_ORD).contains(&i) {
            Val::Some(Box::new(Val::Char(i as u8 as char)))
        } else {
            Val::Unit
        }
    }

    /// Computes the Morel expression `Char.fromString s`.
    ///
    /// Attempts to scan a character or ML escape sequence from the string `s`.
    /// Does not skip leading whitespace.
    pub(crate) fn from_string(s: &str) -> Val {
        if s.is_empty() {
            return Val::Unit; // NONE
        }

        let bytes = s.as_bytes();
        // A raw non-printable character is not a character constant:
        // it has to be written as the escape sequence that stands for
        // it. `\009` is three characters, not a tab.
        if bytes[0] != b'\\' && !(0x20..0x7F).contains(&bytes[0]) {
            return Val::Unit;
        }

        // Check for escape sequences.
        if bytes[0] == b'\\' {
            if bytes.len() < 2 {
                return Val::Unit; // NONE - incomplete escape
            }

            return match bytes[1] {
                // Standard escapes
                b'a' => Val::Some(Box::new(Val::Char('\x07'))), // bell
                b'b' => {
                    Val::Some(Box::new(Val::Char('\x08'))) // backspace
                }
                b't' => Val::Some(Box::new(Val::Char('\t'))),
                b'n' => Val::Some(Box::new(Val::Char('\n'))),
                b'v' => {
                    // vertical tab
                    Val::Some(Box::new(Val::Char('\x0B')))
                }
                b'f' => {
                    // form feed
                    Val::Some(Box::new(Val::Char('\x0C')))
                }
                b'r' => Val::Some(Box::new(Val::Char('\r'))),
                b'\\' => Val::Some(Box::new(Val::Char('\\'))),
                b'"' => Val::Some(Box::new(Val::Char('"'))),
                b'^' => {
                    // Control character: \^X where X is A-Z or @ [ \ ] ^ _
                    if bytes.len() < 3 {
                        return Val::Unit; // NONE
                    }
                    let ctrl_char = bytes[2];
                    if (b'@'..=b'_').contains(&ctrl_char) {
                        let code = (ctrl_char - b'@') as char;
                        return Val::Some(Box::new(Val::Char(code)));
                    }
                    Val::Unit // NONE
                }
                // Decimal escape: \ddd where ddd is 0-255
                b'0'..=b'9' => {
                    let mut num = 0;
                    let mut i = 1;
                    while i < bytes.len() && i < 4 && bytes[i].is_ascii_digit()
                    {
                        num = num * 10 + (bytes[i] - b'0') as i32;
                        i += 1;
                    }
                    if num <= 255 {
                        return Val::Some(Box::new(Val::Char(
                            num as u8 as char,
                        )));
                    }
                    Val::Unit // NONE
                }
                _ => Val::Unit, // NONE - unknown escape
            };
        }

        // Regular character
        if let Some(c) = s.chars().next() {
            Val::Some(Box::new(Val::Char(c)))
        } else {
            Val::Unit // NONE
        }
    }

    /// Computes the Morel expression `Char.isAlpha c`.
    ///
    /// Returns true if `c` is a letter (lowercase or uppercase).
    pub(crate) fn is_alpha(c: char) -> bool {
        c.is_ascii_alphabetic()
    }

    /// Computes the Morel expression `Char.isAlphaNum c`.
    ///
    /// Returns true if `c` is alphanumeric (a letter or a decimal digit).
    pub(crate) fn is_alpha_num(c: char) -> bool {
        c.is_ascii_alphanumeric()
    }

    /// Computes the Morel expression `Char.isAscii c`.
    ///
    /// Returns true if 0 ≤ ord c ≤ 127.
    pub(crate) fn is_ascii(c: char) -> bool {
        c.is_ascii()
    }

    /// Computes the Morel expression `Char.isCntrl c`.
    ///
    /// Returns true if `c` is a control character.
    pub(crate) fn is_cntrl(c: char) -> bool {
        c.is_ascii_control()
    }

    /// Computes the Morel expression `Char.isDigit c`.
    ///
    /// Returns true if `c` is a decimal digit (0 to 9).
    pub(crate) fn is_digit(c: char) -> bool {
        c.is_ascii_digit()
    }

    /// Computes the Morel expression `Char.isGraph c`.
    ///
    /// Returns true if `c` is a graphical character (printable and
    /// not whitespace).
    pub(crate) fn is_graph(c: char) -> bool {
        c.is_ascii_graphic()
    }

    /// Computes the Morel expression `Char.isHexDigit c`.
    ///
    /// Returns true if `c` is a hexadecimal digit.
    pub(crate) fn is_hex_digit(c: char) -> bool {
        c.is_ascii_hexdigit()
    }

    /// Computes the Morel expression `Char.isLower c`.
    ///
    /// Returns true if `c` is a lowercase letter (a to z).
    pub(crate) fn is_lower(c: char) -> bool {
        c.is_ascii_lowercase()
    }

    /// Computes the Morel expression `Char.isOctDigit c`.
    ///
    /// Returns true if `c` is an octal digit (0 to 7).
    pub(crate) fn is_oct_digit(c: char) -> bool {
        matches!(c, '0'..='7')
    }

    /// Computes the Morel expression `Char.isPrint c`.
    ///
    /// Returns true if `c` is a printable character (space or visible).
    pub(crate) fn is_print(c: char) -> bool {
        c.is_ascii_graphic() || c == ' '
    }

    /// Computes the Morel expression `Char.isPunct c`.
    ///
    /// Returns true if `c` is a punctuation character (graphical but
    /// not alphanumeric).
    pub(crate) fn is_punct(c: char) -> bool {
        c.is_ascii_punctuation()
    }

    /// Computes the Morel expression `Char.isSpace c`.
    ///
    /// Returns true if `c` is a whitespace character.
    pub(crate) fn is_space(c: char) -> bool {
        matches!(c, ' ' | '\t' | '\n' | '\x0b' | '\x0c' | '\r')
    }

    /// Computes the Morel expression `Char.isUpper c`.
    ///
    /// Returns true if `c` is an uppercase letter (A to Z).
    pub(crate) fn is_upper(c: char) -> bool {
        c.is_ascii_uppercase()
    }

    /// Computes the Morel expression `Char.notContains s c`.
    ///
    /// Returns true if the character `c` does not occur in the string `s`;
    /// false otherwise.
    pub(crate) fn not_contains(s: &str, c: char) -> bool {
        !s.contains(c)
    }

    /// Computes the Morel expression `Char.ord c`.
    ///
    /// Returns the code of character `c`.
    pub(crate) fn ord(c: char) -> i32 {
        c as i32
    }

    /// Computes the Morel expression `Char.pred c`.
    /// May throw [BuiltInExn::Chr].
    ///
    /// Returns the predecessor of `c`.
    pub(crate) fn pred(c: char, span: &Span) -> Result<Val, MorelError> {
        if c == Self::MIN_CHAR {
            Err(MorelError::Runtime(BuiltInExn::Chr, span.clone()))
        } else {
            let code = (c as u8) - 1;
            Ok(Val::Char(code as char))
        }
    }

    /// Computes the Morel expression `Char.succ c`.
    /// May throw [BuiltInExn::Chr].
    ///
    /// Returns the character immediately following `c`.
    pub(crate) fn succ(c: char, span: &Span) -> Result<Val, MorelError> {
        if c == Self::MAX_CHAR {
            Err(MorelError::Runtime(BuiltInExn::Chr, span.clone()))
        } else {
            let code = (c as u8) + 1;
            Ok(Val::Char(code as char))
        }
    }

    /// Computes the Morel expression `Char.toCString c`.
    ///
    /// Converts a char into a string using C-style escapes
    /// (octal for non-printable).
    #[allow(clippy::wrong_self_convention)]
    pub(crate) fn to_c_string(c: char) -> String {
        let code = c as u8;
        match c {
            '\x07' => "\\a".to_string(),
            '\x08' => "\\b".to_string(),
            '\t' => "\\t".to_string(),
            '\n' => "\\n".to_string(),
            '\x0B' => "\\v".to_string(),
            '\x0C' => "\\f".to_string(),
            '\r' => "\\r".to_string(),
            '\\' => "\\\\".to_string(),
            '"' => "\\\"".to_string(),
            '\'' => "\\'".to_string(),
            '?' => "\\?".to_string(),
            _ if code < 32 => format!("\\{:03o}", code),
            _ if code >= 127 => {
                // Use octal escape for codes 127-255
                format!("\\{:03o}", code)
            }
            _ => c.to_string(), // Printable character
        }
    }

    /// Computes the Morel expression `Char.toLower c`.
    ///
    /// Returns the lowercase letter corresponding to `c` if `c` is a letter
    /// (a to z or A to Z); otherwise returns `c`.
    #[allow(clippy::wrong_self_convention)]
    pub(crate) fn to_lower(c: char) -> char {
        c.to_lowercase().next().unwrap_or(c)
    }

    /// Computes the Morel expression `Char.toString c`.
    ///
    /// Converts a character to how it appears in a character literal.
    ///
    /// For example, 'a' becomes "#\"a\"" and therefore returns "a".
    /// Character 0 becomes "\\^@". Character 255 becomes "\\255".
    /// Character 9 becomes "\\t".
    #[allow(clippy::wrong_self_convention)]
    pub(crate) fn to_string(c: char) -> String {
        let code = c as u8;
        match c {
            '\x07' => "\\a".to_string(), // alert/bell
            '\x08' => "\\b".to_string(), // backspace
            '\t' => "\\t".to_string(),   // tab (9)
            '\n' => "\\n".to_string(),   // newline (10)
            '\x0B' => "\\v".to_string(), // vertical tab (11)
            '\x0C' => "\\f".to_string(), // form feed (12)
            '\r' => "\\r".to_string(),   // carriage return (13)
            '"' => "\\\"".to_string(),   // double quote (34)
            '\\' => "\\\\".to_string(),  // backslash (92)
            _ if code < 32 => {
                // chr(0) = "\^@", chr(1) = "\^A", ..., chr(31) = "\^_"
                format!("\\^{}", (code + 64) as char)
            }
            _ if code >= 127 => {
                // Use decimal notation for codes 127-255
                format!("\\{}", code)
            }
            _ => c.to_string(),
        }
    }

    /// Computes the Morel expression `Char.toUpper c`.
    ///
    /// Returns the uppercase letter corresponding to `c` if `c` is a letter
    /// (a to z or A to Z); otherwise returns `c`.
    #[allow(clippy::wrong_self_convention)]
    pub(crate) fn to_upper(c: char) -> char {
        c.to_uppercase().next().unwrap_or(c)
    }
}
