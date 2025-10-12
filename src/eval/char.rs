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

/// Support for the `char` primitive type and the `Char` structure.
pub struct Char;

impl Char {
    // lint: sort until '#}' where '##pub'

    // Constants
    pub(crate) const MAX_CHAR: char = '\u{00FF}';
    pub(crate) const MAX_ORD: i32 = 255;
    pub(crate) const MIN_CHAR: char = '\u{0000}';

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
        let trimmed = s.trim_start();
        Self::from_string(trimmed)
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
        c.is_alphabetic()
    }

    /// Computes the Morel expression `Char.isAlphaNum c`.
    ///
    /// Returns true if `c` is alphanumeric (a letter or a decimal digit).
    pub(crate) fn is_alpha_num(c: char) -> bool {
        c.is_alphanumeric()
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
        c.is_control()
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
        !c.is_whitespace() && !c.is_control()
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
        c.is_lowercase()
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
        !c.is_control()
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
        c.is_whitespace()
    }

    /// Computes the Morel expression `Char.isUpper c`.
    ///
    /// Returns true if `c` is an uppercase letter (A to Z).
    pub(crate) fn is_upper(c: char) -> bool {
        c.is_uppercase()
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
            _ if code < 32 => {
                // Control characters: use \^X notation for codes 0-31
                format!("\\^{}", (b'@' + code) as char)
            }
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
