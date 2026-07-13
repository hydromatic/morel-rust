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

//! Syntax highlighting for a line of Morel typed at the shell prompt.
//!
//! [`highlight`] tokenizes the input and wraps each token in ANSI escapes
//! according to a [`ColorScheme`]. The tokenizer classifies each span into a
//! [`Category`] — keyword, symbol, numeric, string, comment, type variable,
//! constant, or (the default, unstyled) identifier — a simplification of
//! Morel-Java's `MorelHighlighter`, which additionally distinguishes bound
//! variables and function names that all render unstyled here anyway.

use crate::eval::color_scheme::{Category, ColorScheme};
use crate::syntax::parser::is_reserved_word;

/// Identifiers that are highlighted as constants rather than plain
/// identifiers.
const CONSTANTS: &[&str] = &["false", "nil", "true"];

/// Highlights a line of Morel input, returning it with ANSI escape sequences
/// applied per `scheme`. Spans whose category has no style (and everything
/// under the `none` scheme) are left unchanged.
pub fn highlight(line: &str, scheme: &ColorScheme) -> String {
    let mut out = String::new();
    for (start, end, category) in tokenize(line) {
        let text = &line[start..end];
        let spec = category.map_or("", |c| scheme.spec(c));
        let prefix = ansi_prefix(spec);
        if prefix.is_empty() {
            out.push_str(text);
        } else {
            out.push_str(&prefix);
            out.push_str(text);
            out.push_str("\x1b[0m");
        }
    }
    out
}

/// Splits `s` into contiguous spans, each tagged with a [`Category`] or
/// `None` (whitespace and other unstyled text). Spans cover the whole input
/// in order.
fn tokenize(s: &str) -> Vec<(usize, usize, Option<Category>)> {
    let b = s.as_bytes();
    let n = b.len();
    let mut spans = Vec::new();
    let mut i = 0;
    while i < n {
        let c = b[i] as char;
        if c == '(' && i + 1 < n && b[i + 1] == b'*' {
            // Block comment "(* ... *)", possibly nested.
            let end = scan_comment(b, i);
            spans.push((i, end, Some(Category::Comment)));
            i = end;
        } else if c == '"' {
            // String literal.
            let end = scan_string(b, i);
            spans.push((i, end, Some(Category::String)));
            i = end;
        } else if c == '\'' && i + 1 < n && (b[i + 1] as char).is_alphabetic() {
            // Type variable: 'a, 'b, ...
            let mut end = i + 1;
            while end < n && is_ident_char(b[end] as char) {
                end += 1;
            }
            spans.push((i, end, Some(Category::TypeVar)));
            i = end;
        } else if c.is_alphabetic() || c == '_' {
            // Identifier or keyword.
            let mut end = i + 1;
            while end < n && is_ident_char(b[end] as char) {
                end += 1;
            }
            let word = &s[i..end];
            let category = if is_reserved_word(word) {
                Category::Keyword
            } else if end < n && b[end] == b'.' {
                // A structure name, e.g. `List` in `List.map`.
                Category::TypeVar
            } else if CONSTANTS.contains(&word) {
                Category::Constant
            } else {
                Category::Identifier
            };
            spans.push((i, end, Some(category)));
            i = end;
        } else if c.is_ascii_digit() {
            // Numeric literal: int, word (0w7), real (1.5) or scientific.
            let end = scan_number(b, i);
            spans.push((i, end, Some(Category::Numeric)));
            i = end;
        } else if c.is_whitespace() {
            let mut end = i + 1;
            while end < n && (b[end] as char).is_whitespace() {
                end += 1;
            }
            spans.push((i, end, None));
            i = end;
        } else {
            // A run of symbol/operator characters.
            let mut end = i + 1;
            while end < n && is_symbol_char(b[end] as char) {
                end += 1;
            }
            spans.push((i, end, Some(Category::Symbol)));
            i = end;
        }
    }
    spans
}

/// Whether `c` can continue an identifier or type variable.
fn is_ident_char(c: char) -> bool {
    c.is_alphanumeric() || c == '_' || c == '\''
}

/// Whether `c` is a symbol/operator character (not the start of a comment,
/// string, type variable, word, or number, and not whitespace).
fn is_symbol_char(c: char) -> bool {
    !c.is_alphanumeric()
        && !c.is_whitespace()
        && c != '"'
        && c != '\''
        && c != '_'
}

/// Returns the byte index just past a comment starting at `i`. A `(*)` begins
/// a line comment, which runs to the end of the line; any other `(*` begins a
/// block comment, which may nest and runs to the matching `*)` (or the whole
/// rest of the input if it is unterminated).
fn scan_comment(b: &[u8], start: usize) -> usize {
    let n = b.len();
    // "(*)" is a line comment: it runs to the end of the line.
    if start + 2 < n && b[start + 2] == b')' {
        let mut j = start + 3;
        while j < n && b[j] != b'\n' {
            j += 1;
        }
        return j;
    }
    // Otherwise "(*" is a block comment, which may nest.
    let mut depth = 0;
    let mut j = start;
    while j < n {
        if j + 1 < n && b[j] == b'(' && b[j + 1] == b'*' {
            depth += 1;
            j += 2;
        } else if j + 1 < n && b[j] == b'*' && b[j + 1] == b')' {
            depth -= 1;
            j += 2;
            if depth == 0 {
                return j;
            }
        } else {
            j += 1;
        }
    }
    n
}

/// Returns the byte index just past a `"..."` string starting at `i`
/// (skipping `\`-escapes); the whole rest of the input if it is unterminated.
fn scan_string(b: &[u8], i: usize) -> usize {
    let n = b.len();
    let mut j = i + 1;
    while j < n {
        match b[j] {
            b'\\' if j + 1 < n => j += 2,
            b'"' => return j + 1,
            _ => j += 1,
        }
    }
    n
}

/// Returns the byte index just past a numeric literal starting at `i`:
/// integer, word (`0w7`, `0wx1F`), real (`1.5`) or scientific (`1e~7`).
fn scan_number(b: &[u8], start: usize) -> usize {
    let n = b.len();
    let digit = |k: usize| k < n && b[k].is_ascii_digit();
    let hex = |k: usize| k < n && (b[k] as char).is_ascii_hexdigit();

    // Word literal: 0w<digits> or 0wx<hex>.
    if b[start] == b'0' && start + 1 < n && b[start + 1] == b'w' {
        if start + 2 < n && (b[start + 2] == b'x' || b[start + 2] == b'X') {
            let mut k = start + 3;
            while hex(k) {
                k += 1;
            }
            if k > start + 3 {
                return k;
            }
        } else {
            let mut k = start + 2;
            while digit(k) {
                k += 1;
            }
            if k > start + 2 {
                return k;
            }
        }
    }

    let mut i = start;
    while digit(i) {
        i += 1;
    }
    // Fractional part.
    if i + 1 < n && b[i] == b'.' && digit(i + 1) {
        i += 2;
        while digit(i) {
            i += 1;
        }
    }
    // Exponent: [eE] ~? digits.
    if i < n && (b[i] == b'e' || b[i] == b'E') {
        let mut j = i + 1;
        if j < n && b[j] == b'~' {
            j += 1;
        }
        if digit(j) {
            i = j + 1;
            while digit(i) {
                i += 1;
            }
        }
    }
    i
}

/// Converts a style spec such as `"bold cyan"` or `"italic 245"` into the
/// leading ANSI SGR sequence (e.g. `"\x1b[1;36m"`), or `""` if the spec is
/// empty or unrecognized.
fn ansi_prefix(spec: &str) -> String {
    let mut params: Vec<String> = Vec::new();
    for token in spec.split_whitespace() {
        let attr = match token {
            "bold" => Some("1"),
            "faint" => Some("2"),
            "italic" => Some("3"),
            "underline" => Some("4"),
            "blink" => Some("5"),
            "inverse" => Some("7"),
            "conceal" => Some("8"),
            "crossed-out" => Some("9"),
            _ => None,
        };
        if let Some(a) = attr {
            params.push(a.to_string());
        } else if let Some(code) = color_code(token) {
            params.push(code);
        }
    }
    if params.is_empty() {
        String::new()
    } else {
        format!("\x1b[{}m", params.join(";"))
    }
}

/// The ANSI foreground parameter(s) for a color token: an ANSI color name, a
/// 0–255 palette index (`38;5;N`), or `#rrggbb` (`38;2;r;g;b`).
fn color_code(token: &str) -> Option<String> {
    let base = match token {
        "black" => 30,
        "red" => 31,
        "green" => 32,
        "yellow" => 33,
        "blue" => 34,
        "magenta" => 35,
        "cyan" => 36,
        "white" => 37,
        "bright-black" => 90,
        "bright-red" => 91,
        "bright-green" => 92,
        "bright-yellow" => 93,
        "bright-blue" => 94,
        "bright-magenta" => 95,
        "bright-cyan" => 96,
        "bright-white" => 97,
        _ => -1,
    };
    if base >= 0 {
        return Some(base.to_string());
    }
    if let Some(hex) = token.strip_prefix('#')
        && hex.len() == 6
        && let (Ok(r), Ok(g), Ok(b)) = (
            u8::from_str_radix(&hex[0..2], 16),
            u8::from_str_radix(&hex[2..4], 16),
            u8::from_str_radix(&hex[4..6], 16),
        )
    {
        return Some(format!("38;2;{};{};{}", r, g, b));
    }
    if let Ok(idx) = token.parse::<u8>() {
        return Some(format!("38;5;{}", idx));
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::eval::color_scheme::{DARK, NONE};

    fn cats(s: &str) -> Vec<(&str, Option<Category>)> {
        tokenize(s)
            .into_iter()
            .map(|(a, b, c)| (&s[a..b], c))
            .collect()
    }

    #[test]
    fn test_tokenize_categories() {
        assert_eq!(
            cats("val x = 1;"),
            vec![
                ("val", Some(Category::Keyword)),
                (" ", None),
                ("x", Some(Category::Identifier)),
                (" ", None),
                ("=", Some(Category::Symbol)),
                (" ", None),
                ("1", Some(Category::Numeric)),
                (";", Some(Category::Symbol)),
            ]
        );
    }

    #[test]
    fn test_tokenize_string_comment_tyvar_struct() {
        assert_eq!(
            cats(r#""hi" (* c *) 'a List.map"#),
            vec![
                (r#""hi""#, Some(Category::String)),
                (" ", None),
                ("(* c *)", Some(Category::Comment)),
                (" ", None),
                ("'a", Some(Category::TypeVar)),
                (" ", None),
                ("List", Some(Category::TypeVar)), // structure name
                (".", Some(Category::Symbol)),
                ("map", Some(Category::Identifier)),
            ]
        );
    }

    #[test]
    fn test_line_comment_ends_at_newline() {
        // "(*)" is a line comment: it ends at the newline, so the code on the
        // next line is not swallowed as a comment.
        assert_eq!(
            cats("b (*) flour,\nc"),
            vec![
                ("b", Some(Category::Identifier)),
                (" ", None),
                ("(*) flour,", Some(Category::Comment)),
                ("\n", None),
                ("c", Some(Category::Identifier)),
            ]
        );
        // A "(* ... *)" block comment still spans to its close.
        assert_eq!(
            cats("(* a\nb *) c"),
            vec![
                ("(* a\nb *)", Some(Category::Comment)),
                (" ", None),
                ("c", Some(Category::Identifier)),
            ]
        );
    }

    #[test]
    fn test_numbers_and_constants() {
        assert_eq!(cats("0w7")[0], ("0w7", Some(Category::Numeric)));
        assert_eq!(cats("1.5e~3")[0], ("1.5e~3", Some(Category::Numeric)));
        assert_eq!(cats("0wx1F")[0], ("0wx1F", Some(Category::Numeric)));
        assert_eq!(cats("true")[0], ("true", Some(Category::Constant)));
    }

    #[test]
    fn test_ansi_prefix() {
        assert_eq!(ansi_prefix("bold cyan"), "\x1b[1;36m");
        assert_eq!(ansi_prefix("italic 245"), "\x1b[3;38;5;245m");
        assert_eq!(ansi_prefix("underline red"), "\x1b[4;31m");
        assert_eq!(ansi_prefix("green"), "\x1b[32m");
        assert_eq!(ansi_prefix("italic bright-black"), "\x1b[3;90m");
        assert_eq!(ansi_prefix("#ff8800"), "\x1b[38;2;255;136;0m");
        assert_eq!(ansi_prefix(""), "");
    }

    #[test]
    fn test_highlight_line_comment_then_code() {
        // After a "(*)" line comment and a newline, the next line's keyword is
        // highlighted normally, not swallowed as part of the comment.
        let out = highlight("(*) c\nval", &DARK);
        assert!(out.contains("\x1b[3;38;5;245m(*) c\x1b[0m"));
        assert!(out.contains("\x1b[1;36mval\x1b[0m"));
    }

    #[test]
    fn test_highlight_none_is_unchanged() {
        // The `none` scheme applies no styling.
        assert_eq!(highlight("val x = 1;", &NONE), "val x = 1;");
    }

    #[test]
    fn test_highlight_dark_styles_keyword() {
        // A keyword gets the dark scheme's "bold cyan" and a reset.
        let out = highlight("val x", &DARK);
        assert!(out.starts_with("\x1b[1;36mval\x1b[0m"));
        // The plain identifier `x` is left unstyled.
        assert!(out.ends_with(" x"));
    }
}
