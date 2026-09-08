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
//! The scanner splits the input into spans, each carrying the [`Class`]
//! that morel-java's `MorelHighlighter` gives it — a Rouge CSS class,
//! finer than the [`Category`] the shell colors by, because it tells a
//! name being bound from one being used and punctuation from operators.
//! [`highlight`] maps those classes down to categories and wraps each
//! span in ANSI escapes; [`highlight_concise`] writes them in the format
//! `Test.highlight` returns, which `script/highlight.smli` asserts.
//!
//! The scanner is lenient and never fails, whatever it is given: the
//! shell re-highlights the buffer on every keystroke, so most of what it
//! sees is a partly typed line that is not valid Morel.

use crate::eval::color_scheme::{Category, ColorScheme};

/// Identifiers that the shell colors as constants rather than plain
/// identifiers. The scanner does not single them out — morel-java gives
/// them the plain-name class — so this applies only on the way to a
/// [`Category`].
const CONSTANTS: &[&str] = &["false", "nil", "true"];

/// Standard ML reserved words that Morel implements. Every one of
/// these is a keyword of the Morel grammar.
pub(crate) const SML_KEYWORDS: &[&str] = &[
    // lint: sort until '];'
    "and",
    "andalso",
    "as",
    "case",
    "datatype",
    "div",
    "else",
    "end",
    "eqtype",
    "exception",
    "fn",
    "fun",
    "if",
    "in",
    "let",
    "mod",
    "of",
    "op",
    "orelse",
    "raise",
    "rec",
    "sig",
    "signature",
    "then",
    "type",
    "val",
    "where",
    "with",
];

/// Standard ML reserved words that Morel does not implement. They are
/// highlighted so that Standard ML code, which a Morel document may
/// quote, reads correctly; the Morel parser knows none of them.
pub(crate) const UNIMPLEMENTED_SML_KEYWORDS: &[&str] = &[
    // lint: sort until '];'
    "abstype",
    "do",
    "handle",
    "infix",
    "infixr",
    "local",
    "nonfix",
    "open",
    "sharing",
    "struct",
    "structure",
    "while",
    "withtype",
];

/// Morel's own keywords. Deliberately its own set rather than the
/// parser's `RESERVED_WORDS`: it also holds the words the parser treats
/// contextually (`all`, `lenient`, `or`), which are keywords only where
/// a record modifier expects them.
pub(crate) const MOREL_KEYWORDS: &[&str] = &[
    // lint: sort until '];'
    "all",
    "asOpt",
    "check",
    "compute",
    "current",
    "distinct",
    "elem",
    "elements",
    "except",
    "exists",
    "extend",
    "forall",
    "from",
    "full",
    "group",
    "implies",
    "inst",
    "intersect",
    "into",
    "join",
    "left",
    "lenient",
    "notelem",
    "o",
    "on",
    "or",
    "order",
    "ordinal",
    "over",
    "remove",
    "rename",
    "replace",
    "require",
    "right",
    "skip",
    "take",
    "through",
    "type_string",
    "typeof",
    "union",
    "unorder",
    "yield",
    "yieldAll",
];

/// Words that the parser treats as ordinary identifiers but that are
/// highlighted as keywords all the same. `not` is a function, `bool ->
/// bool`, but it reads as an operator and is colored like one.
pub(crate) const PSEUDO_KEYWORDS: &[&str] = &["not"];

/// Whether the highlighter colors `word` as a keyword: the union of
/// [`SML_KEYWORDS`], [`UNIMPLEMENTED_SML_KEYWORDS`], [`MOREL_KEYWORDS`]
/// and [`PSEUDO_KEYWORDS`].
fn is_keyword(word: &str) -> bool {
    [
        SML_KEYWORDS,
        UNIMPLEMENTED_SML_KEYWORDS,
        MOREL_KEYWORDS,
        PSEUDO_KEYWORDS,
    ]
    .iter()
    .any(|words| words.binary_search(&word).is_ok())
}

/// Characters that group into a single punctuation token.
const PUNCT_CHARS: &str = "()[]{}=,;|.";

/// What a token is, named after the Rouge CSS class morel-java's
/// highlighter emits for it.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum Class {
    /// Reserved word.
    Kr,
    /// String literal.
    S2,
    /// The `(*` that opens a comment.
    C,
    /// The rest of a comment, through its `*)`.
    Cm,
    /// Type variable, or a structure name before a `.`.
    Nn,
    /// Numeric literal.
    Mi,
    /// Operator.
    O,
    /// Name bound by `val`, or by a `from` generator.
    Nv,
    /// Name bound by `fun`.
    Nf,
    /// Plain identifier.
    N,
    /// Punctuation.
    P,
    /// Whitespace, which carries no class.
    Plain,
}

impl Class {
    /// The CSS class name, or `None` for text written verbatim.
    fn name(self) -> Option<&'static str> {
        match self {
            Class::Kr => Some("kr"),
            Class::S2 => Some("s2"),
            Class::C => Some("c"),
            Class::Cm => Some("cm"),
            Class::Nn => Some("nn"),
            Class::Mi => Some("mi"),
            Class::O => Some("o"),
            Class::Nv => Some("nv"),
            Class::Nf => Some("nf"),
            Class::N => Some("n"),
            Class::P => Some("p"),
            Class::Plain => None,
        }
    }

    /// The category the shell colors this token by. `text` is the token,
    /// needed only to spot a constant among the plain names.
    fn category(self, text: &str) -> Option<Category> {
        match self {
            Class::Kr => Some(Category::Keyword),
            Class::S2 => Some(Category::String),
            Class::C | Class::Cm => Some(Category::Comment),
            Class::Nn => Some(Category::TypeVar),
            Class::Mi => Some(Category::Numeric),
            Class::O | Class::P => Some(Category::Symbol),
            Class::Nv | Class::Nf | Class::N => {
                if CONSTANTS.contains(&text) {
                    Some(Category::Constant)
                } else {
                    Some(Category::Identifier)
                }
            }
            Class::Plain => None,
        }
    }
}

/// Highlights a line of Morel input, returning it with ANSI escape
/// sequences applied per `scheme`. Spans whose category has no style (and
/// everything under the `none` scheme) are left unchanged. Adjacent spans
/// of one category are wrapped together, so a comment does not accumulate
/// an escape sequence per token.
pub fn highlight(line: &str, scheme: &ColorScheme) -> String {
    let mut out = String::new();
    let mut run: Option<(usize, usize, Option<Category>)> = None;
    let flush = |run: Option<(usize, usize, Option<Category>)>,
                 out: &mut String| {
        let Some((start, end, category)) = run else {
            return;
        };
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
    };
    for (start, end, class) in tokenize(line) {
        let category = class.category(&line[start..end]);
        match run {
            Some((s, e, c)) if c == category && e == start => {
                run = Some((s, end, c));
            }
            other => {
                flush(other, &mut out);
                run = Some((start, end, category));
            }
        }
    }
    flush(run, &mut out);
    out
}

/// Writes each token as its CSS class followed by the token's text in
/// braces — `val x = 1` becomes `kr{val} nv{x} p{=} mi{1}`. Whitespace is
/// written verbatim. This is what `Test.highlight` returns.
pub fn highlight_concise(s: &str) -> String {
    let mut out = String::new();
    for (start, end, class) in tokenize(s) {
        match class.name() {
            Some(name) => {
                out.push_str(name);
                out.push('{');
                out.push_str(&s[start..end]);
                out.push('}');
            }
            None => out.push_str(&s[start..end]),
        }
    }
    out
}

/// Tells an identifier that is being bound from one that is being used.
/// Carried across tokens by [`tokenize`].
#[derive(Default)]
struct Context {
    /// Whether the previous keyword was `fun`, so that the next name is
    /// the name of the function being declared.
    awaiting_fun_name: bool,

    /// `None` outside a `val` pattern; otherwise the bracket depth within
    /// it. Every identifier in a `val` pattern is being bound. The
    /// pattern ends at an `=` at depth 0.
    val_pat_depth: Option<u32>,

    /// Where we are in a `from`: a generator pattern, where identifiers
    /// are being bound, or the expression after the generator's `in`.
    from_state: FromState,

    /// Bracket depth within a generator expression, so that only a
    /// top-level `,` starts another generator.
    from_depth: u32,
}

/// Where [`Context`] is within a `from`.
#[derive(Copy, Clone, Eq, PartialEq, Default)]
enum FromState {
    /// Not in a `from`.
    #[default]
    None,
    /// In a generator pattern; identifiers are being bound.
    Pat,
    /// In the expression after a generator's `in`.
    Expr,
}

impl Context {
    /// Notes that `word`, a keyword, has been scanned.
    fn keyword(&mut self, word: &str) {
        self.awaiting_fun_name = false;
        match word {
            "val" => {
                self.val_pat_depth = Some(0);
                self.from_state = FromState::None;
            }
            "fun" => {
                self.awaiting_fun_name = true;
                self.val_pat_depth = None;
                self.from_state = FromState::None;
            }
            "from" => {
                self.from_state = FromState::Pat;
                self.from_depth = 0;
                self.val_pat_depth = None;
            }
            // `in` after a from-pattern: switch to expression mode.
            "in" if self.from_state == FromState::Pat => {
                self.from_state = FromState::Expr;
                self.from_depth = 0;
            }
            // `join` introduces another generator pattern.
            "join" if self.from_state == FromState::Expr => {
                self.from_state = FromState::Pat;
            }
            // End of the generator list; no more patterns expected.
            "where" | "yield" | "group" | "order"
                if self.from_state == FromState::Pat
                    || self.from_state == FromState::Expr
                        && self.from_depth == 0 =>
            {
                self.from_state = FromState::None;
            }
            _ => {}
        }
    }

    /// Notes that a run of punctuation has been scanned. Tracks bracket
    /// depth; a `,` in a generator expression starts another generator,
    /// and an `=` at depth 0 ends a `val` pattern. Being in a `val`
    /// pattern and being in a generator expression are mutually
    /// exclusive, because `from` clears the former.
    fn punct(&mut self, text: &str) {
        if self.val_pat_depth.is_none() && self.from_state != FromState::Expr {
            return;
        }
        for p in text.chars() {
            match p {
                '(' | '[' | '{' => match self.val_pat_depth {
                    Some(d) => self.val_pat_depth = Some(d + 1),
                    None => self.from_depth += 1,
                },
                ')' | ']' | '}' => match self.val_pat_depth {
                    Some(d) if d > 0 => self.val_pat_depth = Some(d - 1),
                    _ if self.from_depth > 0 => self.from_depth -= 1,
                    _ => {}
                },
                ',' if self.from_state == FromState::Expr
                    && self.from_depth == 0 =>
                {
                    self.from_state = FromState::Pat;
                }
                '=' if self.val_pat_depth == Some(0) => {
                    self.val_pat_depth = None;
                }
                _ => {}
            }
        }
    }
}

/// Splits `s` into contiguous spans, each tagged with the [`Class`] of the
/// token it holds. Spans cover the whole input, in order.
fn tokenize(s: &str) -> Vec<(usize, usize, Class)> {
    let b = s.as_bytes();
    let n = b.len();
    let mut spans = Vec::new();
    let mut cx = Context::default();
    let mut i = 0;
    while i < n {
        let c = b[i] as char;
        if c == '(' && i + 1 < n && b[i + 1] == b'*' {
            // Comment: the `(*` and the rest of it are separate tokens,
            // as Rouge writes them.
            let end = scan_comment(b, i);
            spans.push((i, i + 2, Class::C));
            if i + 2 < end {
                spans.push((i + 2, end, Class::Cm));
            }
            i = end;
        } else if c == '"' {
            let end = scan_string(b, i);
            spans.push((i, end, Class::S2));
            i = end;
        } else if c == '\'' && i + 1 < n && (b[i + 1] as char).is_alphabetic() {
            // Type variable: 'a, 'b, 'alpha.
            let mut end = i + 1;
            while end < n && is_ident_char(b[end] as char) {
                end += 1;
            }
            spans.push((i, end, Class::Nn));
            i = end;
        } else if c.is_alphabetic() || c == '_' || c == '`' {
            // Identifier, quoted identifier, or keyword.
            let quoted = c == '`';
            let end = if quoted {
                // A quoted identifier such as `from` or `let val` is a
                // single name, whatever it contains; never a keyword.
                scan_quoted_identifier(b, i)
            } else {
                let mut end = i + 1;
                while end < n && is_ident_char(b[end] as char) {
                    end += 1;
                }
                end
            };
            let word = &s[i..end];
            let class = if !quoted && is_keyword(word) {
                cx.keyword(word);
                Class::Kr
            } else if end < n && b[end] == b'.' {
                // A name immediately before `.` is a structure name.
                cx.val_pat_depth = None;
                cx.awaiting_fun_name = false;
                Class::Nn
            } else if cx.val_pat_depth.is_some() {
                Class::Nv
            } else if cx.awaiting_fun_name {
                cx.awaiting_fun_name = false;
                Class::Nf
            } else if cx.from_state == FromState::Pat {
                Class::Nv
            } else {
                Class::N
            };
            spans.push((i, end, class));
            i = end;
        } else if c.is_ascii_digit() {
            // Numeric literal. A leading `~` is a token of its own.
            let end = scan_number(b, i);
            spans.push((i, end, Class::Mi));
            i = end;
        } else if i + 1 < n
            && matches!(
                (c, b[i + 1]),
                (':', b':') | (':', b'=') | ('=', b'>') | ('-', b'>')
            )
        {
            // `::`, `:=`, `=>`, `->`, each ahead of the single character
            // it starts with.
            spans.push((i, i + 2, Class::O));
            i += 2;
        } else if PUNCT_CHARS.contains(c) {
            let mut end = i + 1;
            while end < n && PUNCT_CHARS.contains(b[end] as char) {
                end += 1;
            }
            cx.punct(&s[i..end]);
            spans.push((i, end, Class::P));
            i = end;
        } else if c == ':' {
            // Lone colon: a type annotation.
            spans.push((i, i + 1, Class::P));
            i += 1;
        } else if c.is_whitespace() {
            let mut end = i + 1;
            while end < n && (b[end] as char).is_whitespace() {
                end += 1;
            }
            spans.push((i, end, Class::Plain));
            i = end;
        } else {
            // An operator, or any other character the scanner does not
            // recognize — `~`, `&`, `\`, a lone `'`.
            spans.push((i, i + 1, Class::O));
            i += 1;
        }
    }
    spans
}

/// Returns the byte index just past the quoted identifier starting at
/// `start`. A doubled backtick is an escaped backtick and does not end
/// the identifier. An unterminated identifier runs to the end of the
/// input: the shell re-highlights the buffer on every keystroke, so a
/// partly typed line is not valid Morel and must still highlight.
fn scan_quoted_identifier(b: &[u8], start: usize) -> usize {
    let n = b.len();
    let mut j = start + 1;
    while j < n {
        if b[j] == b'`' {
            if j + 1 < n && b[j + 1] == b'`' {
                j += 2;
            } else {
                return j + 1;
            }
        } else {
            j += 1;
        }
    }
    n
}

/// Whether `c` can continue an identifier or type variable.
fn is_ident_char(c: char) -> bool {
    c.is_alphanumeric() || c == '_' || c == '\''
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
            // Skip the escape sequence; the guard makes sure that a trailing
            // backslash in an unterminated string does not skip past the end
            // of the buffer.
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
    use crate::syntax::parser::RESERVED_WORDS;
    use std::collections::HashMap;

    /// Categories, in the coarser terms the shell colors by, as
    /// `highlight` groups them.
    fn cats(s: &str) -> Vec<(&str, Option<Category>)> {
        let mut runs: Vec<(usize, usize, Option<Category>)> = Vec::new();
        for (start, end, class) in tokenize(s) {
            let category = class.category(&s[start..end]);
            match runs.last_mut() {
                Some(last) if last.2 == category && last.1 == start => {
                    last.1 = end
                }
                _ => runs.push((start, end, category)),
            }
        }
        runs.into_iter().map(|(a, b, c)| (&s[a..b], c)).collect()
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

    /// The keywords the grammar defines, from its
    /// `_name = @{ "word" ... }` rules, and those its `keywords` rule
    /// makes reserved. A rule's name is not always its word --
    /// `_yieldall` matches `yieldAll` -- so both come from the literal.
    fn grammar_keywords() -> (Vec<String>, Vec<String>) {
        let pest = include_str!("../syntax/morel.pest");
        let mut words: HashMap<&str, &str> = HashMap::new();
        for l in pest.lines() {
            if let Some(rest) = l.strip_prefix('_')
                && let Some((name, rest)) = rest.split_once(" = @{ \"")
                && let Some((word, _)) = rest.split_once('"')
            {
                words.insert(name, word);
            }
        }
        let mut defined: Vec<String> =
            words.values().map(|w| w.to_string()).collect();
        defined.sort();
        let start = pest.find("\nkeywords = {\n").expect("keywords rule");
        let end = pest[start..].find("\n}\n").expect("end of rule") + start;
        let reserved = pest[start..end]
            .lines()
            .filter_map(|l| l.trim().trim_start_matches("| ").strip_prefix('_'))
            .map(|name| words[name].to_string())
            .collect();
        (defined, reserved)
    }

    /// Tests that the highlighter colors exactly the grammar's keywords,
    /// plus the two categories of word that are deliberately not
    /// keywords of it.
    ///
    /// A keyword the parser knows and the highlighter does not is a bug
    /// -- the word is a keyword on the screen and back-ticked on output,
    /// yet displayed as an identifier. The converse is a bug too, and a
    /// quieter one: `desc` sat in the Morel list long after the language
    /// stopped having it, coloring a name no program can use.
    ///
    /// So the comparison is by equality. The words the highlighter
    /// colors that the grammar does not know are accounted for by
    /// category -- Standard ML keywords Morel does not implement, and
    /// identifiers colored as keywords anyway -- and the categories are
    /// disjoint, so every word belongs to exactly one and none can hide.
    #[test]
    fn test_keywords_match_grammar() {
        // `all`, `lenient` and `or` are keywords only where a record
        // modifier expects them, and no identifier can occur; everywhere
        // else they are ordinary identifiers, and need no back-ticks.
        const NON_RESERVED: &[&str] = &["all", "lenient", "or"];
        let (defined, reserved) = grammar_keywords();
        assert_eq!(
            reserved, RESERVED_WORDS,
            "the grammar's `keywords` rule and RESERVED_WORDS disagree"
        );
        let mut extra: Vec<&String> =
            defined.iter().filter(|k| !reserved.contains(k)).collect();
        extra.sort();
        assert_eq!(
            extra, NON_RESERVED,
            "a keyword the grammar defines is neither reserved nor one of \
             the three that are keywords only in a record modifier"
        );
        // The categories partition the words the highlighter colors:
        // their union is every such word, and no word is in two of them.
        let mut all: Vec<&str> = SML_KEYWORDS
            .iter()
            .chain(UNIMPLEMENTED_SML_KEYWORDS)
            .chain(MOREL_KEYWORDS)
            .chain(PSEUDO_KEYWORDS)
            .copied()
            .collect();
        all.sort_unstable();
        let shared: Vec<&str> = all
            .windows(2)
            .filter(|w| w[0] == w[1])
            .map(|w| w[0])
            .collect();
        assert!(shared.is_empty(), "a word in two categories: {:?}", shared);
        // The words left when the two non-grammar categories are removed
        // are the grammar's keywords, exactly.
        let mut highlighted: Vec<&str> =
            SML_KEYWORDS.iter().chain(MOREL_KEYWORDS).copied().collect();
        highlighted.sort_unstable();
        let defined: Vec<&str> = defined.iter().map(String::as_str).collect();
        assert_eq!(
            highlighted, defined,
            "the highlighter and the grammar disagree about keywords"
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
