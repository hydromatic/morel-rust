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

//! Splitting a stream of input lines into complete Morel statements.
//!
//! Every front end — the interactive shell, piped stdin, `.smli`
//! scripts, and `use`-file execution — buffers input lines until they
//! form a complete statement (one that ends with `;` and is not inside
//! a comment). This module holds that shared logic so there is a single
//! implementation, rather than a copy per caller.

use crate::syntax::parser::{StatementPrefix, statement_prefix_end};

/// Returns the level of comment nesting at the end of the string.
///
/// Examples:
/// * Depth 0: `(* comment *)`
/// * Depth 1: `(* comment (* nested *)`
/// * Depth 1: `(*) line comment`
/// * Depth 0: `(*) line comment\n`
/// * Depth -1: `code; *)`
/// * Depth 0: `"(*)" ^ "(*)"`  (parentheses inside strings are not comments)
pub(crate) fn comment_depth(code: &str) -> i32 {
    let mut depth = 0;
    let mut buf = [' '; 3]; // cyclic buffer
    let n = 3;
    let mut i = n;
    let mut in_line_comment = false;
    let mut in_string = false;
    let mut in_string_escape = false;
    for c in code.chars() {
        if in_string {
            // Inside a string literal: track escape sequences and closing
            // quote; do not interpret comment syntax.
            if in_string_escape {
                in_string_escape = false;
            } else if c == '\\' {
                in_string_escape = true;
            } else if c == '"' {
                in_string = false;
                buf = [' '; 3]; // reset look-back to avoid false positives
            }
            continue;
        }

        // Opening a string literal (only when not inside any comment).
        if c == '"' && depth == 0 && !in_line_comment {
            in_string = true;
            continue;
        }

        if buf[i % n] == '(' && c == '*' && !in_line_comment {
            // We say "(*", which is a block comment.
            // (It may turn out to be "(*)", a line comment.)
            depth += 1;
        } else if buf[i % n] == '*' && c == ')' {
            if buf[(i - 1) % n] == '(' {
                // We saw "(*)", which is a line comment.
                // We already increased the depth when we saw "(*".
                // Now we set a flag to decrease the depth when we next see a
                // newline.
                in_line_comment = true;
            } else {
                // "*)" closes a block comment when depth > 0. Outside a comment
                // (e.g., "(op *)") it's code, not a closer — leave depth at 0.
                if !in_line_comment && depth > 0 {
                    depth -= 1;
                }
            }
        } else if c == '\n' && in_line_comment {
            depth -= 1;
            in_line_comment = false;
        }
        i += 1;
        buf[i % n] = c;
    }
    depth
}

/// Returns whether `buf` forms a complete statement.
///
/// `buf` is a statement buffer whose lines are joined by `'\n'` with no
/// trailing newline. It is complete when it ends with `;` and that `;`
/// is not inside a comment.
pub(crate) fn is_complete(buf: &str) -> bool {
    buf.ends_with(';') && comment_depth(buf) == 0
}

/// Returns `buf` with the interior of every comment and string literal
/// replaced by spaces, so that a plain scan of the result sees only code.
///
/// Morel's `(*)` runs to end of line; `(*` otherwise opens a block
/// comment, and block comments nest. The quotes delimiting a string are
/// kept, so a string literal still reads as code.
fn blank_noncode(buf: &str) -> String {
    let mut out = String::with_capacity(buf.len());
    let mut chars = buf.char_indices().peekable();
    let mut depth = 0usize;
    let mut in_line_comment = false;
    let mut in_string = false;
    let mut in_string_escape = false;
    while let Some((_, c)) = chars.next() {
        if in_string {
            out.push(if c == '\n' { '\n' } else { ' ' });
            if in_string_escape {
                in_string_escape = false;
            } else if c == '\\' {
                in_string_escape = true;
            } else if c == '"' {
                in_string = false;
                out.pop();
                out.push('"');
            }
            continue;
        }
        if in_line_comment {
            out.push(if c == '\n' { '\n' } else { ' ' });
            if c == '\n' {
                in_line_comment = false;
            }
            continue;
        }
        if c == '(' && chars.peek().is_some_and(|&(_, d)| d == '*') {
            chars.next();
            // `(*)` is a line comment even inside a block comment: the
            // `*)` in `(* ... (*) close *) ... *)` belongs to the line
            // comment, and does not close the block.
            if chars.peek().is_some_and(|&(_, d)| d == ')') {
                chars.next();
                in_line_comment = true;
                out.push_str("   ");
            } else {
                depth += 1;
                out.push_str("  ");
            }
            continue;
        }
        if depth > 0 {
            if c == '*' && chars.peek().is_some_and(|&(_, d)| d == ')') {
                chars.next();
                depth -= 1;
                out.push_str("  ");
                continue;
            }
            out.push(if c == '\n' { '\n' } else { ' ' });
            continue;
        }
        if c == '"' {
            in_string = true;
        }
        out.push(c);
    }
    out
}

/// Returns whether `buf` contains a `;` that is not inside a comment or
/// a string literal.
///
/// A cheap pre-test for [`split_statement`]: no such `;` means there is
/// certainly no complete statement, and the parser need not be run.
pub(crate) fn has_semicolon(buf: &str) -> bool {
    blank_noncode(buf).contains(';')
}

/// Returns whether `buf` holds anything but whitespace and comments.
///
/// A script ends with a comment -- `(*) End foo.smli` -- which is left
/// in the buffer when the input runs out, and is not an unterminated
/// statement to complain about.
pub(crate) fn has_code(buf: &str) -> bool {
    !blank_noncode(buf).trim().is_empty()
}

/// Splits the first complete statement off `buf`, returning it (with its
/// terminating `;`) and the remainder.
///
/// A line may hold more than one statement, and a statement may hold
/// semicolons of its own -- `let val i = 0; val j = 1; in i + j end;` is
/// one statement, `val a = 1; val b = 2;` is two -- so where a statement
/// ends is a question for the parser, not for a scan of the text.
///
/// Returns `None` while `buf` holds only the start of a statement -- a
/// half-typed `let val i = 0;` is one, and more input may finish it. A
/// buffer that no further input could mend is handed over whole, so that
/// the error is reported where the user wrote it rather than at end of
/// input, which would take the rest of the file with it.
pub(crate) fn split_statement(buf: &str) -> Option<(&str, &str)> {
    if !has_semicolon(buf) {
        return None;
    }
    // `:t` is a shell directive, not grammar, and `Kernel` strips it
    // before parsing. Blank it here too, in place, so that the offset
    // the parser reports still indexes into `buf`.
    match statement_prefix_end(&blank_directives(buf)) {
        StatementPrefix::Complete(end) => Some(buf.split_at(end)),
        StatementPrefix::Incomplete => None,
        StatementPrefix::Malformed => Some((buf, "")),
    }
}

/// Returns `buf` with a line-leading `:t` replaced by two spaces.
///
/// Same length, so an offset into the result is an offset into `buf`.
fn blank_directives(buf: &str) -> String {
    let mut out = String::with_capacity(buf.len());
    for (i, line) in buf.split('\n').enumerate() {
        if i > 0 {
            out.push('\n');
        }
        let indent = line.len() - line.trim_start().len();
        if line[indent..].starts_with(":t") {
            out.push_str(&line[..indent]);
            out.push_str("  ");
            out.push_str(&line[indent + 2..]);
        } else {
            out.push_str(line);
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_comment_depth() {
        assert_eq!(comment_depth("(* comment *)"), 0);
        assert_eq!(comment_depth("(* comment (* nested *)"), 1);
        // A bare `*)` not preceded by an open `(*` is treated as
        // ordinary code (not a stray comment-closer); depth stays
        // at 0. This is what the parenthesised operator `(op *)`
        // looks like to `comment_depth` after stripping the `(`
        // and identifier — the closing `*)` must not turn a
        // statement-buffer's depth negative.
        assert_eq!(comment_depth("code; *)"), 0);
        assert_eq!(comment_depth("(* (* nested (* deeper *) *) *)"), 0);
        assert_eq!(comment_depth("(*) line comment"), 1);
        assert_eq!(comment_depth("(*) line comment\n"), 0);
        let s = r#"(* If a block comment
   contains a (*) comment close *) in a line comment
   then it is ignored. *)
"#;
        assert_eq!(comment_depth(s), 0);
        // Parentheses inside string literals are not comments.
        assert_eq!(comment_depth(r#""(*)" ^ "(*)""#), 0);
        assert_eq!(comment_depth(r#""(*)" ^ "(*)""#), 0);
        assert_eq!(comment_depth(r#"val x = "(*) not a comment""#), 0);
        // Escaped quote inside a string does not end the string.
        assert_eq!(comment_depth(r#""a\"(*) not a comment\"b""#), 0);
        // A (*) line comment with (*fake block*) inside it:
        // the fake (*) should NOT increment depth; only the \n matters.
        assert_eq!(comment_depth("(*) line comment with (* fake\n"), 0);
        // Multi-line: expression ^ (*) line comment with fake (* \n ^ rest;
        assert_eq!(
            comment_depth("\"a\" ^ (*) line comment (* fake\n\"b\";\n"),
            0
        );
    }

    #[test]
    fn test_is_complete() {
        // A statement ending in ';' outside a comment is complete.
        assert!(is_complete("val x = 1;"));
        assert!(is_complete("val x =\n  1 + 2;"));
        // A ';' inside a string does not stop the real terminator counting.
        assert!(is_complete(r#"val s = "a;b";"#));
        // No terminating ';' — incomplete.
        assert!(!is_complete("val x = 1"));
        assert!(!is_complete("from e in emps"));
        // Ends with ';' but that ';' is inside an unterminated block
        // comment (depth 1) — incomplete.
        assert!(!is_complete("(* a ;"));
    }

    #[test]
    fn test_has_semicolon() {
        assert!(has_semicolon("val x = 1;"));
        assert!(has_semicolon("val x = 1; (* c *)"));
        assert!(!has_semicolon("val x = 1"));
        // A ';' inside a comment or a string does not count.
        assert!(!has_semicolon("(* a ; b *)"));
        assert!(!has_semicolon("(*) a ; b"));
        assert!(!has_semicolon(r#"val s = "a;b""#));
        assert!(has_semicolon(r#"val s = "a;b";"#));
    }

    #[test]
    fn test_split_statement() {
        assert_eq!(split_statement("val x = 1;"), Some(("val x = 1;", "")));
        // Two statements on one line are two statements.
        assert_eq!(
            split_statement("val a = 1; val b = 2;"),
            Some(("val a = 1;", " val b = 2;"))
        );
        // A statement is complete before a trailing comment.
        assert_eq!(
            split_statement("val a = 1; (* c *)"),
            Some(("val a = 1;", " (* c *)"))
        );
        // The semicolons inside a `let` are not terminators.
        assert_eq!(
            split_statement("let val i = 0; val j = 1; in i + j end;"),
            Some(("let val i = 0; val j = 1; in i + j end;", ""))
        );
        // Nothing complete yet.
        assert_eq!(split_statement("val x ="), None);
        assert_eq!(split_statement("let val i = 0;"), None);
        assert_eq!(split_statement("(* a ;"), None);
        // Malformed: no further input can mend it, so it is handed over
        // whole and the error is reported where it was written.
        assert_eq!(split_statement("val = ;"), Some(("val = ;", "")));
        assert_eq!(split_statement("1 \\ 2;"), Some(("1 \\ 2;", "")));
        // ... but an unfinished one still waits for more.
        assert_eq!(split_statement("let val i = 0;"), None);
    }
}
