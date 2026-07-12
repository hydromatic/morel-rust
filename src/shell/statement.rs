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
}
