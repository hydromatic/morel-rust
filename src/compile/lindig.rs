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

//! Pretty-printer that lays out a document within a line-width limit.
//!
//! The [`Doc`] algebraic type represents a set of possible layouts for a
//! document; [`render`] chooses the best layout that fits a given line
//! width.
//!
//! The design draws on a line of work on pretty-printing combinators:
//! Oppen's "Prettyprinting" (1980), Wadler's "A prettier printer" (2002),
//! and Leijen's `Column`, `Nesting`, and `FlatAlt` extensions (which enable
//! [`align`]). The module is named after Christian Lindig, whose "Strictly
//! Pretty" (2000) gives the strict, iterative rendering algorithm used here:
//! [`render`] makes a single pass over an explicit work list, running in time
//! linear in the size of the document and using constant native stack
//! however deeply the document nests.

use std::cell::OnceCell;
use std::fmt;
use std::rc::Rc;

/// A document that can be laid out in multiple ways.
///
/// Instances are created via the free functions in this module.
#[derive(Clone)]
pub enum Doc {
    /// The empty document.
    Empty,
    /// Literal text.
    Text(Rc<str>),
    /// Newline, then `indent` spaces, then the rest.
    Line,
    /// `primary` when broken across lines; `flat` when flattened to one line.
    FlatAlt(Rc<Doc>, Rc<Doc>),
    /// Concatenation of `a` followed by `b`.
    Cat(Rc<Doc>, Rc<Doc>),
    /// Increase indentation by `indent` for the sub-document.
    Nest(i32, Rc<Doc>),
    /// Lay out `doc` flat if it fits the remaining space, otherwise broken.
    Group(Rc<Doc>),
    /// Choose `wide` if its first line fits the remaining space, otherwise
    /// `narrow`.
    Union(Rc<Doc>, Rc<Doc>),
    /// Access the current column to produce a document.
    Column(Rc<dyn Fn(i32) -> Doc>),
    /// Access the current nesting level to produce a document.
    Nesting(Rc<dyn Fn(i32) -> Doc>),
}

impl fmt::Debug for Doc {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Doc::Empty => write!(f, "Empty"),
            Doc::Text(s) => write!(f, "Text({})", s),
            Doc::Line => write!(f, "Line"),
            Doc::FlatAlt(..) => write!(f, "FlatAlt"),
            Doc::Cat(..) => write!(f, "Cat"),
            Doc::Nest(i, _) => write!(f, "Nest({})", i),
            Doc::Group(_) => write!(f, "Group"),
            Doc::Union(..) => write!(f, "Union"),
            Doc::Column(_) => write!(f, "Column"),
            Doc::Nesting(_) => write!(f, "Nesting"),
        }
    }
}

// -- Primitives -----------------------------------------------------------

/// The empty document.
pub fn empty() -> Doc {
    Doc::Empty
}

/// A line break that is replaced by a space when flattened.
///
/// This is the most common separator for [`group`]: when the group fits on
/// one line the line breaks become spaces.
pub fn line() -> Doc {
    Doc::FlatAlt(Rc::new(Doc::Line), Rc::new(Doc::Text(Rc::from(" "))))
}

/// A line break that is replaced by nothing when flattened.
pub fn line_break() -> Doc {
    Doc::FlatAlt(Rc::new(Doc::Line), Rc::new(Doc::Empty))
}

/// A space when it fits, otherwise a line break. Equivalent to
/// `group(line())`.
pub fn soft_line() -> Doc {
    group(line())
}

/// Nothing when it fits, otherwise a line break. Equivalent to
/// `group(line_break())`.
pub fn soft_break() -> Doc {
    group(line_break())
}

/// A line break that is always rendered, even when flattened.
pub fn hard_line() -> Doc {
    Doc::Line
}

/// Creates a document containing literal text. The text must not contain
/// newlines; use [`line()`] or [`hard_line`] for those.
pub fn text(s: &str) -> Doc {
    if s.is_empty() {
        Doc::Empty
    } else {
        Doc::Text(Rc::from(s))
    }
}

// -- Composition ----------------------------------------------------------

/// Concatenation: `a` followed by `b`.
pub fn beside(a: Doc, b: Doc) -> Doc {
    Doc::Cat(Rc::new(a), Rc::new(b))
}

/// Increases indentation of `doc` by `indent` spaces.
pub fn nest(indent: i32, doc: Doc) -> Doc {
    assert!(indent >= 0, "indent must be nonnegative: {}", indent);
    nest_unchecked(indent, doc)
}

/// Marks `doc` as a group: [`render`] lays the group out flat (line breaks
/// become their flat alternatives) if it fits the remaining width, and
/// otherwise lays it out broken.
pub fn group(doc: Doc) -> Doc {
    if matches!(doc, Doc::Group(_)) {
        doc // already a group
    } else {
        Doc::Group(Rc::new(doc))
    }
}

/// Lays out `wide` if its first line fits the remaining space, otherwise
/// `narrow`. Unlike [`group`], the alternatives may differ in structure.
pub fn union(wide: Doc, narrow: Doc) -> Doc {
    Doc::Union(Rc::new(wide), Rc::new(narrow))
}

/// Lays out `doc` with the nesting level set to the current column.
pub fn align(doc: Doc) -> Doc {
    // The relative nesting "k - i" is negative when the current column k is
    // left of the current indent i, so it must bypass the nonnegative check
    // that the public "nest" applies to caller-supplied indents.
    Doc::Column(Rc::new(move |k| {
        let doc = doc.clone();
        Doc::Nesting(Rc::new(move |i| nest_unchecked(k - i, doc.clone())))
    }))
}

/// Lays out `doc` with a nesting level of `indent` relative to the current
/// column. Equivalent to `align(nest(indent, doc))`.
pub fn hang(indent: i32, doc: Doc) -> Doc {
    assert!(indent >= 0, "indent must be nonnegative: {}", indent);
    align(nest_unchecked(indent, doc))
}

/// Indents `doc` by `indent` spaces, and then aligns subsequent lines to the
/// first.
pub fn indent(indent: i32, doc: Doc) -> Doc {
    assert!(indent >= 0, "indent must be nonnegative: {}", indent);
    beside(text(&spaces(indent)), align(nest_unchecked(indent, doc)))
}

// -- List combinators -----------------------------------------------------

/// Concatenates documents horizontally, separated by spaces.
pub fn hsep(docs: Vec<Doc>) -> Doc {
    fold(docs, with_space)
}

/// Concatenates documents vertically, separated by line breaks.
pub fn vsep(docs: Vec<Doc>) -> Doc {
    fold(docs, with_line)
}

/// Concatenates documents separated by spaces if they fit on one line,
/// otherwise separates them with line breaks. Equivalent to
/// `group(vsep(docs))`.
pub fn sep(docs: Vec<Doc>) -> Doc {
    group(vsep(docs))
}

/// Concatenates documents horizontally with no separator.
pub fn hcat(docs: Vec<Doc>) -> Doc {
    fold(docs, beside)
}

/// Concatenates documents vertically, separated by empty line breaks.
pub fn vcat(docs: Vec<Doc>) -> Doc {
    fold(docs, with_line_break)
}

/// Concatenates documents with no separator if they fit on one line,
/// otherwise separates them with line breaks. Equivalent to
/// `group(vcat(docs))`.
pub fn cat(docs: Vec<Doc>) -> Doc {
    group(vcat(docs))
}

/// Concatenates documents, filling each line with as many as will fit,
/// separated by spaces.
pub fn fill_sep(docs: Vec<Doc>) -> Doc {
    fold(docs, with_soft_line)
}

/// Concatenates documents, filling each line with as many as will fit, with
/// no separator.
pub fn fill_cat(docs: Vec<Doc>) -> Doc {
    fold(docs, with_soft_break)
}

/// Packs documents onto as many lines as needed, putting as many as fit on
/// each line, joined by `glue` when packed and by a line break otherwise.
///
/// Unlike [`fill_sep`] and [`fill_cat`], each gap is decided by whether the
/// *following* document, laid out flat, fits on the current line; a document
/// is treated as an indivisible unit even if it contains its own line breaks.
///
/// Not called `fill`: in Leijen's printer, and in Haskell's
/// `prettyprinter` after it, `fill i d` pads `d` with spaces to width
/// `i`, a member of the `fill`/`fillBreak` padding family unrelated to
/// `fill_sep`/`fill_cat`. This name says what it does and leaves
/// `fill` free for its conventional meaning.
pub fn pack(glue: &Doc, docs: &[Doc]) -> Doc {
    if docs.is_empty() {
        return empty();
    }
    // The first element renders normally; each later element is preceded by a
    // gap that is either `glue` (stay on the line) or a line break. Built
    // right-to-left so each suffix is shared (linear, not exponential).
    let n = docs.len();
    let mut tail = empty();
    for i in (1..n).rev() {
        let x = docs[i].clone();
        let rest = tail;
        tail = union(
            beside(glue.clone(), beside(flatten(&x), rest.clone())),
            beside(hard_line(), beside(x, rest)),
        );
    }
    beside(docs[0].clone(), tail)
}

/// Returns the flattened form of `doc`: every soft line break takes its flat
/// alternative and every [`group`] is laid out flat. A [`hard_line`] cannot
/// be flattened and is left as a line break.
pub fn flatten(doc: &Doc) -> Doc {
    match doc {
        Doc::Empty | Doc::Line => doc.clone(),
        Doc::Text(_) => doc.clone(),
        Doc::Cat(a, b) => beside(flatten(a), flatten(b)),
        Doc::Nest(indent, d) => Doc::Nest(*indent, Rc::new(flatten(d))),
        Doc::FlatAlt(_, flat) => flatten(flat),
        Doc::Group(d) => flatten(d),
        Doc::Union(wide, _) => flatten(wide),
        Doc::Column(f) => {
            let f = Rc::clone(f);
            Doc::Column(Rc::new(move |k| flatten(&f(k))))
        }
        Doc::Nesting(f) => {
            let f = Rc::clone(f);
            Doc::Nesting(Rc::new(move |i| flatten(&f(i))))
        }
    }
}

/// Intersperses `separator` between the documents.
///
/// For example, `punctuate(text(","), [a, b, c])` returns
/// `[beside(a, text(",")), beside(b, text(",")), c]`.
pub fn punctuate(separator: &Doc, docs: Vec<Doc>) -> Vec<Doc> {
    if docs.len() <= 1 {
        return docs;
    }
    let n = docs.len();
    let mut result = Vec::with_capacity(n);
    for (i, d) in docs.into_iter().enumerate() {
        if i < n - 1 {
            result.push(beside(d, separator.clone()));
        } else {
            result.push(d);
        }
    }
    result
}

/// Encloses a list of documents between `open` and `close`, separated by
/// `separator`.
pub fn enclose_sep(
    open: Doc,
    close: Doc,
    separator: &Doc,
    docs: Vec<Doc>,
) -> Doc {
    if docs.is_empty() {
        return beside(open, close);
    }
    if docs.len() == 1 {
        let d = docs.into_iter().next().unwrap();
        return beside(open, beside(d, close));
    }
    let punctuated = punctuate(separator, docs);
    group(beside(open, beside(align(vsep(punctuated)), close)))
}

// -- Bracketing helpers ---------------------------------------------------

/// Encloses `doc` in parentheses.
pub fn parens(doc: Doc) -> Doc {
    beside(text("("), beside(doc, text(")")))
}

/// Encloses `doc` in braces.
pub fn braces(doc: Doc) -> Doc {
    beside(text("{"), beside(doc, text("}")))
}

/// Encloses `doc` in square brackets.
pub fn brackets(doc: Doc) -> Doc {
    beside(text("["), beside(doc, text("]")))
}

// -- Rendering ------------------------------------------------------------

/// Layout mode of a work-list item: `Flat` suppresses line breaks.
#[derive(Copy, Clone, Eq, PartialEq)]
enum Mode {
    Flat,
    Break,
}

/// An entry in the work list for the layout algorithm: render `doc` at the
/// given indent and mode, then continue with `next`. The list is immutable,
/// so the tail can be shared between the flat and broken alternatives of a
/// group without copying.
struct Item {
    indent: i32,
    mode: Mode,
    doc: Doc,
    next: Option<Rc<Item>>,
}

/// Renders a document to a string, choosing the best layout for the given
/// line width.
pub fn render(width: i32, doc: Doc) -> String {
    let mut b = String::new();
    let mut thunk = Thunk::new(
        width,
        0,
        Some(Rc::new(Item {
            indent: 0,
            mode: Mode::Break,
            doc,
            next: None,
        })),
    );
    loop {
        match &*thunk.force() {
            Out::End => return b,
            Out::Text(t, rest) => {
                b.push_str(t);
                thunk = Rc::clone(rest);
            }
            Out::Line(indent, _flat, rest) => {
                b.push('\n');
                push_spaces(&mut b, *indent);
                thunk = Rc::clone(rest);
            }
        }
    }
}

/// Lays out the work list until it produces the next output chunk.
///
/// Each chunk carries a [`Thunk`] for the rest of the stream, so the
/// layout is produced on demand; [`fits`] forces only as much of it as
/// the fit test needs, and `Thunk` memoizes what has been forced, so
/// that a later pass does not redo the work.
fn best(width: i32, col: i32, item: Option<Rc<Item>>) -> Out {
    // Only `Text` and `Line` advance the column, and both return, so
    // `col` stays put for as long as this loop runs.
    let mut item = item;
    while let Some(it) = item {
        let i = it.indent;
        let mode = it.mode;
        let next = it.next.clone();
        match &it.doc {
            Doc::Empty => {
                item = next;
            }
            Doc::Text(t) => {
                let len = t.chars().count() as i32;
                return Out::Text(
                    Rc::clone(t),
                    Thunk::new(width, col + len, next),
                );
            }
            Doc::Cat(a, c) => {
                let tail = Rc::new(Item {
                    indent: i,
                    mode,
                    doc: (**c).clone(),
                    next,
                });
                item = Some(Rc::new(Item {
                    indent: i,
                    mode,
                    doc: (**a).clone(),
                    next: Some(tail),
                }));
            }
            Doc::Nest(n, d) => {
                item = Some(Rc::new(Item {
                    indent: i + n,
                    mode,
                    doc: (**d).clone(),
                    next,
                }));
            }
            Doc::Line => {
                // A bare line cannot be flattened, so one that survives
                // into a flat layout still emits a line break but marks
                // the layout as not fitting; that is what makes a group
                // containing `hard_line` always break.
                return Out::Line(
                    i,
                    mode == Mode::Flat,
                    Thunk::new(width, i, next),
                );
            }
            Doc::FlatAlt(primary, flat) => {
                let d = if mode == Mode::Flat { flat } else { primary };
                item = Some(Rc::new(Item {
                    indent: i,
                    mode,
                    doc: (**d).clone(),
                    next,
                }));
            }
            Doc::Group(inner) => {
                // Inside a flat layout every group is flat too, and needs
                // no decision. Otherwise the group is flat if its
                // flattened layout, followed by whatever comes after it,
                // reaches the end of the line within the page width. The
                // lookahead is exact: it measures the stream that
                // rendering would emit, including the text that a
                // downstream group contributes to this line before it
                // breaks.
                let flat = Some(Rc::new(Item {
                    indent: i,
                    mode: Mode::Flat,
                    doc: (**inner).clone(),
                    next: next.clone(),
                }));
                if mode == Mode::Flat {
                    item = flat;
                    continue;
                }
                let thunk = Thunk::new(width, col, flat);
                if fits(width - col, Rc::clone(&thunk)) {
                    return (*thunk.force()).clone();
                }
                item = Some(Rc::new(Item {
                    indent: i,
                    mode: Mode::Break,
                    doc: (**inner).clone(),
                    next,
                }));
            }
            Doc::Union(wide, narrow) => {
                // A union always makes its own decision (it is not forced
                // flat by an enclosing flat layout), so the gaps of a
                // `pack` break independently.
                let thunk = Thunk::new(
                    width,
                    col,
                    Some(Rc::new(Item {
                        indent: i,
                        mode: Mode::Flat,
                        doc: (**wide).clone(),
                        next: next.clone(),
                    })),
                );
                if fits(width - col, Rc::clone(&thunk)) {
                    return (*thunk.force()).clone();
                }
                item = Some(Rc::new(Item {
                    indent: i,
                    mode: Mode::Break,
                    doc: (**narrow).clone(),
                    next,
                }));
            }
            Doc::Column(f) => {
                item = Some(Rc::new(Item {
                    indent: i,
                    mode,
                    doc: f(col),
                    next,
                }));
            }
            Doc::Nesting(f) => {
                item = Some(Rc::new(Item {
                    indent: i,
                    mode,
                    doc: f(i),
                    next,
                }));
            }
        }
    }
    Out::End
}

// -- Private helpers ------------------------------------------------------

/// Folds a list of documents using a binary operator.
fn fold(docs: Vec<Doc>, op: fn(Doc, Doc) -> Doc) -> Doc {
    let mut iter = docs.into_iter().rev();
    match iter.next() {
        None => empty(),
        Some(mut result) => {
            for d in iter {
                result = op(d, result);
            }
            result
        }
    }
}

fn nest_unchecked(indent: i32, doc: Doc) -> Doc {
    if indent == 0 {
        doc
    } else {
        Doc::Nest(indent, Rc::new(doc))
    }
}

fn with_space(a: Doc, b: Doc) -> Doc {
    beside(a, beside(text(" "), b))
}

fn with_line(a: Doc, b: Doc) -> Doc {
    beside(a, beside(line(), b))
}

fn with_line_break(a: Doc, b: Doc) -> Doc {
    beside(a, beside(line_break(), b))
}

fn with_soft_line(a: Doc, b: Doc) -> Doc {
    beside(a, beside(soft_line(), b))
}

fn with_soft_break(a: Doc, b: Doc) -> Doc {
    beside(a, beside(soft_break(), b))
}

/// Returns whether the rest of the layout fits in the remaining space
/// on the current line. Scans the output stream forward until the
/// first line break (which ends the current line, so what precedes it
/// fits) or until the remaining space runs out.
///
/// Because the scan consumes the chunks that rendering will emit, the
/// layout decisions it passes over have already been made -- and are
/// memoized, so the caller that commits to this stream, and any later
/// scan over it, gets them for free.
fn fits(remaining: i32, thunk: Rc<Thunk>) -> bool {
    let mut remaining = remaining;
    let mut thunk = thunk;
    loop {
        if remaining < 0 {
            return false;
        }
        let out = thunk.force();
        match &*out {
            Out::End => return true,
            Out::Text(t, rest) => {
                remaining -= t.chars().count() as i32;
                thunk = Rc::clone(rest);
            }
            // A line break ends the current line, so what precedes it
            // fits -- unless it is a bare line that a flat layout could
            // not flatten, in which case the layout is invalid and the
            // group must break.
            Out::Line(_, flat, _) => return !flat,
        }
    }
}

// -- Output stream --------------------------------------------------------

/// A chunk of laid-out output: literal text, a line break, or the end
/// of the stream. Leijen calls this a `SimpleDoc`: a document from
/// which every layout choice has been removed.
#[derive(Clone)]
enum Out {
    /// The end of the stream.
    End,
    /// Literal text, then the rest of the stream.
    Text(Rc<str>, Rc<Thunk>),
    /// A line break and `indent` spaces, then the rest of the stream.
    /// `flat` marks a bare line that reached a flat layout, which no
    /// layout can honour; [`fits`] rejects it.
    Line(i32, bool, Rc<Thunk>),
}

/// The unforced rest of an output stream: the work list to lay out,
/// and the result once laid out. Memoizing is what makes the fit test
/// affordable -- every scan that passes over a decision shares the one
/// that was made, rather than making it again.
struct Thunk {
    width: i32,
    col: i32,
    item: Option<Rc<Item>>,
    out: OnceCell<Rc<Out>>,
}

impl Thunk {
    fn new(width: i32, col: i32, item: Option<Rc<Item>>) -> Rc<Self> {
        Rc::new(Thunk {
            width,
            col,
            item,
            out: OnceCell::new(),
        })
    }

    fn force(&self) -> Rc<Out> {
        Rc::clone(self.out.get_or_init(|| {
            Rc::new(best(self.width, self.col, self.item.clone()))
        }))
    }
}

/// Returns a string of `n` spaces.
fn spaces(n: i32) -> String {
    " ".repeat(n.max(0) as usize)
}

fn push_spaces(b: &mut String, n: i32) {
    for _ in 0..n.max(0) {
        b.push(' ');
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A union whose narrow branch continues on the same line -- an
    /// elision combinator, "full form if it fits, else `...`" -- is
    /// measured by what that branch actually emits.
    ///
    /// This is the case a fit test cannot get right by treating a
    /// union as the end of the line. It happens to work for every
    /// union built today -- those of [`pack`] and of Morel's own
    /// printer -- because each has a narrow branch that begins with a
    /// line break. `PP` cannot express it, so it lives here.
    #[test]
    fn test_fits_measures_chosen_union_branch() {
        let elided = union(text("alpha bravo charlie"), text("..."));
        let doc = beside(text("["), beside(elided, text("] tail")));
        // Wide: the full form fits.
        assert_eq!(render(80, doc.clone()), "[alpha bravo charlie] tail");
        // Narrow: the full form does not, so the narrow branch is
        // taken -- and the enclosing scan measures "...", not an
        // assumed end of line.
        assert_eq!(render(10, doc), "[...] tail");
    }

    /// Renders a wide tuple whose elements each wrap in their own
    /// group -- one nested decision point per separator.
    ///
    /// A fit test that re-decides each downstream group re-scans the
    /// same suffix at every level, so this costs O(2^n); scanning the
    /// shared output stream instead makes it linear. Before, n=27 took
    /// about 295 seconds, and n=1000 was out of reach.
    #[test]
    fn test_wide_tuple_of_groups() {
        const SIZE: usize = 1000;
        let elements: Vec<Doc> =
            (0..SIZE).map(|n| group(text(&n.to_string()))).collect();
        let doc = enclose_sep(text("("), text(")"), &text(","), elements);
        let s = render(79, doc);
        assert_eq!(s.matches(',').count(), SIZE - 1);
        for line in s.split('\n') {
            assert!(
                line.chars().count() <= 79,
                "line over the width: {:?}",
                line
            );
        }
    }
}
