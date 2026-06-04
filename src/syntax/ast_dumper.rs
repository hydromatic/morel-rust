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

//! Produces a parenthesized S-expression dump of an AST node.
//!
//! The output is intended to make tree structure (operator precedence,
//! declaration shape, attribute attachment) easily assertable from
//! `.smli` scripts via `Sys.parseTree`. It is not intended to be
//! re-parsable; use the `Display` impl for that.
//!
//! Each non-leaf node is rendered as `(kind child1 child2 ...)` where
//! `kind` is a stable lowercase tag for the node's variant. Leaves
//! (literals, identifiers, type variables) are rendered atomically.

use crate::syntax::ast::{
    Attribute, AttributePayload, Decl, DeclKind, Expr, ExprKind, LabeledExpr,
    Literal, LiteralKind, Match, Pat, PatField, PatKind, RangeItem, Statement,
    StatementKind, Type, TypeKind, ValBind,
};

/// Returns an S-expression dump of the statement. Wraps with
/// `(attributedExp ...)` when the outer expression has `[@id]`
/// attributes, or `(attributedDecl ...)` when the outer declaration
/// has `[@@id]` attributes; attribute-less statements dump as before.
pub fn dump(stmt: &Statement) -> String {
    let mut b = String::new();
    let has_attrs = !stmt.attributes.is_empty();
    let wrapper = if has_attrs {
        match &stmt.kind {
            StatementKind::Expr(_) => "attributedExp",
            StatementKind::Decl(_) => "attributedDecl",
        }
    } else {
        ""
    };
    if has_attrs {
        b.push('(');
        b.push_str(wrapper);
        b.push(' ');
    }
    match &stmt.kind {
        StatementKind::Expr(e) => dump_expr_kind(&mut b, e),
        StatementKind::Decl(d) => dump_decl_kind(&mut b, d),
    }
    if has_attrs {
        for attr in &stmt.attributes {
            b.push(' ');
            dump_attribute(&mut b, attr);
        }
        b.push(')');
    }
    b
}

fn dump_expr(b: &mut String, e: &Expr) {
    if e.attributes.is_empty() {
        dump_expr_kind(b, &e.kind);
    } else {
        b.push_str("(attributedExp ");
        dump_expr_kind(b, &e.kind);
        for attr in &e.attributes {
            b.push(' ');
            dump_attribute(b, attr);
        }
        b.push(')');
    }
}

fn dump_expr_kind(b: &mut String, e: &ExprKind<Expr>) {
    match e {
        // lint: sort until '#}' where '##ExprKind::'
        ExprKind::Aggregate(a, c) => infix(b, "aggregate", a, c),
        ExprKind::AndAlso(a, c) => infix(b, "andalso", a, c),
        ExprKind::Annotated(e, t) => {
            b.push_str("(annotatedExp ");
            dump_expr(b, e);
            b.push(' ');
            dump_type(b, t);
            b.push(')');
        }
        ExprKind::Append(a, c) => infix(b, "append", a, c),
        ExprKind::Apply(a, c) => infix(b, "apply", a, c),
        ExprKind::Caret(a, c) => infix(b, "caret", a, c),
        ExprKind::Case(scrutinee, arms) => {
            b.push_str("(case ");
            dump_expr(b, scrutinee);
            for m in arms {
                b.push(' ');
                dump_match(b, m);
            }
            b.push(')');
        }
        ExprKind::Compose(a, c) => infix(b, "compose", a, c),
        ExprKind::Cons(a, c) => infix(b, "cons", a, c),
        ExprKind::Current => b.push_str("current"),
        ExprKind::Div(a, c) => infix(b, "div", a, c),
        ExprKind::Divide(a, c) => infix(b, "divide", a, c),
        ExprKind::Elem(a, c) => infix(b, "elem", a, c),
        ExprKind::Elements => b.push_str("elements"),
        ExprKind::Equal(a, c) => infix(b, "equal", a, c),
        ExprKind::Exists(_) => dump_query(b, "exists", e),
        ExprKind::Fn(arms) => {
            b.push_str("(fn");
            for m in arms {
                b.push(' ');
                dump_match(b, m);
            }
            b.push(')');
        }
        ExprKind::Forall(_) => dump_query(b, "forall", e),
        ExprKind::From(_) => dump_query(b, "from", e),
        ExprKind::GreaterThan(a, c) => infix(b, "greaterThan", a, c),
        ExprKind::GreaterThanOrEqual(a, c) => {
            infix(b, "greaterThanOrEqual", a, c)
        }
        ExprKind::Identifier(name) => {
            b.push_str("(id ");
            b.push_str(name);
            b.push(')');
        }
        ExprKind::If(cond, then_, else_) => {
            b.push_str("(if ");
            dump_expr(b, cond);
            b.push(' ');
            dump_expr(b, then_);
            b.push(' ');
            dump_expr(b, else_);
            b.push(')');
        }
        ExprKind::Implies(a, c) => infix(b, "implies", a, c),
        ExprKind::LessThan(a, c) => infix(b, "lessThan", a, c),
        ExprKind::LessThanOrEqual(a, c) => infix(b, "lessThanOrEqual", a, c),
        ExprKind::Let(decls, body) => {
            b.push_str("(let");
            for d in decls {
                b.push(' ');
                dump_decl(b, d);
            }
            b.push(' ');
            dump_expr(b, body);
            b.push(')');
        }
        ExprKind::List(args) => list(b, "list", args.iter(), dump_expr),
        ExprKind::Literal(lit) => dump_literal(b, lit),
        ExprKind::Minus(a, c) => infix(b, "minus", a, c),
        ExprKind::Mod(a, c) => infix(b, "mod", a, c),
        ExprKind::Negate(a) => prefix(b, "negate", a),
        ExprKind::NotElem(a, c) => infix(b, "notElem", a, c),
        ExprKind::NotEqual(a, c) => infix(b, "notEqual", a, c),
        ExprKind::OpSection(name) => {
            b.push_str("(opSection ");
            b.push_str(name);
            b.push(')');
        }
        ExprKind::OrElse(a, c) => infix(b, "orelse", a, c),
        ExprKind::Ordinal => b.push_str("ordinal"),
        ExprKind::Plus(a, c) => infix(b, "plus", a, c),
        ExprKind::Raise(e) => prefix(b, "raise", e),
        ExprKind::RangeList(items) => {
            b.push_str("(rangeList");
            for item in items {
                b.push(' ');
                match item {
                    RangeItem::Point(e) => prefix(b, "point", e),
                    RangeItem::Closed(lo, hi) => infix(b, "closed", lo, hi),
                    RangeItem::ClosedOpen(lo, hi) => {
                        infix(b, "closedOpen", lo, hi)
                    }
                    RangeItem::OpenClosed(lo, hi) => {
                        infix(b, "openClosed", lo, hi)
                    }
                    RangeItem::Open(lo, hi) => infix(b, "open", lo, hi),
                    RangeItem::AtLeast(e) => prefix(b, "atLeast", e),
                    RangeItem::GreaterThan(e) => prefix(b, "greaterThan", e),
                    RangeItem::AtMost(e) => prefix(b, "atMost", e),
                    RangeItem::LessThan(e) => prefix(b, "lessThan", e),
                    RangeItem::All => b.push_str("all"),
                }
            }
            b.push(')');
        }
        ExprKind::Record(base, fields) => {
            b.push_str("(record");
            if let Some(base) = base {
                b.push_str(" (with ");
                dump_expr(b, base);
                b.push(')');
            }
            for f in fields {
                b.push(' ');
                dump_labeled_expr(b, f);
            }
            b.push(')');
        }
        ExprKind::RecordSelector(name) => {
            b.push_str("(recordSelector ");
            b.push_str(name);
            b.push(')');
        }
        ExprKind::SafeRecordSelector(name) => {
            b.push_str("(safeRecordSelector ");
            b.push_str(name);
            b.push(')');
        }
        ExprKind::Times(a, c) => infix(b, "times", a, c),
        ExprKind::Tuple(args) => list(b, "tuple", args.iter(), dump_expr),
    }
}

/// Renders a query expression (`from`, `exists`, `forall`) by falling
/// back to the unparsed source text. The inner step list is not
/// enumerated by the dumper.
fn dump_query(b: &mut String, kind: &str, e: &ExprKind<Expr>) {
    b.push('(');
    b.push_str(kind);
    b.push(' ');
    b.push_str(&format!("{}", e));
    b.push(')');
}

fn dump_literal(b: &mut String, lit: &Literal) {
    match &lit.kind {
        // lint: sort until '#}' where '##LiteralKind::'
        LiteralKind::Bool(v) => {
            b.push_str("(bool_literal ");
            b.push_str(if *v { "true" } else { "false" });
            b.push(')');
        }
        LiteralKind::Char(s) => {
            // `s` is the source form including `#"..."`.
            b.push_str("(char_literal ");
            b.push_str(s);
            b.push(')');
        }
        LiteralKind::Fn(f) => {
            b.push_str("(fn_literal ");
            b.push_str(&format!("{:?}", f));
            b.push(')');
        }
        LiteralKind::Int(s) => {
            b.push_str("(int_literal ");
            b.push_str(s);
            b.push(')');
        }
        LiteralKind::Real(s) => {
            b.push_str("(real_literal ");
            b.push_str(s);
            b.push(')');
        }
        LiteralKind::String(s) => {
            // `s` is the source form including the surrounding double quotes.
            b.push_str("(string_literal ");
            b.push_str(s);
            b.push(')');
        }
        LiteralKind::Unit => b.push_str("(unit_literal)"),
    }
}

fn dump_match(b: &mut String, m: &Match) {
    b.push_str("(match ");
    dump_pat(b, &m.pat);
    b.push(' ');
    dump_expr(b, &m.expr);
    b.push(')');
}

fn dump_labeled_expr(b: &mut String, f: &LabeledExpr) {
    match &f.label {
        Some(label) => {
            b.push('(');
            b.push_str(&label.name);
            b.push(' ');
            dump_expr(b, &f.expr);
            b.push(')');
        }
        None => dump_expr(b, &f.expr),
    }
}

fn dump_pat(b: &mut String, p: &Pat) {
    match &p.kind {
        // lint: sort until '#}' where '##PatKind::'
        PatKind::Annotated(pat, ty) => {
            b.push_str("(annotatedPat ");
            dump_pat(b, pat);
            b.push(' ');
            dump_type(b, ty);
            b.push(')');
        }
        PatKind::As(name, inner) => {
            b.push_str("(asPat ");
            b.push_str(name);
            b.push(' ');
            dump_pat(b, inner);
            b.push(')');
        }
        PatKind::Cons(head, tail) => {
            b.push_str("(consPat ");
            dump_pat(b, head);
            b.push(' ');
            dump_pat(b, tail);
            b.push(')');
        }
        PatKind::Constructor(name, arg) => {
            b.push_str("(conPat ");
            b.push_str(name);
            if let Some(arg) = arg {
                b.push(' ');
                dump_pat(b, arg);
            }
            b.push(')');
        }
        PatKind::Identifier(name) => {
            b.push_str("(idPat ");
            b.push_str(name);
            b.push(')');
        }
        PatKind::List(pats) => list(b, "listPat", pats.iter(), dump_pat),
        PatKind::Literal(lit) => {
            b.push_str("(litPat ");
            dump_literal(b, lit);
            b.push(')');
        }
        PatKind::Record(fields, ellipsis) => {
            b.push_str("(recordPat");
            if *ellipsis {
                b.push_str(" ...");
            }
            for f in fields {
                b.push(' ');
                match f {
                    PatField::Labeled(_, name, pat) => {
                        b.push('(');
                        b.push_str(name);
                        b.push(' ');
                        dump_pat(b, pat);
                        b.push(')');
                    }
                    PatField::Anonymous(_, pat) => dump_pat(b, pat),
                }
            }
            b.push(')');
        }
        PatKind::Tuple(pats) => list(b, "tuplePat", pats.iter(), dump_pat),
        PatKind::Wildcard => b.push_str("wildcard"),
    }
}

fn dump_type(b: &mut String, t: &Type) {
    if !t.attributes.is_empty() {
        b.push_str("(attributedType ");
        dump_type_kind(b, t);
        for attr in &t.attributes {
            b.push(' ');
            dump_attribute(b, attr);
        }
        b.push(')');
        return;
    }
    dump_type_kind(b, t);
}

fn dump_type_kind(b: &mut String, t: &Type) {
    match &t.kind {
        // lint: sort until '#}' where '##TypeKind::'
        TypeKind::App(args, head) => {
            b.push_str("(appType ");
            dump_type(b, head);
            for a in args {
                b.push(' ');
                dump_type(b, a);
            }
            b.push(')');
        }
        TypeKind::Composite(ts) => list(b, "composite", ts.iter(), dump_type),
        TypeKind::Con(name) => {
            b.push_str("(con ");
            b.push_str(name);
            b.push(')');
        }
        TypeKind::Expression(e) => {
            b.push_str("(exprType ");
            dump_expr(b, e);
            b.push(')');
        }
        TypeKind::Fn(p, r) => {
            b.push_str("(fnType ");
            dump_type(b, p);
            b.push(' ');
            dump_type(b, r);
            b.push(')');
        }
        TypeKind::Id(name) => {
            b.push_str("(named ");
            b.push_str(name);
            b.push(')');
        }
        TypeKind::Record(fields) => {
            b.push_str("(recordType");
            for f in fields {
                b.push(' ');
                b.push('(');
                b.push_str(&f.label.name);
                b.push(' ');
                dump_type(b, &f.type_);
                b.push(')');
            }
            b.push(')');
        }
        TypeKind::Tuple(ts) => list(b, "tupleType", ts.iter(), dump_type),
        TypeKind::Unit => b.push_str("(unitType)"),
        TypeKind::Var(name) => {
            b.push_str("(tyVar ");
            b.push_str(name);
            b.push(')');
        }
    }
}

fn dump_decl(b: &mut String, d: &Decl) {
    dump_decl_kind(b, &d.kind);
}

fn dump_attribute(b: &mut String, attr: &Attribute) {
    b.push_str("(attribute ");
    b.push_str(attr.kind.prefix());
    b.push_str(&attr.name);
    if let Some(payload) = &attr.payload {
        match payload {
            AttributePayload::Expr(e) => {
                b.push(' ');
                dump_expr(b, e);
            }
            AttributePayload::Type(t) => {
                b.push_str(" : ");
                dump_type(b, t);
            }
        }
    }
    b.push(')');
}

fn dump_decl_kind(b: &mut String, d: &DeclKind) {
    match d {
        // lint: sort until '#}' where '##DeclKind::'
        DeclKind::Datatype(_) => dump_decl_source(b, "datatype", d),
        DeclKind::FloatingAttr(attr) => {
            b.push_str("(floatingAttrDecl ");
            dump_attribute(b, attr);
            b.push(')');
        }
        DeclKind::Fun(funs) => {
            // Render as `(funBind (funMatch name ...))`: the name lives
            // on `FunBind` in the AST (every match in a funBind shares
            // it), but the dump form attaches it to each `funMatch`.
            b.push_str("(fun");
            for fb in funs {
                b.push(' ');
                b.push_str("(funBind");
                for fm in &fb.matches {
                    b.push(' ');
                    b.push_str("(funMatch ");
                    b.push_str(&fb.name);
                    for p in &fm.pats {
                        b.push(' ');
                        dump_pat(b, p);
                    }
                    if let Some(t) = &fm.type_ {
                        b.push(' ');
                        dump_type(b, t);
                    }
                    b.push(' ');
                    dump_expr(b, &fm.expr);
                    b.push(')');
                }
                b.push(')');
            }
            b.push(')');
        }
        DeclKind::Over(name) => {
            b.push_str("(over ");
            b.push_str(name);
            b.push(')');
        }
        DeclKind::Signature(_) => dump_decl_source(b, "signature_decl", d),
        DeclKind::Type(_) => dump_decl_source(b, "type_decl", d),
        DeclKind::Val(rec, inst, binds) => {
            b.push_str("(val");
            if *rec {
                b.push_str(" rec");
            }
            if *inst {
                b.push_str(" inst");
            }
            for vb in binds {
                b.push(' ');
                dump_val_bind(b, vb);
            }
            b.push(')');
        }
    }
}

/// Renders a declaration by falling back to the unparsed source text.
/// Used for declaration shapes the dumper has not enumerated in
/// detail (currently `type`, `datatype`, and `signature`).
fn dump_decl_source(b: &mut String, kind: &str, d: &DeclKind) {
    b.push('(');
    b.push_str(kind);
    b.push(' ');
    b.push_str(&format!("{}", d));
    b.push(')');
}

fn dump_val_bind(b: &mut String, vb: &ValBind) {
    b.push_str("(valBind ");
    dump_pat(b, &vb.pat);
    if let Some(t) = &vb.type_annotation {
        b.push(' ');
        dump_type(b, t);
    }
    b.push(' ');
    dump_expr(b, &vb.expr);
    b.push(')');
}

fn infix(b: &mut String, kind: &str, a: &Expr, c: &Expr) {
    b.push('(');
    b.push_str(kind);
    b.push(' ');
    dump_expr(b, a);
    b.push(' ');
    dump_expr(b, c);
    b.push(')');
}

fn prefix(b: &mut String, kind: &str, a: &Expr) {
    b.push('(');
    b.push_str(kind);
    b.push(' ');
    dump_expr(b, a);
    b.push(')');
}

fn list<'a, T: 'a, I: Iterator<Item = &'a T>, F: Fn(&mut String, &T)>(
    b: &mut String,
    kind: &str,
    items: I,
    f: F,
) {
    b.push('(');
    b.push_str(kind);
    for item in items {
        b.push(' ');
        f(b, item);
    }
    b.push(')');
}
