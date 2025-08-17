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

use crate::parser::parser::Rule;
use pest::iterators::Pair;
use std::fmt::Write;

/// Simple byte span for AST nodes - stores just start/end positions
#[derive(Debug, Clone, Copy)]
pub struct Span {
    pub start: usize,
    pub end: usize,
}

impl Span {
    pub fn from_span(span: &pest::Span) -> Self {
        Self {
            start: span.start(),
            end: span.end(),
        }
    }

    /// Convert back to line/column using the original input
    pub fn to_line_col(&self, input: &str) -> ((usize, usize), (usize, usize)) {
        let start_pos =
            pest::Position::new(input, self.start).unwrap().line_col();
        let end_pos = pest::Position::new(input, self.end).unwrap().line_col();
        (start_pos, end_pos)
    }
}

/// Trait possessed by all abstract syntax tree (AST) nodes
pub trait Ast {
    /// Returns the string representation of the AST node.
    fn unparse(&self, s: &mut String);

    /// Returns the byte span of the AST node.
    fn span(&self) -> Span;
}

/// Tagged union of expressions and declarations.
#[derive(Debug, Clone)]
pub enum Node {
    Expr(Expr),
    Decl(Decl),
}

/// Abstract syntax tree (AST) of an expression.
#[derive(Debug, Clone)]
pub enum Expr {
    // Literals
    IntLiteral(Span, String),
    RealLiteral(Span, String),
    StringLiteral(Span, String),
    CharLiteral(Span, String),
    BoolLiteral(Span, bool),
    UnitLiteral(Span),

    // Identifiers and selectors
    Identifier(Span, String),
    RecordSelector(Span, String),
    Current(Span),
    Ordinal(Span),

    // Binary operations
    Plus(Span, Box<Expr>, Box<Expr>),
    Minus(Span, Box<Expr>, Box<Expr>),
    Times(Span, Box<Expr>, Box<Expr>),
    Divide(Span, Box<Expr>, Box<Expr>),
    Div(Span, Box<Expr>, Box<Expr>),
    Mod(Span, Box<Expr>, Box<Expr>),
    Caret(Span, Box<Expr>, Box<Expr>),

    // Comparison operations
    Equal(Span, Box<Expr>, Box<Expr>),
    NotEqual(Span, Box<Expr>, Box<Expr>),
    LessThan(Span, Box<Expr>, Box<Expr>),
    LessThanOrEqual(Span, Box<Expr>, Box<Expr>),
    GreaterThan(Span, Box<Expr>, Box<Expr>),
    GreaterThanOrEqual(Span, Box<Expr>, Box<Expr>),

    // List operations
    Cons(Span, Box<Expr>, Box<Expr>),
    Append(Span, Box<Expr>, Box<Expr>),

    // Logical operations
    AndAlso(Span, Box<Expr>, Box<Expr>),
    OrElse(Span, Box<Expr>, Box<Expr>),
    Implies(Span, Box<Expr>, Box<Expr>),

    // Relational operations
    Elem(Span, Box<Expr>, Box<Expr>),
    NotElem(Span, Box<Expr>, Box<Expr>),

    // Unary operations
    Negate(Span, Box<Expr>),

    // Function operations
    Apply(Span, Box<Expr>, Box<Expr>),
    O(Span, Box<Expr>, Box<Expr>), // function composition

    // Aggregate operations
    Aggregate(Span, Box<Expr>, Box<Expr>), // expr over expr

    // Control structures
    If(Span, Box<Expr>, Box<Expr>, Box<Expr>),
    Case(Span, Box<Expr>, Vec<CaseArm>),
    Let(Span, Vec<Decl>, Box<Expr>),
    Fn(Span, Vec<FunMatch>),

    // Data structures
    Tuple(Span, Vec<Expr>),
    List(Span, Vec<Expr>),
    Record(Span, Vec<NamedExpr>),

    // Relational expressions
    From(Span, Box<FromExpr>),

    // Type annotation
    Annotated(Span, Box<Expr>, Type),
}

/// Named expression for records and relational operations
#[derive(Debug, Clone)]
pub struct NamedExpr {
    pub name: Option<String>,
    pub expr: Expr,
}

/// Case arm in a case expression
#[derive(Debug, Clone)]
pub struct CaseArm {
    pub pat: Pat,
    pub expr: Expr,
}

/// Function match in a fn expression
#[derive(Debug, Clone)]
pub struct FunMatch {
    pub pat: Pat,
    pub expr: Expr,
}

/// From expression structure
#[derive(Debug, Clone)]
pub struct FromExpr {
    pub from_items: Vec<FromItem>,
    pub where_clause: Option<Box<Expr>>,
    pub group_clause: Option<Vec<NamedExpr>>,
    pub compute_clause: Option<Vec<NamedExpr>>,
    pub order_clause: Option<Vec<Expr>>,
    pub yield_clause: Option<Box<Expr>>,
}

/// From item (pattern in expression)
#[derive(Debug, Clone)]
pub struct FromItem {
    pub pat: Pat,
    pub expr: Expr,
}

/// Abstract syntax tree (AST) of a pattern.
#[derive(Debug, Clone)]
pub enum Pat {
    Wildcard(Span),
    Identifier(Span, String),
    IntLiteral(Span, String),
    RealLiteral(Span, String),
    StringLiteral(Span, String),
    CharLiteral(Span, String),
    BoolLiteral(Span, bool),
    Tuple(Span, Vec<Pat>),
    List(Span, Vec<Pat>),
    Record(Span, Vec<PatField>),
    Cons(Span, Box<Pat>, Box<Pat>),
    Constructor(Span, String, Option<Box<Pat>>),
    As(Span, Box<Pat>, String),
    Annotated(Span, Box<Pat>, Type),
}

/// Pattern field in record patterns
#[derive(Debug, Clone)]
pub struct PatField {
    pub name: String,
    pub pat: Option<Pat>,
}

/// Abstract syntax tree (AST) of a declaration.
#[derive(Debug, Clone)]
pub enum Decl {
    Val(Span, Vec<ValBind>),
    Fun(Span, Vec<FunBind>),
    Type(Span, Vec<TypeBind>),
    Datatype(Span, Vec<DatatypeBind>),
}

/// Value binding
#[derive(Debug, Clone)]
pub struct ValBind {
    pub rec: bool,
    pub pat: Pat,
    pub type_annotation: Option<Type>,
    pub expr: Expr,
}

/// Function binding
#[derive(Debug, Clone)]
pub struct FunBind {
    pub name: String,
    pub matches: Vec<FunMatch>,
}

/// Type binding
#[derive(Debug, Clone)]
pub struct TypeBind {
    pub type_vars: Vec<String>,
    pub name: String,
    pub type_expr: Type,
}

/// Datatype binding
#[derive(Debug, Clone)]
pub struct DatatypeBind {
    pub type_vars: Vec<String>,
    pub name: String,
    pub constructors: Vec<ConBind>,
}

/// Constructor binding
#[derive(Debug, Clone)]
pub struct ConBind {
    pub name: String,
    pub type_expr: Option<Type>,
}

/// Abstract syntax tree (AST) of a type.
#[derive(Debug, Clone)]
pub enum Type {
    Var(Span, String),
    Con(Span, String),
    Fn(Span, Box<Type>, Box<Type>),
    Tuple(Span, Vec<Type>),
    Record(Span, Vec<TypeField>),
    App(Span, Box<Type>, Vec<Type>),
}

/// Type field in record types
#[derive(Debug, Clone)]
pub struct TypeField {
    pub name: String,
    pub type_expr: Type,
}

impl Ast for Node {
    fn unparse(&self, s: &mut String) {
        match self {
            Node::Expr(x) => x.unparse(s),
            Node::Decl(x) => x.unparse(s),
        }
    }

    fn span(&self) -> Span {
        match self {
            Node::Expr(x) => x.span(),
            Node::Decl(x) => x.span(),
        }
    }
}

impl Ast for Expr {
    fn unparse(&self, s: &mut String) {
        match self {
            Expr::Identifier(_, name) => s.push_str(name),
            Expr::IntLiteral(_, value) => s.push_str(value),
            Expr::RealLiteral(_, value) => s.push_str(value),
            Expr::StringLiteral(_, value) => {
                write!(s, "\"{}\"", value).unwrap()
            }
            Expr::CharLiteral(_, value) => write!(s, "#\"{}\"", value).unwrap(),
            Expr::BoolLiteral(_, value) => {
                s.push_str(if *value { "true" } else { "false" })
            }
            Expr::UnitLiteral(_) => s.push_str("()"),
            _ => s.push_str("<expr>"), // TODO: implement for all variants
        }
    }

    fn span(&self) -> Span {
        match self {
            Expr::IntLiteral(span, _) => *span,
            Expr::RealLiteral(span, _) => *span,
            Expr::StringLiteral(span, _) => *span,
            Expr::CharLiteral(span, _) => *span,
            Expr::BoolLiteral(span, _) => *span,
            Expr::UnitLiteral(span) => *span,
            Expr::Identifier(span, _) => *span,
            _ => panic!("Span not implemented for this expression variant"),
        }
    }
}

impl Ast for Decl {
    fn unparse(&self, s: &mut String) {
        match self {
            Decl::Val(_, binds) => {
                s.push_str("val ");
                if let Some(first_bind) = binds.first() {
                    if first_bind.rec {
                        s.push_str("rec ");
                    }
                    first_bind.pat.unparse(s);
                    if let Some(ref type_annotation) =
                        first_bind.type_annotation
                    {
                        s.push_str(": ");
                        match type_annotation {
                            Type::Con(_, name) => s.push_str(name),
                            _ => s.push_str("<type>"),
                        }
                    }
                    s.push_str(" = ");
                    first_bind.expr.unparse(s);
                }
            }
            _ => s.push_str("<decl>"),
        }
    }

    fn span(&self) -> Span {
        match self {
            Decl::Val(span, _) => *span,
            Decl::Fun(span, _) => *span,
            Decl::Type(span, _) => *span,
            Decl::Datatype(span, _) => *span,
        }
    }
}

impl Ast for Pat {
    fn unparse(&self, s: &mut String) {
        match self {
            Pat::Identifier(_, name) => s.push_str(name),
            Pat::Wildcard(_) => s.push('_'),
            _ => s.push_str("<pat>"),
        }
    }

    fn span(&self) -> Span {
        match self {
            Pat::Wildcard(span) => *span,
            Pat::Identifier(span, _) => *span,
            _ => panic!("Span not implemented for this pattern variant"),
        }
    }
}

/// Builds a statement (expression or declaration) from parsed pairs.
pub fn build_statement(pair: Pair<Rule>) -> Node {
    let inner = pair.into_inner().next().unwrap();
    match inner.as_rule() {
        Rule::expr => Node::Expr(build_expr(inner)),
        Rule::decl => Node::Decl(build_decl(inner)),
        _ => panic!("Unexpected rule in statement: {:?}", inner.as_rule()),
    }
}

/// Builds an expression from parsed pairs.
pub fn build_expr(pair: Pair<Rule>) -> Expr {
    match pair.as_rule() {
        Rule::expr => {
            // If it's an expr rule, get the inner expression
            let inner = pair.into_inner().next().unwrap();
            build_expr(inner)
        }
        Rule::expr_annotated => {
            // Handle annotated expressions
            let inner = pair.into_inner().next().unwrap();
            build_expr(inner)
        }
        Rule::expr_implies => {
            let inner = pair.into_inner().next().unwrap();
            build_expr(inner)
        }
        Rule::expr_orelse => {
            let inner = pair.into_inner().next().unwrap();
            build_expr(inner)
        }
        Rule::expr_andalso => {
            let inner = pair.into_inner().next().unwrap();
            build_expr(inner)
        }
        Rule::expr_o => {
            let inner = pair.into_inner().next().unwrap();
            build_expr(inner)
        }
        Rule::expr_relational => {
            let inner = pair.into_inner().next().unwrap();
            build_expr(inner)
        }
        Rule::expr_cons => {
            let inner = pair.into_inner().next().unwrap();
            build_expr(inner)
        }
        Rule::expr_additive => {
            let inner = pair.into_inner().next().unwrap();
            build_expr(inner)
        }
        Rule::expr_multiplicative => {
            let inner = pair.into_inner().next().unwrap();
            build_expr(inner)
        }
        Rule::expr_over => {
            let inner = pair.into_inner().next().unwrap();
            build_expr(inner)
        }
        Rule::expr_unary => {
            let inner = pair.into_inner().next().unwrap();
            build_expr(inner)
        }
        Rule::expr_application => {
            let inner = pair.into_inner().next().unwrap();
            build_expr(inner)
        }
        Rule::expr_postfix => {
            let inner = pair.into_inner().next().unwrap();
            build_expr(inner)
        }
        Rule::atom => {
            let inner = pair.into_inner().next().unwrap();
            build_expr(inner)
        }
        Rule::literal => build_literal(pair),
        Rule::identifier => {
            let span = Span::from_span(&pair.as_span());
            Expr::Identifier(span, pair.as_str().to_string())
        }
        _ => {
            let span = Span::from_span(&pair.as_span());
            Expr::Identifier(
                span,
                format!("<unknown_expr:{:?}>", pair.as_rule()),
            )
        }
    }
}

/// Builds a literal from parsed pairs.
pub fn build_literal(pair: Pair<Rule>) -> Expr {
    match pair.as_rule() {
        Rule::literal => {
            // If it's a literal rule, get the inner literal type
            let inner = pair.into_inner().next().unwrap();
            build_literal(inner)
        }
        Rule::numeric_literal => {
            // Handle numeric literal by getting the specific type inside
            let inner = pair.into_inner().next().unwrap();
            build_literal(inner)
        }
        Rule::non_negative_integer_literal | Rule::negative_integer_literal => {
            let span = Span::from_span(&pair.as_span());
            Expr::IntLiteral(span, pair.as_str().to_string())
        }
        Rule::real_literal | Rule::scientific_literal => {
            let span = Span::from_span(&pair.as_span());
            Expr::RealLiteral(span, pair.as_str().to_string())
        }
        Rule::string_literal => {
            let span = Span::from_span(&pair.as_span());
            let content = pair.as_str();
            // Remove quotes and handle escapes
            let unquoted = &content[1..content.len() - 1];
            Expr::StringLiteral(span, unquoted.to_string())
        }
        Rule::char_literal => {
            let span = Span::from_span(&pair.as_span());
            let content = pair.as_str();
            // Remove #" and "
            let unquoted = &content[2..content.len() - 1];
            Expr::CharLiteral(span, unquoted.to_string())
        }
        Rule::bool_literal => {
            let span = Span::from_span(&pair.as_span());
            let value = pair.as_str() == "true";
            Expr::BoolLiteral(span, value)
        }
        Rule::unit_literal => {
            let span = Span::from_span(&pair.as_span());
            Expr::UnitLiteral(span)
        }
        _ => {
            let span = Span::from_span(&pair.as_span());
            Expr::IntLiteral(
                span,
                format!("<unknown_literal:{:?}>", pair.as_rule()),
            )
        }
    }
}

/// Builds a declaration from parsed pairs.
pub fn build_decl(pair: Pair<Rule>) -> Decl {
    let inner = pair.into_inner().next().unwrap();
    match inner.as_rule() {
        Rule::val_decl => build_val_decl(inner),
        _ => panic!("Unexpected declaration rule: {:?}", inner.as_rule()),
    }
}

/// Builds a value declaration from parsed pairs.
pub fn build_val_decl(pair: Pair<Rule>) -> Decl {
    let span = Span::from_span(&pair.as_span());
    let mut inner = pair.into_inner();

    // The grammar should produce: "val" pat [":" type_expr] ["=" expr]
    // We need to process all the inner parts
    let mut has_rec = false;
    let mut pat = None;
    let mut type_annotation = None;
    let mut expr = None;

    while let Some(part) = inner.next() {
        match part.as_rule() {
            Rule::val_bind => {
                // Process the val_bind rule
                let mut val_inner = part.into_inner();
                while let Some(val_part) = val_inner.next() {
                    match val_part.as_rule() {
                        Rule::pat => pat = Some(build_pat(val_part)),
                        Rule::type_expr => {
                            type_annotation = Some(build_type(val_part))
                        }
                        Rule::expr => expr = Some(build_expr(val_part)),
                        _ if val_part.as_str() == "rec" => has_rec = true,
                        _ => {} // Skip other tokens like "=" and ":"
                    }
                }
            }
            Rule::pat => pat = Some(build_pat(part)),
            Rule::type_expr => type_annotation = Some(build_type(part)),
            Rule::expr => expr = Some(build_expr(part)),
            _ if part.as_str() == "rec" => has_rec = true,
            _ => {} // Skip tokens like "val", "=", ":"
        }
    }

    let val_bind = ValBind {
        rec: has_rec,
        pat: pat.unwrap_or_else(|| {
            let dummy_span = Span { start: 0, end: 0 };
            Pat::Identifier(dummy_span, "<missing_pat>".to_string())
        }),
        type_annotation,
        expr: expr.unwrap_or_else(|| {
            let dummy_span = Span { start: 0, end: 0 };
            Expr::UnitLiteral(dummy_span)
        }),
    };

    Decl::Val(span, vec![val_bind])
}

/// Builds a pattern from parsed pairs.
pub fn build_pat(pair: Pair<Rule>) -> Pat {
    match pair.as_rule() {
        Rule::pat => {
            // Recursively handle pattern rules
            let inner = pair.into_inner().next().unwrap();
            build_pat(inner)
        }
        Rule::pat_annotated => {
            let inner = pair.into_inner().next().unwrap();
            build_pat(inner)
        }
        Rule::pat_as => {
            let inner = pair.into_inner().next().unwrap();
            build_pat(inner)
        }
        Rule::pat_cons => {
            let inner = pair.into_inner().next().unwrap();
            build_pat(inner)
        }
        Rule::pat_atom => {
            let inner = pair.into_inner().next().unwrap();
            build_pat(inner)
        }
        Rule::id_pat => {
            let inner = pair.into_inner().next().unwrap();
            build_pat(inner)
        }
        Rule::identifier => {
            let span = Span::from_span(&pair.as_span());
            Pat::Identifier(span, pair.as_str().to_string())
        }
        _ => {
            let span = Span::from_span(&pair.as_span());
            Pat::Identifier(span, format!("<unknown_pat:{:?}>", pair.as_rule()))
        }
    }
}

/// Builds a type from parsed pairs.
pub fn build_type(pair: Pair<Rule>) -> Type {
    let span = Span::from_span(&pair.as_span());
    Type::Con(span, pair.as_str().to_string())
}
