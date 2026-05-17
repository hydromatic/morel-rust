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

//! Abstract syntax tree for Datalog programs. Mirrors the morel-java
//! `DatalogAst` (hydromatic/morel#323).
//!
//! A Datalog program consists of declarations, facts, rules, and
//! directives. See `docs/datalog.md` for the surface syntax.

use std::collections::HashMap;
use std::fmt::{self, Display, Formatter};

/// A complete Datalog program.
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct Program {
    pub statements: Vec<Statement>,
}

impl Program {
    pub fn new(statements: Vec<Statement>) -> Self {
        Self { statements }
    }

    /// Indexes declarations by name.
    pub fn declarations(&self) -> HashMap<&str, &Declaration> {
        let mut out = HashMap::new();
        for s in &self.statements {
            if let Statement::Declaration(d) = s {
                out.insert(d.name.as_str(), d);
            }
        }
        out
    }

    pub fn inputs(&self) -> Vec<&Input> {
        self.statements
            .iter()
            .filter_map(|s| match s {
                Statement::Input(i) => Some(i),
                _ => None,
            })
            .collect()
    }

    pub fn outputs(&self) -> Vec<&Output> {
        self.statements
            .iter()
            .filter_map(|s| match s {
                Statement::Output(o) => Some(o),
                _ => None,
            })
            .collect()
    }
}

/// Top-level statement: declaration, input, output, fact, or rule.
#[derive(Clone, Eq, PartialEq, Debug)]
pub enum Statement {
    Declaration(Declaration),
    Input(Input),
    Output(Output),
    Fact(Fact),
    Rule(Rule),
}

/// A relation declaration: `.decl relation(var:type, ...)`.
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct Declaration {
    pub name: String,
    pub params: Vec<Param>,
}

impl Declaration {
    pub fn arity(&self) -> usize {
        self.params.len()
    }
}

impl Display for Declaration {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, ".decl {}(", self.name)?;
        for (i, p) in self.params.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{}", p)?;
        }
        write!(f, ")")
    }
}

/// A parameter in a relation declaration: `name:type`.
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct Param {
    pub name: String,
    pub ty: DatalogType,
}

impl Display for Param {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}:{}", self.name, self.ty)
    }
}

/// Datalog primitive types. Souffle's `symbol` and `number` are renamed
/// to `string` and `int` to match Morel.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum DatalogType {
    Int,
    String,
}

impl Display for DatalogType {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            DatalogType::Int => "int",
            DatalogType::String => "string",
        })
    }
}

/// `.input relation [file_name]`.
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct Input {
    pub relation: String,
    pub file_name: Option<String>,
}

impl Input {
    /// The effective file name: explicit if given, else `<relation>.csv`.
    pub fn effective_file_name(&self) -> String {
        self.file_name
            .clone()
            .unwrap_or_else(|| format!("{}.csv", self.relation))
    }
}

/// `.output relation`.
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct Output {
    pub relation: String,
}

/// A fact: `relation(value, ...).`
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct Fact {
    pub atom: Atom,
}

/// A rule: `head :- body.`
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct Rule {
    pub head: Atom,
    pub body: Vec<BodyAtom>,
}

/// An element of a rule body: either a positive/negated atom, or a
/// comparison.
#[derive(Clone, Eq, PartialEq, Debug)]
pub enum BodyAtom {
    Atom { atom: Atom, negated: bool },
    Comparison { left: Term, op: CompOp, right: Term },
}

/// Comparison operators usable in a rule body.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum CompOp {
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
}

impl CompOp {
    pub fn symbol(self) -> &'static str {
        match self {
            CompOp::Eq => "=",
            CompOp::Ne => "!=",
            CompOp::Lt => "<",
            CompOp::Le => "<=",
            CompOp::Gt => ">",
            CompOp::Ge => ">=",
        }
    }
}

impl Display for CompOp {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        f.write_str(self.symbol())
    }
}

/// An atom: `relation(term, ...)`.
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct Atom {
    pub name: String,
    pub terms: Vec<Term>,
}

impl Atom {
    pub fn arity(&self) -> usize {
        self.terms.len()
    }
}

/// A term: a variable, an arithmetic expression, or a constant.
#[derive(Clone, Eq, PartialEq, Debug)]
pub enum Term {
    Variable(String),
    Arith {
        left: Box<Term>,
        op: ArithOp,
        right: Box<Term>,
    },
    IntConst(i64),
    StringConst(String),
}

/// Arithmetic operators usable in terms.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum ArithOp {
    Plus,
    Minus,
    Times,
    Divide,
}

impl ArithOp {
    pub fn symbol(self) -> &'static str {
        match self {
            ArithOp::Plus => "+",
            ArithOp::Minus => "-",
            ArithOp::Times => "*",
            ArithOp::Divide => "/",
        }
    }
}

impl Display for ArithOp {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        f.write_str(self.symbol())
    }
}
