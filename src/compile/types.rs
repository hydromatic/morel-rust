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

use crate::unify::unifier::Term;
use std::collections::{BTreeMap, HashMap};
use std::fmt::{Display, Formatter};

/// Represents a resolved type in the system.
#[derive(Debug, Clone, PartialEq)]
pub enum Type {
    Primitive(PrimitiveType),
    Fn(Box<Type>, Box<Type>),

    /// `Record(progressive, arg_name_types)` represents the type
    /// `{name0: arg0, ... nameN: argN}`. If `progressive`, the
    /// arguments may grow over time.
    Record(bool, BTreeMap<Label, Type>),

    /// `List(element_type)` represents the type `element_type list`.
    List(Box<Type>),

    /// `Tuple(args)` represents the type `arg0 * ... * argN`.
    Tuple(Vec<Type>),
    Variable(TypeVariable),
    Named(Vec<Type>, String),

    /// `Alias(name, type_, args)` represents the declaration
    /// `type name = args type_`; for example,
    /// `type int_pair_list = (int * int) list`.
    Alias(String, Box<Type>, Vec<Type>),
    Data(String, Vec<Type>),

    /// `Forall(type_, parameter_count)` represents the type
    /// `forall tyVars ... type_`, where there are parameter_count
    /// type variables `'a`, `'b`, etc.
    Forall(Box<Type>, usize),

    /// `Multi(types)` represents an overloaded type `type0 or ... typeN`.
    Multi(Vec<Type>),
}

impl Type {
    /// Returns the definition of a record type. Panics on any other type,
    /// including a tuple type.
    pub fn expect_record(&self) -> (bool, &BTreeMap<Label, Type>) {
        match self {
            Type::Record(progressive, fields) => (*progressive, fields),
            _ => panic!("Expected record type"),
        }
    }

    /// Returns a list of this type's fields. Panics if this type is not a
    /// record or tuple.
    pub fn field_types(&self) -> Vec<Type> {
        match self {
            Type::Record(_, fields) => {
                fields.values().cloned().collect::<Vec<_>>()
            }
            Type::Tuple(field_types) => field_types.to_vec(),
            _ => panic!("Expected record type"),
        }
    }

    /// Returns the ordinal of a field with a given name.
    /// Always returns None if not a record or tuple type.
    pub fn lookup_field(&self, field_name: &str) -> Option<usize> {
        match self {
            Type::Record(_, fields) => fields
                .iter()
                .enumerate()
                .find(|(_, (name, _))| name.matches(field_name))
                .map(|(i, _)| i),
            Type::Tuple(field_types) => {
                field_name
                    .parse::<usize>()
                    .ok()
                    .filter(|&i| i > 0 && i <= field_types.len())
                    .map(|i| i - 1) // Convert from 1-based to 0-based indexing
            }
            _ => None,
        }
    }

    /// Describes a list of types, with given left and right precedence
    /// and given opening, separator, and closing strings.
    fn describe_list(
        types: &[Type],
        f: &mut Formatter,
        op: &Op,
        mut left: u8,
        mut right: u8,
    ) -> std::fmt::Result {
        let surround =
            if op.always_surround || left > op.left || right > op.right {
                left = 0;
                right = 0;
                true
            } else {
                false
            };
        if surround {
            f.write_str(op.open)?;
        }
        for (i, type_) in types.iter().enumerate() {
            if i == 0 {
                type_.describe(f, left, op.right)?;
            } else if i == types.len() - 1 {
                f.write_str(op.sep)?;
                type_.describe(f, op.right, right)?;
            } else {
                f.write_str(op.sep)?;
                type_.describe(f, op.right, op.left)?;
            }
        }
        if surround {
            f.write_str(op.close)?;
        }
        Ok(())
    }

    fn describe(
        &self,
        f: &mut Formatter<'_>,
        left: u8,
        right: u8,
    ) -> std::fmt::Result {
        match self {
            // lint: sort until '#}' where '##Type::'
            Type::Alias(name, _, _) => f.write_str(name),
            Type::Fn(param, result) => {
                const OP: Op = Op::FN;
                if left > OP.left || right > OP.right {
                    write!(f, "(")?;
                    self.describe(f, 0, 0)?;
                    return write!(f, ")");
                }
                param.describe(f, left, OP.left)?;
                write!(f, " -> ")?;
                result.describe(f, OP.right, right)
            }
            Type::List(elem_type) => {
                const OP: Op = Op::APPLY;
                if left > OP.left || right > OP.right {
                    write!(f, "(")?;
                    self.describe(f, 0, 0)?;
                    return write!(f, ")");
                }
                elem_type.describe(f, left, OP.right)?;
                write!(f, " list")
            }
            Type::Named(args, name) => {
                const OP: Op = Op::LIST;
                if args.len() == 1 {
                    args.first().unwrap().describe(f, left, OP.left)?;
                } else {
                    Self::describe_list(args, f, &OP, left, right)?;
                }
                write!(f, " {}", name)
            }
            Type::Primitive(p) => f.write_str(p.as_str()),
            Type::Record(progressive, fields) => {
                f.write_str("{")?;
                for (i, (name, field_type)) in fields.iter().enumerate() {
                    if i > 0 {
                        f.write_str(", ")?;
                    }
                    write!(f, "{}:{}", name, field_type)?;
                }
                if *progressive {
                    if fields.is_empty() {
                        write!(f, "...")?;
                    } else {
                        write!(f, ", ...")?;
                    }
                }
                f.write_str("}")
            }
            Type::Tuple(types) => {
                const OP: Op = Op::TUPLE;
                Self::describe_list(types, f, &OP, left, right)?;
                Ok(())
            }
            Type::Variable(var) => f.write_str(var.name().as_str()),
            _ => todo!(),
        }
    }

    pub fn contains_progressive(&self) -> bool {
        false // TODO
    }
}

impl Display for Type {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        self.describe(f, 0, 0)
    }
}

/// Primitive types in the ML-like language.
#[derive(Debug, Clone, PartialEq)]
pub enum PrimitiveType {
    Unit,
    Bool,
    Int,
    Real,
    String,
    Char,
}

impl PrimitiveType {
    pub fn as_str(&self) -> &'static str {
        match &self {
            PrimitiveType::Bool => "bool",
            PrimitiveType::Char => "char",
            PrimitiveType::Int => "int",
            PrimitiveType::Real => "real",
            PrimitiveType::String => "string",
            PrimitiveType::Unit => "unit",
        }
    }

    pub fn parse_name(name: &str) -> Option<PrimitiveType> {
        match name {
            "bool" => Some(PrimitiveType::Bool),
            "char" => Some(PrimitiveType::Char),
            "int" => Some(PrimitiveType::Int),
            "real" => Some(PrimitiveType::Real),
            "string" => Some(PrimitiveType::String),
            "unit" => Some(PrimitiveType::Unit),
            _ => None,
        }
    }
}

/// Type variable.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct TypeVariable {
    pub id: usize,
}

impl TypeVariable {
    /// Creates a type variable with a given ordinal.
    pub(crate) fn new(id: usize) -> Self {
        TypeVariable { id }
    }

    /// Returns the name of this type variable: "'a" for 0, "'b" for 1,
    /// "'z" for 25, "'ba" for 26, "'bb" for 27, etc.
    pub fn name(&self) -> String {
        let mut s = String::new();
        let mut i = self.id;
        loop {
            let c = (b'a' + (i % 26) as u8) as char;
            s.push(c);
            i /= 26;
            if i == 0 {
                break;
            }
        }
        s.push('\'');
        s.chars().rev().collect()
    }
}

/// Label for a field in a record type.
///
/// Has a sort order that puts numeric fields first, in numeric order.
#[derive(Debug, Clone, Eq, Ord, PartialOrd, PartialEq)]
pub enum Label {
    Ordinal(usize),
    String(String),
}

impl Label {
    /// Returns whether this label is equal to a string.
    pub fn matches(&self, name: &str) -> bool {
        match &self {
            Label::Ordinal(i) => i.to_string().eq(name),
            Label::String(s) => s.eq(name),
        }
    }

    /// Returns whether a collection of labels is the ordinal labels
    /// \[1, 2, ... N\].
    pub fn are_contiguous<I>(labels: I) -> bool
    where
        I: IntoIterator<Item = Label>,
    {
        let mut i: usize = 1;
        for label in labels.into_iter() {
            match label {
                Label::Ordinal(j) if i == j => {
                    i += 1;
                }
                _ => {
                    return false;
                }
            }
        }
        true
    }
}

impl<T: AsRef<str> + Into<String>> From<T> for Label {
    /// Converts a string to a label. If the string is a natural number, it
    /// becomes a [Label::Ordinal], otherwise a [Label::String].
    fn from(s: T) -> Label {
        s.as_ref()
            .parse::<usize>()
            .map_or_else(|_| Label::String(s.as_ref().into()), Label::Ordinal)
    }
}

impl Display for Label {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Label::String(s) => write!(f, "{}", s),
            Label::Ordinal(i) => write!(f, "{}", i),
        }
    }
}

/// Operator definition. Includes left and right precedence, and the opening,
/// closing, and separator strings to use when printing a list.
pub struct Op {
    pub left: u8,
    pub right: u8,
    pub open: &'static str,
    pub close: &'static str,
    pub sep: &'static str,
    pub always_surround: bool,
}

impl Op {
    /// Creates an operator definition.
    const fn new(
        left: u8,
        right: u8,
        open: &'static str,
        sep: &'static str,
        close: &'static str,
        always_surround: bool,
    ) -> Self {
        Op {
            left,
            right,
            open,
            close,
            sep,
            always_surround,
        }
    }

    /// The list operator has a low precedence. An example is `(int, string)`
    /// that appears before the type application `(int, string) tree`.
    pub const LIST: Op = Op::new(16, 17, "(", ", ", ")", true);

    /// The function arrow "->" is right-associative and has a lower precedence
    /// than the tuple constructor "*".
    pub const FN: Op = Op::new(13, 12, "(", " -> ", ")", false);

    /// The tuple constructor "*" or product type operator is left-associative
    /// and has a lower precedence than type-application.
    pub const TUPLE: Op = Op::new(14, 15, "(", " * ", ")", false);

    /// The type-application operator is right-associative and has a
    /// high precedence. An example is `int option list`:
    ///
    /// ```sml
    /// [SOME 0];
    /// val it = [SOME 0] : int option list
    /// ```
    pub const APPLY: Op = Op::new(16, 17, "", " ", "", false);
}

#[cfg(test)]
mod tests {
    use crate::compile::types::TypeVariable;

    #[test]
    fn test_type_variable() {
        let a = TypeVariable::new(0);
        let b = TypeVariable::new(1);
        assert_ne!(a, b);

        assert_eq!(a.name(), "'a");
        assert_eq!(b.name(), "'b");
        assert_eq!(TypeVariable::new(25).name(), "'z");
        assert_eq!(TypeVariable::new(26).name(), "'ba");
        assert_eq!(TypeVariable::new(27).name(), "'bb");
    }

    #[test]
    fn test_are_contiguous_integers() {
        use crate::compile::types::are_contiguous_integers;

        fn check(strings: &[&str]) -> bool {
            let owned: Vec<String> =
                strings.iter().map(|s| s.to_string()).collect();
            let refs: Vec<&String> = owned.iter().collect();
            are_contiguous_integers(&refs)
        }

        assert!(check(&[])); // Empty collection
        assert!(check(&["1"])); // Single element
        assert!(check(&["1", "2", "3"])); // Contiguous integers
        assert!(!check(&["1", "3", "4"])); // Missing "2"
        assert!(!check(&["0", "1", "2"])); // Wrong start
        assert!(!check(&["a", "b"])); // Non-numeric
    }
}

/// Returns whether the collection is `["1", "2", ... n]`.
///
/// See also: [ordinal_names].
pub(crate) fn are_contiguous_integers<I, S>(strings: I) -> bool
where
    I: IntoIterator<Item = S>,
    S: AsRef<str>,
{
    for (i, string) in strings.into_iter().enumerate() {
        let expected = (i + 1).to_string();
        if string.as_ref() != expected {
            return false;
        }
    }
    true
}

/// Returns a list of strings ["1", ..., n].
pub(crate) fn ordinal_names(n: usize) -> Vec<String> {
    let mut v = vec![];
    for i in 0..n {
        v.push((i + 1).to_string());
    }
    v
}

/// Substitution mapping type variables to unifier variables.
#[derive(Debug, Clone)]
#[allow(dead_code)]
pub enum Subst {
    Empty,
    Cons {
        parent: Box<Subst>,
        type_var: TypeVariable,
        variable: Term,
    },
}

impl Subst {
    /// Creates a new substitution by adding a (type_var, variable) mapping.
    pub fn plus(&self, type_var: &TypeVariable, variable: Term) -> Self {
        Subst::Cons {
            parent: Box::new(self.clone()),
            type_var: type_var.clone(),
            variable,
        }
    }

    /// Gets the variable associated with a type variable.
    pub fn get(&self, type_var: &TypeVariable) -> Option<Term> {
        let mut current = self;
        loop {
            match current {
                Subst::Empty => return None,
                Subst::Cons {
                    parent,
                    type_var: current_type_var,
                    variable,
                } => {
                    if current_type_var == type_var {
                        return Some(variable.clone());
                    }
                    current = parent;
                }
            }
        }
    }
}

impl Display for Subst {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let mut map = HashMap::new(); // TODO: deterministic order
        let mut current = self;

        loop {
            match current {
                Subst::Empty => break,
                Subst::Cons {
                    parent,
                    type_var,
                    variable,
                } => {
                    map.entry(type_var.clone()).or_insert(variable.clone());
                    current = parent;
                }
            }
        }

        write!(f, "{:?}", map)
    }
}
