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

use crate::compile::library;
use crate::compile::library::BuiltIn;
use crate::compile::type_resolver::TypeResolver;
use crate::compile::types::Type;
use crate::eval::code::{Code, LIBRARY};
use crate::eval::val::Val;
use crate::syntax::ast::{Expr, Pat, PatKind, TypeScheme};
use crate::unify::unifier::{Term, Var};
use std::collections::HashMap;
use std::fmt::Display;
use std::rc::Rc;
use strum::EnumProperty;

/// What kind of value is bound?
#[derive(Debug, Clone)]
pub enum BindType {
    Val(Term),
    Constructor(Term),
}

/// Environment for type resolution, mapping names to terms.
pub trait TypeEnv {
    /// Gets the term associated with a name.
    /// May consult or modify the `unifier` to construct the [Term].
    fn get(&self, name: &str, t: &mut TypeResolver) -> Option<BindType>;

    /// Binds a name to a term, returning a new environment.
    fn bind(&self, name: String, term: Term) -> Rc<dyn TypeEnv>;

    /// Binds multiple names to terms.
    fn bind_all(&self, bindings: &[(String, Term)]) -> Rc<dyn TypeEnv>;

    /// Creates a builder.
    fn builder(&self) -> TypeEnvBuilder;
}

impl TypeEnv for EmptyTypeEnv {
    fn get(&self, _name: &str, _t: &mut TypeResolver) -> Option<BindType> {
        None
    }

    fn bind(&self, name: String, term: Term) -> Rc<dyn TypeEnv> {
        let mut bindings = HashMap::new();
        bindings.insert(name, term);
        Rc::new(SimpleTypeEnv {
            parent: Rc::new(self.clone()),
            bindings,
        })
    }

    fn bind_all(&self, bindings: &[(String, Term)]) -> Rc<dyn TypeEnv> {
        let binding_map = bindings.iter().cloned().collect();
        Rc::new(SimpleTypeEnv {
            parent: Rc::new(self.clone()),
            bindings: binding_map,
        })
    }

    fn builder(&self) -> TypeEnvBuilder {
        TypeEnvBuilder {
            env: Rc::new(self.clone()) as Rc<dyn TypeEnv>,
        }
    }
}

impl TypeEnv for SimpleTypeEnv {
    fn get(&self, name: &str, t: &mut TypeResolver) -> Option<BindType> {
        if let Some(b) = self.bindings.get(name) {
            Some(BindType::Val(b.clone()))
        } else {
            self.parent.get(name, t)
        }
    }

    fn bind(&self, name: String, term: Term) -> Rc<dyn TypeEnv> {
        let mut new_bindings = self.bindings.clone();
        new_bindings.insert(name, term);
        Rc::new(SimpleTypeEnv {
            parent: self.parent.clone(),
            bindings: new_bindings,
        })
    }

    fn bind_all(&self, bindings: &[(String, Term)]) -> Rc<dyn TypeEnv> {
        let mut new_bindings = self.bindings.clone();
        for (name, term) in bindings {
            new_bindings.insert(name.clone(), term.clone());
        }
        Rc::new(SimpleTypeEnv {
            parent: self.parent.clone(),
            bindings: new_bindings,
        })
    }

    fn builder(&self) -> TypeEnvBuilder {
        TypeEnvBuilder {
            env: Rc::new(self.clone()),
        }
    }
}

impl TypeEnv for FunTypeEnv {
    fn get(&self, name: &str, tr: &mut TypeResolver) -> Option<BindType> {
        if let Some(b) = library::lookup(name) {
            match b {
                BuiltIn::Fn(f) => {
                    if let Some((t, _)) = LIBRARY.fn_map.get(&f) {
                        let term = tr.type_to_term(t);
                        return Some(
                            if f.get_bool("constructor").unwrap_or(false) {
                                BindType::Constructor(Term::Variable(term))
                            } else {
                                BindType::Val(Term::Variable(term))
                            },
                        );
                    }
                }
                BuiltIn::Record(r) => {
                    if let Some((t, _)) = LIBRARY.structure_map.get(&r) {
                        return Some(BindType::Val(Term::Variable(
                            tr.type_to_term(t),
                        )));
                    }
                }
            }
        }
        self.parent.get(name, tr)
    }

    fn bind(&self, name: String, term: Term) -> Rc<dyn TypeEnv> {
        // Cannot mutate a FunTypeEnv. Create a SimpleTypeEnv with this
        // FunTypeEnv as its parent.
        let mut bindings = HashMap::new();
        bindings.insert(name, term);
        Rc::new(SimpleTypeEnv {
            parent: Rc::new(self.clone()),
            bindings,
        })
    }

    fn bind_all(&self, bindings: &[(String, Term)]) -> Rc<dyn TypeEnv> {
        // Cannot mutate a FunTypeEnv. Create a SimpleTypeEnv with this
        // FunTypeEnv as its parent.
        let binding_map = bindings.iter().cloned().collect();
        Rc::new(SimpleTypeEnv {
            parent: Rc::new(self.clone()),
            bindings: binding_map,
        })
    }

    fn builder(&self) -> TypeEnvBuilder {
        TypeEnvBuilder {
            env: Rc::new(self.clone()),
        }
    }
}

/// Empty type environment.
#[derive(Debug, Clone)]
pub struct EmptyTypeEnv;

/// Simple type environment backed by a HashMap,
/// delegating to a parent.
#[derive(Clone)]
pub struct SimpleTypeEnv {
    pub parent: Rc<dyn TypeEnv>,
    pub bindings: HashMap<String, Term>,
}

/// Type alias for the resolver function to reduce complexity.
pub type ResolverFn =
    Rc<dyn Fn(&str, &mut dyn TypeSchemeResolver) -> Option<Term>>;

/// Simple type environment backed by a function from names to terms.
/// Delegates to a parent.
#[derive(Clone)]
pub struct FunTypeEnv {
    pub parent: Rc<dyn TypeEnv>,
}

pub trait TypeSchemeResolver {
    /// Converts a type scheme AST to a term.
    fn deduce_type_scheme(&mut self, type_scheme: &TypeScheme) -> Rc<Var>;
}

/// Holds a type environment while it is mutated.
///
/// In the future, an implementation may consolidate environments.
pub struct TypeEnvBuilder {
    env: Rc<dyn TypeEnv>,
}

impl TypeEnvBuilder {
    pub fn push(&mut self, name: String, term: Term) {
        self.env = self.env.bind(name, term);
    }

    pub fn build(self) -> Rc<dyn TypeEnv> {
        self.env
    }
}

/// Identifier. A pattern that just consists of a name. It maps to
/// a [PatKind::Identifier] or [PatKind::As].
///
/// The following declaration binds patterns `w`, `x`, `y`, and `z`:
///
/// ```sml
/// val (w, x) as y = (1, 2)
/// and z = 3
/// ```
#[derive(Debug, Clone, PartialEq)]
pub struct Id {
    pub name: String,
    pub ordinal: usize,
    // pub type_: Box<Type>,
}

impl Id {
    pub fn new(name: &str, ordinal: usize) -> Self {
        Self {
            name: name.to_string(),
            ordinal,
        }
    }
}

/// Binding of a name to a type and a value.
///
/// Used in [crate::shell::main::Environment].
#[derive(Debug, Clone)]
pub struct Binding {
    pub id: Id,
    // pub term: Term,
    pub overload_id: Option<String>,
    pub value: Option<Val>,
}

impl Binding {}

impl Binding {
    pub(crate) fn get_type(&self) -> Box<Type> {
        todo!()
    }

    pub(crate) fn of_code(_p0: &PatKind, _p1: Code) -> Binding {
        todo!()
    }

    pub(crate) fn inst_of(_x1: &Pat, _x10: &Expr) -> Self {
        todo!()
    }

    pub(crate) fn inst_of_val(_x1: Pat, _x2: Pat, _x10: &Val) -> Self {
        todo!()
    }

    pub(crate) fn of_name(name: &str) -> Self {
        Self::of_name_value(name, &None)
    }

    pub(crate) fn of_name_value(name: &str, value: &Option<Val>) -> Self {
        Binding {
            id: Id::new(name, 0),
            value: value.clone(),
            overload_id: None,
        }
    }

    pub(crate) fn of(pat: &Pat, val: &Val) -> Self {
        let name1 = match pat.kind.clone() {
            PatKind::Identifier(name) => name,
            PatKind::As(name, _pat) => name,
            _ => panic!("Not an identifier or as pattern"),
        };
        Binding {
            id: Id::new(&name1, 0),
            value: Some(val.clone()),
            overload_id: None,
        }
    }

    pub(crate) fn inst(_p0: Pat, _p1: Option<&str>, _p2: Expr) -> Self {
        todo!()
    }
}

impl Display for Binding {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Some(ref v) = self.value {
            write!(f, "{}: {}", self.id.name, v)
        } else {
            write!(f, "{}: none", self.id.name)
        }
    }
}
