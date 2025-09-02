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

use crate::compile::unifier::{Term, Var};
use crate::syntax::ast::TypeScheme;
use std::collections::HashMap;
use std::rc::Rc;

/// Environment for type resolution, mapping names to terms.
pub trait TypeEnv {
    /// Gets the term associated with a name.
    /// May consult or modify the `unifier` to construct the [Term].
    fn get(&self, name: &str, t: &mut dyn TypeSchemeResolver) -> Option<Term>;

    /// Binds a name to a term, returning a new environment.
    fn bind(&self, name: String, term: Term) -> Rc<dyn TypeEnv>;

    /// Binds multiple names to terms.
    fn bind_all(&self, bindings: &[(String, Term)]) -> Rc<dyn TypeEnv>;

    /// Creates a builder.
    fn builder(&self) -> TypeEnvBuilder;
}

impl TypeEnv for EmptyTypeEnv {
    fn get(
        &self,
        _name: &str,
        _t: &mut dyn TypeSchemeResolver,
    ) -> Option<Term> {
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
    fn get(&self, name: &str, t: &mut dyn TypeSchemeResolver) -> Option<Term> {
        if let Some(b) = self.bindings.get(name) {
            Some(b.clone())
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
    fn get(&self, name: &str, t: &mut dyn TypeSchemeResolver) -> Option<Term> {
        if let Some(b) = (self.resolve)(name, t) {
            Some(b)
        } else {
            self.parent.get(name, t)
        }
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

/// Simple type environment backed by a function from names to terms.
/// delegating to a parent.
#[derive(Clone)]
pub struct FunTypeEnv {
    pub parent: Rc<dyn TypeEnv>,
    pub resolve: Rc<dyn Fn(&str, &mut dyn TypeSchemeResolver) -> Option<Term>>,
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
