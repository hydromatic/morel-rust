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

use crate::compile::core::Pat;
use crate::compile::library::{BuiltIn, BuiltInFunction, BuiltInRecord};
use crate::compile::type_env::Binding;
use crate::compile::type_resolver::TypeMap;
use crate::eval::code::EagerV2::SysSet;
use crate::eval::session::Session;
use crate::eval::val::Val;
use crate::shell::main::{MorelError, Shell};
use std::collections::BTreeMap;
use std::rc::Rc;
use std::sync::LazyLock;
use strum::EnumProperty;

/// Effects that can be applied to modify the state of the current shell or
/// session.
///
/// This allows evaluation to be pure while still describing side effects.
/// Shell and session are immutable during statement execution; statements such
/// as `Sys.set("output", "tabular")` do not modify the session while the
/// command is executing; the shell mutates its own and the session state after
/// the command completes.
#[derive(Debug, Clone)]
pub enum Effect {
    /// Emits an output line.
    EmitLine(String),
    /// Sets a shell property.
    SetShellProp(String, Val),
    /// Sets a session property.
    SetSessionProp(String, Val),
    /// Adds a binding to the environment.
    AddBinding(Binding),
}

/// Generated code that can be evaluated.
#[derive(Clone)]
pub enum Code {
    // lint: sort until '^}$'
    ApplyE2(Eager2),
    ApplyEV2(EagerV2, Box<Code>, Box<Code>),
    Constant(Val),
    Link(Rc<Option<Code>>),
    Match(Vec<(Pat, Code)>, Rc<Code>),
    Tuple(Vec<Code>),
}

impl Code {
    pub fn eval(&self, v: &mut EvalEnv) -> Result<Val, MorelError> {
        match &self {
            // lint: sort until '#}' where '##Code::'
            Code::ApplyE2(_) => {
                todo!()
            }
            Code::ApplyEV2(eager, code0, code1) => {
                let v0 = code0.eval(v)?;
                let v1 = code1.eval(v)?;
                eager.apply(v, v0, v1)
            }
            Code::Constant(c) => Ok(c.clone()),
            Code::Link(_) => {
                todo!()
            }
            Code::Match(_, _) => {
                todo!()
            }
            Code::Tuple(codes) => {
                let mut values = Vec::with_capacity(codes.capacity());
                for code in codes {
                    values.push(code.eval(v)?);
                }
                Ok(Val::List(values))
            }
        }
    }
}

/// Utilities for [Code].
pub struct Codes;

impl Codes {
    pub(crate) fn constant(v: Val) -> Box<Code> {
        Box::new(Code::Constant(v))
    }

    pub(crate) fn apply(f: BuiltInFunction, codes: &[Box<Code>]) -> Box<Code> {
        match built_in_to_applicable(f) {
            Some(impl_) => Self::native(impl_, codes),
            _ => todo!("{:?}", f),
        }
    }

    pub(crate) fn native(impl_: Impl, codes: &[Box<Code>]) -> Box<Code> {
        match impl_ {
            // lint: sort until '#}' where '##Impl::'
            Impl::E2(e2) => Box::new(Code::ApplyE2(e2)),
            Impl::EV2(ev2) => {
                // TODO: handle cases like 'let args = (1, 2) in f args
                // end'; see Gather in Morel-Java
                assert_eq!(codes.len(), 2);
                Box::new(Code::ApplyEV2(
                    ev2,
                    codes[0].clone(),
                    codes[1].clone(),
                ))
            }
        }
    }

    pub fn list(codes: &[Code]) -> Box<Code> {
        Self::tuple(codes)
    }

    pub fn tuple(codes: &[Code]) -> Box<Code> {
        Box::new(Code::Tuple(codes.to_vec()))
    }
}

/// Evaluation environment for [Code].
///
/// Function parameters holding an evaluation environment are typically named
/// `v`.
pub enum EvalEnv<'a> {
    /// Trivial environment with no session. To be used for
    /// simple tasks such as compilation.
    Empty,

    /// Root environment with immutable references and effects collector.
    Root(&'a Session, &'a Shell, &'a mut Vec<Effect>, &'a TypeMap),

    /// Child environment.
    Child(&'a mut EvalEnv<'a>),
}

impl EvalEnv<'_> {
    /// Emits an effect to be applied later.
    pub fn emit_effect(&mut self, effect: Effect) {
        match self {
            EvalEnv::Empty => {
                // No effects can be emitted in the empty environment.
            }
            EvalEnv::Root(_session, _shell, effects, _type_map) => {
                effects.push(effect);
            }
            EvalEnv::Child(parent) => {
                // For child environments, we need to delegate to the parent.
                // This requires careful handling of the mutable borrow.
                parent.emit_effect(effect);
            }
        }
    }

    /// Returns the root.
    pub fn root(&self) -> Option<(&Session, &Shell, &TypeMap)> {
        match self {
            EvalEnv::Empty => None,
            EvalEnv::Root(session, shell, _effects, type_map) => {
                Some((session, shell, type_map))
            }
            EvalEnv::Child(parent) => parent.root(),
        }
    }

    /// Returns the session.
    pub fn session(&self) -> Option<&Session> {
        if let Some((session, _shell, _type_map)) = self.root() {
            Some(session)
        } else {
            None
        }
    }

    /// Returns the shell.
    pub fn shell(&self) -> Option<&Shell> {
        if let Some((_, shell, _type_map)) = self.root() {
            Some(shell)
        } else {
            None
        }
    }

    /// Returns the type map.
    pub fn type_map(&self) -> Option<&TypeMap> {
        if let Some((_session, _shell, type_map)) = self.root() {
            Some(type_map)
        } else {
            None
        }
    }
}

/// Implementation of a function is an [Eager2] or ...
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Impl {
    E2(Eager2),
    EV2(EagerV2),
}

pub struct Applicable;

/// Function implementation that takes two arguments.
/// The arguments are eagerly evaluated before the function is called.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Eager2 {
    // lint: sort until '#}'
    IntPlus,
}

/// Function implementation that takes two arguments and an evaluation
/// environment.
/// The arguments are eagerly evaluated before the function is called.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum EagerV2 {
    // lint: sort until '#}'
    SysSet,
}

impl EagerV2 {
    fn implements(
        &self,
        map: &mut BTreeMap<BuiltInFunction, Impl>,
        f: BuiltInFunction,
    ) {
        map.insert(f, Impl::EV2(*self));
    }

    // Passing Val by value is OK because it is small.
    #[allow(clippy::needless_pass_by_value)]
    fn apply(
        &self,
        v: &mut EvalEnv,
        a0: Val,
        a1: Val,
    ) -> Result<Val, MorelError> {
        match &self {
            // lint: sort until '#}' where '##[A-Z]'
            SysSet => {
                let prop = a0.expect_string();
                let val = a1;
                v.emit_effect(Effect::SetShellProp(prop, val));
                Ok(Val::Unit)
            }
        }
    }
}

impl Eager2 {
    // Passing Val by value is OK because it is small.
    #[allow(clippy::needless_pass_by_value)]
    fn apply(&self, a0: Val, a1: Val) -> Val {
        match &self {
            // lint: sort until '#}' where '##[A-Z]'
            Eager2::IntPlus => Val::Int(a0.expect_int() + a1.expect_int()),
        }
    }

    fn implements(
        &self,
        map: &mut BTreeMap<BuiltInFunction, Impl>,
        f: BuiltInFunction,
    ) {
        map.insert(f, Impl::E2(*self));
    }
}

pub struct Lib {
    pub fn_map: BTreeMap<BuiltInFunction, Impl>,
    pub rec_map: BTreeMap<BuiltInRecord, BTreeMap<String, Impl>>,
}

pub static LIBRARY: LazyLock<Lib> = LazyLock::new(|| {
    #[allow(clippy::enum_glob_use)]
    use crate::compile::library::BuiltInFunction::*;
    use crate::compile::library::BuiltInRecord::Sys;

    let mut fn_map: BTreeMap<BuiltInFunction, Impl> = BTreeMap::new();

    // lint: sort until '^$' erase '^.*, '
    Eager2::IntPlus.implements(&mut fn_map, IntPlus);
    EagerV2::SysSet.implements(&mut fn_map, SysSet);

    // Pass over the table and make sure that if a built-in has a parent,
    // its parent exists and contains the child.
    let mut rec_map: BTreeMap<BuiltInRecord, BTreeMap<String, Impl>> =
        BTreeMap::new();
    add_rec(&mut rec_map, &fn_map, Sys);

    Lib { fn_map, rec_map }
});

fn add_rec(
    rec_map: &mut BTreeMap<BuiltInRecord, BTreeMap<String, Impl>>,
    fn_map: &BTreeMap<BuiltInFunction, Impl>,
    r: BuiltInRecord,
) {
    let mut child_map = BTreeMap::new();
    let parent_name = r.get_str("name").unwrap();
    for (f, imp) in fn_map {
        if let Some((parent, name)) = BuiltIn::Fn(*f).heritage()
            && parent == parent_name
        {
            child_map.insert(name.to_string(), *imp);
        }
    }
    rec_map.insert(r, child_map);
}

fn built_in_to_applicable(b: BuiltInFunction) -> Option<Impl> {
    LIBRARY.fn_map.get(&b).copied()
}
