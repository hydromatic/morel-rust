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

use crate::compile::inliner::Binding as BindingInner;
use crate::eval::code::LIBRARY;
use std::collections::BTreeMap;
use std::sync::LazyLock;
use strum::{EnumCount, EnumProperty, IntoEnumIterator};
use strum_macros::{EnumCount, EnumIter, EnumProperty, EnumString};

/// Returns the datatype of a built-in function or record.
pub fn name_to_type(id: &str) -> Option<&str> {
    if let Some(b) = BY_NAME.get(id) {
        match b {
            BuiltIn::Fn(f) => f.get_str("type"),
            BuiltIn::Record(f) => f.get_str("type"),
        }
    } else {
        None
    }
}

/// Looks up a built-in function by name.
pub fn name_to_fn(id: &str) -> Option<BuiltInFunction> {
    if let Some(BuiltIn::Fn(f)) = BY_NAME.get(id) {
        Some(*f)
    } else {
        None
    }
}

/// Looks up a built-in record by name.
pub fn name_to_rec(id: &str) -> Option<BuiltInRecord> {
    if let Some(BuiltIn::Record(f)) = BY_NAME.get(id) {
        Some(*f)
    } else {
        None
    }
}

/// List of built-in functions and operators.
/// Generally wrapped in a [crate::syntax::ast::LiteralKind].`Fn`.
///
/// The types are held as string properties (accessible via strum's
/// [EnumProperty]) and are parsed and converted to terms on demand. This is a
/// win when there are a lot of built-in operators.
#[derive(Debug, Clone, Copy, Eq, Ord, PartialEq, PartialOrd)]
#[repr(u8)]
#[derive(EnumCount, EnumString, EnumProperty, EnumIter)]
pub enum BuiltInFunction {
    // lint: sort until '^}$' where '##[A-Z]'
    #[strum(props(
        p = "Bool",
        name = "op andalso",
        type = "bool * bool -> bool"
    ))]
    BoolAndAlso,
    #[strum(props(p = "G", name = "false", type = "bool"))]
    BoolFalse,
    #[strum(props(
        p = "Bool",
        name = "op if",
        type = "forall 1 bool * 'a * 'a -> 'a"
    ))]
    BoolIf,
    #[strum(props(
        p = "Bool",
        name = "op implies",
        type = "bool * bool -> bool"
    ))]
    BoolImplies,
    #[strum(props(
        p = "Bool",
        name = "op orelse",
        type = "bool * bool -> bool"
    ))]
    BoolOrElse,
    #[strum(props(p = "G", name = "true", type = "bool"))]
    BoolTrue,
    #[strum(props(p = "G", name = "op =", type = "forall 1 'a * 'a -> bool"))]
    GOpEq,
    #[strum(props(p = "G", name = "op >=", type = "forall 1 'a * 'a -> bool"))]
    GOpGe,
    #[strum(props(p = "G", name = "op >", type = "forall 1 'a * 'a -> bool"))]
    GOpGt,
    #[strum(props(p = "G", name = "op <=", type = "forall 1 'a * 'a -> bool"))]
    GOpLe,
    #[strum(props(p = "G", name = "op <", type = "forall 1 'a * 'a -> bool"))]
    GOpLt,
    #[strum(props(p = "G", name = "op <>", type = "forall 1 'a * 'a -> bool"))]
    GOpNe,
    #[strum(props(p = "Int", name = "op div", type = "int * int -> int"))]
    IntDiv,
    #[strum(props(p = "Int", name = "op -", type = "int * int -> int"))]
    IntMinus,
    #[strum(props(p = "Int", name = "op mod", type = "int * int -> int"))]
    IntMod,
    #[strum(props(p = "Int", name = "op +", type = "int * int -> int"))]
    IntPlus,
    #[strum(props(p = "Int", name = "op *", type = "int * int -> int"))]
    IntTimes,
    #[strum(props(
        p = "List",
        global = true,
        name = "nil",
        type = "forall 1 'a list"
    ))]
    ListNil,
    #[strum(props(
        p = "List",
        name = "op ::",
        type = "forall 1 'a * 'a list -> 'a list"
    ))]
    ListOpCons,
    #[strum(props(p = "Real", name = "op /", type = "real * real -> real"))]
    OptionNone,
    #[strum(props(p = "Option", name = "NONE", type = "forall 1 'a option"))]
    OptionSome,
    #[strum(props(
        p = "Option",
        name = "SOME",
        type = "forall 1 'a -> 'a option"
    ))]
    RealDivide,
    #[strum(props(
        p = "Sys",
        name = "set",
        global = true,
        type = "forall 1 string * 'a -> unit"
    ))]
    SysSet,
}

impl BuiltInFunction {
    pub(crate) fn name(&self) -> &'static str {
        self.get_str("name").unwrap()
    }
}

/// List of built-in modules.
#[derive(Debug, Clone, Copy, Eq, Ord, PartialEq, PartialOrd)]
#[repr(u8)]
#[derive(EnumCount, EnumString, EnumProperty, EnumIter)]
pub enum BuiltInRecord {
    // lint: sort until '^}$' where '##[A-Z]'
    #[strum(props(name = "Int", type = "{op +: int * int -> int"))]
    Int,
    #[strum(props(name = "Sys", type = "forall 1 {set: string * 'a -> unit}"))]
    Sys,
}

impl BuiltInRecord {
    pub(crate) fn name(&self) -> &'static str {
        self.get_str("name").unwrap()
    }
}

/// Built-in function or record.
#[repr(u8)]
#[derive(Debug, Clone, Copy, Eq, PartialEq, PartialOrd, Ord)]
pub enum BuiltIn {
    Fn(BuiltInFunction),
    Record(BuiltInRecord),
}

impl BuiltIn {
    pub fn get_type(&self) -> Option<&str> {
        match self {
            BuiltIn::Fn(f) => f.get_str("type"),
            BuiltIn::Record(r) => r.get_str("type"),
        }
    }

    /// If the built-in belongs to a record, returns the path of the parent
    /// record and the name of the built-in within its parent.
    pub(crate) fn heritage(&self) -> Option<(&str, &str)> {
        match self {
            BuiltIn::Fn(f) => {
                if let Some(p) = f.get_str("p")
                    && let Some(name) = f.get_str("name")
                {
                    Some((p, name))
                } else {
                    None
                }
            }
            BuiltIn::Record(r) => {
                if let Some(p) = r.get_str("p")
                    && let Some(name) = r.get_str("name")
                {
                    Some((p, name))
                } else {
                    None
                }
            }
        }
    }

    pub(crate) fn key(&self) -> u8 {
        match self {
            BuiltIn::Fn(f) => (*f as u8) + (BuiltInRecord::COUNT as u8),
            BuiltIn::Record(r) => *r as u8,
        }
    }
}

static BY_NAME: LazyLock<BTreeMap<&str, BuiltIn>> = LazyLock::new(|| {
    let mut map = BTreeMap::new();
    for e in BuiltInFunction::iter() {
        map.insert(e.get_str("name").unwrap(), BuiltIn::Fn(e));
    }
    for e in BuiltInRecord::iter() {
        map.insert(e.get_str("name").unwrap(), BuiltIn::Record(e));
    }
    map
});

pub(crate) fn populate_env(map: &mut BTreeMap<&str, BindingInner>) {
    for (r, fields) in LIBRARY.rec_map.clone() {
        let mut values = Vec::new();
        for val in fields.values() {
            values.push(BindingInner::Single(*val));
        }
        map.insert(r.name(), BindingInner::List(values));
    }
    for (f, imp) in LIBRARY.fn_map.clone() {
        if f.get_bool("global").is_some_and(|b| b) {
            map.insert(f.name(), BindingInner::Single(imp));
        }
    }
}
