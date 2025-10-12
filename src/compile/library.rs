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

use crate::compile::types::Type;
use crate::eval::code::{Impl, LIBRARY};
use crate::eval::val::Val;
use std::collections::BTreeMap;
use std::sync::LazyLock;
use strum::{EnumCount, EnumProperty, IntoEnumIterator};
use strum_macros::{EnumCount, EnumIter, EnumProperty, EnumString};

/// Returns the datatype of a built-in function or record.
pub fn name_to_type(id: &str) -> Option<Type> {
    if let Some(b) = BY_NAME.get(id) {
        match b {
            BuiltIn::Fn(f) => Some(*f.get_type()),
            BuiltIn::Record(r) => r.get_type(),
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
    #[strum(props(p = "Bool", name = "op andalso", global = true))]
    #[strum(props(type = "bool * bool -> bool"))]
    BoolAndAlso,
    #[strum(props(name = "false", type = "bool"))]
    BoolFalse,
    #[strum(props(p = "Bool", name = "op if", global = true))]
    #[strum(props(type = "forall 1 bool * 'a * 'a -> 'a"))]
    BoolIf,
    #[strum(props(p = "Bool", name = "op implies", global = true))]
    #[strum(props(type = "bool * bool -> bool"))]
    BoolImplies,
    #[strum(props(p = "Bool", name = "op =", type = "bool * bool -> bool"))]
    BoolOpEq,
    #[strum(props(p = "Bool", name = "op <>", type = "bool * bool -> bool"))]
    BoolOpNe,
    #[strum(props(p = "Bool", name = "not", global = true))]
    #[strum(props(type = "bool -> bool"))]
    BoolOpNot,
    #[strum(props(p = "Bool", name = "op orelse", global = true))]
    #[strum(props(type = "bool * bool -> bool"))]
    BoolOrElse,
    #[strum(props(p = "Bool", name = "toString", type = "bool -> string"))]
    BoolToString,
    #[strum(props(name = "true", type = "bool"))]
    BoolTrue,
    #[strum(props(p = "Char", name = "chr", global = true))]
    #[strum(props(type = "int -> char", throws = "Chr"))]
    CharChr,
    #[strum(props(p = "Char", name = "compare"))]
    #[strum(props(type = "char * char -> `order`"))]
    CharCompare,
    #[strum(props(p = "Char", name = "contains"))]
    #[strum(props(type = "string -> char -> bool"))]
    CharContains,
    #[strum(props(p = "Char", name = "fromCString"))]
    #[strum(props(type = "string -> char option"))]
    CharFromCString,
    #[strum(props(p = "Char", name = "fromInt"))]
    #[strum(props(type = "int -> char option"))]
    CharFromInt,
    #[strum(props(p = "Char", name = "fromString"))]
    #[strum(props(type = "string -> char option"))]
    CharFromString,
    #[strum(props(p = "Char", name = "isAlpha", type = "char -> bool"))]
    CharIsAlpha,
    #[strum(props(p = "Char", name = "isAlphaNum", type = "char -> bool"))]
    CharIsAlphaNum,
    #[strum(props(p = "Char", name = "isAscii", type = "char -> bool"))]
    CharIsAscii,
    #[strum(props(p = "Char", name = "isCntrl", type = "char -> bool"))]
    CharIsCntrl,
    #[strum(props(p = "Char", name = "isDigit", type = "char -> bool"))]
    CharIsDigit,
    #[strum(props(p = "Char", name = "isGraph", type = "char -> bool"))]
    CharIsGraph,
    #[strum(props(p = "Char", name = "isHexDigit", type = "char -> bool"))]
    CharIsHexDigit,
    #[strum(props(p = "Char", name = "isLower", type = "char -> bool"))]
    CharIsLower,
    #[strum(props(p = "Char", name = "isOctDigit", type = "char -> bool"))]
    CharIsOctDigit,
    #[strum(props(p = "Char", name = "isPrint", type = "char -> bool"))]
    CharIsPrint,
    #[strum(props(p = "Char", name = "isPunct", type = "char -> bool"))]
    CharIsPunct,
    #[strum(props(p = "Char", name = "isSpace", type = "char -> bool"))]
    CharIsSpace,
    #[strum(props(p = "Char", name = "isUpper", type = "char -> bool"))]
    CharIsUpper,
    #[strum(props(p = "Char", name = "maxChar", type = "char"))]
    CharMaxChar,
    #[strum(props(p = "Char", name = "maxOrd", type = "int"))]
    CharMaxOrd,
    #[strum(props(p = "Char", name = "minChar", type = "char"))]
    CharMinChar,
    #[strum(props(p = "Char", name = "notContains"))]
    #[strum(props(type = "string -> char -> bool"))]
    CharNotContains,
    #[strum(props(p = "Char", name = "op =", type = "char * char -> bool"))]
    CharOpEq,
    #[strum(props(p = "Char", name = "op >=", type = "char * char -> bool"))]
    CharOpGe,
    #[strum(props(p = "Char", name = "op >", type = "char * char -> bool"))]
    CharOpGt,
    #[strum(props(p = "Char", name = "op <=", type = "char * char -> bool"))]
    CharOpLe,
    #[strum(props(p = "Char", name = "op <", type = "char * char -> bool"))]
    CharOpLt,
    #[strum(props(p = "Char", name = "op <>", type = "char * char -> bool"))]
    CharOpNe,
    #[strum(props(p = "Char", name = "ord", global = true))]
    #[strum(props(type = "char -> int"))]
    CharOrd,
    #[strum(props(p = "Char", name = "pred", throws = "Chr"))]
    #[strum(props(type = "char -> char"))]
    CharPred,
    #[strum(props(p = "Char", name = "succ", throws = "Chr"))]
    #[strum(props(type = "char -> char"))]
    CharSucc,
    #[strum(props(p = "Char", name = "toCString", type = "char -> string"))]
    CharToCString,
    #[strum(props(p = "Char", name = "toLower", type = "char -> char"))]
    CharToLower,
    #[strum(props(p = "Char", name = "toString", type = "char -> string"))]
    CharToString,
    #[strum(props(p = "Char", name = "toUpper", type = "char -> char"))]
    CharToUpper,
    #[strum(props(name = "op =", global = true))]
    #[strum(props(type = "forall 1 'a * 'a -> bool"))]
    GOpEq,
    #[strum(props(name = "op >=", global = true))]
    #[strum(props(type = "forall 1 'a * 'a -> bool"))]
    GOpGe,
    #[strum(props(name = "op >", global = true))]
    #[strum(props(type = "forall 1 'a * 'a -> bool"))]
    GOpGt,
    #[strum(props(name = "op <=", global = true))]
    #[strum(props(type = "forall 1 'a * 'a -> bool"))]
    GOpLe,
    #[strum(props(name = "op <", global = true))]
    #[strum(props(type = "forall 1 'a * 'a -> bool"))]
    GOpLt,
    #[strum(props(name = "op -", global = true))]
    #[strum(props(type = "forall 1 'a * 'a -> 'a"))]
    GOpMinus,
    #[strum(props(name = "op <>", global = true))]
    #[strum(props(type = "forall 1 'a * 'a -> bool"))]
    GOpNe,
    #[strum(props(name = "op ~", global = true))]
    #[strum(props(type = "forall 1 'a -> 'a"))]
    GOpNegate,
    #[strum(props(name = "op +", global = true))]
    #[strum(props(type = "forall 1 'a * 'a -> 'a"))]
    GOpPlus,
    #[strum(props(name = "op *", global = true))]
    #[strum(props(type = "forall 1 'a * 'a -> 'a"))]
    GOpTimes,
    #[strum(props(p = "General", name = "ignore", global = true))]
    #[strum(props(type = "forall 1 'a -> unit"))]
    GeneralIgnore,
    #[strum(props(p = "General", name = "op o", global = true))]
    #[strum(props(type = "forall 3 ('a -> 'b) * ('c -> 'a) -> 'c -> 'b"))]
    GeneralOpO,
    #[strum(props(p = "Int", name = "abs", type = "int -> int"))]
    IntAbs,
    #[strum(props(p = "Int", name = "compare", type = "int * int -> `order`"))]
    IntCompare,
    #[strum(props(p = "Int", name = "div"))]
    #[strum(props(type = "int * int -> int"))]
    IntDiv,
    #[strum(props(p = "Int", name = "fromInt", type = "int -> int"))]
    IntFromInt,
    #[strum(props(p = "Int", name = "fromLarge", type = "int -> int"))]
    IntFromLarge,
    #[strum(props(p = "Int", name = "fromString"))]
    #[strum(props(type = "string -> int option"))]
    IntFromString,
    #[strum(props(p = "Int", name = "max", type = "int * int -> int"))]
    IntMax,
    #[strum(props(p = "Int", name = "maxInt", type = "int option"))]
    IntMaxInt,
    #[strum(props(p = "Int", name = "min", type = "int * int -> int"))]
    IntMin,
    #[strum(props(p = "Int", name = "minInt", type = "int option"))]
    IntMinInt,
    #[strum(props(name = "op -", type = "int * int -> int"))]
    IntMinus,
    #[strum(props(p = "Int", name = "mod"))]
    #[strum(props(type = "int * int -> int"))]
    IntMod,
    #[strum(props(name = "op ~", type = "int -> int"))]
    IntNegate,
    #[strum(props(name = "op div", global = true))]
    #[strum(props(type = "int * int -> int"))]
    IntOpDiv,
    #[strum(props(name = "op =", type = "int * int -> bool"))]
    IntOpEq,
    #[strum(props(name = "op >=", type = "int * int -> bool"))]
    IntOpGe,
    #[strum(props(name = "op >", type = "int * int -> bool"))]
    IntOpGt,
    #[strum(props(name = "op <=", type = "int * int -> bool"))]
    IntOpLe,
    #[strum(props(name = "op <", type = "int * int -> bool"))]
    IntOpLt,
    #[strum(props(name = "op mod", global = true))]
    #[strum(props(type = "int * int -> int"))]
    IntOpMod,
    #[strum(props(name = "op <>", type = "int * int -> bool"))]
    IntOpNe,
    #[strum(props(name = "op +", type = "int * int -> int"))]
    IntPlus,
    #[strum(props(p = "Int", name = "precision", type = "int option"))]
    IntPrecision,
    #[strum(props(p = "Int", name = "quot", type = "int * int -> int"))]
    IntQuot,
    #[strum(props(p = "Int", name = "rem", type = "int * int -> int"))]
    IntRem,
    #[strum(props(p = "Int", name = "sameSign", type = "int * int -> bool"))]
    IntSameSign,
    #[strum(props(p = "Int", name = "sign", type = "int -> int"))]
    IntSign,
    #[strum(props(name = "op *", type = "int * int -> int"))]
    IntTimes,
    #[strum(props(p = "Int", name = "toInt", type = "int -> int"))]
    IntToInt,
    #[strum(props(p = "Int", name = "toLarge", type = "int -> int"))]
    IntToLarge,
    #[strum(props(p = "Int", name = "toString", type = "int -> string"))]
    IntToString,
    #[strum(props(p = "List", name = "map", global = true))]
    #[strum(props(type = "forall 2 ('a -> 'b) -> 'a list -> 'b list"))]
    ListMap,
    #[strum(props(p = "List", name = "nil", global = true))]
    #[strum(props(type = "forall 1 'a list", constructor = true))]
    ListNil,
    #[strum(props(p = "List", name = "op @", global = true))]
    #[strum(props(type = "forall 1 'a list * 'a list -> 'a list"))]
    ListOpAt,
    #[strum(props(p = "List", name = "op ::", global = true))]
    #[strum(props(type = "forall 1 'a * 'a list -> 'a list"))]
    ListOpCons,
    #[strum(props(p = "List", name = "tabulate"))]
    #[strum(props(type = "forall 1 int * (int -> 'a) -> 'a list"))]
    ListTabulate,
    #[strum(props(p = "Option", name = "app"))]
    #[strum(props(type = "forall 1 ('a -> unit) -> 'a option -> unit"))]
    OptionApp,
    #[strum(props(p = "Option", name = "compose"))]
    #[strum(props(
        type = "forall 3 ('a -> 'b) * ('c -> 'a option) -> 'c -> 'b option"
    ))]
    OptionCompose,
    #[strum(props(p = "Option", name = "composePartial"))]
    #[strum(props(
        type = "forall 3 ('a -> 'b option) * ('c -> 'a option) -> \
                'c -> 'b option"
    ))]
    OptionComposePartial,
    #[strum(props(p = "Option", name = "filter"))]
    #[strum(props(type = "forall 1 ('a -> bool) -> 'a -> 'a option"))]
    OptionFilter,
    #[strum(props(p = "Option", name = "getOpt", global = true))]
    #[strum(props(type = "forall 1 'a option * 'a -> 'a"))]
    OptionGetOpt,
    #[strum(props(p = "Option", name = "isSome", global = true))]
    #[strum(props(type = "forall 1 'a option -> bool"))]
    OptionIsSome,
    #[strum(props(p = "Option", name = "join"))]
    #[strum(props(type = "forall 1 'a option option -> 'a option"))]
    OptionJoin,
    #[strum(props(p = "Option", name = "map"))]
    #[strum(props(type = "forall 2 ('a -> 'b) -> 'a option -> 'b option"))]
    OptionMap,
    #[strum(props(p = "Option", name = "mapPartial"))]
    #[strum(props(
        type = "forall 2 ('a -> 'b option) -> 'a option -> 'b option"
    ))]
    OptionMapPartial,
    #[strum(props(p = "Option", name = "NONE", global = true))]
    #[strum(props(type = "forall 1 'a option", constructor = true))]
    OptionNone,
    #[strum(props(p = "Option", name = "SOME", global = true))]
    #[strum(props(type = "forall 1 'a -> 'a option", constructor = true))]
    OptionSome,
    #[strum(props(p = "Option", name = "valOf", global = true))]
    #[strum(props(type = "forall 1 'a option -> 'a", throws = "Option"))]
    OptionValOf,
    #[strum(props(p = "Order", name = "EQUAL", global = true))]
    #[strum(props(type = "`order`", constructor = true))]
    OrderEqual,
    #[strum(props(p = "Order", name = "GREATER", global = true))]
    #[strum(props(type = "`order`", constructor = true))]
    OrderGreater,
    #[strum(props(p = "Order", name = "LESS", global = true))]
    #[strum(props(type = "`order`", constructor = true))]
    OrderLess,
    #[strum(props(p = "Real", name = "op /", global = true))]
    #[strum(props(type = "real * real -> real"))]
    RealDivide,
    #[strum(props(p = "Real", name = "op ~", type = "real -> real"))]
    RealNegate,
    #[strum(props(p = "Real", name = "op =", type = "real * real -> bool"))]
    RealOpEq,
    #[strum(props(p = "Real", name = "op >=", type = "real * real -> bool"))]
    RealOpGe,
    #[strum(props(p = "Real", name = "op >", type = "real * real -> bool"))]
    RealOpGt,
    #[strum(props(p = "Real", name = "op <=", type = "real * real -> bool"))]
    RealOpLe,
    #[strum(props(p = "Real", name = "op <", type = "real * real -> bool"))]
    RealOpLt,
    #[strum(props(p = "Real", name = "op -", type = "real * real -> real"))]
    RealOpMinus,
    #[strum(props(p = "Real", name = "op <>", type = "real * real -> bool"))]
    RealOpNe,
    #[strum(props(p = "Real", name = "op +", type = "real * real -> real"))]
    RealOpPlus,
    #[strum(props(p = "Real", name = "op *", type = "real * real -> real"))]
    RealOpTimes,
    #[strum(props(p = "String", name = "collate"))]
    #[strum(props(
        type = "(char * char -> `order`) -> string * string -> `order`"
    ))]
    StringCollate,
    #[strum(props(p = "String", name = "compare"))]
    #[strum(props(type = "string * string -> `order`"))]
    StringCompare,
    #[strum(props(p = "String", name = "concat", global = true))]
    #[strum(props(type = "string list -> string"))]
    StringConcat,
    #[strum(props(p = "String", name = "concatWith"))]
    #[strum(props(type = "string -> string list -> string"))]
    StringConcatWith,
    #[strum(props(p = "String", name = "explode", global = true))]
    #[strum(props(type = "string -> char list"))]
    StringExplode,
    #[strum(props(p = "String", name = "extract", throws = "Subscript"))]
    #[strum(props(type = "string * int * int option -> string"))]
    StringExtract,
    #[strum(props(p = "String", name = "fields"))]
    #[strum(props(type = "(char -> bool) -> string -> string list"))]
    StringFields,
    #[strum(props(p = "String", name = "implode", global = true))]
    #[strum(props(type = "char list -> string"))]
    StringImplode,
    #[strum(props(p = "String", name = "isPrefix"))]
    #[strum(props(type = "string -> string -> bool"))]
    StringIsPrefix,
    #[strum(props(p = "String", name = "isSubstring"))]
    #[strum(props(type = "string -> string -> bool"))]
    StringIsSubstring,
    #[strum(props(p = "String", name = "isSuffix"))]
    #[strum(props(type = "string -> string -> bool"))]
    StringIsSuffix,
    #[strum(props(p = "String", name = "map"))]
    #[strum(props(type = "(char -> char) -> string -> string"))]
    StringMap,
    #[strum(props(p = "String", name = "maxSize", type = "int"))]
    StringMaxSize,
    #[strum(props(p = "String", name = "op ^", global = true))]
    #[strum(props(type = "string * string -> string"))]
    StringOpCaret,
    #[strum(props(p = "String", name = "op ="))]
    #[strum(props(type = "string * string -> bool"))]
    StringOpEq,
    #[strum(props(p = "String", name = "op >="))]
    #[strum(props(type = "string * string -> bool"))]
    StringOpGe,
    #[strum(props(p = "String", name = "op >"))]
    #[strum(props(type = "string * string -> bool"))]
    StringOpGt,
    #[strum(props(p = "String", name = "op <="))]
    #[strum(props(type = "string * string -> bool"))]
    StringOpLe,
    #[strum(props(p = "String", name = "op <"))]
    #[strum(props(type = "string * string -> bool"))]
    StringOpLt,
    #[strum(props(p = "String", name = "op <>"))]
    #[strum(props(type = "string * string -> bool"))]
    StringOpNe,
    #[strum(props(p = "String", name = "size", global = true))]
    #[strum(props(type = "string -> int"))]
    StringSize,
    #[strum(props(p = "String", name = "str", global = true))]
    #[strum(props(type = "char -> string"))]
    StringStr,
    #[strum(props(p = "String", name = "sub", throws = "Subscript"))]
    #[strum(props(type = "string * int -> char"))]
    StringSub,
    #[strum(props(p = "String", name = "substring", global = true))]
    #[strum(props(type = "string * int * int -> string"))]
    #[strum(props(throws = "Subscript"))]
    StringSubstring,
    #[strum(props(p = "String", name = "tokens"))]
    #[strum(props(type = "(char -> bool) -> string -> string list"))]
    StringTokens,
    #[strum(props(p = "String", name = "translate"))]
    #[strum(props(type = "(char -> string) -> string -> string"))]
    StringTranslate,
    #[strum(props(p = "Sys", name = "plan", global = true))]
    #[strum(props(type = "unit -> string"))]
    SysPlan,
    #[strum(props(p = "Sys", name = "set", global = true))]
    #[strum(props(type = "forall 1 string * 'a -> unit"))]
    SysSet,
    #[strum(props(p = "Sys", name = "unset", global = true))]
    #[strum(props(type = "forall 1 string -> unit"))]
    SysUnset,
}

impl BuiltInFunction {
    pub fn get_impl(&self) -> Impl {
        LIBRARY.fn_map.get(self).expect("fn impl").1
    }

    pub fn get_type(&self) -> Box<Type> {
        Box::new(LIBRARY.fn_map.get(self).expect("fn type").0.clone())
    }

    pub(crate) fn name(&self) -> &'static str {
        self.get_str("name").unwrap()
    }

    /// Returns "p.name" if there is a package `p`, otherwise just "name".
    pub(crate) fn full_name(&self) -> String {
        let name = self.get_str("name").unwrap();
        if let Some(p) = self.get_str("p") {
            format!("{}.{}", p, name)
        } else {
            name.to_string()
        }
    }

    pub(crate) fn is_constructor(&self) -> bool {
        self.get_bool("constructor").is_some_and(|b| b)
    }

    pub(crate) fn is_global(&self) -> bool {
        self.get_bool("global").is_some_and(|b| b)
    }
}

/// List of built-in records. They represent structures of the standard basis
/// library, including `General`, `Int` and `String`.
#[derive(Debug, Clone, Copy, Eq, Ord, PartialEq, PartialOrd)]
#[repr(u8)]
#[derive(EnumCount, EnumString, EnumProperty, EnumIter)]
pub enum BuiltInRecord {
    // lint: sort until '^}$' where '##[A-Z]'
    #[strum(props(name = "Bool"))]
    Bool,
    #[strum(props(name = "Char"))]
    Char,
    #[strum(props(name = "General"))]
    General,
    #[strum(props(name = "Int"))]
    Int,
    #[strum(props(name = "List"))]
    List,
    #[strum(props(name = "Option"))]
    Option,
    #[strum(props(name = "String"))]
    String,
    #[strum(props(name = "Sys"))]
    Sys,
}

impl BuiltInRecord {
    pub(crate) fn name(&self) -> &'static str {
        self.get_str("name").unwrap()
    }

    pub(crate) fn get_type(&self) -> Option<Type> {
        if let Some((t, _v)) = LIBRARY.structure_map.get(self) {
            Some(t.clone())
        } else {
            None
        }
    }
}

/// Built-in exception.
#[derive(Debug, Clone, Copy, Eq, Ord, PartialEq, PartialOrd)]
#[repr(u8)]
#[derive(
    EnumCount, EnumString, EnumProperty, EnumIter, strum_macros::Display,
)]
pub enum BuiltInExn {
    #[strum(props(p = "General"))]
    Bind,
    #[strum(props(p = "General"))]
    Chr,
    #[strum(props(p = "Option"))]
    Option,
    #[strum(props(p = "General", explain = "subscript out of bounds"))]
    Subscript,
}

impl BuiltInExn {
    pub(crate) fn explain(&self) -> Option<&'static str> {
        self.get_str("explain")
    }

    pub(crate) fn package(&self) -> &'static str {
        self.get_str("p").unwrap()
    }
}

/*
The following exceptions are in Morel Java but not yet in Morel Rust.

DIV("General", "Div"),
DOMAIN("General", "Domain"),
EMPTY("List", "Empty"),
OVERFLOW("General", "Overflow"),
ERROR("Interact", "Error"), // not in standard basis
SIZE("General", "Size"),
UNEQUAL_LENGTHS("ListPair", "UnequalLengths"),
UNORDERED("IEEEReal", "Unordered");
 */

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
    for f in BuiltInFunction::iter() {
        if f.is_global() {
            map.insert(f.get_str("name").unwrap(), BuiltIn::Fn(f));
        }
    }
    for r in BuiltInRecord::iter() {
        map.insert(r.get_str("name").unwrap(), BuiltIn::Record(r));
    }
    map
});

pub(crate) fn populate_env(map: &mut BTreeMap<&str, (Type, Option<Val>)>) {
    // Add built-in records to the environment
    map.extend(
        LIBRARY.structure_map.iter().map(|(r, (type_, v))| {
            (r.name(), (type_.clone(), Some(v.clone())))
        }),
    );

    // Until we can deduce type for records, keep the old logic that provides
    // the "set" function.
    map.extend(
        LIBRARY
            .fn_map
            .iter()
            .filter(|(f, _)| f.get_bool("global").is_some_and(|b| b))
            .map(|(f, (t, _))| (f.name(), (t.clone(), Some(Val::Fn(*f))))),
    );

    // Add global built-in functions to the environment.
    map.extend(
        LIBRARY
            .fn_map
            .iter()
            .map(|(f, (t, _))| {
                (
                    f.name(),
                    (
                        t.clone(),
                        if !f.is_global() {
                            None
                        } else if let Type::Fn(_, _) = t {
                            Some(Val::Fn(*f))
                        } else if f == &BuiltInFunction::ListNil {
                            Some(Val::List(Vec::new()))
                        } else {
                            None
                        },
                    ),
                )
            })
            .filter(|(_name, (_t, v))| v.is_some()),
    );
}

/// Looks up a built-in (function or structure) by name.
pub fn lookup(name: &str) -> Option<BuiltIn> {
    LIBRARY.name_to_built_in.get(name).cloned()
}
