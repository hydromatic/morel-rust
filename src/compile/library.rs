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
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Debug)]
#[repr(u16)]
#[derive(EnumCount, EnumIter, EnumProperty, EnumString)]
pub enum BuiltInFunction {
    // lint: sort until '^}$' where '##[A-Z]'
    /// `bag` is a synonym for `Bag.fromList`
    #[strum(props(name = "bag", global = true))]
    #[strum(props(type = "forall 1 'a list -> 'a bag"))]
    Bag,
    #[strum(props(p = "Bag", name = "all"))]
    #[strum(props(type = "forall 1 ('a -> bool) -> 'a bag -> bool"))]
    BagAll,
    #[strum(props(p = "Bag", name = "app"))]
    #[strum(props(type = "forall 1 ('a -> unit) -> 'a bag -> unit"))]
    BagApp,
    #[strum(props(p = "Bag", name = "at"))]
    #[strum(props(type = "forall 1 'a bag * 'a bag -> 'a bag"))]
    BagAt,
    #[strum(props(p = "Bag", name = "collate"))]
    #[strum(props(
        type = "forall 1 ('a * 'a -> `order`) -> 'a bag * 'a bag -> \
                `order`"
    ))]
    BagCollate,
    #[strum(props(p = "Bag", name = "concat"))]
    #[strum(props(type = "forall 1 'a bag list -> 'a bag"))]
    BagConcat,
    #[strum(props(p = "Bag", name = "drop", throws = "Subscript"))]
    #[strum(props(type = "forall 1 'a bag * int -> 'a bag"))]
    BagDrop,
    #[strum(props(p = "Bag", name = "exists"))]
    #[strum(props(type = "forall 1 ('a -> bool) -> 'a bag -> bool"))]
    BagExists,
    #[strum(props(p = "Bag", name = "filter"))]
    #[strum(props(type = "forall 1 ('a -> bool) -> 'a bag -> 'a bag"))]
    BagFilter,
    #[strum(props(p = "Bag", name = "find"))]
    #[strum(props(type = "forall 1 ('a -> bool) -> 'a bag -> 'a option"))]
    BagFind,
    #[strum(props(p = "Bag", name = "fold"))]
    #[strum(props(type = "forall 2 ('a * 'b -> 'b) -> 'b -> 'a bag -> 'b"))]
    BagFold,
    #[strum(props(p = "Bag", name = "fromList"))]
    #[strum(props(type = "forall 1 'a list -> 'a bag"))]
    BagFromList,
    #[strum(props(p = "Bag", name = "getItem"))]
    #[strum(props(type = "forall 1 'a bag -> ('a * 'a bag) option"))]
    BagGetItem,
    #[strum(props(p = "Bag", name = "hd", throws = "Empty"))]
    #[strum(props(type = "forall 1 'a bag -> 'a"))]
    BagHd,
    #[strum(props(p = "Bag", name = "length"))]
    #[strum(props(type = "forall 1 'a bag -> int"))]
    BagLength,
    #[strum(props(p = "Bag", name = "map"))]
    #[strum(props(type = "forall 2 ('a -> 'b) -> 'a bag -> 'b bag"))]
    BagMap,
    #[strum(props(p = "Bag", name = "mapPartial"))]
    #[strum(props(type = "forall 2 ('a -> 'b option) -> 'a bag -> 'b bag"))]
    BagMapPartial,
    #[strum(props(p = "Bag", name = "nil", global = true))]
    #[strum(props(type = "forall 1 'a bag", constructor = true))]
    BagNil,
    #[strum(props(p = "Bag", name = "null"))]
    #[strum(props(type = "forall 1 'a bag -> bool"))]
    BagNull,
    #[strum(props(p = "Bag", name = "partition"))]
    #[strum(props(
        type = "forall 1 ('a -> bool) -> 'a bag -> 'a bag * 'a bag"
    ))]
    BagPartition,
    #[strum(props(p = "Bag", name = "tabulate", throws = "Size"))]
    #[strum(props(type = "forall 1 int * (int -> 'a) -> 'a bag"))]
    BagTabulate,
    #[strum(props(p = "Bag", name = "take", throws = "Subscript"))]
    #[strum(props(type = "forall 1 'a bag * int -> 'a bag"))]
    BagTake,
    #[strum(props(p = "Bag", name = "tl", throws = "Empty"))]
    #[strum(props(type = "forall 1 'a bag -> 'a bag"))]
    BagTl,
    #[strum(props(p = "Bag", name = "toList"))]
    #[strum(props(type = "forall 1 'a bag -> 'a list"))]
    BagToList,
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
    #[strum(props(p = "Either", name = "app"))]
    #[strum(props(
        type = "forall 2 ('a -> unit) * ('b -> unit) -> ('a,'b) either -> unit"
    ))]
    EitherApp,
    #[strum(props(p = "Either", name = "appLeft"))]
    #[strum(props(type = "forall 2 ('a -> unit) -> ('a,'b) either -> unit"))]
    EitherAppLeft,
    #[strum(props(p = "Either", name = "appRight"))]
    #[strum(props(type = "forall 2 ('a -> unit) -> ('b,'a) either -> unit"))]
    EitherAppRight,
    #[strum(props(p = "Either", name = "asLeft"))]
    #[strum(props(type = "forall 2 ('a,'b) either -> 'a option"))]
    EitherAsLeft,
    #[strum(props(p = "Either", name = "asRight"))]
    #[strum(props(type = "forall 2 ('a,'b) either -> 'b option"))]
    EitherAsRight,
    #[strum(props(p = "Either", name = "fold"))]
    #[strum(props(
        type = "forall 3 ('a * 'c -> 'c) * ('b * 'c -> 'c) -> 'c -> ('a,'b) \
        either -> 'c"
    ))]
    EitherFold,
    #[strum(props(name = "INL", global = true))]
    #[strum(props(type = "forall 2 'a -> ('a,'b) either", constructor = true))]
    EitherInl,
    #[strum(props(name = "INR", global = true))]
    #[strum(props(type = "forall 2 'b -> ('a,'b) either", constructor = true))]
    EitherInr,
    #[strum(props(p = "Either", name = "isLeft"))]
    #[strum(props(type = "forall 2 ('a,'b) either -> bool"))]
    EitherIsLeft,
    #[strum(props(p = "Either", name = "isRight"))]
    #[strum(props(type = "forall 2 ('a,'b) either -> bool"))]
    EitherIsRight,
    #[strum(props(p = "Either", name = "map"))]
    #[strum(props(
        type = "forall 4 ('a -> 'c) * ('b -> 'd) -> ('a,'b) either -> \
        ('c,'d) either"
    ))]
    EitherMap,
    #[strum(props(p = "Either", name = "mapLeft"))]
    #[strum(props(
        type = "forall 3 ('a -> 'c) -> ('a,'b) either -> ('c,'b) either"
    ))]
    EitherMapLeft,
    #[strum(props(p = "Either", name = "mapRight"))]
    #[strum(props(
        type = "forall 3 ('a -> 'c) -> ('b,'a) either -> ('b,'c) either"
    ))]
    EitherMapRight,
    #[strum(props(p = "Either", name = "partition"))]
    #[strum(props(type = "forall 2 ('a,'b) either list -> 'a list * 'b list"))]
    EitherPartition,
    #[strum(props(p = "Either", name = "proj"))]
    #[strum(props(type = "forall 1 ('a,'a) either -> 'a"))]
    EitherProj,
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
    #[strum(props(p = "ListPair", name = "all"))]
    #[strum(props(
        type = "forall 2 ('a * 'b -> bool) -> 'a list * 'b list -> bool"
    ))]
    LPAll,
    #[strum(props(p = "ListPair", name = "allEq"))]
    #[strum(props(
        type = "forall 2 ('a * 'b -> bool) -> 'a list * 'b list -> bool"
    ))]
    LPAllEq,
    #[strum(props(p = "ListPair", name = "app"))]
    #[strum(props(
        type = "forall 2 ('a * 'b -> unit) -> 'a list * 'b list -> unit"
    ))]
    LPApp,
    #[strum(props(p = "ListPair", name = "appEq", throws = "UnequalLengths"))]
    #[strum(props(
        type = "forall 2 ('a * 'b -> unit) -> 'a list * 'b list -> unit"
    ))]
    LPAppEq,
    #[strum(props(p = "ListPair", name = "exists"))]
    #[strum(props(
        type = "forall 2 ('a * 'b -> bool) -> 'a list * 'b list -> bool"
    ))]
    LPExists,
    #[strum(props(p = "ListPair", name = "foldl"))]
    #[strum(props(
        type = "forall 3 ('a * 'b * 'c -> 'c) -> 'c -> 'a list * 'b list -> 'c"
    ))]
    LPFoldl,
    #[strum(props(
        p = "ListPair",
        name = "foldlEq",
        throws = "UnequalLengths"
    ))]
    #[strum(props(
        type = "forall 3 ('a * 'b * 'c -> 'c) -> 'c -> 'a list * 'b list -> 'c"
    ))]
    LPFoldlEq,
    #[strum(props(p = "ListPair", name = "foldr"))]
    #[strum(props(
        type = "forall 3 ('a * 'b * 'c -> 'c) -> 'c -> 'a list * 'b list -> 'c"
    ))]
    LPFoldr,
    #[strum(props(
        p = "ListPair",
        name = "foldrEq",
        throws = "UnequalLengths"
    ))]
    #[strum(props(
        type = "forall 3 ('a * 'b * 'c -> 'c) -> 'c -> 'a list * 'b list -> 'c"
    ))]
    LPFoldrEq,
    #[strum(props(p = "ListPair", name = "map"))]
    #[strum(props(
        type = "forall 3 ('a * 'b -> 'c) -> 'a list * 'b list -> 'c list"
    ))]
    LPMap,
    #[strum(props(p = "ListPair", name = "mapEq", throws = "UnequalLengths"))]
    #[strum(props(
        type = "forall 3 ('a * 'b -> 'c) -> 'a list * 'b list -> 'c list"
    ))]
    LPMapEq,
    #[strum(props(p = "ListPair", name = "unzip"))]
    #[strum(props(type = "forall 2 ('a * 'b) list -> 'a list * 'b list"))]
    LPUnzip,
    #[strum(props(p = "ListPair", name = "zip"))]
    #[strum(props(type = "forall 2 'a list * 'b list -> ('a * 'b) list"))]
    LPZip,
    #[strum(props(p = "ListPair", name = "zipEq", throws = "UnequalLengths"))]
    #[strum(props(type = "forall 2 'a list * 'b list -> ('a * 'b) list"))]
    LPZipEq,
    #[strum(props(p = "List", name = "all"))]
    #[strum(props(type = "forall 1 ('a -> bool) -> 'a list -> bool"))]
    ListAll,
    #[strum(props(p = "List", name = "app", global = true))]
    #[strum(props(type = "forall 1 ('a -> unit) -> 'a list -> unit"))]
    ListApp,
    #[strum(props(p = "List", name = "at"))]
    #[strum(props(type = "forall 1 'a list * 'a list -> 'a list"))]
    ListAt,
    #[strum(props(p = "List", name = "collate"))]
    #[strum(props(
        type = "forall 1 ('a * 'a -> `order`) -> 'a list * 'a list -> \
                `order`"
    ))]
    ListCollate,
    #[strum(props(p = "List", name = "concat"))]
    #[strum(props(type = "forall 1 'a list list -> 'a list"))]
    ListConcat,
    #[strum(props(p = "List", name = "drop", throws = "Subscript"))]
    #[strum(props(type = "forall 1 'a list * int -> 'a list"))]
    ListDrop,
    #[strum(props(p = "List", name = "except"))]
    #[strum(props(type = "forall 1 'a list * 'a list -> 'a list"))]
    ListExcept,
    #[strum(props(p = "List", name = "exists"))]
    #[strum(props(type = "forall 1 ('a -> bool) -> 'a list -> bool"))]
    ListExists,
    #[strum(props(p = "List", name = "filter"))]
    #[strum(props(type = "forall 1 ('a -> bool) -> 'a list -> 'a list"))]
    ListFilter,
    #[strum(props(p = "List", name = "find"))]
    #[strum(props(type = "forall 1 ('a -> bool) -> 'a list -> 'a option"))]
    ListFind,
    #[strum(props(p = "List", name = "foldl", global = true))]
    #[strum(props(type = "forall 2 ('a * 'b -> 'b) -> 'b -> 'a list -> 'b"))]
    ListFoldl,
    #[strum(props(p = "List", name = "foldr", global = true))]
    #[strum(props(type = "forall 2 ('a * 'b -> 'b) -> 'b -> 'a list -> 'b"))]
    ListFoldr,
    #[strum(props(p = "List", name = "getItem"))]
    #[strum(props(type = "forall 1 'a list -> ('a * 'a list) option"))]
    ListGetItem,
    #[strum(props(p = "List", name = "hd", global = true, throws = "Empty"))]
    #[strum(props(type = "forall 1 'a list -> 'a"))]
    ListHd,
    #[strum(props(p = "List", name = "intersect"))]
    #[strum(props(type = "forall 1 'a list * 'a list -> 'a list"))]
    ListIntersect,
    #[strum(props(p = "List", name = "last", throws = "Empty"))]
    #[strum(props(type = "forall 1 'a list -> 'a"))]
    ListLast,
    #[strum(props(p = "List", name = "length", global = true))]
    #[strum(props(type = "forall 1 'a list -> int"))]
    ListLength,
    #[strum(props(p = "List", name = "map", global = true))]
    #[strum(props(type = "forall 2 ('a -> 'b) -> 'a list -> 'b list"))]
    ListMap,
    #[strum(props(p = "List", name = "mapPartial"))]
    #[strum(props(type = "forall 2 ('a -> 'b option) -> 'a list -> 'b list"))]
    ListMapPartial,
    #[strum(props(p = "List", name = "mapi"))]
    #[strum(props(type = "forall 2 (int * 'a -> 'b) -> 'a list -> 'b list"))]
    ListMapi,
    #[strum(props(p = "List", name = "nil", global = true))]
    #[strum(props(type = "forall 1 'a list", constructor = true))]
    ListNil,
    #[strum(props(p = "List", name = "nth", throws = "Subscript"))]
    #[strum(props(type = "forall 1 'a list * int -> 'a"))]
    ListNth,
    #[strum(props(p = "List", name = "null", global = true))]
    #[strum(props(type = "forall 1 'a list -> bool"))]
    ListNull,
    #[strum(props(p = "List", name = "op @", global = true))]
    #[strum(props(type = "forall 1 'a list * 'a list -> 'a list"))]
    ListOpAt,
    #[strum(props(p = "List", name = "op ::", global = true))]
    #[strum(props(type = "forall 1 'a * 'a list -> 'a list"))]
    ListOpCons,
    #[strum(props(p = "List", name = "partition"))]
    #[strum(props(
        type = "forall 1 ('a -> bool) -> 'a list -> 'a list * 'a list"
    ))]
    ListPartition,
    #[strum(props(p = "List", name = "rev", global = true))]
    #[strum(props(type = "forall 1 'a list -> 'a list"))]
    ListRev,
    #[strum(props(p = "List", name = "revAppend"))]
    #[strum(props(type = "forall 1 'a list * 'a list -> 'a list"))]
    ListRevAppend,
    #[strum(props(p = "List", name = "tabulate", throws = "Size"))]
    #[strum(props(type = "forall 1 int * (int -> 'a) -> 'a list"))]
    ListTabulate,
    #[strum(props(p = "List", name = "take", throws = "Subscript"))]
    #[strum(props(type = "forall 1 'a list * int -> 'a list"))]
    ListTake,
    #[strum(props(p = "List", name = "tl", global = true, throws = "Empty"))]
    #[strum(props(type = "forall 1 'a list -> 'a list"))]
    ListTl,
    #[strum(props(p = "Math", name = "acos", type = "real -> real"))]
    MathAcos,
    #[strum(props(p = "Math", name = "asin", type = "real -> real"))]
    MathAsin,
    #[strum(props(p = "Math", name = "atan", type = "real -> real"))]
    MathAtan,
    #[strum(props(p = "Math", name = "atan2", type = "real * real -> real"))]
    MathAtan2,
    #[strum(props(p = "Math", name = "cos", type = "real -> real"))]
    MathCos,
    #[strum(props(p = "Math", name = "cosh", type = "real -> real"))]
    MathCosh,
    #[strum(props(p = "Math", name = "e", type = "real"))]
    MathE,
    #[strum(props(p = "Math", name = "exp", type = "real -> real"))]
    MathExp,
    #[strum(props(p = "Math", name = "ln", type = "real -> real"))]
    MathLn,
    #[strum(props(p = "Math", name = "log10", type = "real -> real"))]
    MathLog10,
    #[strum(props(p = "Math", name = "pi", type = "real"))]
    MathPi,
    #[strum(props(p = "Math", name = "pow", type = "real * real -> real"))]
    MathPow,
    #[strum(props(p = "Math", name = "sin", type = "real -> real"))]
    MathSin,
    #[strum(props(p = "Math", name = "sinh", type = "real -> real"))]
    MathSinh,
    #[strum(props(p = "Math", name = "sqrt", type = "real -> real"))]
    MathSqrt,
    #[strum(props(p = "Math", name = "tan", type = "real -> real"))]
    MathTan,
    #[strum(props(p = "Math", name = "tanh", type = "real -> real"))]
    MathTanh,
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
    /// `real` is a synonym for `Real.fromInt`
    #[strum(props(name = "real", type = "int -> real", global = true))]
    Real,
    #[strum(props(p = "Real", name = "abs", type = "real -> real"))]
    RealAbs,
    #[strum(props(p = "Real", name = "ceil", global = true))]
    #[strum(props(type = "real -> int", throws = "Overflow"))]
    RealCeil,
    #[strum(props(p = "Real", name = "checkFloat"))]
    #[strum(props(type = "real -> real", throws = "Div, Overflow"))]
    RealCheckFloat,
    #[strum(props(p = "Real", name = "compare"))]
    #[strum(props(type = "real * real -> `order`", throws = "Unordered"))]
    RealCompare,
    #[strum(props(p = "Real", name = "copySign"))]
    #[strum(props(type = "real * real -> real"))]
    RealCopySign,
    #[strum(props(p = "Real", name = "op /", global = true))]
    #[strum(props(type = "real * real -> real"))]
    RealDivide,
    #[strum(props(p = "Real", name = "floor", global = true))]
    #[strum(props(type = "real -> int", throws = "Overflow"))]
    RealFloor,
    #[strum(props(p = "Real", name = "fromInt", type = "int -> real"))]
    RealFromInt,
    #[strum(props(p = "Real", name = "fromManExp"))]
    #[strum(props(type = "{exp:int, man:real} -> real"))]
    RealFromManExp,
    #[strum(props(p = "Real", name = "fromString"))]
    #[strum(props(type = "string -> real option"))]
    RealFromString,
    #[strum(props(p = "Real", name = "isFinite", type = "real -> bool"))]
    RealIsFinite,
    #[strum(props(p = "Real", name = "isNan", type = "real -> bool"))]
    RealIsNan,
    #[strum(props(p = "Real", name = "isNormal", type = "real -> bool"))]
    RealIsNormal,
    #[strum(props(p = "Real", name = "max", type = "real * real -> real"))]
    RealMax,
    #[strum(props(p = "Real", name = "maxFinite", type = "real"))]
    RealMaxFinite,
    #[strum(props(p = "Real", name = "min", type = "real * real -> real"))]
    RealMin,
    #[strum(props(p = "Real", name = "minNormalPos", type = "real"))]
    RealMinNormalPos,
    #[strum(props(p = "Real", name = "minPos", type = "real"))]
    RealMinPos,
    #[strum(props(p = "Real", name = "negInf", type = "real"))]
    RealNegInf,
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
    #[strum(props(p = "Real", name = "posInf", type = "real"))]
    RealPosInf,
    #[strum(props(p = "Real", name = "precision", type = "int"))]
    RealPrecision,
    #[strum(props(p = "Real", name = "radix", type = "int"))]
    RealRadix,
    #[strum(props(p = "Real", name = "realCeil", type = "real -> real"))]
    RealRealCeil,
    #[strum(props(p = "Real", name = "realFloor", type = "real -> real"))]
    RealRealFloor,
    #[strum(props(p = "Real", name = "realMod", type = "real -> real"))]
    RealRealMod,
    #[strum(props(p = "Real", name = "realRound", type = "real -> real"))]
    RealRealRound,
    #[strum(props(p = "Real", name = "realTrunc", type = "real -> real"))]
    RealRealTrunc,
    #[strum(props(p = "Real", name = "rem", type = "real * real -> real"))]
    RealRem,
    #[strum(props(p = "Real", name = "round", global = true))]
    #[strum(props(type = "real -> int", throws = "Overflow"))]
    RealRound,
    #[strum(props(p = "Real", name = "sameSign"))]
    #[strum(props(type = "real * real -> bool"))]
    RealSameSign,
    #[strum(props(p = "Real", name = "sign"))]
    #[strum(props(type = "real -> int", throws = "Domain"))]
    RealSign,
    #[strum(props(p = "Real", name = "signBit", type = "real -> bool"))]
    RealSignBit,
    #[strum(props(p = "Real", name = "split"))]
    #[strum(props(type = "real -> {frac:real, whole:real}"))]
    RealSplit,
    #[strum(props(p = "Real", name = "toManExp"))]
    #[strum(props(type = "real -> {man:real, exp:int}"))]
    RealToManExp,
    #[strum(props(p = "Real", name = "toString", type = "real -> string"))]
    RealToString,
    #[strum(props(p = "Real", name = "trunc", global = true))]
    #[strum(props(type = "real -> int", throws = "Overflow"))]
    RealTrunc,
    #[strum(props(p = "Real", name = "unordered"))]
    #[strum(props(type = "real * real -> bool"))]
    RealUnordered,
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
    /// `vector` is a synonym for `Vector.fromList`
    #[strum(props(name = "vector", global = true, throws = "Size"))]
    #[strum(props(type = "forall 1 'a list -> 'a vector"))]
    Vector,
    #[strum(props(p = "Vector", name = "all"))]
    #[strum(props(type = "forall 1 ('a -> bool) -> 'a vector -> bool"))]
    VectorAll,
    #[strum(props(p = "Vector", name = "app"))]
    #[strum(props(type = "forall 1 ('a -> unit) -> 'a vector -> unit"))]
    VectorApp,
    #[strum(props(p = "Vector", name = "appi"))]
    #[strum(props(type = "forall 1 (int * 'a -> unit) -> 'a vector -> unit"))]
    VectorAppi,
    #[strum(props(p = "Vector", name = "collate"))]
    #[strum(props(
        type = "forall 1 ('a * 'a -> `order`) -> 'a vector * 'a vector -> \
                `order`"
    ))]
    VectorCollate,
    #[strum(props(p = "Vector", name = "concat", throws = "Size"))]
    #[strum(props(type = "forall 1 'a vector list -> 'a vector"))]
    VectorConcat,
    #[strum(props(p = "Vector", name = "exists"))]
    #[strum(props(type = "forall 1 ('a -> bool) -> 'a vector -> bool"))]
    VectorExists,
    #[strum(props(p = "Vector", name = "find"))]
    #[strum(props(type = "forall 1 ('a -> bool) -> 'a vector -> 'a option"))]
    VectorFind,
    #[strum(props(p = "Vector", name = "findi"))]
    #[strum(props(
        type = "forall 1 (int * 'a -> bool) -> 'a vector -> (int * 'a) option"
    ))]
    VectorFindi,
    #[strum(props(p = "Vector", name = "foldl"))]
    #[strum(props(type = "forall 2 ('a * 'b -> 'b) -> 'b -> 'a vector -> 'b"))]
    VectorFoldl,
    #[strum(props(p = "Vector", name = "foldli"))]
    #[strum(props(
        type = "forall 2 (int * 'a * 'b -> 'b) -> 'b -> 'a vector -> 'b"
    ))]
    VectorFoldli,
    #[strum(props(p = "Vector", name = "foldr"))]
    #[strum(props(type = "forall 2 ('a * 'b -> 'b) -> 'b -> 'a vector -> 'b"))]
    VectorFoldr,
    #[strum(props(p = "Vector", name = "foldri"))]
    #[strum(props(
        type = "forall 2 (int * 'a * 'b -> 'b) -> 'b -> 'a vector -> 'b"
    ))]
    VectorFoldri,
    #[strum(props(p = "Vector", name = "fromList", throws = "Size"))]
    #[strum(props(type = "forall 1 'a list -> 'a vector"))]
    VectorFromList,
    #[strum(props(p = "Vector", name = "length"))]
    #[strum(props(type = "forall 1 'a vector -> int"))]
    VectorLength,
    #[strum(props(p = "Vector", name = "map"))]
    #[strum(props(type = "forall 2 ('a -> 'b) -> 'a vector -> 'b vector"))]
    VectorMap,
    #[strum(props(p = "Vector", name = "mapi"))]
    #[strum(props(
        type = "forall 2 (int * 'a -> 'b) -> 'a vector -> 'b vector"
    ))]
    VectorMapi,
    #[strum(props(p = "Vector", name = "maxLen", type = "int"))]
    VectorMaxLen,
    #[strum(props(p = "Vector", name = "sub", throws = "Subscript"))]
    #[strum(props(type = "forall 1 'a vector * int -> 'a"))]
    VectorSub,
    #[strum(props(p = "Vector", name = "tabulate", throws = "Size"))]
    #[strum(props(type = "forall 1 int * (int -> 'a) -> 'a vector"))]
    VectorTabulate,
    #[strum(props(p = "Vector", name = "update", throws = "Subscript"))]
    #[strum(props(type = "forall 1 'a vector * int * 'a -> 'a vector"))]
    VectorUpdate,
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
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Debug)]
#[repr(u8)]
#[derive(EnumCount, EnumIter, EnumProperty, EnumString)]
pub enum BuiltInRecord {
    // lint: sort until '^}$' where '##[A-Z]'
    #[strum(props(name = "Bag"))]
    Bag,
    #[strum(props(name = "Bool"))]
    Bool,
    #[strum(props(name = "Char"))]
    Char,
    #[strum(props(name = "Either"))]
    Either,
    #[strum(props(name = "General"))]
    General,
    #[strum(props(name = "Int"))]
    Int,
    #[strum(props(name = "List"))]
    List,
    #[strum(props(name = "ListPair"))]
    ListPair,
    #[strum(props(name = "Math"))]
    Math,
    #[strum(props(name = "Option"))]
    Option,
    #[strum(props(name = "Real"))]
    Real,
    #[strum(props(name = "String"))]
    String,
    #[strum(props(name = "Sys"))]
    Sys,
    #[strum(props(name = "Vector"))]
    Vector,
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
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Debug)]
#[repr(u8)]
#[derive(
    EnumCount, EnumIter, EnumProperty, EnumString, strum_macros::Display,
)]
pub enum BuiltInExn {
    #[strum(props(p = "General"))]
    Bind,
    #[strum(props(p = "General"))]
    Chr,
    #[strum(props(p = "General", explain = "divide by zero"))]
    Div,
    #[strum(props(p = "General", explain = "domain error"))]
    Domain,
    #[strum(props(p = "List"))]
    Empty,
    #[strum(props(p = "Option"))]
    Option,
    #[strum(props(p = "General", explain = "overflow"))]
    Overflow,
    #[strum(props(p = "General"))]
    Size,
    #[strum(props(p = "General", explain = "subscript out of bounds"))]
    Subscript,
    #[strum(props(p = "ListPair"))]
    UnequalLengths,
    #[strum(props(p = "IEEEReal"))]
    Unordered,
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

EMPTY("List", "Empty"),
ERROR("Interact", "Error"), // not in standard basis
SIZE("General", "Size"),
UNEQUAL_LENGTHS("ListPair", "UnequalLengths"),
 */

/// Built-in function or record.
#[repr(u16)]
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Debug)]
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

    pub(crate) fn key(&self) -> u16 {
        match self {
            BuiltIn::Fn(f) => (*f as u16) + (BuiltInRecord::COUNT as u16),
            BuiltIn::Record(r) => *r as u16,
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
                        } else if f == &BuiltInFunction::ListNil
                            || f == &BuiltInFunction::BagNil
                        {
                            // Both List.nil and Bag.nil are empty Val::List
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
