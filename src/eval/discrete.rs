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

//! Discrete ordered types: enumeration of successor/predecessor and
//! min/max values for types used in `Range.discreteSetOf`.
//!
//! Port of `Discrete.java` and `Discretes.java` from morel-java commit
//! b4a0c4b1.
//!
//! Covers `int`, `char`, `bool`, `unit`; tuples/records of discretes;
//! `'a descending` where `'a` is discrete; the built-in sum types
//! `order`, `'a option`, and `('a, 'b) either` (each using their
//! dedicated `Val` variant rather than `Val::Constructor`); and
//! user-defined sum types whose constructors are each either nullary
//! or wrap a discrete arg type.

use crate::compile::types::{Label, PrimitiveType, Type};
use crate::eval::char::Char;
use crate::eval::order::Order;
use crate::eval::val::{self, Val};
use std::cmp::Ordering;
use std::collections::HashMap;
use std::sync::Arc;

/// Represents a discrete ordered type: each value (except the max) has
/// a unique successor. Analogous to Guava's `DiscreteDomain`.
pub trait Discrete: Send + Sync {
    /// Returns the successor of `v`, or `None` if `v` is the maximum
    /// value of this type.
    fn next(&self, v: &Val) -> Option<Val>;
    /// Returns the predecessor of `v`, or `None` if `v` is the minimum
    /// value of this type.
    fn prev(&self, v: &Val) -> Option<Val>;
    /// Returns the minimum value of this type, or `None` if unbounded.
    fn min_value(&self) -> Option<Val>;
    /// Returns the maximum value of this type, or `None` if unbounded.
    fn max_value(&self) -> Option<Val>;
}

pub struct IntDiscrete;

impl Discrete for IntDiscrete {
    fn next(&self, v: &Val) -> Option<Val> {
        let n = v.expect_int();
        if n == i32::MAX {
            None
        } else {
            Some(Val::Int(n + 1))
        }
    }
    fn prev(&self, v: &Val) -> Option<Val> {
        let n = v.expect_int();
        if n == i32::MIN {
            None
        } else {
            Some(Val::Int(n - 1))
        }
    }
    fn min_value(&self) -> Option<Val> {
        Some(Val::Int(i32::MIN))
    }
    fn max_value(&self) -> Option<Val> {
        Some(Val::Int(i32::MAX))
    }
}

pub struct CharDiscrete;

impl Discrete for CharDiscrete {
    fn next(&self, v: &Val) -> Option<Val> {
        let c = v.expect_char();
        let code = c as u32;
        if code >= Char::MAX_ORD as u32 {
            None
        } else {
            char::from_u32(code + 1).map(Val::Char)
        }
    }
    fn prev(&self, v: &Val) -> Option<Val> {
        let c = v.expect_char();
        let code = c as u32;
        if code == 0 {
            None
        } else {
            char::from_u32(code - 1).map(Val::Char)
        }
    }
    fn min_value(&self) -> Option<Val> {
        Some(Val::Char('\u{0000}'))
    }
    fn max_value(&self) -> Option<Val> {
        char::from_u32(Char::MAX_ORD as u32).map(Val::Char)
    }
}

pub struct BoolDiscrete;

impl Discrete for BoolDiscrete {
    fn next(&self, v: &Val) -> Option<Val> {
        if v.expect_bool() {
            None
        } else {
            Some(Val::Bool(true))
        }
    }
    fn prev(&self, v: &Val) -> Option<Val> {
        if v.expect_bool() {
            Some(Val::Bool(false))
        } else {
            None
        }
    }
    fn min_value(&self) -> Option<Val> {
        Some(Val::Bool(false))
    }
    fn max_value(&self) -> Option<Val> {
        Some(Val::Bool(true))
    }
}

pub struct UnitDiscrete;

impl Discrete for UnitDiscrete {
    fn next(&self, _v: &Val) -> Option<Val> {
        None
    }
    fn prev(&self, _v: &Val) -> Option<Val> {
        None
    }
    fn min_value(&self) -> Option<Val> {
        Some(Val::Unit)
    }
    fn max_value(&self) -> Option<Val> {
        Some(Val::Unit)
    }
}

/// Discrete for a tuple / record: lexicographic step on the rightmost
/// component, carrying into the next component on overflow.
pub struct TupleDiscrete {
    components: Vec<Arc<dyn Discrete>>,
}

impl TupleDiscrete {
    fn step(&self, v: &Val, forward: bool) -> Option<Val> {
        let values = v.expect_list();
        let n = self.components.len();
        for i in (0..n).rev() {
            let stepped = if forward {
                self.components[i].next(&values[i])
            } else {
                self.components[i].prev(&values[i])
            };
            if let Some(s) = stepped {
                let mut result: Vec<Val> = values.to_vec();
                result[i] = s;
                for (j, slot) in
                    result.iter_mut().enumerate().skip(i + 1).take(n - i - 1)
                {
                    let extreme = if forward {
                        self.components[j].min_value()
                    } else {
                        self.components[j].max_value()
                    };
                    *slot = extreme?;
                }
                return Some(Val::List(result));
            }
        }
        None
    }

    fn extreme(&self, min: bool) -> Option<Val> {
        let mut out: Vec<Val> = Vec::with_capacity(self.components.len());
        for d in &self.components {
            let x = if min { d.min_value() } else { d.max_value() }?;
            out.push(x);
        }
        Some(Val::List(out))
    }
}

impl Discrete for TupleDiscrete {
    fn next(&self, v: &Val) -> Option<Val> {
        self.step(v, true)
    }
    fn prev(&self, v: &Val) -> Option<Val> {
        self.step(v, false)
    }
    fn min_value(&self) -> Option<Val> {
        self.extreme(true)
    }
    fn max_value(&self) -> Option<Val> {
        self.extreme(false)
    }
}

/// Discrete for the `'a descending` datatype: next/prev are swapped
/// from the inner discrete order.
pub struct DescendingDiscrete {
    inner: Arc<dyn Discrete>,
}

impl Discrete for DescendingDiscrete {
    fn next(&self, v: &Val) -> Option<Val> {
        let inner_val = match v {
            Val::Constructor(val::DESC_ORDINAL, inner) => inner.as_ref(),
            _ => panic!("DescendingDiscrete::next: expected DESC value"),
        };
        self.inner
            .prev(inner_val)
            .map(|x| Val::Constructor(val::DESC_ORDINAL, Box::new(x)))
    }
    fn prev(&self, v: &Val) -> Option<Val> {
        let inner_val = match v {
            Val::Constructor(val::DESC_ORDINAL, inner) => inner.as_ref(),
            _ => panic!("DescendingDiscrete::prev: expected DESC value"),
        };
        self.inner
            .next(inner_val)
            .map(|x| Val::Constructor(val::DESC_ORDINAL, Box::new(x)))
    }
    fn min_value(&self) -> Option<Val> {
        self.inner
            .max_value()
            .map(|x| Val::Constructor(val::DESC_ORDINAL, Box::new(x)))
    }
    fn max_value(&self) -> Option<Val> {
        self.inner
            .min_value()
            .map(|x| Val::Constructor(val::DESC_ORDINAL, Box::new(x)))
    }
}

/// Discrete for the built-in `order` enum: LESS < EQUAL < GREATER.
pub struct OrderDiscrete;

impl Discrete for OrderDiscrete {
    fn next(&self, v: &Val) -> Option<Val> {
        match v {
            Val::Order(o) => match o.0 {
                Ordering::Less => Some(Val::Order(Order(Ordering::Equal))),
                Ordering::Equal => Some(Val::Order(Order(Ordering::Greater))),
                Ordering::Greater => None,
            },
            _ => panic!("OrderDiscrete::next: expected Val::Order"),
        }
    }
    fn prev(&self, v: &Val) -> Option<Val> {
        use crate::eval::order::Order;
        match v {
            Val::Order(o) => match o.0 {
                Ordering::Greater => Some(Val::Order(Order(Ordering::Equal))),
                Ordering::Equal => Some(Val::Order(Order(Ordering::Less))),
                Ordering::Less => None,
            },
            _ => panic!("OrderDiscrete::prev: expected Val::Order"),
        }
    }
    fn min_value(&self) -> Option<Val> {
        use crate::eval::order::Order;
        Some(Val::Order(Order(Ordering::Less)))
    }
    fn max_value(&self) -> Option<Val> {
        use crate::eval::order::Order;
        Some(Val::Order(Order(Ordering::Greater)))
    }
}

/// Discrete for `'a option`: NONE (represented as `Val::Unit`) precedes
/// every `SOME v`.
pub struct OptionDiscrete {
    inner: Arc<dyn Discrete>,
}

impl Discrete for OptionDiscrete {
    fn next(&self, v: &Val) -> Option<Val> {
        match v {
            Val::Unit => self.inner.min_value().map(|x| Val::Some(Box::new(x))),
            Val::Some(s) => self.inner.next(s).map(|x| Val::Some(Box::new(x))),
            _ => {
                panic!("OptionDiscrete::next: expected Val::Unit or Val::Some")
            }
        }
    }
    fn prev(&self, v: &Val) -> Option<Val> {
        match v {
            Val::Unit => None,
            Val::Some(s) => match self.inner.prev(s) {
                Some(x) => Some(Val::Some(Box::new(x))),
                None => Some(Val::Unit),
            },
            _ => {
                panic!("OptionDiscrete::prev: expected Val::Unit or Val::Some")
            }
        }
    }
    fn min_value(&self) -> Option<Val> {
        Some(Val::Unit)
    }
    fn max_value(&self) -> Option<Val> {
        self.inner.max_value().map(|x| Val::Some(Box::new(x)))
    }
}

/// Discrete for `('a, 'b) either`: every `INL a` precedes every `INR b`.
pub struct EitherDiscrete {
    left: Arc<dyn Discrete>,
    right: Arc<dyn Discrete>,
}

impl Discrete for EitherDiscrete {
    fn next(&self, v: &Val) -> Option<Val> {
        match v {
            Val::Inl(l) => match self.left.next(l) {
                Some(x) => Some(Val::Inl(Box::new(x))),
                None => self.right.min_value().map(|x| Val::Inr(Box::new(x))),
            },
            Val::Inr(r) => self.right.next(r).map(|x| Val::Inr(Box::new(x))),
            _ => panic!("EitherDiscrete::next: expected Val::Inl or Val::Inr"),
        }
    }
    fn prev(&self, v: &Val) -> Option<Val> {
        match v {
            Val::Inl(l) => self.left.prev(l).map(|x| Val::Inl(Box::new(x))),
            Val::Inr(r) => match self.right.prev(r) {
                Some(x) => Some(Val::Inr(Box::new(x))),
                None => self.left.max_value().map(|x| Val::Inl(Box::new(x))),
            },
            _ => panic!("EitherDiscrete::prev: expected Val::Inl or Val::Inr"),
        }
    }
    fn min_value(&self) -> Option<Val> {
        self.left.min_value().map(|x| Val::Inl(Box::new(x)))
    }
    fn max_value(&self) -> Option<Val> {
        self.right.max_value().map(|x| Val::Inr(Box::new(x)))
    }
}

/// Discrete for a user-defined sum-type datatype. Constructors are
/// stored at runtime as `Val::Constructor(ordinal, inner)`, where
/// `inner` is `Val::Unit` for nullary constructors or the actual arg
/// value otherwise.
pub struct DataDiscrete {
    constructors: Vec<Option<Arc<dyn Discrete>>>,
}

impl DataDiscrete {
    fn first_of(&self, ord: usize) -> Option<Val> {
        if ord >= self.constructors.len() {
            return None;
        }
        match &self.constructors[ord] {
            None => Some(Val::Constructor(ord, Box::new(Val::Unit))),
            Some(d) => match d.min_value() {
                Some(v) => Some(Val::Constructor(ord, Box::new(v))),
                None => self.first_of(ord + 1),
            },
        }
    }

    fn last_of(&self, ord: usize) -> Option<Val> {
        match &self.constructors[ord] {
            None => Some(Val::Constructor(ord, Box::new(Val::Unit))),
            Some(d) => match d.max_value() {
                Some(v) => Some(Val::Constructor(ord, Box::new(v))),
                None => {
                    if ord == 0 {
                        None
                    } else {
                        self.last_of(ord - 1)
                    }
                }
            },
        }
    }
}

impl Discrete for DataDiscrete {
    fn next(&self, v: &Val) -> Option<Val> {
        let (ord, inner) = match v {
            Val::Constructor(ord, inner) => (*ord, inner.as_ref()),
            _ => panic!(
                "DataDiscrete::next: expected Val::Constructor, got {:?}",
                v
            ),
        };
        if let Some(Some(d)) = self.constructors.get(ord)
            && let Some(next) = d.next(inner)
        {
            return Some(Val::Constructor(ord, Box::new(next)));
        }
        self.first_of(ord + 1)
    }
    fn prev(&self, v: &Val) -> Option<Val> {
        let (ord, inner) = match v {
            Val::Constructor(ord, inner) => (*ord, inner.as_ref()),
            _ => panic!(
                "DataDiscrete::prev: expected Val::Constructor, got {:?}",
                v
            ),
        };
        if let Some(Some(d)) = self.constructors.get(ord)
            && let Some(prev) = d.prev(inner)
        {
            return Some(Val::Constructor(ord, Box::new(prev)));
        }
        if ord == 0 {
            return None;
        }
        self.last_of(ord - 1)
    }
    fn min_value(&self) -> Option<Val> {
        self.first_of(0)
    }
    fn max_value(&self) -> Option<Val> {
        if self.constructors.is_empty() {
            None
        } else {
            self.last_of(self.constructors.len() - 1)
        }
    }
}

/// Substitutes type variables in `type_` using `args` (where
/// `Type::Variable(i)` is replaced with `args[i]`). Mirrors
/// `comparator::instantiate`.
fn instantiate(type_: &Type, args: &[Type]) -> Type {
    match type_ {
        Type::Bag(t) => Type::Bag(Box::new(instantiate(t, args))),
        Type::Data(name, ts) => Type::Data(
            name.clone(),
            ts.iter().map(|t| instantiate(t, args)).collect(),
        ),
        Type::Fn(a, b) => Type::Fn(
            Box::new(instantiate(a, args)),
            Box::new(instantiate(b, args)),
        ),
        Type::List(t) => Type::List(Box::new(instantiate(t, args))),
        Type::Record(p, fields) => Type::Record(
            *p,
            fields
                .iter()
                .map(|(k, v): (&Label, &Type)| {
                    (k.clone(), instantiate(v, args))
                })
                .collect(),
        ),
        Type::Tuple(ts) => {
            Type::Tuple(ts.iter().map(|t| instantiate(t, args)).collect())
        }
        Type::Variable(tv) if tv.id < args.len() => args[tv.id].clone(),
        _ => type_.clone(),
    }
}

/// Returns a `Discrete` for the given type, or an error describing why
/// the type is not discrete. Convenience wrapper around
/// [`discrete_for_with`] for callers without datatype context (only
/// built-in types will resolve).
pub fn discrete_for(type_: &Type) -> Result<Arc<dyn Discrete>, String> {
    let empty = HashMap::new();
    let empty2 = HashMap::new();
    discrete_for_with(type_, &empty, &empty2)
}

/// Like [`discrete_for`] but with access to the type system's user-
/// defined datatype constructor tables, so user-defined sum types
/// resolve as well.
pub fn discrete_for_with(
    type_: &Type,
    datatype_constructors: &HashMap<String, Vec<String>>,
    constructor_arg_types: &HashMap<String, Type>,
) -> Result<Arc<dyn Discrete>, String> {
    let recurse = |t: &Type| {
        discrete_for_with(t, datatype_constructors, constructor_arg_types)
    };
    match type_ {
        Type::Primitive(p) => match p {
            PrimitiveType::Int => Ok(Arc::new(IntDiscrete)),
            PrimitiveType::Char => Ok(Arc::new(CharDiscrete)),
            PrimitiveType::Bool => Ok(Arc::new(BoolDiscrete)),
            PrimitiveType::Unit => Ok(Arc::new(UnitDiscrete)),
            _ => Err(format!("not a discrete type: {}", type_)),
        },
        Type::Tuple(ts) => {
            let components: Result<Vec<_>, _> =
                ts.iter().map(recurse).collect();
            Ok(Arc::new(TupleDiscrete {
                components: components?,
            }))
        }
        Type::Record(_, fields) => {
            let components: Result<Vec<_>, _> =
                fields.values().map(recurse).collect();
            Ok(Arc::new(TupleDiscrete {
                components: components?,
            }))
        }
        Type::Named(args, name) | Type::Data(name, args) => match name.as_str()
        {
            "descending" if !args.is_empty() => {
                let inner = recurse(&args[0])?;
                Ok(Arc::new(DescendingDiscrete { inner }))
            }
            "order" => Ok(Arc::new(OrderDiscrete)),
            "option" if !args.is_empty() => {
                let inner = recurse(&args[0])?;
                Ok(Arc::new(OptionDiscrete { inner }))
            }
            "either" if args.len() >= 2 => {
                let left = recurse(&args[0])?;
                let right = recurse(&args[1])?;
                Ok(Arc::new(EitherDiscrete { left, right }))
            }
            _ => {
                // User-defined sum-type datatype: each constructor is
                // either nullary (no entry in `constructor_arg_types`)
                // or wraps a discrete arg type. Type variables in the
                // arg types are instantiated via the dataType's
                // `args`.
                let cons = datatype_constructors
                    .get(name)
                    .ok_or_else(|| format!("not a discrete type: {}", type_))?;
                let mut constructors: Vec<Option<Arc<dyn Discrete>>> =
                    Vec::with_capacity(cons.len());
                for con_name in cons {
                    match constructor_arg_types.get(con_name) {
                        None => constructors.push(None),
                        Some(t) => {
                            let inst = instantiate(t, args);
                            // morel-java collapses inner errors into
                            // "not a discrete type: <whole type>".
                            let d = discrete_for_with(
                                &inst,
                                datatype_constructors,
                                constructor_arg_types,
                            )
                            .map_err(|_| {
                                format!("not a discrete type: {}", type_)
                            })?;
                            constructors.push(Some(d));
                        }
                    }
                }
                Ok(Arc::new(DataDiscrete { constructors }))
            }
        },
        _ => Err(format!("not a discrete type: {}", type_)),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn int_next_prev() {
        let d = IntDiscrete;
        assert_eq!(d.next(&Val::Int(3)), Some(Val::Int(4)));
        assert_eq!(d.prev(&Val::Int(3)), Some(Val::Int(2)));
        assert_eq!(d.next(&Val::Int(i32::MAX)), None);
        assert_eq!(d.prev(&Val::Int(i32::MIN)), None);
    }

    #[test]
    fn bool_steps() {
        let d = BoolDiscrete;
        assert_eq!(d.next(&Val::Bool(false)), Some(Val::Bool(true)));
        assert_eq!(d.next(&Val::Bool(true)), None);
        assert_eq!(d.prev(&Val::Bool(false)), None);
        assert_eq!(d.min_value(), Some(Val::Bool(false)));
        assert_eq!(d.max_value(), Some(Val::Bool(true)));
    }

    #[test]
    fn tuple_bool_bool_enumeration() {
        // bool * bool has 4 values: (F,F), (F,T), (T,F), (T,T).
        let d = TupleDiscrete {
            components: vec![Arc::new(BoolDiscrete), Arc::new(BoolDiscrete)],
        };
        let mut v = d.min_value().unwrap();
        let mut seen = vec![v.clone()];
        while let Some(next) = d.next(&v) {
            seen.push(next.clone());
            v = next;
        }
        assert_eq!(seen.len(), 4);
        assert_eq!(
            seen[0],
            Val::List(vec![Val::Bool(false), Val::Bool(false)])
        );
        assert_eq!(seen[3], Val::List(vec![Val::Bool(true), Val::Bool(true)]));
    }

    #[test]
    fn descending_reverses() {
        let d = DescendingDiscrete {
            inner: Arc::new(IntDiscrete),
        };
        let desc_3 = Val::Constructor(val::DESC_ORDINAL, Box::new(Val::Int(3)));
        let desc_2 = Val::Constructor(val::DESC_ORDINAL, Box::new(Val::Int(2)));
        // next(DESC 3) = DESC 2 (reversed).
        assert_eq!(d.next(&desc_3), Some(desc_2));
    }

    #[test]
    fn real_is_not_discrete() {
        match discrete_for(&Type::Primitive(PrimitiveType::Real)) {
            Err(msg) => assert_eq!(msg, "not a discrete type: real"),
            Ok(_) => panic!("expected error"),
        }
    }

    #[test]
    fn string_is_not_discrete() {
        match discrete_for(&Type::Primitive(PrimitiveType::String)) {
            Err(msg) => assert_eq!(msg, "not a discrete type: string"),
            Ok(_) => panic!("expected error"),
        }
    }
}
