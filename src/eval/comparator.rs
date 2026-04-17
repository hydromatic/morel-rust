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

//! Comparators for ordering values in queries.
//!
//! This module provides a trait-based comparator system for comparing
//! values of different types. Comparators are used by OrderRowSink to
//! sort query results.

use crate::compile::types::Type;
use crate::eval::val::{self, Val};
use std::cmp::Ordering;
use std::collections::HashMap;
use std::sync::{Arc, OnceLock};

/// A trait for comparing two values.
///
/// This is used by OrderRowSink to sort rows based on order keys.
/// Different implementations handle different types and sort orders.
pub trait Comparator: Send + Sync {
    /// Compares two values and returns their ordering.
    fn compare(&self, a: &Val, b: &Val) -> Ordering;
}

/// A comparator that uses natural ordering based on runtime value
/// tags. Handles primitives, lists, tuples, option, either, order,
/// and user-defined constructors. Does not handle `DESC` (the
/// `descending` type); use `ReverseComparator` for that.
#[derive(Clone)]
pub struct NaturalComparator;

impl Comparator for NaturalComparator {
    fn compare(&self, a: &Val, b: &Val) -> Ordering {
        match (a, b) {
            // lint: sort until '#}' where '##\(Val::'
            (Val::Bool(x), Val::Bool(y)) => x.cmp(y),
            (Val::Char(x), Val::Char(y)) => x.cmp(y),
            (
                Val::Constructor(ord_a, inner_a),
                Val::Constructor(ord_b, inner_b),
            ) => ord_a
                .cmp(ord_b)
                .then_with(|| self.compare(inner_a, inner_b)),
            (Val::Inl(_), Val::Inr(_)) => Ordering::Less,
            (Val::Inl(a), Val::Inl(b)) => self.compare(a, b),
            (Val::Inr(_), Val::Inl(_)) => Ordering::Greater,
            (Val::Inr(a), Val::Inr(b)) => self.compare(a, b),
            (Val::Int(x), Val::Int(y)) => x.cmp(y),
            (Val::List(xs), Val::List(ys)) => {
                for (x, y) in xs.iter().zip(ys.iter()) {
                    match self.compare(x, y) {
                        Ordering::Equal => continue,
                        other => return other,
                    }
                }
                xs.len().cmp(&ys.len())
            }
            (Val::Order(a), Val::Order(b)) => a.cmp(b),
            (Val::Real(x), Val::Real(y)) => {
                x.partial_cmp(y).unwrap_or(Ordering::Equal)
            }
            (Val::Some(_), Val::Unit) => Ordering::Greater,
            (Val::Some(a), Val::Some(b)) => self.compare(a, b),
            (Val::String(x), Val::String(y)) => x.cmp(y),
            (Val::Unit, Val::Some(_)) => Ordering::Less,
            (Val::Unit, Val::Unit) => Ordering::Equal,
            // #}
            _ => Ordering::Equal,
        }
    }
}

/// A comparator for tuples/records that compares fields lexicographically.
///
/// Each field has its own comparator, allowing for mixed types and
/// custom orderings per field.
pub struct TupleComparator {
    field_comparators: Vec<Arc<dyn Comparator>>,
}

impl TupleComparator {
    /// Creates a new tuple comparator with the given field comparators.
    pub fn new(field_comparators: Vec<Arc<dyn Comparator>>) -> Self {
        Self { field_comparators }
    }
}

impl Comparator for TupleComparator {
    fn compare(&self, a: &Val, b: &Val) -> Ordering {
        let a_list = a.expect_list();
        let b_list = b.expect_list();

        for (i, comparator) in self.field_comparators.iter().enumerate() {
            let cmp = comparator.compare(&a_list[i], &b_list[i]);
            if cmp != Ordering::Equal {
                return cmp;
            }
        }
        Ordering::Equal
    }
}

/// Compares option values: NONE (Unit) < SOME.
pub struct OptionComparator {
    inner: Arc<dyn Comparator>,
}

impl Comparator for OptionComparator {
    fn compare(&self, a: &Val, b: &Val) -> Ordering {
        match (a, b) {
            (Val::Unit, Val::Unit) => Ordering::Equal,
            (Val::Unit, Val::Some(_)) => Ordering::Less,
            (Val::Some(_), Val::Unit) => Ordering::Greater,
            (Val::Some(a), Val::Some(b)) => self.inner.compare(a, b),
            _ => Ordering::Equal,
        }
    }
}

/// Compares either values: INL < INR.
pub struct EitherComparator {
    left: Arc<dyn Comparator>,
    right: Arc<dyn Comparator>,
}

impl Comparator for EitherComparator {
    fn compare(&self, a: &Val, b: &Val) -> Ordering {
        match (a, b) {
            (Val::Inl(a), Val::Inl(b)) => self.left.compare(a, b),
            (Val::Inl(_), Val::Inr(_)) => Ordering::Less,
            (Val::Inr(_), Val::Inl(_)) => Ordering::Greater,
            (Val::Inr(a), Val::Inr(b)) => self.right.compare(a, b),
            _ => Ordering::Equal,
        }
    }
}

/// Compares user-defined datatype constructors by ordinal, then
/// payload. Payload comparators are built lazily to handle
/// recursive datatypes (e.g. `'a tree`).
pub struct DataComparator {
    constructors: Vec<Option<Type>>,
    payload_comparators: OnceLock<Vec<Option<Arc<dyn Comparator>>>>,
    datatype_constructors: HashMap<String, Vec<String>>,
    constructor_arg_types: HashMap<String, Type>,
}

impl Comparator for DataComparator {
    fn compare(&self, a: &Val, b: &Val) -> Ordering {
        match (a, b) {
            (
                Val::Constructor(ord_a, inner_a),
                Val::Constructor(ord_b, inner_b),
            ) => ord_a.cmp(ord_b).then_with(|| {
                let payloads = self.payload_comparators.get_or_init(|| {
                    self.constructors
                        .iter()
                        .map(|arg_type| {
                            arg_type.as_ref().map(|t| {
                                comparator_for_with(
                                    t,
                                    &self.datatype_constructors,
                                    &self.constructor_arg_types,
                                )
                            })
                        })
                        .collect()
                });
                if let Some(cmp) = payloads.get(*ord_a).and_then(|c| c.as_ref())
                {
                    cmp.compare(inner_a, inner_b)
                } else {
                    Ordering::Equal
                }
            }),
            _ => Ordering::Equal,
        }
    }
}

/// Compares lists lexicographically using an element comparator.
pub struct ListComparator {
    element: Arc<dyn Comparator>,
}

impl Comparator for ListComparator {
    fn compare(&self, a: &Val, b: &Val) -> Ordering {
        let a_list = a.expect_list();
        let b_list = b.expect_list();
        for (x, y) in a_list.iter().zip(b_list.iter()) {
            match self.element.compare(x, y) {
                Ordering::Equal => continue,
                other => return other,
            }
        }
        a_list.len().cmp(&b_list.len())
    }
}

/// Compares `Val::Order` values (LESS < EQUAL < GREATER).
pub struct OrderComparator;

impl Comparator for OrderComparator {
    fn compare(&self, a: &Val, b: &Val) -> Ordering {
        match (a, b) {
            (Val::Order(a), Val::Order(b)) => a.cmp(b),
            _ => Ordering::Equal,
        }
    }
}

/// A comparator that reverses the order of another comparator.
///
/// This is used for descending sorts. The `DESC x` value is stored
/// as the bare `x` at runtime; the reversal is handled here.
pub struct ReverseComparator {
    inner: Arc<dyn Comparator>,
}

impl ReverseComparator {
    /// Creates a new reverse comparator wrapping the given comparator.
    pub fn new(inner: Arc<dyn Comparator>) -> Self {
        Self { inner }
    }
}

impl Comparator for ReverseComparator {
    fn compare(&self, a: &Val, b: &Val) -> Ordering {
        // Unwrap DESC constructor wrappers, then reverse comparison.
        let a_inner = match a {
            Val::Constructor(val::DESC_ORDINAL, v) => v.as_ref(),
            _ => a,
        };
        let b_inner = match b {
            Val::Constructor(val::DESC_ORDINAL, v) => v.as_ref(),
            _ => b,
        };
        self.inner.compare(b_inner, a_inner)
    }
}

/// Creates a comparator for the given type.
///
/// This is the main entry point for creating comparators based on
/// the type of the expression. The `constructor_arg_types` map is
/// needed for user-defined datatypes to build per-constructor
/// payload comparators.
pub fn comparator_for(type_: &Type) -> Arc<dyn Comparator> {
    comparator_for_with(type_, &HashMap::new(), &HashMap::new())
}

/// Creates a comparator with access to datatype constructor info.
pub fn comparator_for_with(
    type_: &Type,
    datatype_constructors: &HashMap<String, Vec<String>>,
    constructor_arg_types: &HashMap<String, Type>,
) -> Arc<dyn Comparator> {
    match type_ {
        Type::Primitive(_) => Arc::new(NaturalComparator),
        Type::Bag(elem) | Type::List(elem) => Arc::new(ListComparator {
            element: comparator_for_with(
                elem,
                datatype_constructors,
                constructor_arg_types,
            ),
        }),
        Type::Tuple(types) => {
            let field_comparators: Vec<Arc<dyn Comparator>> = types
                .iter()
                .map(|t| {
                    comparator_for_with(
                        t,
                        datatype_constructors,
                        constructor_arg_types,
                    )
                })
                .collect();
            Arc::new(TupleComparator::new(field_comparators))
        }
        Type::Record(_, fields) => {
            let field_comparators: Vec<Arc<dyn Comparator>> = fields
                .values()
                .map(|t| {
                    comparator_for_with(
                        t,
                        datatype_constructors,
                        constructor_arg_types,
                    )
                })
                .collect();
            Arc::new(TupleComparator::new(field_comparators))
        }
        Type::Named(args, name) | Type::Data(name, args) => {
            if name == "descending" && !args.is_empty() {
                let inner = comparator_for_with(
                    &args[0],
                    datatype_constructors,
                    constructor_arg_types,
                );
                Arc::new(ReverseComparator::new(inner))
            } else if name == "option" && !args.is_empty() {
                Arc::new(OptionComparator {
                    inner: comparator_for_with(
                        &args[0],
                        datatype_constructors,
                        constructor_arg_types,
                    ),
                })
            } else if name == "either" && args.len() >= 2 {
                Arc::new(EitherComparator {
                    left: comparator_for_with(
                        &args[0],
                        datatype_constructors,
                        constructor_arg_types,
                    ),
                    right: comparator_for_with(
                        &args[1],
                        datatype_constructors,
                        constructor_arg_types,
                    ),
                })
            } else if name == "order" {
                Arc::new(OrderComparator)
            } else if let Some(cons) = datatype_constructors.get(name) {
                // User-defined datatype: store constructor arg types
                // (instantiated with actual type args) for lazy
                // comparator construction.
                let constructors = cons
                    .iter()
                    .map(|con_name| {
                        constructor_arg_types
                            .get(con_name)
                            .map(|t| instantiate(t, args))
                    })
                    .collect();
                Arc::new(DataComparator {
                    constructors,
                    payload_comparators: OnceLock::new(),
                    datatype_constructors: datatype_constructors.clone(),
                    constructor_arg_types: constructor_arg_types.clone(),
                })
            } else {
                Arc::new(NaturalComparator)
            }
        }
        _ => Arc::new(NaturalComparator),
    }
}

/// Substitutes `Type::Variable(i)` with `args[i]`.
fn instantiate(type_: &Type, args: &[Type]) -> Type {
    use crate::compile::types::Label;
    match type_ {
        // lint: sort until '#}' where '##Type::'
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
        // #}
        _ => type_.clone(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::compile::types::PrimitiveType;

    #[test]
    fn test_natural_comparator_ints() {
        let cmp = NaturalComparator;
        assert_eq!(cmp.compare(&Val::Int(1), &Val::Int(2)), Ordering::Less);
        assert_eq!(cmp.compare(&Val::Int(2), &Val::Int(1)), Ordering::Greater);
        assert_eq!(cmp.compare(&Val::Int(1), &Val::Int(1)), Ordering::Equal);
    }

    #[test]
    fn test_natural_comparator_strings() {
        let cmp = NaturalComparator;
        assert_eq!(
            cmp.compare(
                &Val::String("a".to_string()),
                &Val::String("b".to_string())
            ),
            Ordering::Less
        );
    }

    #[test]
    fn test_tuple_comparator() {
        let cmp = TupleComparator::new(vec![
            Arc::new(NaturalComparator),
            Arc::new(NaturalComparator),
        ]);

        let tuple1 = Val::List(vec![Val::Int(1), Val::Int(2)]);
        let tuple2 = Val::List(vec![Val::Int(1), Val::Int(3)]);

        assert_eq!(cmp.compare(&tuple1, &tuple2), Ordering::Less);
    }

    #[test]
    fn test_reverse_comparator() {
        let inner = Arc::new(NaturalComparator);
        let cmp = ReverseComparator::new(inner);

        assert_eq!(cmp.compare(&Val::Int(1), &Val::Int(2)), Ordering::Greater);
        assert_eq!(cmp.compare(&Val::Int(2), &Val::Int(1)), Ordering::Less);
    }

    #[test]
    fn test_comparator_for_primitive() {
        let cmp = comparator_for(&Type::Primitive(PrimitiveType::Int));
        assert_eq!(cmp.compare(&Val::Int(1), &Val::Int(2)), Ordering::Less);
    }

    #[test]
    fn test_comparator_for_tuple() {
        let cmp = comparator_for(&Type::Tuple(vec![
            Type::Primitive(PrimitiveType::Int),
            Type::Primitive(PrimitiveType::String),
        ]));

        let tuple1 = Val::List(vec![Val::Int(1), Val::String("a".to_string())]);
        let tuple2 = Val::List(vec![Val::Int(1), Val::String("b".to_string())]);

        assert_eq!(cmp.compare(&tuple1, &tuple2), Ordering::Less);
    }
}
