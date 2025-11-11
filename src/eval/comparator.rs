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
use crate::eval::val::Val;
use std::cmp::Ordering;
use std::sync::Arc;

/// A trait for comparing two values.
///
/// This is used by OrderRowSink to sort rows based on order keys.
/// Different implementations handle different types and sort orders.
pub trait Comparator: Send + Sync {
    /// Compares two values and returns their ordering.
    fn compare(&self, a: &Val, b: &Val) -> Ordering;
}

/// A comparator that uses natural ordering for simple types.
///
/// This handles Int, Real, String, Char, Bool using their standard
/// comparison operations.
#[derive(Clone)]
pub struct NaturalComparator;

impl Comparator for NaturalComparator {
    fn compare(&self, a: &Val, b: &Val) -> Ordering {
        use Val::{Bool, Char, Int, List, Real, String};
        match (a, b) {
            (Int(x), Int(y)) => x.cmp(y),
            (Real(x), Real(y)) => {
                // f32 doesn't implement Ord, so use partial_cmp.
                x.partial_cmp(y).unwrap_or(Ordering::Equal)
            }
            (String(x), String(y)) => x.cmp(y),
            (Char(x), Char(y)) => x.cmp(y),
            (Bool(x), Bool(y)) => x.cmp(y),
            (List(xs), List(ys)) => {
                // Lexicographic ordering for lists (tuples).
                for (x, y) in xs.iter().zip(ys.iter()) {
                    match self.compare(x, y) {
                        Ordering::Equal => continue,
                        other => return other,
                    }
                }
                xs.len().cmp(&ys.len())
            }
            // For non-comparable types or mixed types, use Equal.
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

/// A comparator that reverses the order of another comparator.
///
/// This is used for descending sorts.
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
        // Reverse the comparison by swapping arguments.
        self.inner.compare(b, a)
    }
}

/// Creates a comparator for the given type.
///
/// This is the main entry point for creating comparators based on the
/// type of the order expression.
pub fn comparator_for(type_: &Type) -> Arc<dyn Comparator> {
    match type_ {
        Type::Primitive(_) => Arc::new(NaturalComparator),
        Type::List(_) => Arc::new(NaturalComparator),
        Type::Tuple(types) => {
            let field_comparators: Vec<Arc<dyn Comparator>> =
                types.iter().map(|t| comparator_for(t)).collect();
            Arc::new(TupleComparator::new(field_comparators))
        }
        Type::Record(_, fields) => {
            let field_comparators: Vec<Arc<dyn Comparator>> =
                fields.values().map(|t| comparator_for(t)).collect();
            Arc::new(TupleComparator::new(field_comparators))
        }
        Type::Named(args, name) | Type::Data(name, args) => {
            // Check for special type constructors.
            // The descending type can appear as either Named or Data.
            if name == "descending" && !args.is_empty() {
                let inner = comparator_for(&args[0]);
                Arc::new(ReverseComparator::new(inner))
            } else {
                // Default to natural comparator.
                Arc::new(NaturalComparator)
            }
        }
        // Default case: use natural comparator.
        _ => Arc::new(NaturalComparator),
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
