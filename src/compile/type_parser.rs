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

use crate::compile::types::{PrimitiveType, Type, TypeVariable};
use crate::syntax::ast::{Type as AstType, TypeKind, TypeScheme};
use crate::syntax::parser;

/// Converts a type string to a type. Panics on any parse or
/// conversion failure; callers that need to recover from malformed
/// input should use [`try_string_to_type`] instead.
pub fn string_to_type(code: &str) -> Box<Type> {
    try_string_to_type(code)
        .unwrap_or_else(|e| panic!("failed to parse type {:?}: {}", code, e))
}

/// Like [`string_to_type`] but returns the parse/conversion error
/// instead of panicking. The error string is human-readable and not
/// stable.
pub fn try_string_to_type(code: &str) -> Result<Box<Type>, String> {
    let type_scheme = parser::parse_type_scheme(code)
        .map_err(|e| format!("parse error: {}", e))?;
    let mut type_builder = TypeBuilder::new();
    type_builder.ast_to_type_scheme(&type_scheme)
}

struct TypeBuilder {
    ty_vars: Vec<TypeVariable>,
}

impl TypeBuilder {
    fn new() -> Self {
        TypeBuilder { ty_vars: vec![] }
    }

    fn ast_to_type_scheme(
        &mut self,
        type_scheme: &TypeScheme,
    ) -> Result<Box<Type>, String> {
        for i in 0..type_scheme.var_count {
            self.ty_vars.push(TypeVariable::new(i));
        }
        let type_ = self.ast_to_type(&type_scheme.type_)?;
        Ok(if type_scheme.var_count == 0 {
            type_
        } else {
            Type::Forall(type_, type_scheme.var_count).into()
        })
    }

    fn ast_to_type(&mut self, t: &AstType) -> Result<Box<Type>, String> {
        Ok(Box::new(match &t.kind {
            // lint: sort until '#}' where '##TypeKind::'
            TypeKind::App(args, base_type) => {
                let flat_args = AstType::flatten(args);
                let arg_types: Vec<Type> = flat_args
                    .iter()
                    .map(|t| self.ast_to_type(t).map(|b| *b))
                    .collect::<Result<_, _>>()?;
                let base = self.ast_to_type(base_type)?;

                // Check if this is a list type application
                if let TypeKind::Id(name) = &base_type.kind {
                    if name == "list" && args.len() == 1 {
                        let arg =
                            arg_types.into_iter().next().ok_or_else(|| {
                                "list type application with no arg".to_string()
                            })?;
                        Type::List(Box::new(arg))
                    } else if name == "option" && args.len() == 1
                        || name == "either" && args.len() == 2
                        || name == "descending" && args.len() == 1
                        || name == "order" && args.is_empty()
                        || name == "range" && args.len() == 1
                        || name == "continuous_set" && args.len() == 1
                        || name == "discrete_set" && args.len() == 1
                        || name == "variant" && args.is_empty()
                        || name == "time" && args.is_empty()
                        || name == "date" && args.is_empty()
                        || name == "weekday" && args.is_empty()
                        || name == "month" && args.is_empty()
                    {
                        Type::Data(name.clone(), arg_types)
                    } else {
                        Type::Named(arg_types, name.clone())
                    }
                } else {
                    // Generic type application
                    let base_name = match base.as_ref() {
                        Type::Primitive(p) => p.as_str().to_string(),
                        _ => "unknown".to_string(),
                    };
                    Type::Named(arg_types, base_name)
                }
            }
            TypeKind::Fn(from_type, to_type) => {
                let from = self.ast_to_type(from_type)?;
                let to = self.ast_to_type(to_type)?;
                Type::Fn(from, to)
            }
            TypeKind::Id(name) => {
                if let Some(primitive) = PrimitiveType::parse_name(name) {
                    Type::Primitive(primitive)
                } else {
                    // This is a named type (like "list", "option", etc.)
                    Type::Named(vec![], name.clone())
                }
            }
            TypeKind::Record(fields) => {
                use crate::compile::types::Label;
                use std::collections::BTreeMap;

                let mut field_map = BTreeMap::new();
                for field in fields {
                    let label = Label::String(field.label.name.clone());
                    let field_type = *self.ast_to_type(&field.type_)?;
                    field_map.insert(label, field_type);
                }
                Type::Record(false, field_map)
            }
            TypeKind::Tuple(types) => {
                let type_args: Vec<Type> = types
                    .iter()
                    .map(|t| self.ast_to_type(t).map(|b| *b))
                    .collect::<Result<_, _>>()?;
                Type::Tuple(type_args)
            }
            TypeKind::Var(name) => {
                // Handle type variables like 'a, 'b, etc.
                // Don't try to parse the name, just look whether we've seen a
                // variable with the same name before.
                match self.ty_vars.iter().position(|v| &v.name() == name) {
                    Some(index) => Type::Variable(self.ty_vars[index].clone()),
                    None => {
                        return Err(format!("Unknown type variable {}", name));
                    }
                }
            }
            other => {
                return Err(format!("ast_to_type: unsupported {:?}", other));
            }
        }))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::compile::types::{Label, PrimitiveType, Type};
    use std::collections::BTreeMap;

    #[test]
    fn test_parse_type() {
        let t = string_to_type("int");
        assert_eq!(*t, Type::Primitive(PrimitiveType::Int));
    }

    #[test]
    fn test_parse_bool_type() {
        let t = string_to_type("bool");
        assert_eq!(*t, Type::Primitive(PrimitiveType::Bool));
    }

    #[test]
    fn test_parse_function_type() {
        let t = string_to_type("int -> bool");
        assert_eq!(
            *t,
            Type::Fn(
                Box::new(Type::Primitive(PrimitiveType::Int)),
                Box::new(Type::Primitive(PrimitiveType::Bool))
            )
        );
    }

    #[test]
    fn test_parse_record_type() {
        let t = string_to_type("{exp:int, man:real}");

        let mut expected_fields = BTreeMap::new();
        expected_fields.insert(
            Label::String("exp".to_string()),
            Type::Primitive(PrimitiveType::Int),
        );
        expected_fields.insert(
            Label::String("man".to_string()),
            Type::Primitive(PrimitiveType::Real),
        );

        assert_eq!(*t, Type::Record(false, expected_fields));
    }
}
