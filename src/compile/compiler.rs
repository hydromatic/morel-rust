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

use crate::compile::core::{DatatypeBind, Decl, Expr, Pat, TypeBind};
use crate::compile::pretty::Pretty;
use crate::compile::type_env::{Binding, Id};
use crate::compile::type_resolver::TypeMap;
use crate::compile::types::{PrimitiveType, Type};
use crate::eval::code::{Code, Codes, Effect, EvalEnv};
use crate::eval::session::Session;
use crate::eval::val::Val;
use crate::shell::Shell;
use crate::shell::config::Config as ShellConfig;
use crate::shell::main::Environment;
use std::cell::RefCell;
use std::collections::{BTreeMap, HashMap, HashSet};
use std::rc::Rc;

/// Compiles a declaration to code that can be evaluated.
pub fn compile_statement(
    type_map: &TypeMap,
    env: &Environment,
    decl: &Decl,
) -> Box<dyn CompiledStatement> {
    let compiler = Compiler::new(type_map);
    compiler.compile_statement(env, decl, None, &HashSet::new())
}

struct Compiler<'a> {
    type_map: &'a TypeMap,
}

struct Closure;

impl Closure {
    fn bind_recurse(
        pat: &Pat,
        value: &Val,
        mut f: impl FnMut(&Pat, &Val),
    ) -> bool {
        match pat {
            Pat::Identifier(_, _name) => {
                f(pat, value);
                true
            }
            _ => false,
        }
    }
}

impl<'a> Compiler<'a> {
    thread_local! {
        static ORDINAL_CODE: RefCell<Vec<i32>> = RefCell::new(vec![0]);
    }

    fn new(type_map: &'a TypeMap) -> Self {
        Self { type_map }
    }

    fn compile_statement(
        &self,
        env: &Environment,
        decl: &Decl,
        skip_pat: Option<Id>,
        queries_to_wrap: &HashSet<Expr>,
    ) -> Box<dyn CompiledStatement> {
        let mut match_codes = Vec::new();
        let mut bindings = Vec::new();
        let mut actions = Vec::new();
        let cx = Context::new(env.clone());

        self.compile_decl(
            &cx,
            decl,
            skip_pat,
            queries_to_wrap,
            &mut match_codes,
            &mut bindings,
            Some(&mut actions),
        );

        let type_ = match decl {
            Decl::NonRecVal(val_bind) => val_bind.t.clone(),
            _ => Box::new(Type::Primitive(PrimitiveType::Unit)),
        };

        let context = self.create_context(env);

        Box::new(CompiledStatementImpl {
            type_,
            context,
            actions,
        })
    }

    fn compile_decl(
        &self,
        cx: &Context,
        decl: &Decl,
        skip_pat: Option<Id>,
        queries_to_wrap: &HashSet<Expr>,
        match_codes: &mut Vec<Code>,
        bindings: &mut Vec<Binding>,
        actions: Option<&mut Vec<Box<dyn Action>>>,
    ) {
        match decl {
            Decl::NonRecVal(_) | Decl::RecVal(_) => {
                self.compile_val_decl(
                    cx,
                    decl,
                    skip_pat,
                    queries_to_wrap,
                    match_codes,
                    bindings,
                    actions,
                );
            }

            Decl::Over(name) => {
                self.compile_over_decl(name.as_str(), bindings, actions)
            }

            Decl::Type(type_binds) => {
                self.compile_type_decl(type_binds, bindings, actions)
            }

            Decl::Datatype(datatype_binds) => {
                self.compile_datatype_decl(datatype_binds, bindings, actions)
            }
        }
    }

    fn compile_val_decl(
        &self,
        cx: &Context,
        decl: &Decl,
        _skip_pat: Option<Id>,
        _queries_to_wrap: &HashSet<Expr>,
        match_codes: &mut Vec<Code>,
        bindings: &mut Vec<Binding>,
        actions: Option<&mut Vec<Box<dyn Action>>>,
    ) {
        Self::bind_pattern(bindings, decl);
        let binding_count = bindings.len();
        let new_bindings = &bindings.as_slice()[binding_count..];
        let cx1 = cx.bind_all(new_bindings);

        // Collect all bindings first to avoid borrowing issues
        let mut collected_actions = Vec::new();

        decl.for_each_binding(
            &mut |pat: &Pat, expr: &Expr, _overload_pat: &Option<Box<Id>>| {
                let code = self.compile_arg(&cx1, expr);

                let matches = vec![(pat.clone(), (*code).clone())];
                let code2 = Rc::new(Code::Constant(Val::Bool(false)));
                match_codes.push(Code::Match(matches, code2));

                collected_actions.push(ValDeclAction {
                    code,
                    pat: pat.clone(),
                });
            },
        );

        // Add collected actions to the action vector.
        if let Some(actions) = actions {
            for action in collected_actions {
                actions.push(Box::new(action));
            }
        }

        bindings.truncate(binding_count);
    }

    /// Richer than {@link #acceptBinding(TypeSystem, Core.Pat, List)}
    /// because we have the expression.
    fn bind_pattern(bindings: &mut Vec<Binding>, decl: &Decl) {
        let mut p =
            |pat: &Pat, _expr: &Expr, _overload_pat: &Option<Box<Id>>| {
                if let Pat::Identifier(_, name) = pat {
                    let binding = Binding {
                        id: Box::new(Id {
                            name: name.clone(),
                            ordinal: 0,
                        }),
                        overload_id: None,
                        value: None,
                    };
                    bindings.push(binding);
                }
            };
        decl.for_each_binding(&mut p);
    }

    fn compile_over_decl(
        &self,
        _name: &str,
        _bindings: &mut [Binding],
        _actions: Option<&mut Vec<Box<dyn Action>>>,
    ) {
    }

    fn compile_type_decl(
        &self,
        _type_binds: &[TypeBind],
        _bindings: &mut [Binding],
        _actions: Option<&mut Vec<Box<dyn Action>>>,
    ) {
    }

    fn compile_datatype_decl(
        &self,
        _datatype_binds: &[DatatypeBind],
        _bindings: &mut [Binding],
        _actions: Option<&mut Vec<Box<dyn Action>>>,
    ) {
    }

    /// Creates a context.
    ///
    /// The whole way we provide compilation environments (including
    /// [Environment]) to generated code is a mess:
    ///
    /// - This method is protected so that CalciteCompiler can override and get
    ///   a Calcite type factory.
    /// - User-defined functions should have a 'prepare' phase, where they use
    ///   a type factory and environment, that is distinct from the 'eval'
    ///   phase.
    /// - We should pass compile and runtime environments via parameters, not
    ///   thread-locals.
    /// - The fake session is there because a session is mandatory, but we have
    ///   not created a session yet. Lifecycle confusion.
    fn create_context(&self, env: &Environment) -> Context {
        Context::new(env.clone())
    }

    pub fn compile(&self, env: &Environment, expr: &Expr) -> Box<Code> {
        let cx = self.create_context(env);
        self.compile_with_context(&cx, expr)
    }

    /// Compiles the argument to "apply".
    pub fn compile_arg(&self, cx: &Context, expr: &Expr) -> Box<Code> {
        self.compile_with_context(cx, expr)
    }

    /// Compiles the argument to a call, producing a list with N elements if the
    /// argument is an N-tuple.
    pub fn compile_args(&self, cx: &Context, expr: Box<Expr>) -> Vec<Code> {
        if let Expr::Tuple(_, args) = *expr {
            self.compile_arg_list(cx, args.as_slice())
        } else {
            self.compile_arg_list(cx, &[expr])
        }
    }

    /// Compiles the tuple arguments to "apply".
    pub fn compile_arg_list(
        &self,
        cx: &Context,
        expr: &[Box<Expr>],
    ) -> Vec<Code> {
        expr.iter()
            .map(|e| *self.compile_with_context(cx, e))
            .collect()
    }

    /// Compiles the tuple arguments to "apply".
    pub fn compile_arg_types(
        &self,
        cx: &Context,
        expressions: &[Expr],
    ) -> Vec<(Box<Code>, Box<Type>)> {
        let mut result = Vec::new();
        for exp in expressions {
            let code = self.compile_arg(cx, exp);
            let type_ = match exp {
                Expr::Current(t) => t.clone(),
                Expr::Identifier(t, _) => t.clone(),
                Expr::Literal(t, _) => t.clone(),
                Expr::Ordinal(t) => t.clone(),
                Expr::Plus(t, _, _) => t.clone(),
                Expr::RecordSelector(t, _) => t.clone(),
                _ => Box::new(Type::Primitive(PrimitiveType::Unit)),
            };
            result.push((code, type_));
        }
        result
    }

    /// Compiles an expression that is evaluated once per row.
    pub fn compile_row(&self, cx: &Context, expression: &Expr) -> Box<Code> {
        let mut ordinal_slots = vec![0];

        Self::ORDINAL_CODE.with(|oc| {
            let old_slots = oc.replace(ordinal_slots.clone());
            let code = self.compile_with_context(cx, expression);
            ordinal_slots = oc.replace(old_slots);

            if ordinal_slots[0] == 0 {
                code
            } else {
                // The ordinal was used in at least one place.
                // Create a wrapper that will increment the ordinal each time.
                ordinal_slots[0] = -1;
                // TODO: Implement ordinal_inc
                code
            }
        })
    }

    /// Compiles a collection of expressions that are evaluated once per row.
    ///
    /// If one or more of those expressions references `ordinal`, add a
    /// wrapper around the first expression that increments the ordinal,
    /// similar to how `compile_row` does it.
    fn compile_row_map(
        &self,
        cx: &Context,
        name_exps: &[(String, Expr)],
    ) -> BTreeMap<String, Box<Code>> {
        let mut ordinal_slots = vec![0];

        Self::ORDINAL_CODE.with(|oc| {
            let old_slots = oc.replace(ordinal_slots.clone());
            let mut map_codes = BTreeMap::new();

            for (name, exp) in name_exps {
                let code = self.compile_with_context(cx, exp);
                map_codes.insert(name.clone(), code);
            }

            ordinal_slots = oc.replace(old_slots);

            if ordinal_slots[0] > 0 {
                // The ordinal was used in at least one place.
                // Create a wrapper that will increment the ordinal each time.
                ordinal_slots[0] = -1;
                // TODO: Apply ordinal increment wrapper to first code
            }

            map_codes
        })
    }

    pub fn compile_with_context(&self, cx: &Context, expr: &Expr) -> Box<Code> {
        match expr {
            // lint: sort until '#}' where '##Expr::'
            Expr::Apply(_, f, a) => {
                if let Expr::Literal(_t, literal) = f.as_ref()
                    // TODO Maybe remove Val::Impl, and switch back to Val::Fn?
                    // Inliner is too early to be mapping to native functions.
                    && let Val::Impl(f) = literal
                {
                    let codes = self.compile_args(cx, a.clone());
                    let boxed_codes: Vec<Box<Code>> =
                        codes.into_iter().map(Box::new).collect();
                    return Codes::native(*f, &boxed_codes);
                }
                todo!("compile {:}", expr)
            }
            Expr::List(_, args) => {
                let codes = self.compile_arg_list(cx, args);
                Codes::list(&codes)
            }
            Expr::Literal(_t, val) => Codes::constant(val.clone()),
            Expr::Tuple(_, args) => {
                let codes = self.compile_arg_list(cx, args);
                Codes::tuple(&codes)
            }
            _ => todo!("{:?}", expr),
        }
    }

    fn compile_let(&self, _cx: &Context, _let_exp: &Expr) -> Box<Code> {
        todo!("Implement compile_let")
    }

    fn link(_p0: &HashMap<String, Rc<Option<Code>>>, _p1: Pat, _p2: &Code) {
        todo!()
    }
}

/// Something that needs to happen when a declaration is evaluated.
///
/// Usually involves placing a type or value into the bindings that will
/// make up the environment in which the next statement will be executed and
/// printing some text on the screen.
trait Action {
    fn apply(&self, v: &mut EvalEnv);
}

// Simple action implementation
struct ValDeclAction {
    code: Box<Code>,
    pat: Pat,
}

impl Action for ValDeclAction {
    fn apply(&self, v: &mut EvalEnv) {
        match self.code.eval(v) {
            Err(_) => {
                v.emit_effect(Effect::EmitLine(
                    "error in val binding".to_string(),
                ));
            }
            Ok(o) => {
                let pretty = Self::get_pretty(&v.shell().unwrap().config);
                self.pat.bind_recurse(&o, &mut |p2, v2| {
                    // Emit a line 'val <name> = <value> : <type>'. The
                    // pretty-printer ensures that the value is formatted
                    // correctly for its type, and lines are correctly wrapped
                    // and indented per the shell configuration.
                    let mut line = String::new();
                    let id = p2.name().unwrap();
                    let typed_val =
                        Val::new_typed(&id, v2.clone(), &p2.type_());
                    let _ = pretty.pretty(&mut line, &p2.type_(), &typed_val);

                    v.emit_effect(Effect::EmitLine(line));
                });
            }
        }
    }
}

impl ValDeclAction {
    fn get_pretty(shell_config: &ShellConfig) -> Pretty {
        Pretty::new(
            shell_config.line_width.unwrap(),
            shell_config.output.unwrap(),
            shell_config.print_length.unwrap(),
            shell_config.print_depth.unwrap(),
            shell_config.string_depth.unwrap(),
        )
    }
}

/// Compilation context.
#[derive(Clone)]
pub struct Context {
    env: Environment,
}

impl Context {
    pub fn new(env: Environment) -> Self {
        Self { env }
    }

    pub fn bind_all(&self, bindings: &[Binding]) -> Self {
        Self::new(self.env.bind_all(bindings))
    }
}

pub trait CompiledStatement {
    fn get_type(&self) -> &Type;

    /// Evaluates the compiled statement, collecting effects instead of
    /// mutating state.
    fn eval(
        &self,
        session: &Session,
        shell: &Shell,
        _env: &Environment,
        effects: &mut Vec<Effect>,
        type_map: &TypeMap,
    );
}

struct CompiledStatementImpl {
    type_: Box<Type>,
    actions: Vec<Box<dyn Action>>,
    context: Context,
}

impl CompiledStatement for CompiledStatementImpl {
    fn get_type(&self) -> &Type {
        &self.type_
    }

    fn eval(
        &self,
        session: &Session,
        shell: &Shell,
        _env: &Environment,
        effects: &mut Vec<Effect>,
        type_map: &TypeMap,
    ) {
        let mut eval_env = EvalEnv::Root(session, shell, effects, type_map);
        for action in &self.actions {
            action.apply(&mut eval_env);
        }
    }
}

mod calcite_functions {
    use crate::eval::session::Session;
    use crate::shell::main::Environment;

    pub struct Context;

    impl Context {
        pub(crate) fn new(
            _session: Session,
            _environment: Environment,
        ) -> Context {
            todo!()
        }
    }
}
