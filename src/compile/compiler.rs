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

use crate::compile::core::{
    DatatypeBind, Decl, Expr, Match, Pat, Step, StepKind, TypeBind, ValBind,
};
use crate::compile::library::BuiltInFunction;
use crate::compile::pretty::Pretty;
use crate::compile::type_env::{Binding, Id};
use crate::compile::type_resolver::TypeMap;
use crate::compile::types::{PrimitiveType, Type};
use crate::compile::var_collector::VarCollector;
use crate::eval::code::{
    Code, Effect, EvalEnv, EvalMode, Frame, Impl, QueryStep,
};
use crate::eval::frame::FrameDef;
use crate::eval::order::Order;
use crate::eval::session::Session;
use crate::eval::val::Val;
use crate::shell::Shell;
use crate::shell::config::Config as ShellConfig;
use crate::shell::main::Environment;
use crate::shell::prop::Prop;
use std::cell::RefCell;
use std::cmp::Ordering;
use std::collections::{BTreeMap, HashSet};
use std::ops::Deref;
use std::sync::Arc;

/// Compiles a declaration to code that can be evaluated.
pub fn compile_statement(
    type_map: &TypeMap,
    env: &Environment,
    decl: &Decl,
) -> Box<dyn CompiledStatement> {
    let mut compiler = Compiler::new(type_map);
    compiler.compile_statement(env, decl, None, &HashSet::new())
}

struct Compiler<'a> {
    type_map: &'a TypeMap,
    links: Vec<Link>,
}

struct Link {
    name: String,
    code: Option<Arc<Code>>,
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

const UNIT_TYPE: Type = Type::Primitive(PrimitiveType::Unit);

impl<'a> Compiler<'a> {
    thread_local! {
        static ORDINAL_CODE: RefCell<Vec<i32>> = RefCell::new(vec![0]);
    }

    fn new(type_map: &'a TypeMap) -> Self {
        Self {
            type_map,
            links: Vec::new(),
        }
    }

    fn compile_statement(
        &mut self,
        env: &Environment,
        decl: &Decl,
        skip_pat: Option<Id>,
        queries_to_wrap: &HashSet<Expr>,
    ) -> Box<dyn CompiledStatement> {
        let mut match_codes = Vec::new();
        let mut bindings = Vec::new();
        let mut actions = Vec::new();
        let cx = Context::new(env.clone());

        let decl2 = Self::lift_decl(decl);
        let decl = &decl2;

        let mut collector = VarCollector::new(&cx.env);
        match decl {
            Decl::NonRecVal(val_bind) => {
                val_bind.pat.collect_vars(&mut collector);
            }
            Decl::RecVal(val_binds) => {
                for val_bind in val_binds {
                    val_bind.pat.collect_vars(&mut collector);
                }
            }
            Decl::Over(_) => {}
            Decl::Type(_) => {}
            Decl::Datatype(_) => {}
        };
        let cx1 = cx.with_frame(Arc::new(collector.into_frame_def()));

        self.compile_decl(
            &cx1,
            decl,
            skip_pat,
            queries_to_wrap,
            &mut match_codes,
            &mut bindings,
            Some(&mut actions),
        );

        let type_ = match decl {
            Decl::NonRecVal(val_bind) => val_bind.t.clone(),
            _ => UNIT_TYPE.clone(),
        };

        let context = self.create_context(env);
        let link_codes: Vec<Code> = self
            .links
            .iter()
            .filter_map(|link| {
                link.code.as_ref().map(|code| code.deref().clone())
            })
            .collect();

        Box::new(CompiledStatementImpl {
            type_,
            context,
            actions,
            link_codes,
        })
    }

    fn compile_decl(
        &mut self,
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
        &mut self,
        cx: &Context,
        decl: &Decl,
        _skip_pat: Option<Id>,
        _queries_to_wrap: &HashSet<Expr>,
        match_codes: &mut Vec<Code>,
        bindings: &mut Vec<Binding>,
        actions: Option<&mut Vec<Box<dyn Action>>>,
    ) {
        // Remember the ordinal of the first link.
        // After we have defined recursive functions, we will
        // iterate the links again and assign the code.
        let mut link_code_ordinal = self.links.len();

        if let Decl::RecVal(_) = decl {
            decl.for_each_binding(&mut |pat, _, _| {
                pat.for_each_id_pat(&mut |(_, name)| {
                    let link_code = self.create_link(name);
                    bindings.push(Binding::of_name_value(
                        name,
                        &Some(Val::Code(Arc::new(link_code))),
                    ));
                })
            });
        }

        let cx1 = cx.bind_all(bindings);

        // Collect all bindings first to avoid borrowing issues
        let mut collected_actions = Vec::new();

        decl.for_each_binding(
            &mut |pat: &Pat, expr: &Expr, _overload_pat: &Option<Box<Id>>| {
                let pat_code = self.compile_pat(&cx1, pat);
                let expr_code = Arc::new(self.compile_expr(&cx1, None, expr));
                match_codes.push(Code::new_bind(&pat_code, &expr_code));

                // Special treatment for 'val id =' so that 'fun' declarations
                // can be inlined.
                if let Pat::Identifier(_, name) = pat {
                    bindings.push(Binding::of_name_value(
                        name,
                        &Some(Val::Code(expr_code.clone())),
                    ))
                } else {
                    pat.for_each_id_pat(&mut |(_, name)| {
                        bindings.push(Binding::of_name(name))
                    });
                }

                // Populate links for recursive functions. We assume that
                // patterns will be traversed in the same order as before, and
                // therefore that links will be resolved in the same order that
                // they were created.
                if let Decl::RecVal(_) = decl {
                    pat.for_each_id_pat(&mut |(_, _)| {
                        self.links[link_code_ordinal].code =
                            Some(expr_code.clone());
                        link_code_ordinal += 1;
                    })
                }

                collected_actions.push(ValDeclAction {
                    code: expr_code.clone(),
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

    /// Compiles a pattern. Returns a code that returns whether the pattern
    /// matched, and if it matched, makes assignments to the current frame.
    #[allow(clippy::only_used_in_recursion)]
    pub fn compile_pat(&self, cx: &Context, pat: &Pat) -> Code {
        match pat {
            // lint: sort until '#}' where '##Pat::'
            Pat::Cons(_, head, tail) => {
                let head_code = self.compile_pat(cx, head);
                let tail_code = self.compile_pat(cx, tail);
                Code::new_bind_cons(&head_code, &tail_code)
            }
            Pat::Constructor(type_, name, p) => {
                let code = p.clone().map(|p2| self.compile_pat(cx, &p2));
                Code::new_bind_constructor(type_, name, &code)
            }
            Pat::Identifier(_, name) => {
                let slot = cx.frame_def.var_index(name);
                Code::new_bind_slot(&cx.frame_def, slot)
            }
            Pat::List(_, pats) => {
                let codes = pats
                    .iter()
                    .map(|p| self.compile_pat(cx, p))
                    .collect::<Vec<Code>>();
                Code::new_bind_list(&codes)
            }
            Pat::Literal(_, val) => Code::new_bind_literal(val),
            Pat::Tuple(_, pats) => {
                let codes = pats
                    .iter()
                    .map(|p| self.compile_pat(cx, p))
                    .collect::<Vec<Code>>();
                Code::new_bind_tuple(&codes)
            }
            Pat::Wildcard(_) => {
                // no variables to bind;
                // trivially succeeds
                Code::BindWildcard
            }
            _ => {
                todo!("compile_pat: {:?}", pat)
            }
        }
    }

    /// Compiles the argument to "apply".
    pub fn compile_arg(&mut self, cx: &Context, expr: &Expr) -> Code {
        self.compile_expr(cx, None, expr)
    }

    /// Compiles the argument to a call, producing a list with N elements if the
    /// argument is an N-tuple.
    pub fn compile_args(&mut self, cx: &Context, expr: &Expr) -> Vec<Code> {
        match expr {
            Expr::Tuple(_, args) => self.compile_arg_list(cx, args),
            _ => vec![self.compile_expr(cx, None, expr)],
        }
    }

    /// As [Compiler::compile_args], but returns a list of `Box<Code>`.
    #[allow(clippy::vec_box)]
    fn compile_args_boxed(
        &mut self,
        cx: &Context,
        expr: &Expr,
    ) -> Vec<Box<Code>> {
        self.compile_args(cx, expr)
            .into_iter()
            .map(Box::new)
            .collect()
    }

    /// Compiles the tuple arguments to "apply".
    pub fn compile_arg_list(
        &mut self,
        cx: &Context,
        args: &[Expr],
    ) -> Vec<Code> {
        args.iter()
            .map(|e| self.compile_expr(cx, None, e))
            .collect()
    }

    /// Compiles an expression that is evaluated once per row.
    pub fn compile_row(&mut self, cx: &Context, expression: &Expr) -> Code {
        let mut ordinal_slots = vec![0];

        Self::ORDINAL_CODE.with(|oc| {
            let old_slots = oc.replace(ordinal_slots.clone());
            let code = self.compile_expr(cx, None, expression);
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
        &mut self,
        cx: &Context,
        name_exps: &[(String, Expr)],
    ) -> BTreeMap<String, Code> {
        let mut ordinal_slots = vec![0];

        Self::ORDINAL_CODE.with(|oc| {
            let old_slots = oc.replace(ordinal_slots.clone());
            let mut map_codes = BTreeMap::new();

            for (name, exp) in name_exps {
                let code = self.compile_expr(cx, None, exp);
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

    /// Compiles an expression.
    pub fn compile_expr(
        &mut self,
        cx: &Context,
        _pcx: Option<&Context>,
        expr: &Expr,
    ) -> Code {
        match expr {
            // lint: sort until '#}' where '##Expr::'
            Expr::Apply(_, f, a, span) => match f.as_ref() {
                Expr::Literal(_t, Val::Fn(f)) => {
                    let impl_ = f.get_impl();
                    let codes = self.compile_args_boxed(cx, a);
                    // TODO: Support partial application of curried built-in
                    // functions. Currently only works when all arguments are
                    // provided.
                    Code::new_native(impl_, &codes, span)
                }
                // Handle curried application of EF3 functions like
                // List.foldl. Pattern:
                //   ((List.foldl f) init) list => List.foldl (f, init, list)
                Expr::Apply(_, middle_f, second_arg, _) => {
                    if let Expr::Apply(_, inner_f, first_arg, _) =
                        middle_f.as_ref()
                        && let Expr::Literal(_t, Val::Fn(func)) =
                            inner_f.as_ref()
                        && matches!(func.get_impl(), Impl::EF3(_))
                    {
                        // This is a curried call to an EF3 function.
                        // Gather all three arguments.
                        let arg1_code =
                            Box::new(self.compile_arg(cx, first_arg));
                        let arg2_code =
                            Box::new(self.compile_arg(cx, second_arg));
                        let arg3_code = Box::new(self.compile_arg(cx, a));
                        return Code::new_native(
                            func.get_impl(),
                            &[arg1_code, arg2_code, arg3_code],
                            span,
                        );
                    }

                    // Handle curried application of EF4 functions like
                    // ListPair.foldlEq. Pattern:
                    //   ((ListPair.foldlEq f) init) tuple =>
                    //   ListPair.foldlEq (f, init, tuple)
                    if let Expr::Apply(_, inner_f, first_arg, _) =
                        middle_f.as_ref()
                        && let Expr::Literal(_t, Val::Fn(func)) =
                            inner_f.as_ref()
                        && matches!(func.get_impl(), Impl::EF4(_))
                    {
                        // This is a curried call to an EF4 function.
                        // Gather all three arguments.
                        let arg1_code =
                            Box::new(self.compile_arg(cx, first_arg));
                        let arg2_code =
                            Box::new(self.compile_arg(cx, second_arg));
                        let arg3_code = Box::new(self.compile_arg(cx, a));
                        return Code::new_native(
                            func.get_impl(),
                            &[arg1_code, arg2_code, arg3_code],
                            span,
                        );
                    }

                    // Handle curried application of 2-argument EF3 functions
                    // like ListPair.allEq. Pattern:
                    //   (ListPair.allEq f) tuple => ListPair.allEq (f, tuple)
                    if let Expr::Literal(_t, Val::Fn(func)) = middle_f.as_ref()
                        && matches!(func.get_impl(), Impl::EF3(_))
                    {
                        // This is a curried call to a 2-argument EF3 function.
                        // Gather both arguments.
                        let arg1_code =
                            Box::new(self.compile_arg(cx, second_arg));
                        let arg2_code = Box::new(self.compile_arg(cx, a));
                        return Code::new_native(
                            func.get_impl(),
                            &[arg1_code, arg2_code],
                            span,
                        );
                    }

                    // Handle curried application of EV2 and E2 functions like
                    // String.map and String.isPrefix. Pattern:
                    //   (String.map f) s => String.map (f, s)
                    if let Expr::Literal(_t, Val::Fn(func)) = middle_f.as_ref()
                        && matches!(func.get_impl(), Impl::EF2(_) | Impl::E2(_))
                    {
                        // This is a curried call to an EF2 or E2 function.
                        // Gather both arguments.
                        let arg1_code =
                            Box::new(self.compile_arg(cx, second_arg));
                        let arg2_code = Box::new(self.compile_arg(cx, a));
                        return Code::new_native(
                            func.get_impl(),
                            &[arg1_code, arg2_code],
                            span,
                        );
                    }
                    // Fall through to default handling
                    let arg_code = self.compile_arg(cx, a);
                    let fn_code = self.compile_arg(cx, f);
                    Code::new_apply(&fn_code, &arg_code, &[])
                }
                Expr::Identifier(type_, name) => {
                    let arg_code = self.compile_arg(cx, a);
                    let fn_code =
                        if let Some(Val::Code(code)) = &cx.env.get(name) {
                            Code::new_constant(type_, Val::Code(code.clone()))
                        } else {
                            self.compile_arg(cx, f)
                        };
                    Code::new_apply(
                        &fn_code,
                        &arg_code,
                        &cx.frame_def.bound_vars,
                    )
                }
                _ => {
                    let arg_code = self.compile_arg(cx, a);
                    let fn_code = self.compile_arg(cx, f);
                    Code::new_apply(&fn_code, &arg_code, &[])
                }
            },
            Expr::Case(_, expr, matches) => {
                let expr_code = self.compile_expr(cx, None, expr);
                let mut codes = vec![expr_code];

                for m in matches {
                    let pat_code = self.compile_pat(cx, &m.pat);
                    let expr_code = self.compile_expr(cx, None, &m.expr);
                    codes.push(pat_code);
                    codes.push(expr_code);
                }
                Code::new_match(&codes)
            }
            Expr::Fn(_, match_list) => {
                let mut collector = VarCollector::new(&cx.env);
                for m in match_list {
                    m.collect_vars(&mut collector);
                }
                let frame_def = Arc::new(collector.into_frame_def());

                let cx1 = cx.with_frame(frame_def.clone());
                let mut pat_expr_codes = Vec::new();
                assert!(!match_list.is_empty(), "match list is empty");
                for m in match_list {
                    let pat_code = self.compile_pat(&cx1, &m.pat);
                    let expr_code = self.compile_expr(&cx1, Some(cx), &m.expr);
                    pat_expr_codes.push((pat_code, expr_code));
                }
                if frame_def.bound_vars.is_empty() {
                    Code::new_fn(&cx1.frame_def, &pat_expr_codes)
                } else {
                    let mut codes = Vec::new();
                    for binding in &frame_def.bound_vars {
                        // Create code to move the closure values into the
                        // closure. We use pcx because it needs to execute in
                        // the caller's environment.
                        // Use a dummy type (until binding has a type).
                        let type_ = Box::new(UNIT_TYPE);
                        let id = Expr::Identifier(
                            type_,
                            binding.id.name.to_string(),
                        );
                        let code = self.compile_expr(cx, None, &id);
                        codes.push(code);
                    }
                    Code::new_create_closure(
                        &cx1.frame_def,
                        &pat_expr_codes,
                        &codes,
                    )
                }
            }
            Expr::From(_, steps) => {
                let compiled_steps: Vec<QueryStep> = steps
                    .iter()
                    .map(|step| self.compile_step(cx, step))
                    .collect();
                Code::From(compiled_steps)
            }
            Expr::Identifier(_, name) => {
                let slot = cx.frame_def.var_index(name);
                Code::new_get_local(&cx.frame_def, slot)
            }
            Expr::Let(_, decl_list, expr) => {
                let mut bindings = Vec::new();
                let mut match_codes = Vec::new();
                for d in decl_list {
                    self.compile_decl(
                        cx,
                        d,
                        None,
                        &HashSet::new(),
                        &mut match_codes,
                        bindings.as_mut(),
                        None,
                    );
                }
                let cx1 = cx.bind_all(&bindings);
                let code = self.compile_expr(&cx1, Some(cx), expr);
                Code::new_let(&match_codes, code)
            }
            Expr::List(_, args) => {
                let codes = self.compile_arg_list(cx, args);
                Code::new_list(&codes)
            }
            Expr::Literal(type_, val) => {
                // Convert zero-argument constructors to their values
                let val2 = match val {
                    Val::Fn(BuiltInFunction::OptionNone) => Val::Unit,
                    Val::Fn(BuiltInFunction::OrderLess) => {
                        Val::Order(Order(Ordering::Less))
                    }
                    Val::Fn(BuiltInFunction::OrderEqual) => {
                        Val::Order(Order(Ordering::Equal))
                    }
                    Val::Fn(BuiltInFunction::OrderGreater) => {
                        Val::Order(Order(Ordering::Greater))
                    }
                    _ => val.clone(),
                };
                Code::new_constant(type_, val2.clone())
            }
            Expr::RecordSelector(t, slot) => {
                let (record_type, _) = t.expect_fn();
                Code::new_nth(record_type, *slot)
            }
            Expr::Tuple(_, args) => {
                let codes = self.compile_arg_list(cx, args);
                Code::new_tuple(&codes)
            }
            _ => todo!("{:?}", expr),
        }
    }

    fn compile_step(&mut self, cx: &Context, step: &Step) -> QueryStep {
        match &step.kind {
            StepKind::JoinIn(pat, expr, _cond) => {
                let pat_code = self.compile_pat(cx, pat);
                let expr_code = self.compile_expr(cx, None, expr);
                QueryStep::JoinIn(pat_code, expr_code)
            }
            StepKind::Where(expr) => {
                let expr_code = self.compile_expr(cx, None, expr);
                QueryStep::Where(expr_code)
            }
            StepKind::Yield(expr) => {
                let expr_code = self.compile_expr(cx, None, expr);
                QueryStep::Yield(expr_code)
            }
            _ => todo!("compile_step: {:?}", step.kind),
        }
    }

    fn create_link(&mut self, name: &str) -> Code {
        let i = self.links.len();
        self.links.push(Link {
            name: name.to_string(),
            code: None,
        });
        Code::new_link(i, name)
    }

    /// Converts a value declaration into a function whose argument is the
    /// evaluation environment.
    ///
    /// For example, the following declaration references `Foo.bar` from the
    /// environment.
    ///
    /// ```sml
    /// val x = Foo.bar + 2;
    /// ```
    ///
    /// It is converted to
    ///
    /// ```sml
    /// val x = fn {bar: int} => bar + 2;
    /// ```
    ///
    /// If an expression reads nothing from the environment, it still becomes
    /// a function, but the argument is `()`, of type `unit`.
    fn lift_decl(decl: &Decl) -> Decl {
        match decl {
            Decl::NonRecVal(val_bind) => {
                // Convert 'val p = e' to 'val p = fn arg => e'.
                let val_bind2 = Self::lift_val_bind(val_bind);
                Decl::NonRecVal(Box::new(val_bind2))
            }
            Decl::RecVal(val_binds) => {
                // Convert 'val p1 = e1 and p2 = e2'
                // to 'val p1 = fn arg => e1 and p2 = fn arg => e2'.
                let mut val_binds2 = Vec::new();
                for val_bind in val_binds {
                    val_binds2.push(Self::lift_val_bind(val_bind));
                }
                Decl::RecVal(val_binds2)
            }
            _ => decl.clone(),
        }
    }

    fn lift_val_bind(val_bind: &ValBind) -> ValBind {
        let pat2 = val_bind.pat.clone();
        let t2 = val_bind.t.clone();
        let param_type = UNIT_TYPE;
        let result_type = val_bind.expr.type_().clone();
        let fn_type = Type::Fn(Box::new(param_type), result_type);
        let match_ = Match {
            pat: Pat::Literal(Box::new(UNIT_TYPE), Val::Unit),
            expr: val_bind.expr.clone(),
        };
        let expr2 = Expr::Fn(Box::new(fn_type), vec![match_]);
        ValBind::of(&pat2, &t2, &expr2)
    }
}

/// Something that needs to happen when a declaration is evaluated.
///
/// Usually involves placing a type or value into the bindings that will
/// make up the environment in which the next statement will be executed and
/// printing some text on the screen.
trait Action {
    fn apply(&self, r: &mut EvalEnv, f: &mut Frame);
}

// Simple action implementation
struct ValDeclAction {
    code: Arc<Code>,
    pat: Pat,
}

impl Action for ValDeclAction {
    fn apply(&self, r: &mut EvalEnv, f: &mut Frame) {
        // self.code is a function with unit argument.
        self.code.assert_supports_eval_mode(&EvalMode::EagerV1);
        r.emit_effect(Effect::EmitCode(self.code.clone()));
        match self.code.eval_f1(r, f, &Val::Unit) {
            Err(e) => {
                r.emit_effect(Effect::EmitLine(e.to_string()));
            }
            Ok(o) => {
                let pretty = Self::get_pretty(&r.shell.config);
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

                    let binding =
                        Binding::of_name_value(id.as_str(), &Some(v2.clone()));
                    r.emit_effect(Effect::AddBinding(binding));
                    r.emit_effect(Effect::EmitLine(line));
                });
            }
        }
    }
}

impl ValDeclAction {
    fn get_pretty(shell_config: &ShellConfig) -> Pretty {
        Pretty::new(
            shell_config
                .line_width
                .unwrap_or_else(|| Prop::LineWidth.default_value().as_int()),
            shell_config.output.unwrap(),
            shell_config
                .print_length
                .unwrap_or_else(|| Prop::PrintLength.default_value().as_int()),
            shell_config
                .print_depth
                .unwrap_or_else(|| Prop::PrintDepth.default_value().as_int()),
            shell_config
                .string_depth
                .unwrap_or_else(|| Prop::StringDepth.default_value().as_int()),
        )
    }
}

/// Compilation context.
#[derive(Clone)]
pub struct Context {
    env: Environment,

    /// Definition of the current stack frame.
    frame_def: Arc<FrameDef>,
}

impl Context {
    pub fn new(env: Environment) -> Self {
        Self {
            env,
            frame_def: Arc::new(FrameDef::new(&[], &[])),
        }
    }

    pub fn bind_all(&self, bindings: &[Binding]) -> Self {
        Self {
            env: self.env.bind_all(bindings),
            frame_def: self.frame_def.clone(),
        }
    }

    /// Creates a context with a new frame. The frame has space for a new set of
    /// variables.
    ///
    /// This function is called when we start generating code for a function
    /// (`fn`). Space is needed for the function parameters, all the values
    /// bound by the patterns, and by values declared within the body of a
    /// function.
    ///
    /// For example, consider the following function declaration:
    ///
    /// ```sml
    /// fun tree_size EMPTY = 0
    ///   | tree_size LEAF n = 1
    ///   | tree_size NODE (left, right) =
    ///     let
    ///        val left_size = tree_size left
    ///        and right_size = tree_size right
    ///     in
    ///       left_size + right_size
    ///     end
    /// ```
    ///
    /// It desugars to a function value:
    ///
    /// ```sml
    /// val rec tree_size =
    ///   fn EMPTY => 0
    ///    | LEAF n => 1
    ///    | tree_size NODE (left, right) =>
    ///      let
    ///        val left_size = tree_size left
    ///        and right_size = tree_size right
    ///      in
    ///        left_size + right_size
    ///      end;
    /// ```
    ///
    /// The variables are [`n`, `left`, `right`, `left_size`, `right_size`].
    /// (Yes, some of those can be inlined or removed, and some variables
    /// could occupy the same slot. But let's not consider optimizations here.)
    pub(crate) fn with_frame(&self, frame_def: Arc<FrameDef>) -> Self {
        Context {
            env: self.env.clone(),
            frame_def,
        }
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
    type_: Type,
    actions: Vec<Box<dyn Action>>,
    context: Context,
    link_codes: Vec<Code>,
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
        _type_map: &TypeMap,
    ) {
        let mut eval_env =
            EvalEnv::new(session, shell, effects, &self.link_codes);
        let mut vals = vec![];
        let mut frame = Frame { vals: &mut vals };
        for action in &self.actions {
            action.apply(&mut eval_env, &mut frame);
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
