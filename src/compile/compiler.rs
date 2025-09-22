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

use crate::compile::core::{DatatypeBind, Decl, Expr, Match, Pat, TypeBind};
use crate::compile::pretty::Pretty;
use crate::compile::type_env::{Binding, Id};
use crate::compile::type_resolver::TypeMap;
use crate::compile::types::{PrimitiveType, Type};
use crate::eval::code::{Code, Effect, EvalEnv, EvalMode, Frame};
use crate::eval::session::Session;
use crate::eval::val::Val;
use crate::shell::Shell;
use crate::shell::config::Config as ShellConfig;
use crate::shell::main::Environment;
use std::cell::RefCell;
use std::collections::{BTreeMap, HashSet};

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
    code: Option<Code>,
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
            _ => Type::Primitive(PrimitiveType::Unit),
        };

        let context = self.create_context(env);
        let link_codes: Vec<Code> =
            self.links.iter().filter_map(|l| l.code.clone()).collect();

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
        let binding_count = bindings.len();
        Self::bind_pattern(bindings, decl);

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
                        &Some(Val::Code(Box::new(link_code))),
                    ));
                })
            });
        }

        let new_bindings = &bindings.as_slice()[binding_count..];
        let cx1 = cx.bind_all(new_bindings);
        bindings.truncate(binding_count);

        // Collect all bindings first to avoid borrowing issues
        let mut collected_actions = Vec::new();

        decl.for_each_binding(
            &mut |pat: &Pat, expr: &Expr, _overload_pat: &Option<Box<Id>>| {
                let pat_code = self.compile_pat(&cx1, pat);

                let fn_expr = if actions.is_some() {
                    // If there are actions, we are at the top level.
                    // Wrap 'expr' as 'fn () => 'expr'. A function is able to
                    // allocate a frame with space for all local variables.
                    Expr::Fn(
                        Box::new(Type::Fn(
                            Box::new(Type::Primitive(PrimitiveType::Unit)),
                            expr.type_(),
                        )),
                        vec![Match {
                            pat: Pat::Literal(
                                Box::new(Type::Primitive(PrimitiveType::Unit)),
                                Val::Unit,
                            ),
                            expr: expr.clone(),
                        }],
                    )
                } else {
                    expr.clone()
                };
                let expr_code = self.compile_expr(&cx1, &fn_expr);
                match_codes.push(Code::new_bind(&pat_code, &expr_code));

                // Special treatment for 'val id =' so that 'fun' declarations
                // can be inlined.
                if let Pat::Identifier(_, name) = pat {
                    bindings.push(Binding::of_name_value(
                        name,
                        &Some(Val::Code(Box::new(expr_code.clone()))),
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

    /// Richer than {@link #acceptBinding(TypeSystem, Core.Pat, List)}
    /// because we have the expression.
    fn bind_pattern(bindings: &mut Vec<Binding>, decl: &Decl) {
        decl.for_each_binding(
            &mut (|pat: &Pat,
                   _expr: &Expr,
                   _overload_pat: &Option<Box<Id>>| {
                if let Pat::Identifier(_, name) = pat {
                    bindings.push(Binding::of_name(name));
                }
            }),
        );
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
            Pat::Identifier(_, name) => {
                let i = cx.var_index(name);
                Code::new_bind_slot(i, name)
            }
            Pat::Literal(_, val) => Code::new_bind_literal(val),
            Pat::Tuple(_, pats) => {
                let codes = pats
                    .iter()
                    .map(|p| self.compile_pat(cx, p))
                    .collect::<Vec<Code>>();
                Code::new_match_tuple(&codes)
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
        self.compile_expr(cx, expr)
    }

    /// Compiles the argument to a call, producing a list with N elements if the
    /// argument is an N-tuple.
    pub fn compile_args(&mut self, cx: &Context, expr: &Expr) -> Vec<Code> {
        match expr {
            Expr::Tuple(_, args) => self.compile_arg_list(cx, args),
            _ => vec![self.compile_expr(cx, expr)],
        }
    }

    /// Compiles the tuple arguments to "apply".
    pub fn compile_arg_list(
        &mut self,
        cx: &Context,
        args: &[Expr],
    ) -> Vec<Code> {
        args.iter().map(|e| self.compile_expr(cx, e)).collect()
    }

    /// Compiles an expression that is evaluated once per row.
    pub fn compile_row(&mut self, cx: &Context, expression: &Expr) -> Code {
        let mut ordinal_slots = vec![0];

        Self::ORDINAL_CODE.with(|oc| {
            let old_slots = oc.replace(ordinal_slots.clone());
            let code = self.compile_expr(cx, expression);
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
                let code = self.compile_expr(cx, exp);
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
    pub fn compile_expr(&mut self, cx: &Context, expr: &Expr) -> Code {
        match expr {
            // lint: sort until '#}' where '##Expr::'
            Expr::Apply(_, f, a) => {
                match f.as_ref() {
                    Expr::Literal(_t, Val::Fn(f)) => {
                        let impl_ = f.get_impl();
                        let codes = self.compile_args(cx, a);
                        return Code::new_native(impl_, &codes);
                    }
                    Expr::Identifier(_, name) => {
                        if let Some(Val::Code(fn_code)) = cx.env.get(name) {
                            let arg_code = self.compile_arg(cx, a);
                            return Code::new_apply(fn_code, &arg_code);
                        }
                    }
                    _ => {}
                }
                todo!("compile {:}", expr)
            }
            Expr::Case(_, expr, matches) => {
                let expr_code = self.compile_expr(cx, expr);
                let mut codes = vec![expr_code];

                for m in matches {
                    let pat_code = self.compile_pat(cx, &m.pat);
                    let expr_code = self.compile_expr(cx, &m.expr);
                    codes.push(pat_code);
                    codes.push(expr_code);
                }
                Code::new_match(&codes)
            }
            Expr::Fn(_, match_list) => {
                let mut vars = Vec::new();
                match_list.iter().for_each(|m| {
                    m.collect_vars(&mut vars);
                });

                let cx1 = cx.with_frame(&vars);
                let mut pat_expr_codes = Vec::new();
                assert!(!match_list.is_empty(), "match list is empty");
                for m in match_list {
                    let pat_code = self.compile_pat(&cx1, &m.pat);
                    let expr_code = self.compile_expr(&cx1, &m.expr);
                    pat_expr_codes.push((pat_code, expr_code));
                }
                Code::new_fn(&cx1.local_vars, &pat_expr_codes)
            }
            Expr::Identifier(_, name) => Code::GetLocal(cx.var_index(name)),
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
                let code = self.compile_expr(&cx1, expr);
                Code::Let(match_codes, Box::new(code))
            }
            Expr::List(_, args) => {
                let codes = self.compile_arg_list(cx, args);
                Code::new_list(&codes)
            }
            Expr::Literal(_t, val) => Code::new_constant(val.clone()),
            Expr::Tuple(_, args) => {
                let codes = self.compile_arg_list(cx, args);
                Code::new_tuple(&codes)
            }
            _ => todo!("{:?}", expr),
        }
    }

    fn create_link(&mut self, name: &str) -> Code {
        let i = self.links.len();
        self.links.push(Link {
            name: name.to_string(),
            code: None,
        });
        Code::Link(i, name.to_string())
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
    code: Code,
    pat: Pat,
}

impl Action for ValDeclAction {
    fn apply(&self, r: &mut EvalEnv, f: &mut Frame) {
        // self.code is a function with unit argument.
        self.code.assert_supports_eval_mode(&EvalMode::EagerV1);
        match self.code.eval_f1(r, f, &Val::Unit) {
            Err(_) => {
                r.emit_effect(Effect::EmitLine(
                    "error in val binding".to_string(),
                ));
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

                    r.emit_effect(Effect::EmitLine(line));
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

    /// The local variables in the current stack frame.
    local_vars: Vec<Id>,
}

impl Context {
    pub fn new(env: Environment) -> Self {
        Self {
            env,
            local_vars: Vec::new(),
        }
    }

    pub fn bind_all(&self, bindings: &[Binding]) -> Self {
        let local_vars: Vec<Id> =
            bindings.iter().map(|b| b.id.clone()).collect();
        Self {
            env: self.env.bind_all(bindings),
            local_vars,
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
    pub(crate) fn with_frame(&self, vars: &[Id]) -> Self {
        Context {
            env: self.env.clone(),
            local_vars: vars.to_vec(),
        }
    }

    /// Returns the index within the current frame of a variable with a given
    /// name. Panics if not found.
    pub(crate) fn var_index(&self, name: &str) -> usize {
        self.local_vars
            .iter()
            .position(|v| v.name == name)
            .unwrap_or_else(|| {
                panic!(
                    "variable {} not found in frame {:?}",
                    name, self.local_vars
                )
            })
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

impl Pat {
    fn collect_vars(&self, vars: &mut Vec<Id>) {
        match self {
            // lint: sort until '#}' where '##Pat::'
            Pat::As(_, name, pat) => {
                vars.push(Id::new(name, 0));
                pat.collect_vars(vars);
            }
            Pat::Identifier(_, name) => {
                vars.push(Id::new(name, 0));
            }
            Pat::Literal(_, _) => {
                // no variables
            }
            Pat::Tuple(_, pats) => {
                pats.iter().for_each(|p| p.collect_vars(vars));
            }
            Pat::Wildcard(_) => {
                // no variables
            }
            _ => todo!("collect_vars {:?}", self),
        }
    }
}

impl Match {
    fn collect_vars(&self, vars: &mut Vec<Id>) {
        self.pat.collect_vars(vars);
        self.expr.collect_vars(vars);
    }
}

impl Decl {
    fn collect_vars(&self, vars: &mut Vec<Id>) {
        match self {
            Decl::NonRecVal(val_bind) => {
                val_bind.pat.collect_vars(vars);
                val_bind.expr.collect_vars(vars);
            }
            Decl::RecVal(val_binds) => {
                for val_bind in val_binds {
                    val_bind.pat.collect_vars(vars);
                    val_bind.expr.collect_vars(vars);
                }
            }
            _ => {
                // no expressions in other declarations, therefore no variables
            }
        }
    }
}

impl Expr {
    fn collect_vars(&self, vars: &mut Vec<Id>) {
        match self {
            // lint: sort until '#}' where '##Expr::'
            Expr::Apply(_, f, a) => {
                f.collect_vars(vars);
                a.collect_vars(vars);
            }
            Expr::Case(_, expr, matches) => {
                expr.collect_vars(vars);
                matches.iter().for_each(|m| m.collect_vars(vars));
            }
            Expr::Fn(_, matches) => {
                matches.iter().for_each(|m| m.collect_vars(vars));
            }
            Expr::Identifier(_, name) => {
                vars.push(Id::new(name, 0));
            }
            Expr::Let(_, decls, _) => {
                decls.iter().for_each(|d| d.collect_vars(vars));
            }
            Expr::List(_, exprs) | Expr::Tuple(_, exprs) => {
                exprs.iter().for_each(|e| e.collect_vars(vars));
            }
            Expr::Literal(_, _) => {
                // no variables
            }
            _ => todo!("collect_vars {:?}", self),
        }
    }
}
