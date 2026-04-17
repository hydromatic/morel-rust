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
    DatatypeBind, Decl, Expr, Match, Pat, PatField, Step, StepEnv, StepKind,
    TypeBind, ValBind,
};
use crate::compile::library::{BuiltInExn, BuiltInFunction};
use crate::compile::pretty::Pretty;
use crate::compile::type_env::{Binding, Id};
use crate::compile::type_resolver::TypeMap;
use crate::compile::types::{Label, PrimitiveType, Type};
use crate::compile::var_collector::VarCollector;
use crate::eval::code::{
    self, CmpRef, Code, Effect, EvalEnv, EvalMode, Frame, Impl, QueryStep, Span,
};
use crate::eval::comparator::{self, comparator_for};
use crate::eval::frame::FrameDef;
use crate::eval::link_table::LinkTable;
use crate::eval::order::Order;
use crate::eval::row_sink::{RowSink, RowSinkFactory};
use crate::eval::session::Session;
use crate::eval::val::Val;
use crate::shell::Shell;
use crate::shell::config::Config as ShellConfig;
use crate::shell::main::{Environment, MorelError};
use crate::shell::prop::Prop;
use std::cell::RefCell;
use std::cmp::Ordering;
use std::collections::{BTreeMap, HashMap, HashSet};
use std::sync::Arc;

/// Compiles a declaration to code that can be evaluated.
///
/// `link_table` is the shell-wide, persistent table of recursive
/// `Code` references. The compiler reserves and fills slots in
/// it; the slots remain valid forever, so functions defined in
/// this statement can resolve their self-references when invoked
/// from later statements. See [`LinkTable`] for the rationale.
pub fn compile_statement(
    type_map: &TypeMap,
    env: &Environment,
    decl: &Decl,
    link_table: &mut LinkTable,
) -> Box<dyn CompiledStatement> {
    let mut compiler = Compiler::new(type_map, link_table);
    compiler.compile_statement(env, decl, None, &HashSet::new())
}

struct Compiler<'a> {
    type_map: &'a TypeMap,
    /// The shell-wide link table. Recursive function bodies
    /// reserve a slot in this table while compiling their
    /// pattern, then fill it once the body is compiled. Slots
    /// are absolute indices into this table — they remain valid
    /// across statement boundaries, allowing recursive functions
    /// to be invoked from a later statement.
    link_table: &'a mut LinkTable,
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

    fn new(type_map: &'a TypeMap, link_table: &'a mut LinkTable) -> Self {
        Self {
            type_map,
            link_table,
        }
    }

    /// Looks up the ordinal (0-based position) of a constructor within its
    /// datatype declaration. Returns `None` for built-in types.
    fn constructor_ordinal(&self, type_: &Type, name: &str) -> Option<usize> {
        if let Type::Data(datatype_name, _) = type_
            && let Some(constructors) =
                self.type_map.datatype_constructors.get(datatype_name)
        {
            return constructors.iter().position(|c| c == name);
        }
        None
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

        Box::new(CompiledStatementImpl {
            type_,
            context,
            actions,
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
        // Remember the absolute slot of the first link reserved
        // by this declaration. After we have compiled the
        // recursive bodies we walk the patterns in the same order
        // and fill these slots in the shell-wide link table.
        let mut link_code_ordinal = self.link_table.len();

        if let Decl::RecVal(_) = decl {
            decl.for_each_binding(&mut |pat, _, _, _| {
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
            &mut |pat: &Pat,
                  expr: &Expr,
                  _overload_pat: &Option<Box<Id>>,
                  span: &Option<Span>| {
                let pat_code = self.compile_pat(&cx1, pat);
                let expr_code = Arc::new(self.compile_expr(&cx1, None, expr));
                match_codes.push(Code::new_bind_with_span(
                    &pat_code,
                    &expr_code,
                    span.clone(),
                ));

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
                    // Strip the unit-arg wrapper that `lift_decl`
                    // applies to the val expression. The wrapper
                    // has the shape
                    //   Code::Fn(_, [(BindLiteral(Unit), inner)], _)
                    // and exists only so that ValDeclAction can
                    // call eval_f1(unit) to obtain the value.
                    // Recursive references resolve through the
                    // LinkTable and must see the *inner* function
                    // (the actual user-defined fn), not the
                    // wrapper, otherwise calling the function
                    // recursively would re-pass the recursive
                    // argument through the unit-pattern and raise
                    // a Match exception.
                    let inner_code: Arc<Code> = match expr_code.as_ref() {
                        Code::Fn(_, matches, _)
                            if matches.len() == 1
                                && matches!(
                                    matches[0].0,
                                    Code::BindLiteral(Val::Unit)
                                ) =>
                        {
                            Arc::new(matches[0].1.clone())
                        }
                        _ => expr_code.clone(),
                    };
                    pat.for_each_id_pat(&mut |(_, _)| {
                        self.link_table
                            .fill(link_code_ordinal, inner_code.clone());
                        link_code_ordinal += 1;
                    })
                }

                collected_actions.push(ValDeclAction {
                    code: expr_code.clone(),
                    pat: pat.clone(),
                    span: span.clone(),
                    constructor_arg_types: self
                        .type_map
                        .constructor_arg_types
                        .clone(),
                    datatype_constructors: self
                        .type_map
                        .datatype_constructors
                        .clone(),
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
        name: &str,
        _bindings: &mut [Binding],
        actions: Option<&mut Vec<Box<dyn Action>>>,
    ) {
        if let Some(actions) = actions {
            actions.push(Box::new(OverDeclAction {
                name: name.to_string(),
            }));
        }
    }

    fn compile_type_decl(
        &self,
        type_binds: &[TypeBind],
        _bindings: &mut [Binding],
        actions: Option<&mut Vec<Box<dyn Action>>>,
    ) {
        // For each 'type name = body' binding, emit one line of the form
        // 'type name = body'. Multiple type bindings join with '\n'.
        if let Some(actions) = actions {
            for tb in type_binds {
                actions.push(Box::new(TypeDeclAction {
                    name: tb.name.clone(),
                    type_: tb.type_.clone(),
                }));
            }
        }
    }

    fn compile_datatype_decl(
        &self,
        datatype_binds: &[DatatypeBind],
        _bindings: &mut [Binding],
        actions: Option<&mut Vec<Box<dyn Action>>>,
    ) {
        if let Some(actions) = actions {
            for db in datatype_binds {
                actions.push(Box::new(DatatypeDeclAction {
                    datatype_bind: db.clone(),
                }));
            }
        }
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
            Pat::As(_, name, inner) => {
                // 'p as inner_pat' binds 'p' to the value AND recurses
                // into 'inner_pat'. Both apply to the same value, so
                // emit a BindAnd that runs both pattern codes.
                let slot = cx.frame_def.var_index(name);
                let outer_code = Code::new_bind_slot(&cx.frame_def, slot);
                let inner_code = self.compile_pat(cx, inner);
                Code::BindAnd(vec![outer_code, inner_code])
            }
            Pat::Cons(_, head, tail) => {
                let head_code = self.compile_pat(cx, head);
                let tail_code = self.compile_pat(cx, tail);
                Code::new_bind_cons(&head_code, &tail_code)
            }
            Pat::Constructor(type_, name, p) => {
                let code = p.clone().map(|p2| self.compile_pat(cx, &p2));
                let ordinal = self.constructor_ordinal(type_, name);
                Code::new_bind_constructor(type_, name, ordinal, &code)
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
            Pat::Record(_, fields, _) if fields.is_empty() => {
                // Empty record pattern {} matches unit (); trivially succeeds.
                Code::BindWildcard
            }
            Pat::Record(type_, fields, _has_ellipsis) => {
                // Build a name→sub-pat map from the pattern fields.
                let mut field_map: BTreeMap<String, &Pat> = BTreeMap::new();
                for f in fields {
                    match f {
                        PatField::Labeled(name, sub_pat) => {
                            field_map.insert(name.clone(), sub_pat);
                        }
                        PatField::Anonymous(sub_pat) => {
                            if let Some(name) = sub_pat.name() {
                                field_map.insert(name, sub_pat);
                            }
                        }
                        PatField::Ellipsis => {}
                    }
                }
                // For each field in the record type (alphabetical order),
                // emit the sub-pattern code or Wildcard if not mentioned.
                let codes: Vec<Code> =
                    if let Type::Record(_, type_fields) = type_.as_ref() {
                        type_fields
                            .keys()
                            .map(|label| {
                                if let Label::String(name) = label {
                                    if let Some(sub_pat) = field_map.get(name) {
                                        self.compile_pat(cx, sub_pat)
                                    } else {
                                        Code::BindWildcard
                                    }
                                } else {
                                    Code::BindWildcard
                                }
                            })
                            .collect()
                    } else {
                        vec![]
                    };
                Code::new_bind_tuple(&codes)
            }
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
            Expr::Aggregate(_, f, e) => {
                // `f over e`: apply f to a mapped elements list.
                let elements_slot = cx.frame_def.var_index("elements");
                let elements_code =
                    Box::new(Code::new_get_local(&cx.frame_def, elements_slot));

                // Compile the `over` expression and determine whether it
                // needs per-element mapping. If `e` is a trivial read of
                // slot 0 (single-binding identity), elements already
                // contain the right values.
                let e_code = self.compile_expr(cx, None, e);
                let trivial_slot =
                    cx.compute_scan_slots.first().copied().unwrap_or(0);
                let mapped_code = if matches!(
                    &e_code, Code::GetLocal(_, s) if *s == trivial_slot
                ) {
                    elements_code
                } else {
                    Box::new(Code::MapElements(
                        elements_code,
                        Box::new(e_code),
                        cx.compute_scan_slots.clone(),
                    ))
                };

                if let Expr::Literal(_t, Val::Fn(func)) = f.as_ref() {
                    let impl_ = func.get_impl();
                    Code::new_native(impl_, &[mapped_code], &Span::new(""))
                } else {
                    let fn_code = self.compile_expr(cx, None, f);
                    Code::new_apply(&fn_code, &mapped_code, &[])
                }
            }
            Expr::Apply(result_type, f, a, span) => match f.as_ref() {
                Expr::Literal(_t, Val::Fn(f)) => {
                    let impl_ = f.get_impl();
                    // For 1-arg functions (E1, EF1), always compile the
                    // argument as a single Code — even if it's a tuple
                    // expression. The function takes one argument; a
                    // source-level tuple IS that argument.
                    if matches!(impl_, Impl::E1(_) | Impl::EF1(_)) {
                        // Intercept Relational.max/min to use
                        // type-directed comparators.
                        if *f == BuiltInFunction::RelationalMax
                            || *f == BuiltInFunction::RelationalMin
                        {
                            let elem_type = match a.type_().as_ref() {
                                Type::List(e) => *e.clone(),
                                Type::Bag(e) => *e.clone(),
                                _ => *a.type_(),
                            };
                            let cmp = CmpRef(comparator::comparator_for_with(
                                &elem_type,
                                &self.type_map.datatype_constructors,
                                &self.type_map.constructor_arg_types,
                            ));
                            let arg = self.compile_arg(cx, a);
                            return if *f == BuiltInFunction::RelationalMax {
                                Code::Max(cmp, Box::new(arg))
                            } else {
                                Code::Min(cmp, Box::new(arg))
                            };
                        }
                        let arg = self.compile_arg(cx, a);
                        let codes: Vec<Box<Code>> = vec![Box::new(arg)];
                        return Code::new_native(impl_, &codes, span);
                    }
                    // Detect partial application of a curried 2-arg
                    // built-in (e.g., `List.map f`, `Fn.o (f, g)`): the
                    // call's result type is itself a function type.
                    // Eta-expand into a CreateClosure that captures the
                    // supplied first argument and waits for the second.
                    // Use compile_arg (not compile_args_boxed) because we
                    // want the source argument as a single Code, even if
                    // it happens to be a tuple expression — the function's
                    // first parameter takes the whole tuple.
                    // 1-argument partial application of an EF3 or E3
                    // function (e.g., `Fn.curry f`): build a nested
                    // closure. The outer closure captures `f` and
                    // returns an inner closure capturing `(f, x)` that
                    // takes the third argument.
                    if matches!(impl_, Impl::E3(_) | Impl::EF3(_))
                        && matches!(result_type.as_ref(), Type::Fn(_, _))
                    {
                        let cap_code = self.compile_arg(cx, a);
                        let outer_frame = Arc::new(FrameDef::new(
                            &[Binding::of_name("__cap1")],
                            &[Binding::of_name("__arg1")],
                        ));
                        let inner_frame = Arc::new(FrameDef::new(
                            &[
                                Binding::of_name("__cap1"),
                                Binding::of_name("__cap2"),
                            ],
                            &[Binding::of_name("__arg2")],
                        ));
                        let inner_body = match impl_ {
                            Impl::EF3(ef3) => Code::NativeF3(
                                ef3,
                                Box::new(Code::GetLocal(
                                    inner_frame.clone(),
                                    0,
                                )),
                                Box::new(Code::GetLocal(
                                    inner_frame.clone(),
                                    1,
                                )),
                                Box::new(Code::GetLocal(
                                    inner_frame.clone(),
                                    2,
                                )),
                                None,
                            ),
                            Impl::E3(e3) => Code::Native3(
                                e3,
                                Box::new(Code::GetLocal(
                                    inner_frame.clone(),
                                    0,
                                )),
                                Box::new(Code::GetLocal(
                                    inner_frame.clone(),
                                    1,
                                )),
                                Box::new(Code::GetLocal(
                                    inner_frame.clone(),
                                    2,
                                )),
                            ),
                            _ => unreachable!(),
                        };
                        let inner_pat = Code::BindSlot(inner_frame.clone(), 2);
                        let inner_create = Code::CreateClosure(
                            inner_frame,
                            vec![(inner_pat, inner_body)],
                            vec![
                                Code::GetLocal(outer_frame.clone(), 0),
                                Code::GetLocal(outer_frame.clone(), 1),
                            ],
                            None,
                        );
                        let outer_pat = Code::BindSlot(outer_frame.clone(), 1);
                        return Code::CreateClosure(
                            outer_frame,
                            vec![(outer_pat, inner_create)],
                            vec![cap_code],
                            None,
                        );
                    }
                    if matches!(result_type.as_ref(), Type::Fn(_, _))
                        && matches!(impl_, Impl::E2(_) | Impl::EF2(_))
                    {
                        let single_arg = self.compile_arg(cx, a);
                        let codes: Vec<Box<Code>> = vec![Box::new(single_arg)];
                        let frame_def = Arc::new(FrameDef::new(
                            &[Binding::of_name("__cap")],
                            &[Binding::of_name("__arg")],
                        ));
                        let body = match impl_ {
                            Impl::E2(e2) => Code::Native2(
                                e2,
                                Box::new(Code::GetLocal(frame_def.clone(), 0)),
                                Box::new(Code::GetLocal(frame_def.clone(), 1)),
                                false,
                            ),
                            Impl::EF2(ef2) => Code::NativeF2(
                                ef2,
                                Box::new(Code::GetLocal(frame_def.clone(), 0)),
                                Box::new(Code::GetLocal(frame_def.clone(), 1)),
                                None,
                            ),
                            _ => unreachable!(),
                        };
                        let pat = Code::BindSlot(frame_def.clone(), 1);
                        return Code::CreateClosure(
                            frame_def,
                            vec![(pat, body)],
                            vec![*codes[0].clone()],
                            None,
                        );
                    }
                    // Intercept Relational.compare to use a
                    // type-directed comparator.
                    if *f == BuiltInFunction::RelationalCompare {
                        let args = self.compile_args_boxed(cx, a);
                        let elem_type = match a.type_().as_ref() {
                            Type::Tuple(ts) if !ts.is_empty() => ts[0].clone(),
                            _ => *a.type_(),
                        };
                        let cmp = CmpRef(comparator::comparator_for_with(
                            &elem_type,
                            &self.type_map.datatype_constructors,
                            &self.type_map.constructor_arg_types,
                        ));
                        return Code::Compare(
                            cmp,
                            args[0].clone(),
                            args[1].clone(),
                        );
                    }
                    // For 1-argument impls (E1/EF1), compile the
                    // argument as a single value (not destructured).
                    // E.g. `SOME {a=1,b=true}` passes the whole record.
                    let codes = if matches!(impl_, Impl::E1(_) | Impl::EF1(_)) {
                        vec![Box::new(self.compile_arg(cx, a))]
                    } else {
                        self.compile_args_boxed(cx, a)
                    };
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
                    // Only fires when the result is NOT a function type;
                    // otherwise it would shadow partial application of a
                    // truly-3-arg function like Fn.curry.
                    if let Expr::Literal(_t, Val::Fn(func)) = middle_f.as_ref()
                        && matches!(func.get_impl(), Impl::EF3(_))
                        && !matches!(result_type.as_ref(), Type::Fn(_, _))
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

                    // Handle 2-argument partial application of an EF3 or
                    // E3 function (e.g., `Fn.curry f x` returns a closure
                    // expecting one more argument). Eta-expand into a
                    // CreateClosure capturing both arguments.
                    if let Expr::Literal(_, Val::Fn(func)) = middle_f.as_ref()
                        && matches!(func.get_impl(), Impl::EF3(_) | Impl::E3(_))
                        && matches!(result_type.as_ref(), Type::Fn(_, _))
                    {
                        let cap1_code = self.compile_arg(cx, second_arg);
                        let cap2_code = self.compile_arg(cx, a);
                        let frame_def = Arc::new(FrameDef::new(
                            &[
                                Binding::of_name("__cap1"),
                                Binding::of_name("__cap2"),
                            ],
                            &[Binding::of_name("__arg")],
                        ));
                        let body = match func.get_impl() {
                            Impl::EF3(ef3) => Code::NativeF3(
                                ef3,
                                Box::new(Code::GetLocal(frame_def.clone(), 0)),
                                Box::new(Code::GetLocal(frame_def.clone(), 1)),
                                Box::new(Code::GetLocal(frame_def.clone(), 2)),
                                None,
                            ),
                            Impl::E3(e3) => Code::Native3(
                                e3,
                                Box::new(Code::GetLocal(frame_def.clone(), 0)),
                                Box::new(Code::GetLocal(frame_def.clone(), 1)),
                                Box::new(Code::GetLocal(frame_def.clone(), 2)),
                            ),
                            _ => unreachable!(),
                        };
                        let pat = Code::BindSlot(frame_def.clone(), 2);
                        return Code::CreateClosure(
                            frame_def,
                            vec![(pat, body)],
                            vec![cap1_code, cap2_code],
                            None,
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
            Expr::Case(_, expr, matches, span) => {
                let expr_code = self.compile_expr(cx, None, expr);
                let mut codes = vec![expr_code];

                for m in matches {
                    let pat_code = self.compile_pat(cx, &m.pat);
                    let expr_code = self.compile_expr(cx, None, &m.expr);
                    codes.push(pat_code);
                    codes.push(expr_code);
                }
                Code::new_match(&codes, Some(span.clone()))
            }
            Expr::Current(_) => {
                // 'current' is the primary element: the first local variable
                // in the frame (after any bound/captured variables).
                let slot = cx.frame_def.bound_vars.len();
                Code::new_get_local(&cx.frame_def, slot)
            }
            Expr::Fn(_, match_list, fn_span) => {
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
                    Code::new_fn(
                        &cx1.frame_def,
                        &pat_expr_codes,
                        Some(fn_span.clone()),
                    )
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
                        Some(fn_span.clone()),
                    )
                }
            }
            Expr::From(collection_type, steps) => {
                // Use row sinks (push-based evaluation) matching the Java
                // implementation.
                let step_env = if steps.is_empty() {
                    StepEnv::empty()
                } else {
                    steps.last().unwrap().env.clone()
                };

                // Assert that the Exists step, if present, only occurs last.
                debug_assert!(
                    !steps
                        .iter()
                        .take(steps.len().saturating_sub(1))
                        .any(|s| matches!(s.kind, StepKind::Exists)),
                    "Exists step must only occur as the last step"
                );

                // Extract element type from the collection type
                // (Type::List(e) or Type::Bag(e)).
                let element_type = match collection_type.as_ref() {
                    Type::List(e) | Type::Bag(e) => e,
                    _ => collection_type,
                };

                let factory = self.create_row_sink_factory(
                    cx,
                    &step_env,
                    steps,
                    element_type,
                );
                Code::FromRowSink(factory)
            }
            Expr::Identifier(type_, name) => {
                if let Some(slot) = cx.frame_def.try_var_index(name) {
                    Code::new_get_local(&cx.frame_def, slot)
                } else if let Some(val) = cx.env.get(name) {
                    Code::new_constant(type_, val.clone())
                } else if let Some(rec) =
                    crate::compile::library::name_to_rec(name)
                {
                    let (_, val) = code::LIBRARY
                        .structure_map
                        .get(&rec)
                        .expect("structure not in library");
                    Code::new_constant(type_, val.clone())
                } else {
                    cx.frame_def.var_index(name);
                    unreachable!()
                }
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
                // Convert zero-argument constructors to their values.
                let val2 = match val {
                    Val::Fn(BuiltInFunction::BagNil) => Val::List(vec![]),
                    Val::Fn(BuiltInFunction::ListNil) => Val::List(vec![]),
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
            Expr::Ordinal(_) => {
                // 'ordinal' is the row counter written by OrdinalRowSink;
                // the slot was reserved by VarCollector when it saw this.
                let slot = cx.frame_def.var_index("ordinal");
                Code::new_get_local(&cx.frame_def, slot)
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

    /// Creates a row sink factory from query steps.
    /// Matches Java's Compiler.createRowSinkFactory method.
    fn create_row_sink_factory(
        &mut self,
        cx: &Context,
        step_env: &StepEnv,
        steps: &[Step],
        element_type: &Type,
    ) -> RowSinkFactory {
        use crate::eval::row_sink::{
            CollectRowSink, ComputeRowSink, ExceptRowSink, ExistsRowSink,
            GroupRowSink, IntersectRowSink, OrderRowSink, OrdinalFilterRowSink,
            OrdinalRowSink, ScanRowSink, SkipRowSink, TakeRowSink,
            UnionRowSink, UnorderRowSink, WhereRowSink, YieldRowSink,
        };

        if steps.is_empty() {
            // Terminal case: create CollectRowSink.
            let code = self.get_collection_code(cx, step_env, element_type);
            return RowSinkFactory::new(move || {
                Box::new(CollectRowSink::new(code.clone()))
            });
        }

        // Recursive case: process the first step and build the downstream
        // factory.
        let first_step = &steps[0];

        match &first_step.kind {
            // lint: sort until '#}' where '##StepKind::'
            StepKind::Compute(compute_expr) => {
                // Standalone compute step: evaluate expression once over all
                // rows and return a scalar (not a list).
                assert!(steps.len() == 1, "Compute must be the last step");

                let scan_slots: Vec<usize> = step_env
                    .bindings
                    .iter()
                    .filter_map(|b| cx.frame_def.try_var_index(&b.id.name))
                    .collect();

                // Set scan slots so Aggregate/MapElements knows
                // which frame slots to write element values into.
                let mut cx2 = cx.clone();
                cx2.compute_scan_slots = scan_slots.clone();
                let compute_code = self.compile_expr(&cx2, None, compute_expr);
                let elements_slot = cx.frame_def.try_var_index("elements");

                RowSinkFactory::new(move || {
                    Box::new(ComputeRowSink::new(
                        compute_code.clone(),
                        elements_slot,
                        scan_slots.clone(),
                    ))
                })
            }
            StepKind::Distinct => {
                // Distinct is equivalent to `group` on all current
                // bindings with no aggregate.
                let next_factory = self.create_row_sink_factory(
                    cx,
                    &first_step.env,
                    &steps[1..],
                    element_type,
                );

                // Compute the frame slots for the current bindings.
                // Fall back to positional 0..N when binding names
                // are not in the frame.
                let mut slots: Vec<usize> = step_env
                    .bindings
                    .iter()
                    .filter_map(|b| cx.frame_def.try_var_index(&b.id.name))
                    .collect();
                if slots.is_empty() {
                    let n = step_env.bindings.len();
                    slots = (0..n).collect();
                }

                // Build key_code: read current row from frame slots.
                let key_code = if slots.len() == 1 {
                    Code::new_get_local(&cx.frame_def, slots[0])
                } else {
                    Code::new_tuple(
                        &slots
                            .iter()
                            .map(|&s| Code::new_get_local(&cx.frame_def, s))
                            .collect::<Vec<_>>(),
                    )
                };
                let key_slots = slots.clone();
                let key_is_record = slots.len() > 1;
                let scan_slots = slots;

                RowSinkFactory::new(move || {
                    Box::new(GroupRowSink::new(
                        key_code.clone(),
                        None, // no aggregate
                        None, // no elements slot
                        vec![],
                        false,
                        scan_slots.clone(),
                        key_slots.clone(),
                        key_is_record,
                        next_factory.create(),
                    ))
                })
            }
            StepKind::Except(distinct, exprs) => {
                // Translate "except-distinct" as if it were ordinary "except"
                // followed by "distinct".
                let downstream_steps = if *distinct {
                    // Create a Distinct step and append remaining steps.
                    let mut new_steps = vec![Step::new(
                        StepKind::Distinct,
                        first_step.env.clone(),
                    )];
                    new_steps.extend_from_slice(&steps[1..]);
                    new_steps
                } else {
                    steps[1..].to_vec()
                };

                let next_factory = self.create_row_sink_factory(
                    cx,
                    &first_step.env,
                    &downstream_steps,
                    element_type,
                );

                // Compile each except expression into code.
                let codes: Vec<Code> = exprs
                    .iter()
                    .map(|expr| self.compile_expr(cx, None, expr))
                    .collect();
                let slot_count = step_env.bindings.len();

                RowSinkFactory::new(move || {
                    Box::new(ExceptRowSink::new(
                        slot_count,
                        codes.clone(),
                        next_factory.create(),
                    ))
                })
            }
            StepKind::Exists => {
                // The Exists step creates an ExistsRowSink for short-circuit.
                assert_eq!(steps.len(), 1, "Exists must be the last step");
                RowSinkFactory::new(|| Box::new(ExistsRowSink::new()))
            }
            StepKind::Group(key_expr, aggregate_expr) => {
                // Group query: accumulate rows by key, evaluate aggregate.
                // Example: "from i in [1,2,3] group i" or
                // "from e in emps group e.deptno compute {c = count over ()}"

                // The next step processes the grouped results.
                let next_factory = self.create_row_sink_factory(
                    cx,
                    &first_step.env,
                    &steps[1..],
                    element_type,
                );

                // Compile the group key expression.
                let key_code = self.compile_expr(cx, None, key_expr);

                // Determine the frame slots for each key field, and whether
                // the key value needs to be unpacked (record/tuple) or stored
                // directly (scalar).
                //
                // For groups with an aggregate, we need to write each key
                // field to its own named frame slot so that subsequent steps
                // (e.g. yield, order) can reference them by name.  For groups
                // without an aggregate (GROUP alone), the key tuple is stored
                // in slot 0 as a whole, matching the old behaviour.
                // Determine key slots by looking up field names in
                // the frame. Works the same with or without aggregate.
                let (key_slots, key_is_record): (Vec<usize>, bool) =
                    match key_expr.type_().as_ref() {
                        Type::Record(_, fields) if fields.is_empty() => {
                            (vec![], false)
                        }
                        Type::Primitive(PrimitiveType::Unit) => (vec![], false),
                        Type::Record(_, fields) => {
                            let slots: Vec<usize> = fields
                                .keys()
                                .filter_map(|label| {
                                    cx.frame_def
                                        .try_var_index(&label.to_string())
                                })
                                .collect();
                            if slots.len() == fields.len() {
                                (slots, true)
                            } else {
                                (vec![0], false)
                            }
                        }
                        Type::Tuple(types) => {
                            ((0..types.len()).collect(), true)
                        }
                        _ => {
                            // Scalar key: look up its named slot
                            // from the step env's first binding.
                            if let Some(b) = first_step.env.bindings.first() {
                                if let Some(slot) =
                                    cx.frame_def.try_var_index(&b.id.name)
                                {
                                    (vec![slot], false)
                                } else {
                                    (vec![0], false)
                                }
                            } else {
                                (vec![0], false)
                            }
                        }
                    };

                // Scan slot indices for row accumulation.
                let scan_slots: Vec<usize> = step_env
                    .bindings
                    .iter()
                    .filter_map(|b| cx.frame_def.try_var_index(&b.id.name))
                    .collect();

                // Compile aggregate expression and determine slot layout.
                let (
                    aggregate_code,
                    elements_slot,
                    agg_output_slots,
                    agg_is_record,
                ) = if let Some(agg_expr) = aggregate_expr {
                    let mut cx2 = cx.clone();
                    cx2.compute_scan_slots = scan_slots.clone();
                    let agg_code = self.compile_expr(&cx2, None, agg_expr);

                    // Slot where rows_val is written before aggregate eval.
                    let els = cx.frame_def.try_var_index("elements");

                    // Slots for aggregate output fields, in field order.
                    let (out_slots, is_record): (Vec<usize>, bool) =
                        if let Type::Record(_, fields) =
                            agg_expr.type_().as_ref()
                        {
                            (
                                fields
                                    .keys()
                                    .map(|label| {
                                        cx.frame_def
                                            .var_index(&label.to_string())
                                    })
                                    .collect(),
                                true,
                            )
                        } else {
                            // Scalar aggregate: look up the
                            // aggregate's implicit label by name.
                            let label = agg_expr
                                .implicit_label()
                                .unwrap_or_else(|| "agg".to_string());
                            let slot =
                                cx.frame_def.try_var_index(&label).unwrap_or(0);
                            (vec![slot], false)
                        };

                    (Some(agg_code), els, out_slots, is_record)
                } else {
                    (None, None, vec![], false)
                };

                RowSinkFactory::new(move || {
                    Box::new(GroupRowSink::new(
                        key_code.clone(),
                        aggregate_code.clone(),
                        elements_slot,
                        agg_output_slots.clone(),
                        agg_is_record,
                        scan_slots.clone(),
                        key_slots.clone(),
                        key_is_record,
                        next_factory.create(),
                    ))
                })
            }
            StepKind::Intersect(distinct, exprs) => {
                // Translate "intersect-distinct" as if it were an ordinary
                // "intersect" followed by "distinct". (We could also
                // make the inputs distinct.)
                let downstream_steps = if *distinct {
                    // Create a Distinct step and append remaining steps.
                    let mut new_steps = vec![Step::new(
                        StepKind::Distinct,
                        first_step.env.clone(),
                    )];
                    new_steps.extend_from_slice(&steps[1..]);
                    new_steps
                } else {
                    steps[1..].to_vec()
                };

                let next_factory = self.create_row_sink_factory(
                    cx,
                    &first_step.env,
                    &downstream_steps,
                    element_type,
                );

                // Compile each "intersect" expression into code.
                let codes: Vec<Code> = exprs
                    .iter()
                    .map(|expr| self.compile_expr(cx, None, expr))
                    .collect();
                let slot_count = step_env.bindings.len();

                RowSinkFactory::new(move || {
                    Box::new(IntersectRowSink::new(
                        slot_count,
                        codes.clone(),
                        next_factory.create(),
                    ))
                })
            }
            StepKind::Order(expr) => {
                let next_factory = self.create_row_sink_factory(
                    cx,
                    &first_step.env,
                    &steps[1..],
                    element_type,
                );

                // Compile the order expression.
                let order_code = self.compile_expr(cx, None, expr);

                // Compute the actual frame slot indices for each active
                // binding. After a 'yield', named fields may occupy slots
                // beyond index 0, so we cannot assume 0..slot_count.
                // "current" is special: it is not a named frame variable,
                // but lives at bound_vars.len() (the first local slot).
                let binding_slots: Vec<usize> = step_env
                    .bindings
                    .iter()
                    .map(|b| {
                        if b.id.name == "current" {
                            cx.frame_def.bound_vars.len()
                        } else {
                            cx.frame_def.var_index(&b.id.name)
                        }
                    })
                    .collect();

                // Create a comparator for the order expression's type.
                let expr_type = expr.type_();
                let comparator = comparator_for(&expr_type);

                RowSinkFactory::new(move || {
                    Box::new(OrderRowSink::new(
                        order_code.clone(),
                        comparator.clone(),
                        binding_slots.clone(),
                        next_factory.create(),
                    ))
                })
            }
            StepKind::Scan(pat, expr, cond) => {
                let next_factory = self.create_row_sink_factory(
                    cx,
                    &first_step.env,
                    &steps[1..],
                    element_type,
                );
                let pat_code = self.compile_pat(cx, pat);
                let expr_code = self.compile_expr(cx, None, expr);
                let condition_code = if let Some(condition_expr) = cond {
                    self.compile_expr(cx, None, condition_expr)
                } else {
                    Code::new_constant(
                        &Type::Primitive(PrimitiveType::Bool),
                        Val::Bool(true),
                    )
                };

                RowSinkFactory::new(move || {
                    Box::new(ScanRowSink::new(
                        pat_code.clone(),
                        expr_code.clone(),
                        condition_code.clone(),
                        next_factory.create(),
                    ))
                })
            }
            StepKind::Skip(expr) => {
                let next_factory = self.create_row_sink_factory(
                    cx,
                    &first_step.env,
                    &steps[1..],
                    element_type,
                );
                let skip_code = self.compile_expr(cx, None, expr);
                RowSinkFactory::new(move || {
                    Box::new(SkipRowSink::new(
                        skip_code.clone(),
                        next_factory.create(),
                    ))
                })
            }
            StepKind::Take(expr) => {
                let next_factory = self.create_row_sink_factory(
                    cx,
                    &first_step.env,
                    &steps[1..],
                    element_type,
                );
                let take_code = self.compile_expr(cx, None, expr);
                RowSinkFactory::new(move || {
                    Box::new(TakeRowSink::new(
                        take_code.clone(),
                        next_factory.create(),
                    ))
                })
            }
            StepKind::Union(distinct, exprs) => {
                // Translate "union-distinct" as if it were ordinary "union"
                // followed by "distinct". (We could also make the inputs
                // distinct.)
                let downstream_steps = if *distinct {
                    // Create a Distinct step and append remaining steps.
                    let mut new_steps = vec![Step::new(
                        StepKind::Distinct,
                        first_step.env.clone(),
                    )];
                    new_steps.extend_from_slice(&steps[1..]);
                    new_steps
                } else {
                    steps[1..].to_vec()
                };

                let next_factory = self.create_row_sink_factory(
                    cx,
                    &first_step.env,
                    &downstream_steps,
                    element_type,
                );

                // Compile each union expression into code.
                let codes: Vec<Code> = exprs
                    .iter()
                    .map(|expr| self.compile_expr(cx, None, expr))
                    .collect();
                let slot_count = step_env.bindings.len();

                RowSinkFactory::new(move || {
                    Box::new(UnionRowSink::new(
                        slot_count,
                        codes.clone(),
                        next_factory.create(),
                    ))
                })
            }
            StepKind::Unorder => {
                let next_factory = self.create_row_sink_factory(
                    cx,
                    &first_step.env,
                    &steps[1..],
                    element_type,
                );
                RowSinkFactory::new(move || {
                    Box::new(UnorderRowSink::new(next_factory.create()))
                })
            }
            StepKind::Where(expr) => {
                let next_factory = self.create_row_sink_factory(
                    cx,
                    &first_step.env,
                    &steps[1..],
                    element_type,
                );
                let filter_code = self.compile_expr(cx, None, expr);

                let ordinal_slot = if Self::expr_uses_ordinal(expr) {
                    cx.frame_def.try_var_index("ordinal")
                } else {
                    None
                };

                // When 'ordinal' is a yielded field (present in step_env
                // bindings), we need to preserve its value across the
                // counter increment so downstream sinks (e.g.
                // CollectRowSink) still see the original field value.
                let ordinal_is_field = ordinal_slot.is_some()
                    && step_env.bindings.iter().any(|b| b.id.name == "ordinal");

                RowSinkFactory::new(move || {
                    if let Some(slot) = ordinal_slot {
                        Box::new(OrdinalFilterRowSink::new(
                            slot,
                            filter_code.clone(),
                            next_factory.create(),
                            ordinal_is_field,
                        ))
                    } else {
                        Box::new(WhereRowSink::new(
                            filter_code.clone(),
                            next_factory.create(),
                        ))
                    }
                })
            }
            StepKind::Yield(expr) => {
                let yield_code = self.compile_expr(cx, None, expr);
                if steps.len() == 1 {
                    // Terminal yield: collect results, optionally wrapped
                    // with OrdinalRowSink when yield uses 'ordinal'.
                    let ordinal_slot = if Self::expr_uses_ordinal(expr) {
                        cx.frame_def.try_var_index("ordinal")
                    } else {
                        None
                    };
                    RowSinkFactory::new(move || {
                        let collect: Box<dyn RowSink> =
                            Box::new(CollectRowSink::new(yield_code.clone()));
                        if let Some(slot) = ordinal_slot {
                            Box::new(OrdinalRowSink::new(slot, collect))
                        } else {
                            collect
                        }
                    })
                } else {
                    // Non-terminal yield: bind the yielded value to frame
                    // slots so downstream steps can reference the variables.
                    let next_factory = self.create_row_sink_factory(
                        cx,
                        &first_step.env,
                        &steps[1..],
                        element_type,
                    );
                    let yield_type = expr.type_().clone();

                    // If the yield expression references 'ordinal', wrap with
                    // OrdinalRowSink so the counter is written into the frame
                    // slot before the yield expression captures it.
                    let ordinal_slot = if Self::expr_uses_ordinal(expr) {
                        cx.frame_def.try_var_index("ordinal")
                    } else {
                        None
                    };

                    let yield_factory =
                        if let Type::Record(_, fields) = yield_type.as_ref() {
                            // Record yield: unpack each field into its own
                            // slot.
                            let field_slots: Vec<usize> = fields
                                .keys()
                                .filter_map(|label| {
                                    if let Label::String(name) = label {
                                        Some(cx.frame_def.var_index(name))
                                    } else {
                                        None
                                    }
                                })
                                .collect();
                            RowSinkFactory::new(move || {
                                Box::new(YieldRowSink::new_record(
                                    yield_code.clone(),
                                    field_slots.clone(),
                                    next_factory.create(),
                                ))
                            })
                        } else {
                            // Scalar yield: write to the current slot (slot 0
                            // past any bound vars).
                            let current_slot = cx.frame_def.bound_vars.len();
                            RowSinkFactory::new(move || {
                                Box::new(YieldRowSink::new(
                                    yield_code.clone(),
                                    current_slot,
                                    next_factory.create(),
                                ))
                            })
                        };

                    if let Some(slot) = ordinal_slot {
                        RowSinkFactory::new(move || {
                            Box::new(OrdinalRowSink::new(
                                slot,
                                yield_factory.create(),
                            ))
                        })
                    } else {
                        yield_factory
                    }
                }
            }
            _ => todo!("create_row_sink_factory: {:?}", first_step.kind),
        }
    }

    /// Gets the code for collecting bound variables.
    fn get_collection_code(
        &mut self,
        cx: &Context,
        step_env: &StepEnv,
        element_type: &Type,
    ) -> Code {
        if step_env.bindings.is_empty() {
            // No bindings - return unit.
            return Code::new_constant(
                &Type::Primitive(PrimitiveType::Unit),
                Val::Unit,
            );
        }

        // Collect field names sorted alphabetically (like Java).
        let mut field_names: Vec<String> = step_env
            .bindings
            .iter()
            .map(|b| b.id.name.clone())
            .collect();
        field_names.sort();

        if field_names.len() == 1
            && step_env.bindings[0].type_.as_ref() == element_type
        {
            // Single binding matching the element type - just get that
            // variable.
            let name = &field_names[0];
            // "current" is not a named frame slot; it refers to the primary
            // element at index bound_vars.len() (i.e., the first local var).
            let slot = if name == "current" {
                cx.frame_def.bound_vars.len()
            } else {
                cx.frame_def.var_index(name)
            };
            Code::new_get_local(&cx.frame_def, slot)
        } else {
            // Multiple bindings or type mismatch - create a tuple.
            let codes: Vec<Code> = field_names
                .iter()
                .map(|name| {
                    let slot = cx.frame_def.var_index(name);
                    Code::new_get_local(&cx.frame_def, slot)
                })
                .collect();
            Code::Tuple(codes)
        }
    }

    /// Returns true if the expression (or any sub-expression) references
    /// `ordinal`.
    fn expr_uses_ordinal(expr: &Expr) -> bool {
        match expr {
            Expr::Ordinal(_) => true,
            Expr::Apply(_, f, a, _) => {
                Self::expr_uses_ordinal(f) || Self::expr_uses_ordinal(a)
            }
            Expr::Case(_, e, matches, _) => {
                Self::expr_uses_ordinal(e)
                    || matches.iter().any(|m| Self::expr_uses_ordinal(&m.expr))
            }
            Expr::Let(_, _, e) => Self::expr_uses_ordinal(e),
            Expr::List(_, exprs) | Expr::Tuple(_, exprs) => {
                exprs.iter().any(Self::expr_uses_ordinal)
            }
            _ => false,
        }
    }

    fn compile_step(&mut self, cx: &Context, step: &Step) -> QueryStep {
        match &step.kind {
            StepKind::Scan(pat, expr, _cond) => {
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
        let i = self.link_table.reserve(name);
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
        // The lift wraps the original expression as 'fn () => expr'.
        // Use the val binding's source span as the synthetic Fn's span,
        // so a Match exception raised at runtime points back to the
        // user's source.
        let synth_span =
            val_bind.span.clone().unwrap_or_else(|| Span::new("stdIn"));
        let expr2 = Expr::Fn(Box::new(fn_type), vec![match_], synth_span);
        ValBind {
            pat: pat2,
            t: t2,
            expr: expr2,
            overload_pat: val_bind.overload_pat.clone(),
            span: val_bind.span.clone(),
        }
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
    /// Source span of the val binding (pattern + expression). Used to
    /// report the location of a 'Bind' exception when the pattern fails
    /// to match the value at run time.
    span: Option<Span>,
    /// Constructor argument types for the pretty printer.
    constructor_arg_types: HashMap<String, Type>,
    /// Datatype constructor names for the pretty printer.
    datatype_constructors: HashMap<String, Vec<String>>,
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
                let pretty = Self::get_pretty(
                    &r.shell.config,
                    &self.constructor_arg_types,
                    &self.datatype_constructors,
                );
                // Collect bindings into a buffer first; we will only emit
                // them if the pattern matches the value (otherwise we
                // raise the 'Bind' exception).
                let mut emits: Vec<(Box<Pat>, Val)> = Vec::new();
                let matched = self.pat.bind_recurse(&o, &mut |p2, v2| {
                    emits.push((p2, v2.clone()));
                });
                if !matched {
                    // Format identically to MorelError::Runtime so that
                    // every nonexhaustive-pattern failure (whether from
                    // a 'val' decl, a function application, or a 'case'
                    // expression) has the same shape.
                    let loc =
                        self.span.clone().unwrap_or_else(|| Span::new("stdIn"));
                    let err = MorelError::Runtime(BuiltInExn::Bind, loc);
                    r.emit_effect(Effect::EmitLine(err.to_string()));
                    return;
                }
                for (p2, v2) in emits {
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
                }
            }
        }
    }
}

impl ValDeclAction {
    fn get_pretty(
        shell_config: &ShellConfig,
        constructor_arg_types: &HashMap<String, Type>,
        datatype_constructors: &HashMap<String, Vec<String>>,
    ) -> Pretty {
        Pretty::new(
            shell_config
                .line_width
                .unwrap_or_else(|| Prop::LineWidth.default_value().as_int()),
            shell_config
                .output
                .unwrap_or_else(|| Prop::Output.default_value().as_output()),
            shell_config
                .print_length
                .unwrap_or_else(|| Prop::PrintLength.default_value().as_int()),
            shell_config
                .print_depth
                .unwrap_or_else(|| Prop::PrintDepth.default_value().as_int()),
            shell_config
                .string_depth
                .unwrap_or_else(|| Prop::StringDepth.default_value().as_int()),
            constructor_arg_types.clone(),
            datatype_constructors.clone(),
        )
    }
}

/// Action emitted for a `type alias = body` declaration. At evaluation
/// time it just emits the line 'type alias = body' (no value is bound;
/// the alias has already been registered in the type-resolver).
/// Action emitted for an `over` declaration.
struct OverDeclAction {
    name: String,
}

impl Action for OverDeclAction {
    fn apply(&self, r: &mut EvalEnv, _f: &mut Frame) {
        r.emit_effect(Effect::EmitLine(format!("over {}", self.name)));
    }
}

struct TypeDeclAction {
    name: String,
    type_: Type,
}

impl Action for TypeDeclAction {
    fn apply(&self, r: &mut EvalEnv, _f: &mut Frame) {
        r.emit_effect(Effect::EmitLine(format!(
            "type {} = {}",
            self.name, self.type_
        )));
    }
}

/// Action emitted for a `datatype` declaration. At evaluation
/// time it emits one line per datatype bind:
/// `datatype 'a tree = Empty | Node of 'a tree * 'a * 'a tree`.
struct DatatypeDeclAction {
    datatype_bind: DatatypeBind,
}

impl Action for DatatypeDeclAction {
    fn apply(&self, r: &mut EvalEnv, _f: &mut Frame) {
        let db = &self.datatype_bind;
        let type_vars = if db.type_vars.is_empty() {
            String::new()
        } else {
            let vars: Vec<String> = (0..db.type_vars.len())
                .map(|i| format!("'{}", (b'a' + i as u8) as char))
                .collect();
            if vars.len() == 1 {
                format!("{} ", vars[0])
            } else {
                format!("({}) ", vars.join(","))
            }
        };
        let cons: Vec<String> = db
            .constructors
            .iter()
            .map(|c| {
                if let Some(t) = &c.type_ {
                    format!("{} of {}", c.name, t)
                } else {
                    c.name.clone()
                }
            })
            .collect();
        r.emit_effect(Effect::EmitLine(format!(
            "datatype {}{} = {}",
            type_vars,
            db.name,
            cons.join(" | ")
        )));

        // Register each constructor as a runtime binding.
        for (ordinal, con) in db.constructors.iter().enumerate() {
            let val = if con.type_.is_some() {
                // Value-carrying: a Code that wraps arg in
                // Val::Constructor(ordinal, arg).
                Val::Code(Arc::new(Code::ConstructorWrap(ordinal)))
            } else {
                // Nullary: just the tagged value.
                Val::Constructor(ordinal, Box::new(Val::Unit))
            };
            r.emit_effect(Effect::AddBinding(Binding::of_name_value(
                &con.name,
                &Some(val),
            )));
        }
    }
}

/// Compilation context.
#[derive(Clone)]
pub struct Context {
    env: Environment,

    /// Definition of the current stack frame.
    frame_def: Arc<FrameDef>,

    /// Scan slot indices for the current compute step's scan
    /// bindings. Used by Aggregate/MapElements to know which
    /// frame slots to write element values into.
    compute_scan_slots: Vec<usize>,
}

impl Context {
    pub fn new(env: Environment) -> Self {
        Self {
            env,
            frame_def: Arc::new(FrameDef::new(&[], &[])),
            compute_scan_slots: vec![0],
        }
    }

    pub fn bind_all(&self, bindings: &[Binding]) -> Self {
        Self {
            env: self.env.bind_all(bindings),
            frame_def: self.frame_def.clone(),
            compute_scan_slots: self.compute_scan_slots.clone(),
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
            compute_scan_slots: vec![0],
        }
    }
}

pub trait CompiledStatement {
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
}

impl CompiledStatement for CompiledStatementImpl {
    fn eval(
        &self,
        session: &Session,
        shell: &Shell,
        _env: &Environment,
        effects: &mut Vec<Effect>,
        _type_map: &TypeMap,
    ) {
        // Recursive `Code::Link` references resolve through the
        // shell-wide [`LinkTable`], so the per-statement link
        // vector that used to be threaded through `EvalEnv` is
        // gone — `EvalEnv::new` now needs only the shell.
        let mut eval_env = EvalEnv::new(session, shell, effects);
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
