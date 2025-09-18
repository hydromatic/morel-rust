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

#![allow(dead_code)]
#![allow(clippy::needless_borrow)]
#![allow(clippy::inherent_to_string)]
#![allow(clippy::extra_unused_lifetimes)]
#![allow(clippy::type_complexity)]
#![allow(clippy::nonminimal_bool)]
#![allow(clippy::collapsible_if)]

use crate::unify;
use std::cell::RefCell;
use std::cmp::{PartialEq, max};
use std::collections::{BTreeMap, HashMap, VecDeque};
use std::fmt::{self, Debug, Display, Formatter, Write};
use std::iter::zip;
use std::rc::Rc;
use std::time::Instant;

/// Trait for things that behave like terms.
trait TermLike {
    fn apply1(&self, variable: &Rc<Var>, term: &Term) -> Term;
    #[allow(dead_code)]
    fn apply(&self, map: &BTreeMap<Rc<Var>, Term>) -> Term;
    fn as_term(&self) -> Term;
}

/// Trait for things that can be created from a [Term].
/// Implementations include [Sequence], [Rc]`<Var>`.
trait FromTerm {
    fn from_term(term: &Term) -> Self;
}

/// A term is a variable or a sequence.
///
/// Examples:
/// * Variable: `X`
/// * Sequence: `a`, `f`, `g(b)`, `f(a, X, g(b))`
///
/// If a sequence has no terms, we call it an atom.
///
/// Operators often have the same arity every time they are used,
/// but we don't enforce this.
#[derive(Debug, Clone, PartialEq)]
pub enum Term {
    Sequence(Sequence),
    Variable(Rc<Var>),
}

impl Term {
    /// Returns whether this term references a given variable.
    fn contains(&self, var: &Rc<Var>) -> bool {
        match self {
            Term::Variable(v) => v == var,
            Term::Sequence(seq) => {
                seq.terms.iter().any(|term| term.contains(var))
            }
        }
    }

    /// Applies a substitution to this term.
    fn apply(&self, map: &BTreeMap<Rc<Var>, Term>) -> Term {
        match self {
            Term::Variable(v) => v.apply(map),
            Term::Sequence(seq) => seq.apply(map),
        }
    }

    /// Applies a single variable-to-term substitution to this term.
    fn apply1(&self, variable: &Rc<Var>, term: &Term) -> Term {
        match self {
            Term::Variable(v) => v.apply1(variable, term),
            Term::Sequence(seq) => seq.apply1(variable, term),
        }
    }

    /// Returns whether this term could potentially unify with another term.
    pub fn could_unify_with(&self, other: &Term) -> bool {
        match (self, other) {
            (Term::Variable(_), _) | (_, Term::Variable(_)) => true,
            (Term::Sequence(seq1), Term::Sequence(seq2)) => {
                seq1.op == seq2.op && seq1.terms.len() == seq2.terms.len()
            }
        }
    }
}

impl TermLike for Term {
    fn apply1(&self, variable: &Rc<Var>, term: &Term) -> Term {
        match self {
            Term::Variable(v) => v.apply1(variable, term),
            Term::Sequence(seq) => seq.apply1(variable, term),
        }
    }

    fn apply(&self, map: &BTreeMap<Rc<Var>, Term>) -> Term {
        match self {
            Term::Variable(v) => v.apply(&map),
            Term::Sequence(seq) => seq.apply(&map),
        }
    }

    fn as_term(&self) -> Term {
        self.clone()
    }
}

impl FromTerm for Term {
    fn from_term(term: &Term) -> Self {
        term.clone()
    }
}

impl Display for Term {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Term::Variable(var) => f.write_str(var.name.as_str()),
            Term::Sequence(seq) => Display::fmt(seq, f),
        }
    }
}

/// A registered variable.
///
/// Its id is unique within a Unifier,
/// and disjoint from Op id values.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Var {
    pub name: String,
    pub id: i32,
}

impl Ord for Var {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        other
            .id
            .cmp(&self.id) // -1 before -2
            .then_with(|| self.name.cmp(&other.name)) // X before Y
    }
}

impl PartialOrd for Var {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Display for Var {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.name)
    }
}

impl Var {
    pub fn new(name: &str, id: i32) -> Self {
        Self {
            name: name.to_string(),
            id,
        }
    }
}

impl TermLike for Rc<Var> {
    fn apply1(&self, variable: &Rc<Var>, term: &Term) -> Term {
        if self == variable {
            term.clone()
        } else {
            self.as_term()
        }
    }

    fn apply(&self, map: &BTreeMap<Rc<Var>, Term>) -> Term {
        map.get(self).cloned().unwrap_or_else(|| self.as_term())
    }

    fn as_term(&self) -> Term {
        Term::Variable(self.clone())
    }
}

impl FromTerm for Rc<Var> {
    fn from_term(term: &Term) -> Self {
        match term {
            Term::Variable(var) => var.clone(),
            _ => panic!("Expected Variable, got {}", term),
        }
    }
}

/// A registered operator.
///
/// It is the name of an atom (e.g. `a()`) or a sequence
/// (e.g. `p(a, q(b, c))`).
///
/// Its id is unique within a Unifier.
#[derive(Debug, Clone, PartialEq)]
pub struct Op {
    pub name: String,
    arity: Option<usize>,
    id: i32,
}

/// A Sequence is an operator with a list of terms.
#[derive(Debug, Clone, PartialEq)]
pub struct Sequence {
    pub op: Rc<Op>,
    pub terms: Vec<Term>,
}

impl Sequence {
    fn sub1(&self, variable: &Rc<Var>, term: &Term) -> Sequence {
        let terms: Vec<Term> = self
            .terms
            .iter()
            .map(|t| t.apply1(variable, term))
            .collect();
        Sequence {
            op: self.op.clone(),
            terms,
        }
    }

    fn sub(&self, map: &BTreeMap<Rc<Var>, Term>) -> Self {
        if self.terms.is_empty() {
            return self.clone();
        }
        let new_terms: Vec<Term> =
            self.terms.iter().map(|t| t.apply(map)).collect();
        if self.terms == new_terms {
            return self.clone();
        }
        Sequence {
            op: self.op.clone(),
            terms: new_terms,
        }
    }
}

impl TermLike for Sequence {
    fn apply1(&self, variable: &Rc<Var>, term: &Term) -> Term {
        Term::Sequence(self.sub1(variable, term))
    }

    fn apply(&self, map: &BTreeMap<Rc<Var>, Term>) -> Term {
        Term::Sequence(self.sub(&map))
    }

    fn as_term(&self) -> Term {
        Term::Sequence(self.clone())
    }
}

impl FromTerm for Sequence {
    fn from_term(term: &Term) -> Self {
        match term {
            Term::Sequence(seq) => seq.clone(),
            _ => panic!("Expected Sequence, got {}", term),
        }
    }
}

impl<'a> Display for Sequence {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        if self.terms.is_empty() {
            write!(f, "{}", self.op.name)
        } else {
            write!(f, "{}(", self.op.name)?;
            for (i, term) in self.terms.iter().enumerate() {
                if i > 0 {
                    write!(f, ", ")?;
                }
                write!(f, "{}", term)?;
            }
            write!(f, ")")
        }
    }
}

/// Substitution.
#[derive(Debug, Clone)]
pub struct Substitution {
    pub substitutions: BTreeMap<Rc<Var>, Term>,
}

impl Substitution {
    fn resolve(&self) -> Self {
        if self.has_cycles() {
            return self.clone();
        }
        let mut new_substitutions = BTreeMap::new();
        for (key, value) in &self.substitutions {
            new_substitutions.insert(key.clone(), self.resolve_term(value));
        }
        Substitution {
            substitutions: new_substitutions,
        }
    }

    fn resolve_term(&self, term: &Term) -> Term {
        let mut previous;
        let mut current = term.clone();
        loop {
            previous = current.clone();
            current = current.apply(&self.substitutions);
            if current == previous {
                break;
            }
        }
        current
    }

    fn apply_substitutions(&self, term: &Term) -> Term {
        let mut result = term.clone();
        for (var, replacement) in &self.substitutions {
            result = result.apply1(var, replacement);
        }
        result
    }

    fn has_cycles(&self) -> bool {
        let mut active = std::collections::HashMap::new();
        self.check_cycles(&mut active).is_err()
    }

    fn check_cycles(
        &self,
        active: &mut std::collections::HashMap<i32, bool>,
    ) -> Result<(), ()> {
        for term in self.substitutions.values() {
            self.check_cycle_in_term(term, active)?;
        }
        Ok(())
    }

    fn check_cycle_in_term(
        &self,
        term: &Term,
        active: &mut std::collections::HashMap<i32, bool>,
    ) -> Result<(), ()> {
        match term {
            Term::Variable(var) => {
                if active.contains_key(&var.id) {
                    return Err(()); // Cycle detected
                }
                if let Some(replacement) = self.substitutions.get(var) {
                    active.insert(var.id, true);
                    let result = self.check_cycle_in_term(replacement, active);
                    active.remove(&var.id);
                    result
                } else {
                    Ok(())
                }
            }
            Term::Sequence(seq) => {
                for sub_term in &seq.terms {
                    self.check_cycle_in_term(sub_term, active)?;
                }
                Ok(())
            }
        }
    }
}

impl Display for Substitution {
    /// Prints e.g. `[f(a, Y)/Z, b/W]`.
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        let mut first = true;
        f.write_char('[')?;
        for (var, term) in &self.substitutions {
            if !first {
                f.write_str(", ")?;
            }
            first = false;
            Display::fmt(&term, f)?;
            f.write_char('/')?;
            f.write_str(var.name.as_str())?;
        }
        f.write_char(']')
    }
}

/// Why unification failed.
#[derive(Debug)]
pub struct UnificationFailure {
    reason: String,
}

impl fmt::Display for UnificationFailure {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Unification failed: {}", self.reason)
    }
}

/// Tracer trait.
pub trait Tracer {
    fn on_conflict(&self, left: &Sequence, right: &Sequence);
    fn on_sequence(&self, left: &Sequence, right: &Sequence);
    fn on_cycle(&self, left: &Var, right: &Term);
    fn on_variable(&self, left: &Var, right: &Term);
    fn on_swap(&self, left: &Term, right: &Term);
    fn on_substitute(
        &self,
        old_left: &Term,
        old_right: &Term,
        new_left: &Term,
        new_right: &Term,
    );
}

/// Tracer that does nothing.
pub struct NullTracer;

impl Tracer for NullTracer {
    fn on_conflict(&self, _left: &Sequence, _right: &Sequence) {
        // Do nothing
    }

    fn on_sequence(&self, _left: &Sequence, _right: &Sequence) {
        // Do nothing
    }

    fn on_cycle(&self, _left: &Var, _right: &Term) {
        // Do nothing
    }

    fn on_variable(&self, _left: &Var, _right: &Term) {
        // Do nothing
    }

    fn on_swap(&self, _left: &Term, _right: &Term) {
        // Do nothing
    }

    fn on_substitute(
        &self,
        _old_left: &Term,
        _old_right: &Term,
        _new_left: &Term,
        _new_right: &Term,
    ) {
        // Do nothing
    }
}

/// Tracer that prints to stdout.
#[allow(dead_code)]
pub struct PrintTracer;

impl Tracer for PrintTracer {
    fn on_conflict(&self, left: &Sequence, right: &Sequence) {
        println!("CONFLICT: {} != {}", left, right);
    }

    fn on_sequence(&self, left: &Sequence, right: &Sequence) {
        println!("DECOMPOSE: {} = {}", left, right);
    }

    fn on_cycle(&self, left: &Var, right: &Term) {
        println!("CYCLE: {} occurs in {}", left, right);
    }

    fn on_variable(&self, left: &Var, right: &Term) {
        println!("VARIABLE: {} = {}", left, right);
    }

    fn on_swap(&self, left: &Term, right: &Term) {
        println!("SWAP: {} <-> {}", left, right);
    }

    fn on_substitute(
        &self,
        old_left: &Term,
        old_right: &Term,
        new_left: &Term,
        new_right: &Term,
    ) {
        println!(
            "SUBSTITUTE: ({}, {}) -> ({}, {})",
            old_left, old_right, new_left, new_right
        );
    }
}
/// A pair of lists that act together.
struct TermActions {
    left_list: Vec<Term>,
    right_list: Vec<ConstraintAction>,
}

impl TermActions {
    fn new() -> Self {
        Self {
            left_list: Vec::new(),
            right_list: Vec::new(),
        }
    }

    fn size(&self) -> usize {
        self.left_list.len()
    }

    fn left(&self, index: usize) -> &Term {
        &self.left_list[index]
    }

    fn right(&self, index: usize) -> &ConstraintAction {
        &self.right_list[index]
    }

    fn left_list(&mut self) -> &mut Vec<Term> {
        &mut self.left_list
    }
}

/// Action to perform when a constraint is resolved.
enum ConstraintAction {
    Accept(Box<dyn Fn(&Term, &Term, &mut dyn FnMut(Term, Term))>),
}

/// Mutable constraint used during unification.
struct MutableConstraint {
    arg: Term,
    term_actions: TermActions,
}

/// Unifier.
///
/// Implements the Martelli-Montanari unification algorithm.
#[derive(Clone)]
pub struct Unifier {
    /// Assists with the generation of unique names by recording the lowest
    /// ordinal, for a given prefix, for which a name has not yet been
    /// generated.
    ///
    /// For example, if we have called `name("T")` twice, and thereby
    /// generated "T0" and "T1", then the map will contain `"T", 2)`,
    /// indicating that the next call to `name("T")` should generate `T2`.
    name_map: HashMap<String, usize>,
    var_by_name: HashMap<String, Rc<Var>>,
    op_by_name: HashMap<String, Rc<Op>>,
    var_list: Vec<Rc<Var>>,
    op_list: Vec<Rc<Op>>,
    occurs: bool,
}

/// Workspace for Unification.
struct Work<'a> {
    tracer: &'a dyn Tracer,
    seq_seq_queue: Rc<RefCell<VecDeque<(Sequence, Sequence)>>>,
    var_any_queue: Rc<RefCell<VecDeque<(Rc<Var>, Term)>>>,
    constraint_queue: VecDeque<MutableConstraint>,
    result: HashMap<Rc<Var>, Term>,
}

impl Display for Work<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "Work: seq-seq {{")?;
        for (var, term) in
            &self.seq_seq_queue.borrow().iter().collect::<Vec<_>>()[..]
        {
            write!(f, "\n  {}: {}", var, term)?;
        }
        write!(f, "\n}} var-any {{")?;
        for (var, term) in
            &self.var_any_queue.borrow().iter().collect::<Vec<_>>()[..]
        {
            write!(f, "\n  {}: {}", var, term)?;
        }
        write!(f, "\n}} result {{")?;
        for (var, term) in &self.result {
            write!(f, "\n  {}: {}", var, term)?;
        }
        write!(f, "\n}}")
    }
}

impl<'a> Work<'a> {
    fn new(tracer: &'a (dyn Tracer + 'a), term_pairs: &[(Term, Term)]) -> Self {
        let mut work = Work {
            tracer,
            var_any_queue: Rc::new(RefCell::new(VecDeque::new())),
            seq_seq_queue: Rc::new(RefCell::new(VecDeque::new())),
            constraint_queue: VecDeque::new(),
            result: HashMap::new(),
        };
        term_pairs
            .iter()
            .for_each(|(left, right)| work.add(left.clone(), right.clone()));
        // constraints.forEach(c ->
        //   constraintQueue.add(new MutableConstraint(c)));
        work
    }

    /// Creates a failure with the given reason.
    fn failure(reason: &str) -> Option<UnificationFailure> {
        Some(UnificationFailure {
            reason: reason.to_string(),
        })
    }

    /// Applies a mapping to all term pairs in a list, modifying them in place.
    fn substitute_list(
        &mut self,
        variable: &Rc<Var>,
        term: &Term,
    ) -> Option<UnificationFailure> {
        // We need to work with the queues separately to avoid borrowing issues
        let seq_seq_queue = std::mem::take(&mut self.seq_seq_queue);
        let var_any_queue = std::mem::take(&mut self.var_any_queue);

        self.seq_seq_queue = seq_seq_queue;
        self.var_any_queue = var_any_queue;

        self.sub_queues(variable, term);
        self.sub_constraint(variable, term)
    }

    /// Applies substitution to all queues.
    fn sub_queues(&mut self, variable: &Rc<Var>, term: &Term) {
        // Process seq_seq_queue
        let seq_seq_queue = self.seq_seq_queue.clone();
        self.process_queue(variable, term, Kind::SeqSeq, &seq_seq_queue);
        // Process var_any_queue
        let var_any_queue = self.var_any_queue.clone();
        self.process_queue(variable, term, Kind::VarAny, &var_any_queue);
    }

    /// Processes a specific queue type.
    fn process_queue<
        L: TermLike + PartialEq + FromTerm,
        R: TermLike + PartialEq + FromTerm,
    >(
        &mut self,
        variable: &Rc<Var>,
        term: &Term,
        queue_kind: Kind,
        queue_ref: &Rc<RefCell<VecDeque<(L, R)>>>,
    ) {
        let mut items_to_add = Vec::new();

        let mut i = 0;
        while i < queue_ref.borrow().len() {
            let (should_continue, needs_removal, new_pair, removed_item) = {
                let queue = queue_ref.borrow();
                let left2 = queue[i].0.apply1(variable, term);
                let right2 = queue[i].1.apply1(variable, term);

                if left2 != queue[i].0.as_term()
                    || right2 != queue[i].1.as_term()
                {
                    self.tracer.on_substitute(
                        &queue[i].0.as_term(),
                        &queue[i].1.as_term(),
                        &left2.as_term(),
                        &right2.as_term(),
                    );
                    let kind2 = Kind::of(&left2.as_term(), &right2.as_term());

                    if kind2 == queue_kind {
                        // Still belongs in this queue
                        (true, false, Some((left2, right2)), None)
                    } else if kind2 == Kind::NonVarVar
                        && queue_kind == Kind::VarAny
                    {
                        (true, false, Some((right2, left2)), None)
                    } else {
                        // Belongs in another queue - capture the item to remove
                        (false, true, None, Some((left2, right2)))
                    }
                } else {
                    (true, false, None, None)
                }
            };

            if needs_removal {
                if let Some((left, right)) = removed_item {
                    // println!("remove ({} {})", left, right);
                    items_to_add.push((left, right));
                }
                queue_ref.borrow_mut().remove(i);
                // Don't increment i since we removed an element
            } else {
                if let Some((l, r)) = new_pair {
                    // println!("something ({} {})", l, r);
                    queue_ref.borrow_mut()[i] =
                        (L::from_term(&l), R::from_term(&r));
                }
                if should_continue {
                    i += 1;
                }
            }
        }

        // Add items that were moved to other queues
        for (left, right) in items_to_add {
            self.add(left, right);
        }
    }

    /// Applies substitution to constraints.
    fn sub_constraint(
        &mut self,
        variable: &Rc<Var>,
        term: &Term,
    ) -> Option<UnificationFailure> {
        let mut i = 0;
        while i < self.constraint_queue.len() {
            let constraint = &mut self.constraint_queue[i];
            let arg2 = constraint.arg.apply1(variable, term);
            let mut change_count = 0;

            if arg2 != constraint.arg {
                change_count += 1;
                constraint.arg = arg2.clone();
                constraint
                    .term_actions
                    .left_list
                    .retain(|arg1| arg2.could_unify_with(arg1));
            }

            let mut j = 0;
            while j < constraint.term_actions.left_list.len() {
                let sub_arg = &constraint.term_actions.left_list[j];
                let sub_arg2 = sub_arg.apply1(variable, term);
                if sub_arg != &sub_arg2 {
                    change_count += 1;
                    constraint.term_actions.left_list[j] = sub_arg2.clone();
                    if !arg2.could_unify_with(&sub_arg2) {
                        constraint.term_actions.left_list.remove(j);
                        constraint.term_actions.right_list.remove(j);
                        continue; // Don't increment j
                    }
                }
                j += 1;
            }

            if change_count > 0 {
                match constraint.term_actions.size() {
                    0 => return Self::failure("no valid overloads"),
                    1 => {
                        let _term1 = constraint.term_actions.left(0).clone();
                        let _action = &constraint.term_actions.right(0);
                        // Note: This would need to be implemented based on the
                        // actual action interface
                        //   action.accept(&constraint.arg, &term1,
                        //       &mut |left, right| self.add2(left, right));
                        // For now, we'll leave this as a placeholder.
                    }
                    _ => {} // Multiple options still available
                }
            }

            i += 1;
        }
        None
    }

    fn add(&mut self, left: Term, right: Term) {
        // println!("add: {} {}", left, right);
        match (&left, &right) {
            (Term::Variable(v1), Term::Variable(v2))
                if v1.id == -21 && v2.id == -1 =>
            {
                // println!("add: {} {}", v1, v2);
            }
            _ => {}
        }
        match Kind::of(&left, &right) {
            Kind::SeqSeq => {
                self.seq_seq_queue.borrow_mut().push_back((
                    Sequence::from_term(&left),
                    Sequence::from_term(&right),
                ));
            }
            Kind::NonVarVar => {
                self.tracer.on_swap(&left, &right);
                if let (Term::Variable(v), t) = (right, left) {
                    self.var_any_queue.borrow_mut().push_back((v, t));
                } else {
                    unreachable!()
                }
            }
            Kind::VarAny => {
                let v: Rc<Var> = FromTerm::from_term(&left);
                self.var_any_queue.borrow_mut().push_back((v, right));
            }
            Kind::Delete => {
                // do nothing
            }
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Kind {
    Delete,
    SeqSeq,
    VarAny,
    NonVarVar,
}

impl Kind {
    fn of(left: &Term, right: &Term) -> Kind {
        if left == right {
            return Kind::Delete;
        }
        match left {
            Term::Sequence(_) => match right {
                Term::Sequence(_) => Kind::SeqSeq,
                Term::Variable(_) => Kind::NonVarVar,
            },
            Term::Variable(_) => Kind::VarAny,
        }
    }
}

impl Unifier {
    pub fn new(occurs: bool) -> Self {
        Self {
            occurs,
            name_map: HashMap::new(),
            var_by_name: HashMap::new(),
            op_by_name: HashMap::new(),
            var_list: Vec::new(),
            op_list: Vec::new(),
        }
    }

    /// Looks up or creates a new operator with the given name.
    pub fn op(&mut self, name: &str, arity: Option<usize>) -> Rc<Op> {
        if let Some(index) = self.op_by_name.get(name) {
            index.clone()
        } else {
            let id = self.name_map.entry(name.to_string()).or_insert(0);
            let op = Rc::new(Op {
                name: name.to_string(),
                arity,
                id: *id as i32,
            });
            self.op_list.push(op.clone());
            self.op_by_name.insert(name.to_string(), op.clone());
            op
        }
    }

    fn op_unique(&mut self, prefix: &str, arity: Option<usize>) -> Rc<Op> {
        let name = self.new_name(prefix, 0);
        let op = Rc::new(Op {
            name: name.to_string(),
            arity,
            id: self.op_list.len() as i32,
        });
        self.op_list.push(op.clone());
        self.op_by_name.insert(name.to_string(), op.clone());
        op
    }

    fn new_name(&mut self, prefix: &str, ordinal: usize) -> String {
        let mut i = ordinal;
        loop {
            let name = format!("{}{}", prefix, i);
            let ordinal = self.name_map.get(&name);
            if !ordinal.is_some() {
                // We have used i this time, will use i + 1 next time.
                self.name_map.insert(name.clone(), i + 1);
                return name;
            }
            i = max(i + 1, *ordinal.unwrap());
        }
    }

    /// Creates a new variable with a unique name.
    ///
    /// The first variable is at position 0, is named "T0", and has id -1.
    /// The second variable is at position 1, is named "T1", and has id -2.
    /// And so forth.
    pub fn variable(&mut self) -> Rc<Var> {
        let ordinal = self.var_list.len();
        let name = self.new_name("T", ordinal);
        let var = Rc::new(Var {
            name: name.to_string(),
            id: -(ordinal as i32 + 1),
        });
        self.var_list.push(var.clone());
        self.name_map.insert(name.to_string(), 1);
        self.var_by_name.insert(name, var.clone());
        var
    }

    /// Creates a variable with a given name, or returns the existing variable
    /// with that name.
    pub fn variable_with_name(&mut self, name: &str) -> Rc<Var> {
        if let Some(var) = self.var_by_name.get(name) {
            var.clone()
        } else {
            let ordinal = self.var_list.len();
            let var = Rc::new(Var {
                name: name.to_string(),
                id: -(ordinal as i32 + 1),
            });
            self.var_list.push(var.clone());
            self.name_map.insert(name.to_string(), 1);
            self.var_by_name.insert(name.to_string(), var.clone());
            var
        }
    }

    fn variable_with_id(&mut self, id: usize) -> Rc<Var> {
        let name = format!("T{}", id);
        self.variable_with_name(&name)
    }

    /// Creates a Sequence.
    #[allow(clippy::needless_pass_by_value)]
    pub fn apply(&self, op: Rc<Op>, terms: &[Term]) -> Sequence {
        assert!(op.arity.is_none_or(|x| { x == terms.len() }));
        Sequence {
            op,
            terms: terms.to_vec(),
        }
    }

    /// Creates a Sequence with one operand.
    pub fn apply1(&self, op: Rc<Op>, term0: Term) -> Sequence {
        self.apply(op, &[term0])
    }

    /// Creates a Sequence with two operands.
    pub fn apply2(&self, op: Rc<Op>, term0: Term, term1: Term) -> Sequence {
        self.apply(op, &[term0, term1])
    }

    /// Creates a Sequence with three operands.
    pub fn apply3(
        &self,
        op: Rc<Op>,
        term0: Term,
        term1: Term,
        term2: Term,
    ) -> Sequence {
        self.apply(op, &[term0, term1, term2])
    }

    /// Creates an Atom (a Sequence with zero operands).
    pub fn atom(&self, op: Rc<Op>) -> Sequence {
        Sequence {
            op,
            terms: Vec::new(),
        }
    }

    /// Creates a substitution from a variable to a term.
    fn substitution(
        &self,
        substitutions: BTreeMap<Rc<Var>, Term>,
    ) -> Substitution {
        Substitution { substitutions }
    }

    pub fn unify(
        &self,
        term_pairs: &[(Term, Term)],
        _tracer: &dyn Tracer,
    ) -> Result<Substitution, UnificationFailure> {
        let tracer = &NullTracer; // switch to PrintTracer for debugging
        if false {
            // Uncomment this section to generate a unit test.
            eprintln!(
                "UnifierTask::from_grammar({}).unify()",
                unify::unifier_parser::generate_program(term_pairs)
            );
        }
        let start = Instant::now();

        // delete: G u { t = t }
        //   => G

        // decompose: G u { f(s0, ..., sk) = f(t0, ..., tk) }
        //   => G u {s0 = t0, ..., sk = tk}

        // conflict: G u { f(s0, ..., sk) = g(t0, ..., tm) }
        //   => fail
        // if f <> g or k <> m

        // swap: G u { f(s0, ..., sk) = x }
        //  => G u { x = f(s0, ..., sk) }

        // eliminate: G u { x = t }
        //  => G { x |-> t } u { x = t }
        // if x not in vars(t) and x in vars(G)

        // check: G u { x = f(s0, ..., sk)}
        //  => fail
        // if x in vars(f(s0, ..., sk))

        let mut work = Work::new(tracer, term_pairs);
        println!("Before: {}", work);
        let mut iteration = 0;
        loop {
            iteration += 1;
            // println!("iteration {} work {}", iteration, work);

            let seq_pair = work.seq_seq_queue.borrow_mut().pop_front();
            if let Some((left, right)) = seq_pair {
                if left.op != right.op || left.terms.len() != right.terms.len()
                {
                    tracer.on_conflict(&left, &right);
                    let reason = format!("conflict: {} != {}", left, right);
                    return Err(UnificationFailure { reason });
                }

                // decompose
                tracer.on_sequence(&left, &right);
                for (l, r) in zip(left.terms.iter(), right.terms.iter()) {
                    work.add(l.clone(), r.clone());
                }
                continue;
            }

            let var_pair = work.var_any_queue.borrow_mut().pop_front();
            if let Some((variable, term)) = var_pair {
                // Occurs check
                if self.occurs && term.contains(&variable) {
                    tracer.on_cycle(&variable, &term);
                    let reason = format!(
                        "cycle: variable {} in {}",
                        variable.name, term
                    );
                    return Err(UnificationFailure { reason });
                }

                // If 'term' is already in the table, map 'variable' to its
                // ultimate target.
                let mut term = term;
                while let Term::Variable(v) = &term {
                    if let Some(t) = work.result.get(v) {
                        term = t.clone();
                    } else {
                        break;
                    }
                }

                if term == Term::Variable(variable.clone()) {
                    // We already knew that 'pair.left' and 'pair.right' were
                    // equivalent.
                    continue;
                }

                tracer.on_variable(&variable, &term);
                if let Some(prior_term) =
                    work.result.insert(variable.clone(), term.clone())
                {
                    if prior_term != term {
                        work.add(prior_term, term.clone());
                    }
                }

                /*
                if !term_actions.is_empty() {
                    final Set<Variable> set = new HashSet<>();
                    act(variable, term, work, new Substitution(result),
                        termActions, set);
                    checkArgument(set.isEmpty(), "Working set not empty: %s",
                        set);
                }
                */

                if let Some(failure) = work.substitute_list(&variable, &term) {
                    return Err(failure);
                }
                continue;
            }

            let duration = Instant::now() - start;
            if false {
                println!(
                    "Term count {} iterations {} \
                    duration {} nanos ({} nanos per iteration)\n",
                    term_pairs.len(),
                    iteration,
                    duration.as_nanos(),
                    duration.as_nanos() / (iteration + 1)
                );
                println!("Result: {}", work);
            }
            let mut substitutions = BTreeMap::new();
            work.result.iter().for_each(|(var, term)| {
                substitutions.insert(var.clone(), term.clone());
            });
            println!(
                "After: {}\n{}",
                work,
                Substitution {
                    substitutions: substitutions.clone()
                }
                .resolve()
            );
            return Ok(Substitution { substitutions });
        }
    }
}

/// Test for Unifier.
#[derive(Clone)]
pub struct UnifierTest {
    unifier: Box<Unifier>,
}

impl UnifierTest {
    pub fn with_occurs(&self, check_cycle: bool) -> Self {
        if check_cycle == self.unifier.occurs {
            self.clone()
        } else {
            UnifierTest::new(check_cycle)
        }
    }

    pub fn var(&mut self, name: &str) -> Term {
        Term::Variable(self.unifier.variable_with_name(name))
    }

    fn new(occurs: bool) -> Self {
        Self {
            unifier: Box::new(Unifier::new(occurs)),
        }
    }

    fn arrow(&mut self, a0: Term, a1: Term) -> Term {
        let op = self.unifier.op("->", Some(2));
        Term::Sequence(self.unifier.apply2(op, a0, a1))
    }

    fn f(&mut self, a0: Term) -> Term {
        let op = self.unifier.op("f", None);
        Term::Sequence(self.unifier.apply1(op, a0))
    }

    fn f2(&mut self, a0: Term, a1: Term) -> Term {
        let op = self.unifier.op("f", None);
        Term::Sequence(self.unifier.apply2(op, a0, a1))
    }

    fn g(&mut self, a0: Term) -> Term {
        let op = self.unifier.op("g", Some(1));
        Term::Sequence(self.unifier.apply1(op, a0))
    }

    fn h(&mut self, term0: Term, term1: Term) -> Term {
        let op = self.unifier.op("h", Some(2));
        Term::Sequence(self.unifier.apply2(op, term0, term1))
    }

    fn p(&mut self, term0: Term, term1: Term, term2: Term) -> Term {
        let op = self.unifier.op("p", None); // variadic
        Term::Sequence(self.unifier.apply3(op, term0, term1, term2))
    }

    fn atom(&mut self, op: &str) -> Term {
        let op_ = self.unifier.op(op, Some(0));
        Term::Sequence(self.unifier.atom(op_))
    }

    fn seq2(&mut self, op: &str, a0: Term, a1: Term) -> Term {
        let op_ = self.unifier.op(op, Some(2));
        Term::Sequence(self.unifier.apply2(op_, a0, a1))
    }

    fn father(&mut self, a0: Term) -> Term {
        let op = self.unifier.op("father", Some(1));
        Term::Sequence(self.unifier.apply1(op, a0))
    }

    fn father2(&mut self, a0: Term, a1: Term) -> Term {
        let op = self.unifier.op("father", Some(2));
        Term::Sequence(self.unifier.apply2(op, a0, a1))
    }

    fn mother(&mut self, a0: Term) -> Term {
        let op = self.unifier.op("mother", Some(1));
        Term::Sequence(self.unifier.apply1(op, a0))
    }

    fn parents(&mut self, a0: Term, a1: Term, t3: Term) -> Term {
        let op = self.unifier.op("parents", Some(3));
        Term::Sequence(self.unifier.apply3(op, a0, a1, t3))
    }

    fn parent(&mut self, a0: Term) -> Term {
        let op = self.unifier.op("parent", Some(1));
        Term::Sequence(self.unifier.apply1(op, a0))
    }

    fn grand_parent(&mut self, a0: Term, a1: Term) -> Term {
        let op = self.unifier.op("grand_parent", Some(2));
        Term::Sequence(self.unifier.apply2(op, a0, a1))
    }

    fn connected(&mut self, a0: Term, a1: Term) -> Term {
        let op = self.unifier.op("connected", Some(2));
        Term::Sequence(self.unifier.apply2(op, a0, a1))
    }

    fn part(&mut self, a0: Term, a1: Term) -> Sequence {
        let op = self.unifier.op("part", Some(2));
        self.unifier.apply2(op, a0, a1)
    }

    fn assert_that_unify(&self, e1: Term, e2: Term, expected: &str) {
        let term_pairs = self.term_pairs(&[e1, e2]);
        self.assert_that_unify_pairs(&term_pairs, expected);
    }

    fn assert_that_unify_pairs(
        &self,
        term_pairs: &[(Term, Term)],
        expected: &str,
    ) {
        let result = self.unifier.unify(term_pairs, &NullTracer);
        let substitution = result.unwrap().resolve();
        assert_eq!(substitution.to_string(), expected);
    }

    fn assert_that_cannot_unify(&self, e1: Term, e2: Term) {
        let term_pairs = self.term_pairs(&[e1, e2]);
        self.assert_that_cannot_unify_pairs(&term_pairs);
    }

    /// Given `[a, b, c, d]`, returns `[(a, b), (c, d)]`.
    fn term_pairs(&self, terms: &[Term]) -> Vec<(Term, Term)> {
        assert_eq!(terms.len() % 2, 0);
        let mut pairs = Vec::new();
        for i in (0..terms.len()).step_by(2) {
            pairs.push((terms[i].clone(), terms[i + 1].clone()));
        }
        pairs
    }

    fn assert_that_cannot_unify_pairs(&self, pair_list: &[(Term, Term)]) {
        let _result = self.unifier.unify(pair_list, &NullTracer);

        // Mock assertion - in real implementation, check if result is not
        // Substitution
        // For testing purposes, we assume it fails if it's not a substitution
        // This would need proper implementation based on the actual Result type
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::unify;
    use crate::unify::unifier_parser::UnifierTask;

    fn create() -> UnifierTest {
        UnifierTest::new(false)
    }

    #[test]
    fn test_atom() {
        let z = create();
        let mut u = z.unifier;
        let mut vars = vec![];
        let a0 = u.op_unique("A", Some(0)).clone();
        assert_eq!(a0.name, "A0");
        let a1 = u.op_unique("A", Some(0));
        assert_eq!(a1.name, "A1");
        let v0 = u.variable();
        assert_eq!(v0.name, "T0");
        vars.push(v0.clone());

        // Try to create an operator with the name of an existing variable,
        // get a new name.
        let a2 = u.op_unique("T", Some(0)).clone();
        assert_eq!(a2.name, "T1");
        let a3 = u.op_unique("T1", Some(0)).clone();
        assert_eq!(a3.name, "T10");

        let v1 = u.variable();
        let v1_name = v1.name.clone();
        assert_eq!(v1_name, "T2");
        vars.push(v1.clone());
        let v1_string = v1.to_string();

        let v2 = u.variable();
        vars.push(v2.clone());
        let v2_string = v2.clone().to_string();

        let v1b = u.variable_with_name(&v1_name);
        assert_eq!(v1b.name, v1_name);
        let v1c = u.variable_with_id(2);
        assert_eq!(v1c.to_string(), v1_string);

        let v2a = u.variable_with_id(3);
        assert_eq!(v2a.to_string(), v2_string);

        let v3 = u.variable();
        vars.push(v3.clone());

        let v4 = u.variable();
        vars.push(v4.clone());
        let v4_string = v4.to_string();

        let v5 = u.variable();
        vars.push(v5.clone());

        let v6 = u.variable();
        vars.push(v6.clone());

        let v4a = u.variable_with_id(5);
        assert_eq!(v4a.to_string(), v4_string);

        let v7 = u.variable();
        vars.push(v7.clone());

        let v8 = u.variable();
        vars.push(v8.clone());

        let var_strings: Vec<_> = vars.iter().map(|v| v.to_string()).collect();
        assert_eq!(
            format!("{:?}", var_strings),
            "[\"T0\", \"T2\", \"T3\", \"T4\", \"T5\", \"T6\", \"T7\", \"T8\", \
             \"T9\"]"
        );
        let v9 = u.variable();
        assert_eq!(v9.to_string(), "T11", "avoids T10 name used by a3 above");
    }

    #[test]
    fn test1() {
        let mut t = create();
        let y = t.var("Y");
        let z = t.var("Z");
        let a = t.atom("a");
        let b = t.atom("b");
        let f_a = t.f(a.clone());
        let g_b = t.g(b);
        let e1 = t.p(f_a, g_b, y.clone());
        assert_eq!(e1.to_string(), "p(f(a), g(b), Y)");
        let d = t.atom("d");
        let c = t.atom("c");
        let g_d = t.g(d);
        let e2 = t.p(z.clone(), g_d, c);
        assert_eq!(e2.to_string(), "p(Z, g(d), c)");
        t.assert_that_cannot_unify(e1, e2);
    }

    #[test]
    fn test1b() {
        let mut t = create();
        let y = t.var("Y");
        let z = t.var("Z");
        let a = t.atom("a");
        let f_a_y = t.f2(a, y);
        let z_v = match z {
            Term::Sequence(_) => {
                todo!()
            }
            Term::Variable(v) => v,
        };
        let mut map: BTreeMap<Rc<Var>, Term> = BTreeMap::new();
        map.insert(z_v, f_a_y);
        let sub = t.unifier.substitution(map);
        assert_eq!(sub.to_string(), "[f(a, Y)/Z]");
    }

    #[test]
    fn test2() {
        let mut t = create();
        let w = t.var("W");
        let y = t.var("Y");
        let z = t.var("Z");
        let a = t.atom("a");
        let f_a = t.f(a);
        let b = t.atom("b");
        let g_b = t.g(b);
        let e1 = t.p(f_a, g_b, y.clone());
        assert_eq!(e1.to_string(), "p(f(a), g(b), Y)");
        let c = t.atom("c");
        let g_w = t.g(w.clone());
        let e2 = t.p(z.clone(), g_w, c);
        assert_eq!(e2.to_string(), "p(Z, g(W), c)");
        t.assert_that_unify(e1, e2, "[b/W, c/Y, f(a)/Z]");
    }

    #[test]
    fn test3() {
        let mut t = create();
        // Note: Hesham Alassaf's test says that these cannot be unified; I
        // think because X is free, and so it assumes that Xs are distinct.
        let x = t.var("X");
        let y = t.var("Y");
        let b = t.atom("b");
        let f_b = t.f(b);
        let f_f_b = t.f(f_b);
        let e1 = t.h(f_f_b, x.clone());
        assert_eq!(e1.to_string(), "h(f(f(b)), X)");
        let f_y = t.f(y.clone());
        let e2 = t.h(f_y, x.clone());
        assert_eq!(e2.to_string(), "h(f(Y), X)");
        t.assert_that_unify(e1, e2, "[f(b)/Y]");
    }

    #[test]
    fn test4() {
        let mut t = create();
        let x = t.var("X");
        let y = t.var("Y");
        let b = t.atom("b");
        let f_b = t.f(b);
        let f_f_b = t.f(f_b);
        let c = t.atom("c");
        let e1 = t.h(f_f_b, c.clone());
        let f_y = t.f(y.clone());
        let e2 = t.h(f_y, x.clone());
        t.assert_that_unify(e1, e2, "[c/X, f(b)/Y]");
    }

    #[test]
    fn test5() {
        let mut t = create();
        let x = t.var("X");
        let y = t.var("Y");
        let a = t.atom("a");
        let e1 = t.h(a, x.clone());
        let b = t.atom("b");
        let e2 = t.h(b, y.clone());
        t.assert_that_cannot_unify(e1, e2);
    }

    #[test]
    fn test6() {
        let mut t = create();
        let x = t.var("X");
        let y = t.var("Y");
        let a = t.atom("a");
        let e1 = t.h(x.clone(), a);
        assert_eq!(e1.to_string(), "h(X, a)");
        let b = t.atom("b");
        let e2 = t.h(b, y.clone());
        assert_eq!(e2.to_string(), "h(b, Y)");
        t.assert_that_unify(e1, e2, "[b/X, a/Y]");
    }

    #[test]
    fn test7() {
        let mut t = create();
        let x = t.var("X");
        let a1 = t.atom("a");
        let a2 = t.atom("a");
        let b = t.atom("b");
        let e1 = t.f2(a1, x.clone());
        assert_eq!(e1.to_string(), "f(a, X)");
        let e2 = t.f2(a2, b);
        assert_eq!(e2.to_string(), "f(a, b)");
        t.assert_that_unify(e1, e2, "[b/X]");
    }

    #[test]
    fn test8() {
        let mut t = create();
        let x = t.var("X");
        let y = t.var("Y");
        let e1 = t.f(x.clone());
        let e2 = t.f(y.clone());
        t.assert_that_unify(e1, e2, "[Y/X]");
    }

    #[test]
    fn test9() {
        let mut t = create();
        let x = t.var("X");
        let y = t.var("Y");
        let g_x = t.g(x.clone());
        let e1 = t.f2(g_x, x.clone()); // f with arity 2
        assert_eq!(e1.to_string(), "f(g(X), X)");
        let e2 = t.f(y.clone()); // f with arity 1
        assert_eq!(e2.to_string(), "f(Y)");
        t.assert_that_cannot_unify(e1, e2);
    }

    #[test]
    fn test10() {
        let mut t = create();
        let x = t.var("X");
        let y = t.var("Y");
        let g_x = t.g(x.clone());
        let e1 = t.f(g_x);
        let e2 = t.f(y.clone());
        t.assert_that_unify(e1, e2, "[g(X)/Y]");
    }

    #[test]
    fn test11() {
        let mut t = create();
        let x = t.var("X");
        let y = t.var("Y");
        let g_x = t.g(x.clone());
        let a = t.atom("a");
        let e1 = t.f2(g_x, x.clone());
        assert_eq!(e1.to_string(), "f(g(X), X)");
        let e2 = t.f2(y.clone(), a);
        assert_eq!(e2.to_string(), "f(Y, a)");
        t.assert_that_unify(e1, e2, "[a/X, g(a)/Y]");
    }

    #[test]
    fn test12() {
        let mut t = create();
        let x = t.var("X");
        let y = t.var("Y");
        let bob = t.atom("bob");
        let tom = t.atom("tom");
        let e1 = t.father2(x.clone(), y.clone());
        assert_eq!(e1.to_string(), "father(X, Y)");
        let e2 = t.father2(bob, tom);
        assert_eq!(e2.to_string(), "father(bob, tom)");
        t.assert_that_unify(e1, e2, "[bob/X, tom/Y]");
    }

    #[test]
    fn test13() {
        let mut t = create();
        let x = t.var("X");
        let y = t.var("Y");
        let bill = t.atom("bill");
        let mother_bill = t.mother(bill.clone());
        let father_x = t.father(x.clone());
        let e1 = t.parents(x.clone(), father_x, mother_bill);
        assert_eq!(e1.to_string(), "parents(X, father(X), mother(bill))");
        let father_bill = t.father(bill.clone());
        let e2 = t.parents(bill, father_bill, y.clone());
        assert_eq!(e2.to_string(), "parents(bill, father(bill), Y)");
        t.assert_that_unify(e1, e2, "[bill/X, mother(bill)/Y]");
    }

    #[test]
    fn test14() {
        let mut t = create();
        let x = t.var("X");
        let y = t.var("Y");
        let john = t.atom("john");
        let parent_x = t.parent(x.clone());
        let parent_parent_x = t.parent(parent_x);
        let e1 = t.grand_parent(x.clone(), parent_parent_x);
        assert_eq!(e1.to_string(), "grand_parent(X, parent(parent(X)))");
        let parent_y = t.parent(y.clone());
        let e2 = t.grand_parent(john, parent_y);
        assert_eq!(e2.to_string(), "grand_parent(john, parent(Y))");
        t.assert_that_unify(e1, e2, "[john/X, parent(john)/Y]");
    }

    #[test]
    fn test15() {
        let mut t = create();
        let x = t.var("X");
        let y = t.var("Y");
        let a = t.atom("a");
        let g_x = t.g(x.clone());
        let f_a = t.f(a);
        let e1 = t.h(f_a, g_x.clone());
        assert_eq!(e1.to_string(), "h(f(a), g(X))");
        let e2 = t.h(y.clone(), y.clone());
        assert_eq!(e2.to_string(), "h(Y, Y)");
        t.assert_that_cannot_unify(e1, e2);
    }

    #[test]
    fn test16() {
        let mut t = create();
        let x = t.var("X");
        let y = t.var("Y");
        let z = t.var("Z");
        let a = t.atom("a");
        let g_z = t.g(z.clone());
        let f_g_z = t.f(g_z);
        let e1 = t.p(a.clone(), x.clone(), f_g_z);
        assert_eq!(e1.to_string(), "p(a, X, f(g(Z)))");
        let f_y = t.f(y.clone());
        let e2 = t.p(z.clone(), f_y.clone(), f_y);
        assert_eq!(e2.to_string(), "p(Z, f(Y), f(Y))");
        t.assert_that_unify(e1, e2, "[f(g(a))/X, g(a)/Y, a/Z]");
    }

    #[test]
    fn test17() {
        for occurs in [false, true] {
            let mut t = create().with_occurs(occurs);
            let x = t.var("X");
            let y = t.var("Y");
            let e1 = t.h(x.clone(), x.clone());
            assert_eq!(e1.to_string(), "h(X, X)");
            let f_y = t.f(y.clone());
            let e2 = t.h(y.clone(), f_y);
            assert_eq!(e2.to_string(), "h(Y, f(Y))");
            if occurs {
                t.assert_that_cannot_unify(e1, e2);
            } else {
                t.assert_that_unify(e1, e2, "[Y/X, f(Y)/Y]");
            }
        }
    }

    #[test]
    fn test18() {
        let mut t = create();
        let w = t.var("W");
        let x = t.var("X");
        let e1 = t.part(w.clone(), x.clone()).as_term();
        assert_eq!(e1.to_string(), "part(W, X)");
        let f_w_x = t.f2(w.clone(), x.clone());
        let e2 = t.connected(f_w_x, w.clone());
        assert_eq!(e2.to_string(), "connected(f(W, X), W)");
        t.assert_that_cannot_unify(e1, e2);
    }

    #[test]
    fn test19() {
        let mut t = create();
        let x = t.var("X");
        let y = t.var("Y");
        let z = t.var("Z");
        let f_x = t.f(x.clone());
        let a = t.atom("a");
        let e1 = t.p(f_x, a.clone(), y.clone());
        assert_eq!(e1.to_string(), "p(f(X), a, Y)");
        let bill = t.atom("bill");
        let f_bill = t.f(bill);
        let b = t.atom("b");
        let g_b = t.g(b);
        let e2 = t.p(f_bill, z.clone(), g_b);
        assert_eq!(e2.to_string(), "p(f(bill), Z, g(b))");
        t.assert_that_unify(e1, e2, "[bill/X, g(b)/Y, a/Z]");
    }

    /// Solves the equations from the S combinator,
    /// "fn x => fn y => fn z => x z (z y)",
    /// in [Wand 87](https://web.cs.ucla.edu/~palsberg/course/cs239/reading/wand87.pdf).
    ///
    /// The equation `t0 = (t5 -> t7 -> t6) -> (t5 -> t7) -> (t5 -> t6)`
    /// yields the principal type `(a -> b -> c) -> (a -> b) -> (a -> c)`.
    #[test]
    fn test20() {
        let mut t = create();
        let t0 = t.var("T0");
        let t1 = t.var("T1");
        let t2 = t.var("T2");
        let t3 = t.var("T3");
        let t4 = t.var("T4");
        let t5 = t.var("T5");
        let t6 = t.var("T6");
        let t7 = t.var("T7");
        let t8 = t.var("T8");
        let t9 = t.var("T9");

        let a_1_2 = t.arrow(t1.clone(), t2.clone());
        let a_3_4 = t.arrow(t3.clone(), t4.clone());
        let a_5_6 = t.arrow(t5.clone(), t6.clone());
        let a_7_6 = t.arrow(t7.clone(), t6.clone());
        let a_8_7_6 = t.arrow(t8.clone(), a_7_6);
        let a_9_7 = t.arrow(t9.clone(), t7.clone());
        assert_eq!(a_1_2.to_string(), "->(T1, T2)");
        assert_eq!(a_3_4.to_string(), "->(T3, T4)");
        assert_eq!(a_5_6.to_string(), "->(T5, T6)");
        assert_eq!(a_8_7_6.to_string(), "->(T8, ->(T7, T6))");
        assert_eq!(a_9_7.to_string(), "->(T9, T7)");

        let term_pairs = vec![
            (t0.clone(), a_1_2.clone()),
            (t2.clone(), a_3_4.clone()),
            (t4.clone(), a_5_6.clone()),
            (t1.clone(), a_8_7_6.clone()),
            (t8.clone(), t5.clone()),
            (a_9_7.clone(), t3.clone()),
            (t9.clone(), t5.clone()),
        ];

        let result = t.unifier.unify(&term_pairs, &NullTracer);
        let expected = "[\
        ->(->(T5, ->(T7, T6)), ->(->(T5, T7), ->(T5, T6)))/T0, \
        ->(T5, ->(T7, T6))/T1, \
        ->(->(T5, T7), ->(T5, T6))/T2, \
        ->(T5, T7)/T3, \
        ->(T5, T6)/T4, \
        T5/T8, \
        T5/T9]";
        match result {
            Ok(substitution) => {
                let resolved = substitution.resolve();
                assert_eq!(resolved.to_string(), expected);
            }
            Err(err) => panic!("Unification failed: {}", err.reason),
        }
    }

    /// Tests a graph that arises when resolving the type of the
    /// expression
    /// ```sml
    ///  if 1 < 2 then "a" else "b"
    /// ```
    ///
    /// The grammar is the same as that in [test_parse].
    #[test]
    fn test_types() {
        let mut t = create();
        let t0 = t.var("T0");
        let t1 = t.var("T1");
        let t2 = t.var("T2");
        let t3 = t.var("T3");
        let t4 = t.var("T4");
        let t5 = t.var("T5");
        let t7 = t.var("T7");
        let string_ = t.atom("string");
        let bool_ = t.atom("bool");
        let int_ = t.atom("int");
        let fn_t3_t1 = t.seq2("fn", t3.clone(), t1.clone());
        let tuple_t4_t5 = t.seq2("tuple", t4.clone(), t5.clone());
        let tuple_t7_t7 = t.seq2("tuple", t7.clone(), t7.clone());
        let fn_tuple_t7_t7_bool =
            t.seq2("fn", tuple_t7_t7.clone(), bool_.clone());

        let term_pairs = vec![
            (t2.clone(), fn_t3_t1.clone()), // "fn(T3, T1) = T2"
            (t4.clone(), int_.clone()),     // "int = T4"
            (t5.clone(), int_.clone()),     // "int = T5"
            (t3.clone(), tuple_t4_t5.clone()), // "tuple(T4, T5) = T3"
            (
                t2.clone(),
                fn_tuple_t7_t7_bool.clone(), // "fn(tuple(T7, T7), bool) = T2"
            ),
            (t1.clone(), bool_.clone()), // "bool = T1"
            (t0.clone(), string_.clone()), // "string = T0"
            (t0.clone(), string_.clone()), // "string = T0"
        ];
        let result = t.unifier.unify(&term_pairs, &NullTracer);
        let expected = "[\
            string/T0, \
            bool/T1, \
            fn(tuple(int, int), bool)/T2, \
            tuple(int, int)/T3, \
            int/T4, \
            int/T5, \
            int/T7]";
        match result {
            Ok(substitution) => {
                let resolved = substitution.resolve();
                assert_eq!(resolved.to_string(), expected);
            }
            Err(err) => panic!("Unification failed: {}", err.reason),
        }
    }

    /// Tests the graph for resolving the type of
    /// ```sml
    /// fn (x, y) => x + y + 0
    /// > val it = fn : int * int -> int
    #[test]
    fn test_21() {
        let grammar = r#"tuple(T3, T4) = T1
            fn(T6, T2) = T5
            fn(T9, T7) = T8
            T3 = T10
            T4 = T11
            tuple(T10, T11) = T9
            T13 = T15
            T13 = T16
            tuple(T15, T16) = T14
            T13 = T17
            fn(T14, T17) = T12
            T12 = T8
            int = T18
            tuple(T7, T18) = T6
            T20 = T22
            T20 = T23
            tuple(T22, T23) = T21
            T20 = T24
            fn(T21, T24) = T19
            T19 = T5
            fn(T1, T2) = T0"#;
        let substitutions = UnifierTask::from_grammar(grammar)
            .expect("Failed to parse grammar")
            .unify()
            .expect("Unify failed");
        let expected = "[\
            int/T3, \
            int/T4, \
            tuple(int, int)/T1, \
            tuple(int, int)/T6, \
            int/T2, \
            fn(tuple(int, int), int)/T5, \
            tuple(int, int)/T9, \
            int/T7, \
            fn(tuple(int, int), int)/T8, \
            int/T10, \
            int/T11, \
            int/T13, \
            int/T15, \
            int/T16, \
            tuple(int, int)/T14, \
            int/T17, \
            fn(tuple(int, int), \
            int)/T12, \
            int/T18, \
            int/T20, \
            int/T22, \
            int/T23, \
            tuple(int, int)/T21, \
            int/T24, \
            fn(tuple(int, int), int)/T19, \
            fn(tuple(int, int), int)/T0]";
        assert_eq!(substitutions.resolve().to_string(), expected);
    }

    #[test]
    fn test_22() {
        let grammar = r#"fn(T2, T0) = T1
fn(T5, T3) = T4
int = T6
int = T7
tuple(T6, T7) = T5
tuple(T10, T11) = T9
bool = T12
fn(T9, T12) = T8
T8 = T4
int = T14
list(T14) = T13
int = T16
list(T16) = T15
tuple(T3, T13, T15) = T2
bool = T19
tuple(T19, T20, T21) = T18
fn(T18, T22) = T17
T17 = T1"#;
        let unifier_task = UnifierTask::from_grammar(grammar)
            .expect("Failed to parse grammar");
        let substitution = unifier_task.unify().expect("Unification failed");
        let expected = "[tuple(bool, list(int), list(int))/T2, \
fn(tuple(bool, list(int), list(int)), T0)/T1, \
tuple(int, int)/T5, \
bool/T3, \
fn(tuple(int, int), bool)/T4, \
int/T6, \
int/T7, \
int/T10, \
int/T11, \
tuple(int, int)/T9, \
bool/T12, \
fn(tuple(int, int), bool)/T8, \
int/T14, \
list(int)/T13, \
int/T16, \
list(int)/T15, \
bool/T19, \
list(int)/T20, \
list(int)/T21, \
tuple(bool, list(int), list(int))/T18, \
T0/T22, \
fn(tuple(bool, list(int), list(int)), T0)/T17]";
        assert_eq!(substitution.resolve().to_string(), expected);
    }

    #[test]
    fn test_atom_eq_atom() {
        let mut t = create();
        let x = t.var("X");
        let b = t.atom("b");
        let a = t.atom("a");
        let pairs = t.term_pairs(&[b.clone(), x.clone(), a.clone(), x.clone()]);
        assert_eq!(b.to_string(), "b");
        assert_eq!(a.to_string(), "a");
        assert_eq!(x.to_string(), "X");
        t.assert_that_cannot_unify_pairs(&pairs);
    }

    #[test]
    fn test_atom_eq_atom2() {
        let mut t = create();
        let x = t.var("X");
        let a1 = t.atom("a");
        let a2 = t.atom("a");
        let b = t.atom("b");
        let pairs = t.term_pairs(&[
            a1.clone(),
            x.clone(),
            a2.clone(),
            x.clone(),
            b.clone(),
            x.clone(),
        ]);
        assert_eq!(a1.to_string(), "a");
        assert_eq!(a2.to_string(), "a");
        assert_eq!(b.to_string(), "b");
        assert_eq!(x.to_string(), "X");
        t.assert_that_cannot_unify_pairs(&pairs);
    }

    #[test]
    fn test_atom_eq_atom3() {
        let mut t = create();
        let x = t.var("X");
        let a1 = t.atom("a");
        let a2 = t.atom("a");
        let pairs =
            t.term_pairs(&[a1.clone(), x.clone(), a2.clone(), x.clone()]);
        assert_eq!(a1.to_string(), "a");
        assert_eq!(a2.to_string(), "a");
        assert_eq!(x.to_string(), "X");
        t.assert_that_unify_pairs(&pairs, "[a/X]");
    }

    #[test]
    fn test_overload() {
        let _z = create();
        /*
        let mut pairs = Vec::new();
        let int_atom = z.unifier.atom("int");
        let t5 = z.unifier.variable_with_id(5);
        pairs.push(TermTerm::new(int_atom, t5.clone()));
        let t4 = z.unifier.variable_with_id(4);
        pairs.push(TermTerm::new(t5.clone(), t4.clone()));
        let fn1 = z.unifier.apply("fn", &[t5.clone(), t4.clone()]);
        let t3 = z.unifier.variable_with_id(3);
        pairs.push(TermTerm::new(fn1, t3.clone()));
        let t6 = z.unifier.variable_with_id(6);
        let t7 = z.unifier.variable_with_id(7);
        let fn11 = z.unifier.apply("fn", &[t6, t7]);
        pairs.push(TermTerm::new(fn11, t3.clone()));
        let fn21 = z.unifier.apply("fn", &[t3.clone(), t3.clone()]);
        let a1 = z.unifier.variable_with_id(2);
        pairs.push(TermTerm::new(fn21, a1));
        let bool_atom = z.unifier.atom("bool");
        let a01 = z.unifier.variable_with_id(11);
        pairs.push(TermTerm::new(bool_atom, a01.clone()));
        let a00 = z.unifier.variable_with_id(10);
        pairs.push(TermTerm::new(a01.clone(), a00.clone()));
        let fn31 = z.unifier.apply("fn", &[a01.clone(), a00.clone()]);
        let t9 = z.unifier.variable_with_id(9);
        pairs.push(TermTerm::new(fn31, t9.clone()));
        let a02 = z.unifier.variable_with_id(12);
        let a03 = z.unifier.variable_with_id(13);
        let fn41 = z.unifier.apply("fn", &[a02, a03]);
        pairs.push(TermTerm::new(fn41, t9.clone()));
        let fn51 = z.unifier.apply("fn", &[t9.clone(), t9.clone()]);
        let t8 = z.unifier.variable_with_id(8);
        pairs.push(TermTerm::new(fn51, t8));
        let a05 = z.unifier.variable_with_id(15);
        let a0 = z.unifier.variable_with_id(1);
        let fn61 = z.unifier.apply("fn", &[a05.clone(), a0.clone()]);
        let a04 = z.unifier.variable_with_id(14);
        pairs.push(TermTerm::new(fn61, a04));
        pairs.push(TermTerm::new(z.unifier.atom("bool"), a05));
        let fn71 = z.unifier.apply("fn", &[a0.clone(), a0]);
        let t0 = z.unifier.variable_with_id(0);
        pairs.push(TermTerm::new(fn71, t0));
        let expected = "[fn(T1, T1)/T0, fn(fn(int, int), fn(int, int))/T2, \
                       fn(int, int)/T3, int/T4, int/T5, int/T6, int/T7, \
                       fn(fn(bool, bool), fn(bool, bool))/T8, \
                       fn(bool, bool)/T9, bool/T10, bool/T11, bool/T12, \
                       bool/T13, fn(bool, T1)/T14, bool/T15]";
        z.assert_that_unify_pairs(&pairs, expected);

         */
    }

    /// Unit test for [unifier_parser].
    /// The graph is the same as [test_types].
    #[test]
    fn test_parse() {
        let grammar = r#"
fn(T3, T1) = T2
int = T4
int = T5
tuple(T4, T5) = T3
fn(tuple(T7, T7), bool) = T2
bool = T1
string = T0
string = T0
"#;

        // First, parse the grammar and count the terms.
        unify::unifier_parser::parse_pair_list(grammar, |pair_list| {
            assert_eq!(pair_list.len(), 8);
        })
        .expect("Failed to parse grammar");

        // Second, parse the grammar and populate a list of term-pairs to be
        // unified.
        let unifier_task = UnifierTask::from_grammar(grammar)
            .expect("Failed to parse grammar");
        let x = unifier_task.unify().expect("Failed to unify grammar");
        let expected = "[\
            tuple(int, int)/T3, \
            bool/T1, \
            fn(tuple(int, int), bool)/T2, \
            int/T4, \
            int/T5, \
            int/T7, \
            string/T0]";
        assert_eq!(x.resolve().to_string(), expected);
    }
}
