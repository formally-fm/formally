//
// ::formally - the open-source formal methods toolchain
//
// Copyright (c) 2026 Nicola Gigante
//
// Permission is hereby granted, free of charge, to any person obtaining a copy
// of this software and associated documentation files (the "Software"), to deal
// in the Software without restriction, including without limitation the rights
// to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
// copies of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:
//
// The above copyright notice and this permission notice shall be included in
// all copies or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
// AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
// OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
// SOFTWARE.
//

mod utils;
use utils::*;

use crate::formally;

use formally::{
    smt::{
        self, Config, Env, Function, FunctionRef, Let, Quantified, Solver, Sort, Term, TermKind,
        TermPool, ToTerm, Variable,
        backends::Backend,
        theories::{Core, CoreAtom},
    },
    support::{Diagnosable, DiagnosticEmitted, Located, Span},
};

use oxidd::{
    BooleanFunction as _, Function as _, HasLevel, HasWorkers, Manager as _, ManagerRef, Node,
    VarNo, WorkerPool,
    bcdd::{BCDDFunction, BCDDManagerRef},
    error::OutOfMemory,
};

use oxidd_reorder::set_var_order_seq;
use oxidd_rules_bdd::complement_edge::EdgeTag;

use dashmap::DashMap;
use itertools::Itertools;
use rayon::prelude::*;
use thiserror::Error;
use transitive::Transitive;

use std::{
    collections::{HashMap, HashSet},
    fmt::Debug,
    num::NonZero,
    sync::Arc,
};

// type Manager<'m> = <BCDDFunction as oxidd::Function>::Manager<'m>;

#[derive(Debug, Error, Located, Transitive)]
#[allow(clippy::duplicated_attributes)]
#[transitive(from(OutOfMemory, ErrorKind))]
#[transitive(from(DiagnosticEmitted, ErrorKind))]
#[error("{kind}")]
pub struct Error {
    pub kind: ErrorKind,
    pub span: Option<Span>,
}

impl From<ErrorKind> for Error {
    fn from(kind: ErrorKind) -> Self {
        Error { kind, span: None }
    }
}

#[derive(Debug, Error)]
pub enum ErrorKind {
    #[error("maximum memory usage limit reached for BDD nodes")]
    OutOfMemory(#[from] OutOfMemory),
    #[error("unable to instantiate a new SMT backend")]
    BackendError(#[from] DiagnosticEmitted),
}

impl Diagnosable for Error {}

pub fn qe(
    term: &Term,
    pool: &(dyn TermPool + Send + Sync),
    env: Env,
    backend: &'static dyn Backend,
    jobs: Option<NonZero<u32>>,
) -> Result<Term, Error> {
    qe_in(term, pool, env, backend, jobs, &HashMap::new())
}

#[allow(clippy::mutable_key_type)]
fn qe_in(
    term: &Term,
    pool: &(dyn TermPool + Send + Sync),
    env: Env,
    backend: &'static dyn Backend,
    jobs: Option<NonZero<u32>>,
    bindings: &HashMap<Variable, Term>,
) -> Result<Term, Error> {
    match term.kind() {
        TermKind::Constant(_) => Ok(term.clone()),
        TermKind::Atom(atom) => {
            if let FunctionRef::Bound(bound) = &atom.head
                && let Function::Variable(var) = &bound.function
                && let Some(term) = bindings.get(var)
            {
                qe_in(term, pool, env, backend, jobs, bindings)
            } else {
                Ok(smt::Atom {
                    head: atom.head.clone(),
                    arguments: atom
                        .arguments
                        .iter()
                        .map(|arg| qe_in(arg, pool, env.clone(), backend, jobs, bindings))
                        .try_collect()?,
                    span: atom.span(),
                }
                .into_term_in(pool))
            }
        }
        TermKind::Quantified(_) => {
            let mut quantifiers = Vec::new();
            let mut body = term.clone();

            while let TermKind::Quantified(quant) = body.kind() {
                for variable in &*quant.variables {
                    quantifiers.push(Quantifier {
                        quantifier: quant.quantifier,
                        target: variable.clone(),
                    })
                }
                body = quant.body.clone();
            }
            quantifiers.reverse();

            let body = qe_in(&body, pool, env.clone(), backend, jobs, bindings)?;
            QE::new(pool, env, backend, jobs).qe(&quantifiers, &body)
        }
        TermKind::Let(let_) => {
            let mut nested = bindings.clone();
            for bind in &*let_.bindings {
                nested.insert(
                    bind.variable.clone(),
                    qe_in(&bind.def, pool, env.clone(), backend, jobs, bindings)?,
                );
            }
            qe_in(&let_.body, pool, env, backend, jobs, &nested)
        }
    }
}

struct Quantifier {
    quantifier: smt::Quantifier,
    target: Variable,
}

struct QE<'p> {
    manager: BCDDManagerRef,
    top: BCDDFunction,
    bottom: BCDDFunction,
    pool: &'p (dyn TermPool + Send + Sync),
    env: Env,
    backend: &'static dyn Backend,
    atoms: BiMap<Term, VarNo>,
    mentions: HashMap<(Term, Variable), bool>,
    cutoff: Option<VarNo>,
}

impl<'p> QE<'p> {
    pub fn new(
        pool: &'p (dyn TermPool + Send + Sync),
        env: Env,
        backend: &'static dyn Backend,
        jobs: Option<NonZero<u32>>,
    ) -> QE<'p> {
        let jobs = jobs.map(NonZero::get).unwrap_or_else(|| {
            std::thread::available_parallelism()
                .map(NonZero::get)
                .unwrap_or(1) as u32
        });
        let manager = oxidd::bcdd::new_manager(1_073_741_824, 1_048_576, jobs);
        manager.workers().set_split_depth(Some(0));
        QE {
            top: manager.with_manager_shared(|m| BCDDFunction::t(m)),
            bottom: manager.with_manager_shared(|m| BCDDFunction::f(m)),
            manager,
            pool,
            env,
            backend,
            atoms: BiMap::new(),
            mentions: HashMap::new(),
            cutoff: None,
        }
    }

    fn qe(mut self, quantifiers: &[Quantifier], body: &Term) -> Result<Term, Error> {
        let manager = self.manager.clone();
        manager.workers().install(|| self.qe_in(quantifiers, body))
    }

    fn qe_in(&mut self, quantifiers: &[Quantifier], body: &Term) -> Result<Term, Error> {
        let mut body = body.clone();
        let mut prevq = smt::Quantifier::Exists;

        for Quantifier { quantifier, target } in quantifiers {
            match quantifier {
                smt::Quantifier::Forall => eprintln!("eliminating forall {}", target.name()),
                smt::Quantifier::Exists => eprintln!("eliminating exists {}", target.name()),
            }

            if prevq != *quantifier {
                eprintln!("switching quantifiers, negating body...");
                body = Core::not().call([body]).into_term_in(self.pool)
            }
            prevq = *quantifier;

            eprintln!("preprocessing...");
            body = self.coalesce(target, &body);

            eprintln!("collecting atoms...");
            self.collect(target, &body);

            self.print_atoms(target);

            eprintln!("compiling the bdd...");
            let bdd = self.bdd(&body)?;

            eprintln!("bdd compiled! traversing...");
            body = self.eliminate(target, bdd)?;

            eprintln!("traversed!");
        }

        if prevq == smt::Quantifier::Forall {
            eprintln!("final quantifier was universal, negating result...");
            body = self.simplify(&Core::not().call([body]).into_term_in(self.pool));
        }

        Ok(body)
    }

    #[allow(unused)]
    fn print_atoms(&mut self, target: &Variable) {
        eprintln!("levels:");
        let manager = self.manager.clone();
        manager.with_manager_shared(|m| {
            for level in 0..m.num_levels() {
                let var = m.level_to_var(level);
                let atom = self.atoms.by_index(&var).unwrap().clone();

                eprint!(" level {} -> var {}.", level, var);

                if self.mentions(&atom, target) {
                    eprint!(" mentions target!")
                }
                if Some(var) == self.cutoff {
                    eprint!(" cutoff!")
                }
                eprintln!()
            }
        })
    }

    fn top(&self) -> BCDDFunction {
        self.top.clone()
    }

    fn bottom(&self) -> BCDDFunction {
        self.bottom.clone()
    }

    fn eliminate(&mut self, target: &Variable, body: BCDDFunction) -> Result<Term, Error> {
        self.eliminate_in(target, body, &DashMap::new())
    }

    fn eliminate_in(
        &self,
        target: &Variable,
        body: BCDDFunction,
        cache: &DashMap<BCDDFunction, Term>,
    ) -> Result<Term, Error> {
        if let Some(result) = cache.get(&body) {
            return Ok(result.clone());
        }

        let result = match body.cofactors() {
            Some((high, low)) => {
                let (level, guard_var) =
                    body.with_manager_shared(|m, edge| -> Result<_, Error> {
                        let Node::Inner(node) = m.get_node(edge) else {
                            unreachable!()
                        };
                        let level = node.level();
                        let var = m.level_to_var(level);

                        Ok((level, var))
                    })?;

                let total = self.manager.with_manager_shared(|m| m.num_levels());
                let cutoff = self
                    .manager
                    .with_manager_shared(|m| self.cutoff.map(|c| m.var_to_level(c)));
                eprintln!(
                    "eliminating bdd at level {level}/{total}, cutoff {}...",
                    cutoff.map(|c| c.to_string()).unwrap_or("none".into())
                );
                if cutoff.is_none_or(|cutoff| level < cutoff) {
                    let (high, low) = self.manager.workers().join(
                        || self.eliminate_in(target, high, cache),
                        || self.eliminate_in(target, low, cache),
                    );

                    let atom = self.atoms.by_index(&guard_var).unwrap().clone();
                    Core::ite()
                        .call([atom, high?, low?])
                        .into_term_in(self.pool)
                } else {
                    let quant = Quantified {
                        quantifier: smt::Quantifier::Exists,
                        variables: Arc::new([target.clone()]),
                        body: self.term(&body),
                        span: None,
                    }
                    .into_term_in(self.pool);

                    let mut solver = Solver::with_backend(&Config::default(), self.backend)?;
                    solver.import(self.env.clone())?;

                    eprint!("invoking QE backend...");
                    let eliminated = solver.qe(quant)?;
                    eprintln!("QE backend invocation succeeded!");

                    eliminated
                }
            }
            None => body.with_manager_shared(|_, edge| match edge.tag() {
                EdgeTag::None => Core::True().into_term_in(self.pool),
                EdgeTag::Complemented => Core::False().into_term_in(self.pool),
            }),
        };

        cache.insert(body, result.clone());

        Ok(result)
    }

    fn mentions(&mut self, term: &Term, target: &Variable) -> bool {
        let key = (term.clone(), target.clone());
        if let Some(mentions) = self.mentions.get(&key) {
            return *mentions;
        }

        let kind = term.kind();
        let mentions = match kind {
            TermKind::Atom(atom) => {
                if let FunctionRef::Bound(bound) = &atom.head
                    && let Function::Variable(var) = &bound.function
                    && *var == *target
                {
                    true
                } else {
                    atom.arguments.iter().any(|arg| self.mentions(arg, target))
                }
            }
            TermKind::Constant(_) => false,
            TermKind::Let(Let { bindings, body, .. }) => {
                self.mentions(body, target)
                    || bindings.iter().any(|b| self.mentions(&b.def, target))
            }
            _ => unreachable!(),
        };

        self.mentions.insert(key, mentions);

        mentions
    }

    // This may be the key reason of most of the problems.
    //
    // 1. When parallelizing the descent in bdd(), the interaction between Rayon and this lock on
    //    the DashMap causes deadlocks
    //    - we need to collect atoms beforehand and then descend into the term to build the BDD in
    //      parallel, using the DashMap only for lookups
    // 2. The insertion point of new atoms was pathological
    //    - new atoms that do not mention the target were inserted at the top of the order.
    //    - this meant that when reconstructing the BDD, the whole structure of the BDDs has to be
    //      redone from scratch
    //    - this should have been fixed now, and indeed the CPU utilization dropped to 100% probably
    //      because we're doing a lot less work in the parallel apply() and everything is now done
    //      by the sequential descent in bdd()
    // 3. We may also want to cache the association BDD -> term when constructing the BDD instead
    //    recomputing it in the term() function
    fn atom(&self, term: &Term) -> Result<Option<BCDDFunction>, Error> {
        match self.atoms.by_key(term) {
            Some(var) => Ok(Some(
                self.manager
                    .with_manager_shared(|m| BCDDFunction::var(m, *var))?,
            )),
            None => Ok(None),
        }
    }

    fn insert_atom(&mut self, term: Term, mentions: bool) {
        debug_assert_eq!(Sort::of(&term).unwrap(), Core::Bool());

        if self.atoms.by_key(&term).is_some() {
            return;
        }

        let var = self.manager.with_manager_exclusive(|m| {
            let var = m.add_vars(1).start;
            match self.cutoff {
                Some(cutoff) if !mentions => {
                    let cutoff = m.var_to_level(cutoff) as usize;
                    let mut order = (0..m.num_levels()).map(|l| m.level_to_var(l)).collect_vec();
                    order[cutoff..].rotate_right(1);

                    set_var_order_seq(m, &order);
                }
                None if mentions => self.cutoff = Some(var),
                _ => {}
            }

            var
        });

        self.atoms.insert(term, var);
    }

    fn simplify(&self, term: &Term) -> Term {
        self.simplify_in(term, &mut HashMap::new())
    }

    #[allow(clippy::mutable_key_type)]
    fn simplify_in(&self, term: &Term, cache: &mut HashMap<Term, Term>) -> Term {
        if let Some(term) = cache.get(term) {
            return term.clone();
        }

        let TermKind::Atom(atom) = term.kind() else {
            return term.clone();
        };

        let Ok(atom) = CoreAtom::try_from(atom) else {
            return term.clone();
        };

        let result = match atom {
            CoreAtom::True => Core::True().into_term_in(self.pool),
            CoreAtom::False => Core::False().into_term_in(self.pool),
            CoreAtom::Not(arg) => {
                let arg = self.simplify_in(arg, cache);
                if arg == true {
                    Core::False().into_term_in(self.pool)
                } else if arg == false {
                    Core::True().into_term_in(self.pool)
                } else if let TermKind::Atom(atom) = arg.kind()
                    && let Ok(atom) = CoreAtom::try_from(atom)
                    && let CoreAtom::Not(arg) = atom
                {
                    arg.clone()
                } else {
                    Core::not().call([arg.clone()]).into_term_in(self.pool)
                }
            }
            CoreAtom::Implies(args) => {
                let mut heads = Vec::with_capacity(args.len());
                #[allow(clippy::needless_range_loop)]
                for i in 0..args.len() - 1 {
                    heads.push(Core::not().call([args[i].clone()]).into_term_in(self.pool))
                }
                heads.push(args[args.len() - 1].clone());

                self.simplify_in(&Core::or().call(heads).into_term_in(self.pool), cache)
            }
            CoreAtom::And(args) => {
                let args = args
                    .iter()
                    .map(|arg| self.simplify_in(arg, cache))
                    .filter(|arg| *arg != true)
                    .collect_vec();
                if args.iter().any(|arg| *arg == false) {
                    Core::False().into_term_in(self.pool)
                } else if args.len() == 1 {
                    args[0].clone()
                } else if args.is_empty() {
                    Core::True().into_term_in(self.pool)
                } else {
                    let mut flattened = Vec::new();
                    for arg in args {
                        if let TermKind::Atom(atom) = arg.kind()
                            && let Ok(atom) = CoreAtom::try_from(atom)
                            && let CoreAtom::And(args) = atom
                        {
                            flattened.extend(args.iter().cloned())
                        } else {
                            flattened.push(arg.clone())
                        }
                    }

                    Core::and().call(flattened).into_term_in(self.pool)
                }
            }
            CoreAtom::Or(args) => {
                let args = args
                    .iter()
                    .map(|arg| self.simplify_in(arg, cache))
                    .filter(|arg| *arg != false)
                    .collect_vec();
                if args.iter().any(|arg| *arg == true) {
                    Core::True().into_term_in(self.pool)
                } else if args.len() == 1 {
                    args[0].clone()
                } else if args.is_empty() {
                    Core::False().into_term_in(self.pool)
                } else {
                    let mut flattened = Vec::new();
                    for arg in args {
                        if let TermKind::Atom(atom) = arg.kind()
                            && let Ok(atom) = CoreAtom::try_from(atom)
                            && let CoreAtom::Or(args) = atom
                        {
                            flattened.extend(args.iter().cloned())
                        } else {
                            flattened.push(arg.clone())
                        }
                    }

                    Core::or().call(flattened).into_term_in(self.pool)
                }
            }
            CoreAtom::Xor(args) => {
                let args = args
                    .iter()
                    .map(|arg| self.simplify_in(arg, cache))
                    .collect_vec();
                let mut flattened = Vec::new();
                for arg in args {
                    if let TermKind::Atom(atom) = arg.kind()
                        && let Ok(atom) = CoreAtom::try_from(atom)
                        && let CoreAtom::Xor(args) = atom
                    {
                        flattened.extend(args.iter().cloned())
                    } else {
                        flattened.push(arg.clone())
                    }
                }

                Core::xor().call(flattened).into_term_in(self.pool)
            }
            CoreAtom::Equals(args) => Core::equals()
                .call(args.iter().map(|arg| self.simplify_in(arg, cache)))
                .into_term_in(self.pool),
            CoreAtom::Distinct(args) => Core::distinct()
                .call(args.iter().map(|arg| self.simplify_in(arg, cache)))
                .into_term_in(self.pool),
            CoreAtom::Ite(guard, high, low) => {
                let guard = self.simplify_in(guard, cache);
                let high = self.simplify_in(high, cache);
                let low = self.simplify_in(low, cache);

                if guard == true {
                    high
                } else if guard == false {
                    low
                } else if high == true && low == false {
                    guard
                } else if high == false && low == true {
                    self.simplify_in(&Core::not().call([guard]).into_term_in(self.pool), cache)
                } else if high == true && low == true {
                    Core::True().into_term_in(self.pool)
                } else if high == false && low == false {
                    Core::False().into_term_in(self.pool)
                } else if low == true {
                    self.simplify_in(
                        &Core::implies().call([guard, high]).into_term_in(self.pool),
                        cache,
                    )
                } else if low == false {
                    self.simplify_in(
                        &Core::and().call([guard, high]).into_term_in(self.pool),
                        cache,
                    )
                } else if high == true {
                    self.simplify_in(
                        &Core::or().call([guard, low]).into_term_in(self.pool),
                        cache,
                    )
                } else {
                    Core::ite().call([guard, high, low]).into_term_in(self.pool)
                }
            }
        };

        cache.insert(term.clone(), result.clone());

        result
    }

    fn coalesce(&mut self, target: &Variable, term: &Term) -> Term {
        self.coalesce_in(target, &self.simplify(term), &mut HashMap::new())
    }

    #[allow(clippy::mutable_key_type)]
    fn coalesce_in(
        &mut self,
        target: &Variable,
        term: &Term,
        cache: &mut HashMap<Term, Term>,
    ) -> Term {
        if let Some(term) = cache.get(term) {
            return term.clone();
        }

        if !self.mentions(term, target) {
            return term.clone();
        }

        let TermKind::Atom(atom) = term.kind() else {
            unreachable!()
        };

        let Ok(atom) = CoreAtom::try_from(atom) else {
            return term.clone();
        };

        let result = match atom {
            CoreAtom::True => Core::True().into_term_in(self.pool),
            CoreAtom::False => Core::False().into_term_in(self.pool),
            CoreAtom::Not(arg) => Core::not()
                .call([self.coalesce_in(target, arg, cache)])
                .into_term_in(self.pool),
            CoreAtom::And(args) => {
                let mut args = args
                    .iter()
                    .map(|arg| self.coalesce_in(target, arg, cache))
                    .collect_vec();
                let pivot = itertools::partition(&mut args, |arg| self.mentions(arg, target));
                assert_ne!(pivot, 0);

                let mentions = Core::and()
                    .call(args[0..pivot].iter().cloned())
                    .into_term_in(self.pool);
                let no_mentions = args[pivot..args.len()].iter().cloned().collect_vec();

                match &no_mentions[..] {
                    [] => mentions,
                    [t] => Core::and()
                        .call([mentions, t.clone()])
                        .into_term_in(self.pool),
                    [_, ..] => {
                        let no_mentions = Core::and().call(no_mentions).into_term_in(self.pool);
                        Core::and()
                            .call([mentions, no_mentions])
                            .into_term_in(self.pool)
                    }
                }
            }
            CoreAtom::Or(args) => {
                let mut args = args
                    .iter()
                    .map(|arg| self.coalesce_in(target, arg, cache))
                    .collect_vec();
                let pivot = itertools::partition(&mut args, |arg| self.mentions(arg, target));
                assert_ne!(pivot, 0);

                let mentions = Core::or()
                    .call(args[0..pivot].iter().cloned())
                    .into_term_in(self.pool);
                let no_mentions = args[pivot..args.len()].iter().cloned().collect_vec();

                match &no_mentions[..] {
                    [] => mentions,
                    [t] => Core::or()
                        .call([mentions, t.clone()])
                        .into_term_in(self.pool),
                    [_, ..] => {
                        let no_mentions = Core::or().call(no_mentions).into_term_in(self.pool);
                        Core::or()
                            .call([mentions, no_mentions])
                            .into_term_in(self.pool)
                    }
                }
            }
            CoreAtom::Implies(args) => Core::implies()
                .call(args.iter().map(|arg| self.coalesce_in(target, arg, cache)))
                .into_term_in(self.pool),
            CoreAtom::Xor(args) => Core::xor()
                .call(args.iter().map(|arg| self.coalesce_in(target, arg, cache)))
                .into_term_in(self.pool),
            CoreAtom::Equals(args) => Core::equals()
                .call(args.iter().map(|arg| self.coalesce_in(target, arg, cache)))
                .into_term_in(self.pool),
            CoreAtom::Distinct(args) => Core::distinct()
                .call(args.iter().map(|arg| self.coalesce_in(target, arg, cache)))
                .into_term_in(self.pool),
            CoreAtom::Ite(guard, high, low) => {
                let guard = self.coalesce_in(target, guard, cache);
                let high = self.coalesce_in(target, high, cache);
                let low = self.coalesce_in(target, low, cache);

                Core::ite().call([guard, high, low]).into_term_in(self.pool)
            }
        };

        cache.insert(term.clone(), result.clone());

        result
    }

    fn collect(&mut self, target: &Variable, term: &Term) {
        self.cutoff = None;
        self.collect_in(target, term, &mut HashSet::new())
    }

    #[allow(clippy::mutable_key_type)]
    fn collect_in(&mut self, target: &Variable, term: &Term, visited: &mut HashSet<Term>) {
        if visited.contains(term) {
            return;
        }

        visited.insert(term.clone());

        if !self.mentions(term, target) {
            self.insert_atom(term.clone(), false);
            return;
        }

        match term.kind() {
            TermKind::Atom(atom) => {
                if let Ok(atom) = CoreAtom::try_from(atom) {
                    match atom {
                        CoreAtom::True | CoreAtom::False => {}
                        CoreAtom::Not(arg) => self.collect_in(target, arg, visited),
                        CoreAtom::Implies(args)
                        | CoreAtom::And(args)
                        | CoreAtom::Or(args)
                        | CoreAtom::Xor(args) => {
                            for arg in args {
                                self.collect_in(target, arg, visited)
                            }
                        }
                        CoreAtom::Ite(guard, high, low) => {
                            self.collect_in(target, guard, visited);
                            self.collect_in(target, high, visited);
                            self.collect_in(target, low, visited);
                        }
                        CoreAtom::Equals(args) | CoreAtom::Distinct(args) => {
                            if args
                                .iter()
                                .any(|arg| Sort::of(arg).unwrap() == Core::Bool())
                            {
                                for arg in args {
                                    self.collect_in(target, arg, visited)
                                }
                            } else {
                                self.insert_atom(term.clone(), true)
                            }
                        }
                    }
                } else {
                    self.insert_atom(term.clone(), true)
                }
            }
            _ => unreachable!(),
        };
    }

    fn bdd(&self, term: &Term) -> Result<BCDDFunction, Error> {
        self.bdd_in(term, &DashMap::new())
    }

    #[allow(clippy::mutable_key_type)]
    fn bdd_in(
        &self,
        term: &Term,
        cache: &DashMap<Term, BCDDFunction>,
    ) -> Result<BCDDFunction, Error> {
        if let Some(bdd) = cache.get(term) {
            return Ok(bdd.clone());
        }

        if let Some(atom) = self.atom(term)? {
            return Ok(atom.clone());
        }

        let bdd =
            match term.kind() {
                TermKind::Atom(atom) => {
                    if let Ok(atom) = CoreAtom::try_from(atom) {
                        match atom {
                            CoreAtom::True => self.top(),
                            CoreAtom::False => self.bottom(),
                            CoreAtom::Not(arg) => self.bdd_in(arg, cache)?.not()?,
                            CoreAtom::Implies(args) => args
                                .par_iter()
                                .enumerate()
                                .map(|(i, arg)| {
                                    if i == args.len() - 1 {
                                        self.bdd_in(arg, cache)
                                    } else {
                                        Ok(self.bdd_in(arg, cache)?.not()?)
                                    }
                                })
                                .try_reduce(|| self.bottom(), |acc, arg| Ok(acc.or(&arg)?))?,
                            CoreAtom::And(args) => args
                                .par_iter()
                                .map(|arg| self.bdd_in(arg, cache))
                                .try_reduce(|| self.top(), |acc, arg| Ok(acc.and(&arg)?))?,
                            CoreAtom::Or(args) => args
                                .par_iter()
                                .map(|arg| self.bdd_in(arg, cache))
                                .try_reduce(|| self.bottom(), |acc, arg| Ok(acc.or(&arg)?))?,
                            CoreAtom::Xor(args) => args
                                .par_iter()
                                .map(|arg| self.bdd_in(arg, cache))
                                .try_reduce(|| self.bottom(), |acc, arg| Ok(acc.xor(&arg)?))?,
                            CoreAtom::Ite(guard, high, low) => {
                                let (guard, (high, low)) = rayon::join(
                                    || self.bdd_in(guard, cache),
                                    || {
                                        rayon::join(
                                            || self.bdd_in(high, cache),
                                            || self.bdd_in(low, cache),
                                        )
                                    },
                                );

                                guard?.ite(&high?, &low?)?
                            }
                            CoreAtom::Equals(args) | CoreAtom::Distinct(args) => {
                                if args
                                    .iter()
                                    .any(|arg| Sort::of(arg).unwrap() == Core::Bool())
                                {
                                    args.par_iter()
                                        .map(|arg| self.bdd_in(arg, cache))
                                        .try_reduce(
                                            || self.top(),
                                            |acc, arg| Ok(acc.imp(&arg)?.and(&arg.imp(&acc)?)?),
                                        )?
                                } else {
                                    self.atom(term)?.unwrap()
                                }
                            }
                        }
                    } else {
                        self.atom(term)?.unwrap()
                    }
                }
                _ => unreachable!(),
            };

        cache.insert(term.clone(), bdd.clone());

        Ok(bdd)
    }

    #[allow(clippy::mutable_key_type)]
    fn term(&self, bdd: &BCDDFunction) -> Term {
        self.simplify(&self.term_in(bdd, &mut HashMap::new()))
    }

    #[allow(clippy::mutable_key_type)]
    fn term_in(&self, bdd: &BCDDFunction, cache: &mut HashMap<BCDDFunction, Term>) -> Term {
        if let Some(term) = cache.get(bdd) {
            return term.clone();
        }

        let term = match bdd.cofactors() {
            Some((high, low)) => {
                let guard = self.manager.with_manager_shared(|m| {
                    let edge = bdd.as_edge(m);
                    let Node::Inner(node) = m.get_node(edge) else {
                        unreachable!()
                    };
                    self.atoms
                        .by_index(&m.level_to_var(node.level()))
                        .unwrap()
                        .clone()
                });

                let high = self.term_in(&high, cache);
                let low = self.term_in(&low, cache);

                Core::ite().call([guard, high, low]).into_term_in(self.pool)
            }
            None => bdd.with_manager_shared(|_, edge| match edge.tag() {
                EdgeTag::None => Core::True().into_term_in(self.pool),
                EdgeTag::Complemented => Core::False().into_term_in(self.pool),
            }),
        };

        cache.insert(bdd.clone(), term.clone());
        term
    }
}
