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
    BooleanFunction as _, Function as _, HasLevel, HasWorkers, LevelNo, Manager as _, ManagerRef,
    Node, VarNo, WorkerPool,
    bcdd::{BCDDFunction, BCDDManagerRef},
    error::OutOfMemory,
};

use oxidd_reorder::set_var_order_seq;
use oxidd_rules_bdd::complement_edge::EdgeTag;

use dashmap::DashMap;
use either::Either;
use itertools::Itertools;
use parking_lot::RwLock;
use thiserror::Error;
use transitive::Transitive;

use std::{collections::HashMap, fmt::Debug, iter, num::NonZero, sync::Arc};

type Manager<'m> = <BCDDFunction as oxidd::Function>::Manager<'m>;

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
                        variable: variable.clone(),
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
    variable: Variable,
}

struct QE<'p> {
    manager: BCDDManagerRef,
    top: BCDDFunction,
    bottom: BCDDFunction,
    pool: &'p (dyn TermPool + Send + Sync),
    env: Env,
    backend: &'static dyn Backend,
    atoms: SyncBiMap<Term, VarNo>,
    mentions: DashMap<(Term, Variable), bool>,
    cutoff: RwLock<Option<VarNo>>,
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
        manager.workers().set_split_depth(Some(30));
        QE {
            top: manager.with_manager_shared(|m| BCDDFunction::t(m)),
            bottom: manager.with_manager_shared(|m| BCDDFunction::f(m)),
            manager,
            pool,
            env,
            backend,
            atoms: SyncBiMap::new(),
            mentions: DashMap::new(),
            cutoff: RwLock::default(),
        }
    }

    // Idea.
    //
    // Coalescing into single vars the subdags that do not mention the variable being eliminated.
    // Ideal solution:
    // - a single traversal eliminates the current variable and rebuilds the BDD coalescing for the
    //   next variable
    // - how do we coalesce after the last variable has been eliminated?
    //   - we do not coalesce anything, obtaining the final result
    // - new definition of "atom": a maximal Boolean subterm that does not mention the target
    //   variable
    // - the two main functions are bdd() and eliminate():
    //   - bdd() takes a Term and compiles it into a coalesced BDD. Going top down:
    //     - if a term does not mention the target variable, make it a unique atom
    //     - if a term does mention the target variable, recurse on it to make it a BDD
    //   - eliminate() traverses a BDD to eliminate a variable:
    //     - it returns either a BDD or a Term
    //     - after the local QE call:
    //       - if the result mentions the next target variable, call bdd() on it
    //       - if the result does not mention the next target variable, return it as a term
    //     - on a cofactors split:
    //       - if both subcalls return BDDs, combine them into a BDD
    //       - if both subcalls return a Term, combine them with a Term ITE into a term
    //       - if one subcall returns a BDD and the other a Term, give the latter to bdd() and
    //         combine the BDDs.
    // - structure of the main algorithm:
    //   - result := initial term
    //   - for each target variable in elimination order
    //     - if result is a term, call bdd() on it on the current target variable
    //     - result := eliminate(var, next_var, result)
    // - what is `next_var` at the end?
    //   - `None` which will be interpreted by eliminate() as 'always pass it up as a term', so the
    //     final result will be a term as expected.
    // - how to deal with variable order in all this:
    //   - new atoms are easy to insert:
    //     - those that mention the current target variable go down, the others go up.
    //   - at each iteration we reset the list of "relevant" atoms and call `set_var_order_seq` only
    //     on those.
    //   - atoms not involved in the current iteration are forgotten
    //   - the VarNo is still there, but it adds negligible overhead if the BDDs do not use it
    //   - we should make sure unused BDDs from old iterations can be garbage-collected
    fn qe(self, quantifiers: &[Quantifier], body: &Term) -> Result<Term, Error> {
        self.manager
            .workers()
            .install(|| self.qe_in(quantifiers, body))
    }

    fn qe_in(&self, quantifiers: &[Quantifier], body: &Term) -> Result<Term, Error> {
        let mut body = Either::Left(body.clone());
        let mut prevq = smt::Quantifier::Exists;

        for i in 0..quantifiers.len() {
            let target = &quantifiers[i].variable;
            let quantifier = quantifiers[i].quantifier;
            let next = quantifiers.get(i + 1).map(|q| &q.variable);

            match quantifier {
                smt::Quantifier::Forall => eprintln!("eliminating forall {}", target.name()),
                smt::Quantifier::Exists => eprintln!("eliminating exists {}", target.name()),
            }

            let neg = prevq != quantifier;
            prevq = quantifier;

            body = match body {
                Either::Left(mut term) => {
                    eprintln!("partial result is a term");
                    if neg {
                        eprintln!("switching quantifiers, negating term...");
                        term = self.simplify(&Core::not().call([term]).into_term_in(self.pool));
                    }

                    eprintln!("compiling the bdd...");
                    let body = self.bdd(target, &term)?;
                    eprintln!("bdd compiled! traversing...");
                    self.eliminate(target, next, body)?
                }
                Either::Right(mut body) => {
                    eprintln!("partial result is a bdd already.");
                    if neg {
                        eprintln!("switching quantifiers, negating bdd..");
                        body = body.not()?;
                    }
                    eprintln!("traversing...");
                    self.eliminate(target, next, body)?
                }
            };
            eprintln!("traversed!");
        }

        let mut term = match body {
            Either::Left(term) => term,
            Either::Right(bdd) => self.term(&bdd),
        };

        if prevq == smt::Quantifier::Forall {
            eprintln!("final quantifier was universal, negating result...");
            term = self.simplify(&Core::not().call([term]).into_term_in(self.pool));
        }

        Ok(term)
    }

    #[allow(unused)]
    fn stats(&self, m: &Manager<'_>, target: &Variable) {
        eprintln!("atoms ({}):", self.atoms.size());
        for level in 0..m.num_levels() {
            eprint!(" - level {} -> var {}. ", level, m.level_to_var(level));
            let var = m.level_to_var(level);
            let atom = self.atoms.by_index(&var).unwrap();

            if self.mentions(&atom, target) {
                if self.cutoff.read().is_some_and(|c| var == c) {
                    eprintln!("mentions target! cutoff!")
                } else {
                    eprintln!("mentions target!")
                }
            } else {
                eprintln!()
            }
        }
    }

    fn top(&self) -> BCDDFunction {
        self.top.clone()
    }

    fn bottom(&self) -> BCDDFunction {
        self.bottom.clone()
    }

    fn eliminate(
        &self,
        target: &Variable,
        next: Option<&Variable>,
        body: BCDDFunction,
    ) -> Result<Either<Term, BCDDFunction>, Error> {
        let cutoff = match std::mem::take(&mut *self.cutoff.write()) {
            Some(cutoff) => self.manager.with_manager_shared(|m| m.var_to_level(cutoff)),
            None => return Ok(Either::Right(body)),
        };

        self.eliminate_in(target, next, cutoff, body, &DashMap::new())
    }

    fn eliminate_in(
        &self,
        target: &Variable,
        next: Option<&Variable>,
        cutoff: LevelNo,
        body: BCDDFunction,
        cache: &DashMap<BCDDFunction, Either<Term, BCDDFunction>>,
    ) -> Result<Either<Term, BCDDFunction>, Error> {
        if let Some(result) = cache.get(&body) {
            return Ok(result.clone());
        }

        let result = match body.cofactors() {
            Some((high, low)) => {
                let (level, guard_var, guard_bdd) =
                    body.with_manager_shared(|m, edge| -> Result<_, Error> {
                        let Node::Inner(node) = m.get_node(edge) else {
                            unreachable!()
                        };
                        let level = node.level();
                        let var = m.level_to_var(level);

                        Ok((level, var, BCDDFunction::var(m, var)?))
                    })?;

                let total = self.manager.with_manager_shared(|m| m.num_levels());
                eprintln!("eliminating bdd at level {level}/{total}, cutoff {cutoff}...");
                if level < cutoff {
                    let (high, low) = self.manager.workers().join(
                        || self.eliminate_in(target, next, cutoff, high, cache),
                        || self.eliminate_in(target, next, cutoff, low, cache),
                    );

                    match (high?, low?) {
                        (Either::Right(high), Either::Right(low)) => {
                            Either::Right(guard_bdd.ite(&high, &low)?)
                        }
                        (Either::Left(high), Either::Left(low)) => {
                            let atom = self.atoms.by_index(&guard_var).unwrap();
                            Either::Left(
                                Core::ite().call([atom, high, low]).into_term_in(self.pool),
                            )
                        }
                        (Either::Left(high), Either::Right(low)) => {
                            let high = self.bdd(next.unwrap(), &high)?;
                            Either::Right(guard_bdd.ite(&high, &low)?)
                        }
                        (Either::Right(high), Either::Left(low)) => {
                            let low = self.bdd(next.unwrap(), &low)?;
                            Either::Right(guard_bdd.ite(&high, &low)?)
                        }
                    }
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

                    if let Some(next) = next
                        && self.mentions(&eliminated, next)
                    {
                        eprintln!(
                            "QE backend invocation succeeded! result mentions the next target ({})!",
                            next.name()
                        );
                        Either::Right(self.bdd(next, &eliminated)?)
                    } else {
                        eprintln!(
                            "QE backend invocation succeeded! no mentions of the next target ({})!",
                            next.map(|v| v.name().name()).unwrap_or("none")
                        );
                        Either::Left(eliminated)
                    }
                }
            }
            None => body.with_manager_shared(|_, edge| match edge.tag() {
                EdgeTag::None => Either::Left(Core::True().into_term_in(self.pool)),
                EdgeTag::Complemented => Either::Left(Core::False().into_term_in(self.pool)),
            }),
        };

        cache.insert(body, result.clone());

        Ok(result)
    }

    fn mentions(&self, term: &Term, target: &Variable) -> bool {
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

    fn atom(&self, term: Term, mentions: bool) -> Result<BCDDFunction, Error> {
        debug_assert_eq!(Sort::of(&term).unwrap(), Core::Bool());

        self.manager.with_manager_exclusive(|m| {
            let var = self.atoms.by_key_or_insert(term, |_| {
                let var = m.add_vars(1).start;
                let level = m.var_to_level(var);

                let mut cutoff = self.cutoff.write();
                match &*cutoff {
                    Some(_) if !mentions => {
                        let order = iter::once(level)
                            .chain(0..m.num_levels() - 1)
                            .map(|l| m.level_to_var(l))
                            .collect_vec();

                        set_var_order_seq(m, &order);
                    }
                    None if mentions => *cutoff = Some(var),
                    _ => {}
                }

                var
            });
            Ok(BCDDFunction::var(m, var)?)
        })
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

    fn coalesce(&self, target: &Variable, term: &Term) -> Term {
        self.coalesce_in(target, &self.simplify(term), &mut HashMap::new())
    }

    #[allow(clippy::mutable_key_type)]
    fn coalesce_in(&self, target: &Variable, term: &Term, cache: &mut HashMap<Term, Term>) -> Term {
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

    fn bdd(&self, target: &Variable, term: &Term) -> Result<BCDDFunction, Error> {
        eprint!("compiling bdd...");
        let term = self.coalesce(target, term);

        self.bdd_in(target, &term, &mut HashMap::new())
    }

    #[allow(clippy::mutable_key_type)]
    fn bdd_in(
        &self,
        target: &Variable,
        term: &Term,
        cache: &mut HashMap<Term, BCDDFunction>,
    ) -> Result<BCDDFunction, Error> {
        if let Some(bdd) = cache.get(term) {
            return Ok(bdd.clone());
        }

        if !self.mentions(term, target) {
            eprintln!("new atom *not* mentioning the target ({})!", target.name());
            let atom = self.atom(term.clone(), false)?;
            cache.insert(term.clone(), atom.clone());
            return Ok(atom);
        }

        let bdd = match term.kind() {
            TermKind::Atom(atom) => {
                if let Ok(atom) = CoreAtom::try_from(atom) {
                    match atom {
                        CoreAtom::True => self.top(),
                        CoreAtom::False => self.bottom(),
                        CoreAtom::Not(arg) => self.bdd_in(target, arg, cache)?.not()?,
                        CoreAtom::Implies(args) => {
                            let bdds: Vec<_> = args
                                .iter()
                                .map(|arg| self.bdd_in(target, arg, cache))
                                .try_collect()?;
                            bdds.into_iter()
                                .rev()
                                .try_fold(self.bottom(), |acc, arg| arg.imp(&acc))?
                        }
                        CoreAtom::And(args) => {
                            let bdds: Vec<_> = args
                                .iter()
                                .map(|arg| self.bdd_in(target, arg, cache))
                                .try_collect()?;
                            bdds.into_iter()
                                .try_fold(self.top(), |acc, arg| acc.and(&arg))?
                        }
                        CoreAtom::Or(args) => {
                            let bdds: Vec<_> = args
                                .iter()
                                .map(|arg| self.bdd_in(target, arg, cache))
                                .try_collect()?;
                            bdds.into_iter()
                                .try_fold(self.bottom(), |acc, arg| acc.or(&arg))?
                        }
                        CoreAtom::Xor(args) => {
                            let bdds: Vec<_> = args
                                .iter()
                                .map(|arg| self.bdd_in(target, arg, cache))
                                .try_collect()?;
                            bdds.into_iter()
                                .try_fold(self.bottom(), |acc, arg| acc.xor(&arg))?
                        }
                        CoreAtom::Ite(guard, high, low) => {
                            let guard = self.bdd_in(target, guard, cache)?;
                            let high = self.bdd_in(target, high, cache)?;
                            let low = self.bdd_in(target, low, cache)?;

                            guard.ite(&high, &low)?
                        }
                        CoreAtom::Equals(_) | CoreAtom::Distinct(_) => {
                            eprintln!("new atom mentioning the target ({})!", target.name());
                            self.atom(term.clone(), true)?
                        }
                    }
                } else if let Ok(sort) = Sort::of(term)
                    && sort == Core::Bool()
                {
                    eprintln!("new atom mentioning the target ({})!", target.name());
                    self.atom(term.clone(), true)?
                } else {
                    unreachable!();
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
                    self.atoms.by_index(&m.level_to_var(node.level())).unwrap()
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
