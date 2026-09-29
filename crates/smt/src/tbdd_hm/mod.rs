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
    dd::obdd::{BDD, Level, Manager, Node, Tree, Var},
    smt::{
        self, Function, FunctionRef, Let, Quantified, Quantifier, Solver, Sort, Term, TermKind,
        TermPool, ToTerm, Variable,
        theories::{Core, CoreAtom},
    },
    support::Located,
};

use dashmap::DashMap;
use parking_lot::RwLock;

use formally_io::print::Print;
use std::{collections::HashMap, hash::Hash, ops::Deref, sync::Arc};

#[derive(Clone, Hash, PartialEq, Eq)]
struct Atom(Term);

impl Deref for Atom {
    type Target = Term;

    fn deref(&self) -> &Term {
        &self.0
    }
}

pub fn qe(term: &Term, pool: Arc<dyn TermPool + Send + Sync>, solver: &Solver) -> Term {
    if term.is_quantifier_free() {
        return term.clone();
    }

    match term.kind() {
        TermKind::Constant(_) => term.clone(),
        TermKind::Atom(atom) => smt::Atom {
            head: atom.head.clone(),
            arguments: atom
                .arguments
                .iter()
                .map(|arg| qe(arg, pool.clone(), solver))
                .collect(),
            span: atom.span(),
        }
        .into_term_in(&*pool),
        TermKind::Quantified(quant) => {
            let quant = Quantified {
                quantifier: quant.quantifier,
                variables: quant.variables.clone(),
                body: qe(&quant.body, pool.clone(), solver),
                span: quant.span(),
            };

            QE::new(pool, solver).qe(quant)
        }
        TermKind::Let(let_) => Let {
            bindings: let_.bindings.clone(),
            body: qe(&let_.body, pool.clone(), solver),
            span: let_.span(),
        }
        .into_term_in(&*pool),
    }
}

struct QE<'s> {
    manager: Manager,
    pool: Arc<dyn TermPool + Send + Sync>,
    solver: &'s Solver,
    atoms: SyncBiMap<Atom, Var>,
    vars: SyncBiMap<Variable, usize>,
    free: DashMap<Term, BitSet>,
    bdds: DashMap<Term, BDD>,
    // for each Variable, the *highest* Level whose Var corresponds to an Atom that mentions that
    // Variable. The level of this Var is also the insertion point for atoms whose earliest mention
    // is this Variable.
    cutoffs: RwLock<HashMap<Variable, Level>>,
}

impl<'s> QE<'s> {
    pub fn new(pool: Arc<dyn TermPool + Send + Sync>, solver: &'s Solver) -> QE<'s> {
        QE {
            manager: Manager::new(),
            pool: pool.clone(),
            solver,
            atoms: SyncBiMap::new(),
            vars: SyncBiMap::new(),
            free: DashMap::new(),
            bdds: DashMap::new(),
            cutoffs: RwLock::default(),
        }
    }

    // Instead of building the BDD freely and then reorder, we want to place the new variables
    // corresponding to new atoms directly in the right order, including the first time the BDD
    // is built.
    //
    // What we neeed:
    // - a way to efficiently compute which VarSet contains variables that go eliminated later than
    //   those of another VarSet
    //   - precollecting all the variables in advance is needed here
    // - comparing atoms based on which free variables they mention:
    //   - if `a` mentions a projected variable and `a'` does not, then `a' < a`
    //   - if `a` mentions a projected variable to be eliminated before those mentioned by `a'`,
    //     then `a' < a`
    // - keep an up-to-date "insertion offset" for all the variables:
    //   - an atom mentioning only variables not earlier than `v` go to the insertion position
    //     computed from the insertion offset of `v`
    //   - the insertion offset of `v` is the distance of the insertion position of `v` w.r.t. the
    //     previous one.
    //   - so initially all the insertion offsets are zero and the BDD var vector is empty, so it
    //     means "insert at position zero" (which means appending at the end if the vector is
    //     empty).
    //   - when an atom is added we look up the insertion offset of the latest mentioned variable
    //     and sum all the offsets until that to get the actual insertion position, then we add the
    //     variable at that level and increment the insertion offset of that variable.
    // - care for doing all the above correctly concurrently
    //   - we probably need to hold a write lock on the insertion offsets vector and the manager
    //     during the procedure
    fn qe(mut self, quant: Quantified) -> Term {
        eprintln!("qe()...");

        let Quantified {
            variables, body, ..
        } = quant;

        eprintln!(" - setup_variable()...");
        self.setup_variables(&variables, &body);

        eprintln!(" - building initial bdd...");
        let mut result = self.bdd(&body);
        for var in &*variables {
            eprintln!(" - eliminate var: {}", var.name());

            let cutoff = *self.cutoffs.read().get(var).unwrap();
            result = self.eliminate(var.clone(), cutoff, &result);
        }

        eprintln!(" - reconstructing term...");
        self.term(&result)
    }

    fn setup_variables(&mut self, variables: &[Variable], body: &Term) {
        // variables to be eliminated earlier have lower index
        for (i, var) in variables.iter().enumerate() {
            self.vars.insert(var.clone(), i);
        }
        // collecting free variables of the body we setup the indexes also of the other variables
        // so variables that are not eliminated have higher index that those that are.
        self.free(body);

        #[allow(clippy::mutable_key_type)]
        // we setup the cutoffs of all the variables at zero
        let mut cutoffs = HashMap::new();
        for var in self.vars.keys() {
            cutoffs.insert(var, Level::MIN);
        }
        self.cutoffs = RwLock::new(cutoffs);
    }

    // given an atom get the variable whose index is the lowest bit set in the free variable bitset
    fn earliest_mention(&self, atom: &Atom) -> Option<Variable> {
        let free = self.free(&atom.0);
        let index = free.first_one()?;

        Some(self.vars.by_index(&index).unwrap())
    }

    // Here we need to:
    // - look up the Atom and return the Var if found
    // - otherwise:
    //   - find the earliest Variable mentioned by the Atom
    //   - get the cutoff level of that Variable
    //   - add a new Var at that level and associate it with the atom
    //   - increment the cutoff levels of all the lower Variables
    //     - which are the lower Variables?
    //     - Variables that have to be eliminated earlier
    //     - so Variables with a lower index
    fn atom(&self, atom: Atom) -> Var {
        self.atoms.by_key_or_insert(atom, |atom| {
            eprint!(" - new atom: ");
            atom.println(&mut std::io::stderr()).ok();

            let mut cutoffs = self.cutoffs.write();
            match self.earliest_mention(atom) {
                Some(mention) => {
                    let level = *cutoffs.get(&mention).unwrap();
                    let var = self.manager.add_var_at_level(level);

                    // increment the cutoff levels of all the higher Variables
                    let mindex = self.vars.by_key(&mention).unwrap();
                    for (variable, vindex) in self.vars.iter() {
                        if vindex < mindex {
                            *cutoffs.get_mut(&variable).unwrap() += 1;
                        }
                    }

                    var
                }
                None => {
                    let var = self.manager.add_var_at_level(Level::MIN);
                    for variable in self.vars.keys() {
                        *cutoffs.get_mut(&variable).unwrap() += 1;
                    }
                    var
                }
            }
        })
    }

    fn variable(&self, var: Variable) -> usize {
        self.vars.by_key_or_insert(var, |_| self.vars.size())
    }

    fn eliminate(&self, var: Variable, cutoff: Level, bdd: &BDD) -> BDD {
        match bdd.tree() {
            Tree::Node(Node {
                var: guard,
                high,
                low,
            }) => {
                let level = self.manager.level_of(&guard);

                if level < cutoff {
                    let high = self.eliminate(var.clone(), cutoff, &high);
                    let low = self.eliminate(var.clone(), cutoff, &low);

                    self.manager.ite(guard, high, low)
                } else {
                    let quant = Quantified {
                        quantifier: Quantifier::Exists,
                        variables: Arc::new([var]),
                        body: self.term(bdd),
                        span: None,
                    }
                    .into_term_in(&*self.pool);

                    eprint!("calling the QE backend on term:");
                    quant.println(&mut std::io::stderr()).ok();

                    let eliminated = self.solver.qe(quant).unwrap();

                    eprint!("QE backend result: ");
                    eliminated.println(&mut std::io::stderr()).ok();

                    self.bdd(&eliminated)
                }
            }
            Tree::Terminal(true) => self.manager.top(),
            Tree::Terminal(false) => self.manager.top(),
        }
    }

    fn bdd(&self, term: &Term) -> BDD {
        if let Some(bdd) = self.bdds.get(term) {
            return bdd.clone();
        }

        eprintln!(
            " - bdd(), manager size: {}, variables: {}",
            self.manager.size(),
            self.manager.n_vars()
        );

        let bdd = match term.kind() {
            TermKind::Atom(atom) => {
                if let Ok(atom) = CoreAtom::try_from(atom) {
                    match atom {
                        CoreAtom::True => self.manager.top(),
                        CoreAtom::False => self.manager.bottom(),
                        CoreAtom::Not(arg) => !self.bdd(arg),
                        CoreAtom::Implies(args) => {
                            let bdds: Vec<_> = args.iter().map(|arg| self.bdd(arg)).collect();
                            bdds.into_iter()
                                .rev()
                                .fold(self.manager.bottom(), |acc, arg| {
                                    self.manager.implies(acc, arg)
                                })
                        }
                        CoreAtom::And(args) => {
                            let bdds: Vec<_> = args.iter().map(|arg| self.bdd(arg)).collect();
                            bdds.into_iter()
                                .fold(self.manager.top(), |acc, arg| acc & arg)
                        }
                        CoreAtom::Or(args) => {
                            let bdds: Vec<_> = args.iter().map(|arg| self.bdd(arg)).collect();
                            bdds.into_iter()
                                .fold(self.manager.bottom(), |acc, arg| acc | arg)
                        }
                        CoreAtom::Xor(args) => {
                            let bdds: Vec<_> = args.iter().map(|arg| self.bdd(arg)).collect();
                            bdds.into_iter()
                                .fold(self.manager.bottom(), |acc, arg| acc ^ arg)
                        }
                        CoreAtom::Ite(guard, then, else_) => {
                            let guard = self.bdd(guard);
                            let then = self.bdd(then);
                            let else_ = self.bdd(else_);

                            self.manager.ite(guard, then, else_)
                        }
                        CoreAtom::Equals(_) | CoreAtom::Distinct(_) => {
                            BDD::from(self.atom(Atom(term.clone())))
                        }
                    }
                } else if let Ok(sort) = Sort::of(term)
                    && sort == Core::Bool()
                {
                    BDD::from(self.atom(Atom(term.clone())))
                } else {
                    unreachable!();
                }
            }
            TermKind::Constant(_) => unreachable!(),
            TermKind::Quantified(_) => unreachable!(),
            TermKind::Let(_) => todo!(),
        };

        self.bdds.insert(term.clone(), bdd.clone());

        bdd
    }

    fn term(&self, bdd: &BDD) -> Term {
        #[allow(clippy::mutable_key_type)]
        let mut cache = HashMap::new();
        self.term_in(bdd, &mut cache)
    }

    #[allow(clippy::mutable_key_type)]
    fn term_in(&self, bdd: &BDD, cache: &mut HashMap<BDD, Term>) -> Term {
        if let Some(term) = cache.get(bdd) {
            return term.clone();
        }

        let term = match bdd.tree() {
            Tree::Node(Node { var, high, low }) => {
                let guard = self.atoms.by_index(&var).unwrap().0;
                let high = self.term_in(&high, cache);
                let low = self.term_in(&low, cache);

                if high == true && low == false {
                    guard
                } else if high == false && low == true {
                    Core::not().call([guard]).into_term_in(&*self.pool)
                } else if low == true {
                    Core::implies()
                        .call([guard, high])
                        .into_term_in(&*self.pool)
                } else if low == false {
                    Core::and().call([guard, high]).into_term_in(&*self.pool)
                } else if high == true {
                    Core::or().call([guard, low]).into_term_in(&*self.pool)
                } else {
                    Core::ite()
                        .call([guard, high, low])
                        .into_term_in(&*self.pool)
                }
            }
            Tree::Terminal(false) => Core::False().into_term_in(&*self.pool),
            Tree::Terminal(true) => Core::True().into_term_in(&*self.pool),
        };

        cache.insert(bdd.clone(), term.clone());
        term
    }

    fn free(&self, term: &Term) -> BitSet {
        if let Some(bits) = self.free.get(term) {
            return bits.clone();
        }

        let bits = match term.kind() {
            TermKind::Constant(_) => BitSet::new(),
            TermKind::Atom(atom) => {
                let mut bits = BitSet::new();
                if let FunctionRef::Bound(bound) = &atom.head
                    && let Function::Variable(var) = &bound.function
                {
                    bits.set(self.variable(var.clone()), true);
                }
                for arg in &*atom.arguments {
                    bits |= self.free(arg);
                }

                bits
            }
            TermKind::Quantified(quant) => {
                let mut bits = self.free(&quant.body);
                for var in &*quant.variables {
                    bits.set(self.variable(var.clone()), false)
                }
                bits
            }
            TermKind::Let(let_) => {
                let mut bits = self.free(&let_.body);
                for bind in &*let_.bindings {
                    bits.set(self.variable(bind.variable.clone()), false)
                }
                bits
            }
        };
        self.free.insert(term.clone(), bits.clone());

        bits
    }
}
