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

use crate::formally;
use formally::{smt::*, support::Nominal};
use std::ops::Deref;
use std::{
    cell::RefCell,
    collections::{HashMap, HashSet},
    sync::Arc,
};

// What should I do:
//
// ```
// let pool = Pool::new();
//
// let t1: Term = ...;
//
// // intern t1 or return an equal term
// let t2: Term = pool.unique(t1);
//
// // create and intern the term or return an equal term
// let t3: Term = pool.unique(term!(and p #t2));
// ```
//
// When a term is interned, all the subterms are interned, and the returned term is made
// recursively only of interned terms.
//
// A term is looked up recursively.
//

#[derive(Debug, Clone, Default)]
pub struct Pool {
    structural: RefCell<HashSet<Term>>,
    nominals: RefCell<HashMap<*const TermKind, Term>>,
}

impl Pool {
    pub fn new() -> Pool {
        Pool::default()
    }

    pub fn unique(&self, t: impl Unique) -> Term {
        t.unique(self)
    }
}

pub trait Unique {
    fn unique(self, pool: &Pool) -> Term;
}

impl Unique for &Term {
    fn unique(self, pool: &Pool) -> Term {
        // if `t` is nominally equal to an interned term, we return it
        let p = self.kind() as *const TermKind;
        if let Some(t) = pool.nominals.borrow().get(&p) {
            return t.clone();
        }

        // if `t` is structurally equal to an interned term, we return the interned one
        if let Some(t) = pool.structural.borrow().get(self) {
            return t.clone();
        }

        // if the term is not here, we intern it recursively uniquing the subterms
        match self.kind() {
            c @ TermKind::Constant(_) => {
                let t = Term::from(c.clone());
                pool.structural.borrow_mut().insert(t.clone());
                pool.nominals.borrow_mut().insert(t.kind() as *const TermKind, t.clone());
                
                t
            },
            TermKind::Atom(atom) => match atom {
                Atom::Bound(BoundAtom {
                                head,
                                arguments,
                                span,
                            }) => {
                    let arguments = arguments.iter().map(|t| t.unique(pool)).collect();
                    let t = Term::from(TermKind::Atom(Atom::Bound(BoundAtom {
                        head: head.clone(),
                        arguments,
                        span: span.clone(),
                    })));
                    pool.structural.borrow_mut().insert(t.clone());
                    pool.nominals
                        .borrow_mut()
                        .insert(t.kind() as *const TermKind, t.clone());

                    t
                }
                Atom::Unbound(UnboundAtom {
                                  head,
                                  arguments,
                                  span,
                              }) => {
                    let arguments = arguments.iter().map(|t| t.unique(pool)).collect();
                    let t = Term::from(TermKind::Atom(Atom::Unbound(UnboundAtom {
                        head: head.clone(),
                        arguments,
                        span: span.clone(),
                    })));
                    pool.structural.borrow_mut().insert(t.clone());
                    pool.nominals
                        .borrow_mut()
                        .insert(t.kind() as *const TermKind, t.clone());

                    t
                }
            },
        }
    }
}

impl Unique for TermKind {
    fn unique(self, pool: &Pool) -> Term {
        pool.unique(&Term::from(self.clone()))   
    }
}

impl Unique for &macros::Term<'_> {
    fn unique(self, pool: &Pool) -> Term {
        match self {
            macros::Term::Term(t) => t.unique(pool),
            macros::Term::Constant(c) => match c {
                macros::Constant::Integer { value } => pool.unique(&Term::from(Constant::Integer {
                    value: Integer::from(*value),
                    span: None,
                })),
                macros::Constant::Rational { value } => pool.unique(&Term::from(Constant::Rational {
                    value: Rational::from_str_radix(value, 10).unwrap(),
                    span: None,
                })),
            },
            macros::Term::Atom(macros::Atom { head, arguments }) => match head {
                macros::AtomHead::Bound(macros::BoundHead { function }) => {
                    pool.unique(&Term::from(TermKind::Atom(Atom::Bound(BoundAtom {
                        head: Reference {
                            function: function.clone(),
                            span: None,
                        },
                        arguments: arguments.iter().map(|t| pool.unique(t)).collect(),
                        span: None,
                    }))))
                }
                macros::AtomHead::Unbound(macros::UnboundHead { name }) => {
                    pool.unique(&Term::from(TermKind::Atom(Atom::Unbound(UnboundAtom {
                        head: name.clone(),
                        arguments: arguments.iter().map(|t| pool.unique(t)).collect(),
                        span: None,
                    }))))
                }
            },
        }
    }
}
