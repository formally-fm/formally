//
// ::formally - the open-source formal methods toolchain
//
// Copyright (c) 2025 Nicola Gigante
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
use formally::{
    smt::{
        self, TermPool as _,
        smtlib::{ast, interpreter::Interpreter},
        term,
    },
    support::*,
};

impl Interpreter {
    fn sort_to_smt_term(sort: &ast::Sort, solver: &smt::Solver) -> smt::Term {
        match sort {
            ast::Sort::Simple(ast::Identifier::Symbol(name)) => {
                let head = Identifier::from(name.inner()).over(name.span());
                solver.term(term!(#head))
            }
            ast::Sort::Application(ast::SortApplication {
                head: ast::Identifier::Symbol(head),
                args,
                span,
            }) => {
                let head = Identifier::from(head.inner())
                    .into_owned()
                    .over(head.span());
                let args = args
                    .iter()
                    .map(|s| Interpreter::sort_to_smt_term(s, solver));

                solver.term(term!(#head #(#args)*).over(span.clone()))
            }
            _ => todo!(),
        }
    }

    pub(crate) fn sort_to_smt(solver: &smt::Solver, sort: &ast::Sort) -> Result<smt::Sort> {
        let term = Interpreter::sort_to_smt_term(sort, solver);
        let term = solver.env().resolve(&term, smt::Role::Sort, solver)?;

        smt::Sort::evaluate(&term)
    }

    fn constant_to_smt(solver: &smt::Solver, cnst: ast::Constant) -> smt::Term {
        let span = cnst.span();
        let cnst = match cnst {
            ast::Constant::Numeral(n) => smt::Constant::from(n.value),
            ast::Constant::Decimal(_) => todo!(),
            ast::Constant::Hexadecimal(n) => smt::Constant::from(n.value),
            ast::Constant::Binary(n) => smt::Constant::from(n.value),
            ast::Constant::String(_) => todo!(),
        }
        .over(span);

        solver.term(term!(#cnst))
    }

    fn app_to_smt(
        solver: &smt::Solver,
        id: ast::QualifiedIdentifier,
        arguments: &[ast::Term],
        span: Option<Span>,
    ) -> Result<smt::Term> {
        let ast::QualifiedIdentifier {
            id, span: idspan, ..
        } = id;
        match id {
            ast::Identifier::Symbol(symbol) => {
                let mut smtargs = Vec::new();
                for arg in arguments {
                    smtargs.push(Interpreter::term_to_smt(solver, arg.clone())?)
                }

                let syspan = symbol.span();
                let head = Identifier::from(symbol.into_inner()).over(syspan);
                Ok(solver.term(
                    smt::TermKind::Atom(smt::Atom::Unbound(smt::UnboundAtom {
                        head,
                        arguments: smtargs,
                        span: idspan,
                    }))
                    .over(span),
                ))
            }
            _ => todo!(),
        }
    }

    pub(crate) fn term_to_smt(solver: &smt::Solver, term: ast::Term) -> Result<smt::Term> {
        match term {
            ast::Term::Constant(cnst) => Ok(Interpreter::constant_to_smt(solver, cnst)),
            ast::Term::Identifier(id) => {
                let span = id.span.clone();
                Interpreter::app_to_smt(solver, id, &[], span)
            }
            ast::Term::Application(ast::Application { head, args, span }) => {
                Interpreter::app_to_smt(solver, head, &args, span)
            }
            ast::Term::Let(_) => todo!(),
            ast::Term::Lambda(_) => todo!(),
            ast::Term::Exists(exists) => {
                let mut bindings = Vec::new();
                for var in exists.bindings {
                    bindings.push(Interpreter::sorted_var_to_binding(solver, var)?)
                }
                let body = Interpreter::term_to_smt(solver, *exists.body)?;

                Ok(solver.term(smt::TermKind::Quantified(smt::Quantified {
                    quantifier: smt::Quantifier::Exists,
                    bindings,
                    body,
                    span: exists.span.clone(),
                })))
            }
            ast::Term::Forall(forall) => {
                let mut bindings = Vec::new();
                for var in forall.bindings {
                    bindings.push(Interpreter::sorted_var_to_binding(solver, var)?)
                }
                let body = Interpreter::term_to_smt(solver, *forall.body)?;

                Ok(solver.term(smt::TermKind::Quantified(smt::Quantified {
                    quantifier: smt::Quantifier::Forall,
                    bindings,
                    body,
                    span: forall.span.clone(),
                })))
            }
            ast::Term::Match(_) => todo!(),
            ast::Term::Attributed(_) => todo!(),
        }
    }

    fn sorted_var_to_binding(solver: &smt::Solver, var: ast::SortedVar) -> Result<smt::Binding> {
        Ok(smt::Binding::new(
            Identifier::from(var.name.inner()),
            Interpreter::sort_to_smt(solver, &var.sort)?,
            var.span.clone(),
        ))
    }
}
