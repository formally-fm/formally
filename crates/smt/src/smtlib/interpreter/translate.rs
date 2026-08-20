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
        self, ToTerm,
        smtlib::{ast, interpreter::Interpreter},
        term,
    },
    support::*,
};

use std::sync::Arc;

impl Interpreter {
    fn sort_to_smt_term(sort: &ast::Sort, solver: &smt::Solver) -> smt::Term {
        match sort {
            ast::Sort::Simple(ast::Identifier::Symbol(name)) => Identifier::from(name.inner())
                .over(name.span())
                .into_term_in(solver),
            ast::Sort::Application(ast::SortApplication {
                head: ast::Identifier::Symbol(head),
                args,
                span,
            }) => {
                let head = Identifier::from(head.inner())
                    .into_owned()
                    .over(head.span());
                let args: Vec<_> = args
                    .iter()
                    .map(|s| Interpreter::sort_to_smt_term(s, solver))
                    .collect();

                term!(#head #(#args)*)
                    .over(span.clone())
                    .into_term_in(solver)
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

        term!(#cnst).into_term_in(solver)
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
                let term = smt::TermKind::Atom(smt::Atom::Unbound(smt::UnboundAtom {
                    head,
                    arguments: Arc::from(smtargs.into_boxed_slice()),
                    span: idspan,
                }))
                .over(span)
                .into_term_in(solver);

                Ok(term)
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
            ast::Term::Let(let_) => {
                let mut bindings = Vec::new();
                for bind in let_.bindings {
                    bindings.push(Interpreter::binding_to_binding(solver, bind)?)
                }
                let body = Interpreter::term_to_smt(solver, *let_.body)?;
                let term = smt::TermKind::Let(smt::Let {
                    bindings: Arc::from(bindings.into_boxed_slice()),
                    body,
                    span: let_.span.clone(),
                })
                .into_term_in(solver);

                Ok(term)
            }
            ast::Term::Lambda(_) => todo!(),
            ast::Term::Exists(exists) => {
                let mut variables = Vec::new();
                for var in exists.bindings {
                    variables.push(Interpreter::sorted_var_to_variable(solver, var)?)
                }
                let body = Interpreter::term_to_smt(solver, *exists.body)?;
                let term = smt::TermKind::Quantified(smt::Quantified {
                    quantifier: smt::Quantifier::Exists,
                    variables: Arc::from(variables.into_boxed_slice()),
                    body,
                    span: exists.span.clone(),
                })
                .into_term_in(solver);

                Ok(term)
            }
            ast::Term::Forall(forall) => {
                let mut variables = Vec::new();
                for var in forall.bindings {
                    variables.push(Interpreter::sorted_var_to_variable(solver, var)?)
                }
                let body = Interpreter::term_to_smt(solver, *forall.body)?;
                let term = smt::TermKind::Quantified(smt::Quantified {
                    quantifier: smt::Quantifier::Forall,
                    variables: Arc::from(variables.into_boxed_slice()),
                    body,
                    span: forall.span.clone(),
                })
                .into_term_in(solver);

                Ok(term)
            }
            ast::Term::Match(_) => todo!(),
            ast::Term::Attributed(_) => todo!(),
        }
    }

    fn sorted_var_to_variable(solver: &smt::Solver, var: ast::SortedVar) -> Result<smt::Variable> {
        Ok(smt::Variable::new(
            Identifier::from(var.name.inner()),
            Interpreter::sort_to_smt(solver, &var.sort)?,
            var.span.clone(),
        ))
    }

    fn binding_to_binding(solver: &smt::Solver, bind: ast::Binding) -> Result<smt::Binding> {
        let def = Interpreter::term_to_smt(solver, bind.body)?;
        let sort = smt::Sort::of(&def)?;

        Ok(smt::Binding {
            variable: smt::Variable::new(
                Identifier::from(bind.name.inner()),
                sort,
                bind.name.span(),
            ),
            def,
            span: bind.span.clone(),
        })
    }
}
