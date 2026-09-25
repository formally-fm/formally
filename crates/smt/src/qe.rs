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

//! Interfaces for quantifier elimination.
//!
//! This module collects everything regarding quantifier elimination.
//!
//! For now, just the [Backend] trait which is implemented by the result of
//! [Backend::qe()](backends::Backend::qe()), for SMT backends that support QE, but may also be
//! implemented separately by other engines implementing QE exclusively.

use crate::formally;
use formally::{
    smt::{
        self, Atom, Config, Let, Quantified, Sort, Term, TermKind, TermPool, ToTerm,
        TypeCheckError, theories::Core,
    },
    support::{Diagnosable, DiagnosticEmitted, Level, Located, Span},
};

use itertools::Itertools;
use thiserror::Error;
use transitive::Transitive;

use std::{rc::Rc, sync::Arc};

#[derive(Debug, Error, Located, Transitive)]
#[transitive(from(TypeCheckError, ErrorKind))]
#[transitive(from(Box<dyn Diagnosable>, ErrorKind))]
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
    #[error("quantifier elimination expects term of sort Bool, found `{0}`")]
    NotBoolean(Sort),
    #[error(transparent)]
    TypeCheck(#[from] TypeCheckError),
    #[error(transparent)]
    Backend(#[from] Box<dyn Diagnosable>),
}

impl Diagnosable for Error {
    fn level(&self) -> Level {
        match &self.kind {
            ErrorKind::Backend(err) => err.level(),
            _ => Level::Error,
        }
    }

    fn notes(&self) -> DiagnosticEmitted {
        match &self.kind {
            ErrorKind::Backend(err) => err.notes(),
            _ => DiagnosticEmitted,
        }
    }
}

/// A trait for backends providing quantifier elimination functionalities.
pub trait Backend {
    /// Perform quantifier elimination on the given [Quantified] term, constructing the result using
    /// `pool`.
    ///
    /// The method *can assume* the body of the quantified term is *quantifier-free* and well-typed
    /// of Boolean sort.
    fn qe(&self, quant: Quantified) -> Result<Term, Box<dyn Diagnosable>>;

    /// The [TermPool] this backend is using to build terms.
    fn pool(&self) -> Arc<dyn TermPool>;
}

pub struct QE<'q> {
    backend: Box<dyn 'q + Backend>,
}

impl<'q> QE<'q> {
    pub fn new(backend: Box<dyn 'q + Backend>) -> QE<'q> {
        QE { backend }
    }

    pub fn qe(&self, term: &Term) -> Result<Term, Error> {
        let sort = Sort::of(term)?;
        if sort != Core::Bool() {
            return Err(Error {
                kind: ErrorKind::NotBoolean(sort),
                span: term.span(),
            });
        }

        self.qe_inner(term)
    }

    fn qe_inner(&self, term: &Term) -> Result<Term, Error> {
        if term.is_quantifier_free() {
            return Ok(term.clone());
        }

        match term.kind() {
            TermKind::Constant(_) => Ok(term.clone()),
            TermKind::Atom(atom) => Ok(Atom {
                head: atom.head.clone(),
                arguments: atom
                    .arguments
                    .iter()
                    .map(|arg| self.qe(arg))
                    .try_collect()?,
                span: atom.span(),
            }
            .into_term_in(&*self.backend.pool())),
            TermKind::Quantified(quant) => {
                let quant = Quantified {
                    quantifier: quant.quantifier,
                    variables: quant.variables.clone(),
                    body: self.qe(&quant.body)?,
                    span: quant.span(),
                };
                Ok(self.backend.qe(quant)?)
            }
            TermKind::Let(let_) => Ok(Let {
                bindings: let_.bindings.clone(),
                body: self.qe(&let_.body)?,
                span: let_.span(),
            }
            .into_term_in(&*self.backend.pool())),
        }
    }
}
