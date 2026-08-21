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

use crate::*;
use formally::support::*;

use std::panic::AssertUnwindSafe;
use std::{collections::HashMap, iter::zip, sync::Arc};

impl Env {
    /// Perform *name resolution*.
    ///
    /// Name resolution is the process of replacing all the [unbound atoms][UnboundAtom] in a term
    /// with [bound](BoundRef) ones, i.e. replacing raw names with entities. This function should
    /// usually not be needed directly, since [Solver::declare()], [Solver::define()], and
    /// [Solver::require()] properly resolve the terms involved automatically.
    ///
    /// The [environment][Env] argument is used for name lookups, using at top-level the scope
    /// `env.functions` if `role` is [Role::Function] or `env.sorts` if `role` is [Role::Sort].
    ///
    /// Given that SMT-LIB supports name lookup of overloaded symbols based on the sorts of their
    /// arguments, name resolution is tightly coupled with type checking, and for this reason it
    /// may fail with reasons related to type checking. Usually, name resolution has to be performed
    /// before type checking, because type checking of unbound atoms is not possible. This seems
    /// to require double the calls to [Term::type_check()], but the latter caches its results in
    /// `env.context()`, so each subterm gets type-checked only once anyway.
    pub fn resolve(&self, term: &Term, role: Role, pool: &dyn TermPool) -> Result<Term> {
        Ok(match term.kind() {
            TermKind::Constant(_) => term.clone(),
            TermKind::Atom(atom) => self.resolve_atom(atom, role, pool)?.into_term_in(pool),
            TermKind::Quantified(quant) => {
                TermKind::Quantified(self.resolve_quant(quant, role, pool)?).into_term_in(pool)
            }
            TermKind::Let(let_) => {
                TermKind::Let(self.resolve_let(let_, role, pool)?).into_term_in(pool)
            }
        })
    }

    fn resolve_atom(&self, atom: &Atom, role: Role, pool: &dyn TermPool) -> Result<Atom> {
        match &atom.head {
            FunctionRef::Bound(bound) => self.resolve_bound(bound, &atom.arguments, pool),
            FunctionRef::Unbound(unbound) => {
                self.resolve_unbound(unbound, &atom.arguments, role, pool)
            }
        }
    }

    fn resolve_bound(
        &self,
        head: &BoundRef,
        arguments: &[Term],
        pool: &dyn TermPool,
    ) -> Result<Atom> {
        let domain = head.domain(arguments.len());

        if domain.len() != arguments.len() {
            error!(
                head.span(),
                "applied {} arguments to a function of {} parameters",
                arguments.len(),
                domain.len(),
            );
            return Err(DiagnosticEmitted);
        }

        let mut resolved = Vec::new();
        for (sort, arg) in zip(domain, arguments) {
            if sort == Sort::sort() {
                resolved.push(self.resolve(arg, Role::Sort, pool)?);
            } else {
                resolved.push(self.resolve(arg, Role::Function, pool)?);
            }
        }

        Ok(Atom {
            head: FunctionRef::Bound(head.clone()),
            arguments: Arc::from(resolved.into_boxed_slice()),
            span: head.span.clone(),
        })
    }

    fn resolve_unbound(
        &self,
        unbound: &UnboundRef,
        arguments: &[Term],
        role: Role,
        pool: &dyn TermPool,
    ) -> Result<Atom> {
        let head = Identifier::from(unbound.name.name()).over(unbound.name.span());

        self.lookup(head.clone(), role)
            .filter_map(move |f| {
                let bound = BoundRef {
                    function: f.clone(),
                    span: head.span(),
                };
                let atom = Diagnostic::with(
                    NullEmitter,
                    AssertUnwindSafe(|| self.resolve_bound(&bound, arguments, pool)),
                )
                .ok()?;

                let mut arguments = Vec::new();
                for arg in &*atom.arguments {
                    arguments.push(Sort::of(arg).ok()?);
                }

                #[allow(clippy::mutable_key_type)]
                let mut matches = HashMap::new();
                let domain = bound.domain(arguments.len());
                for (sort, arg) in zip(domain, &arguments) {
                    if !sort.matches_with(arg, &mut matches) {
                        return None;
                    }
                }

                Some(atom)
            })
            .one()
    }

    fn resolve_quant(
        &self,
        quant: &Quantified,
        role: Role,
        pool: &dyn TermPool,
    ) -> Result<Quantified> {
        let mut env = Env::new().with_parent(self.clone());

        let mut variables = Vec::with_capacity(quant.variables.len());
        for var in &*quant.variables {
            match var {
                QuantifiedVariable::Bound(var) => {
                    variables.push(QuantifiedVariable::Bound(var.clone()));
                    env.functions
                        .add(var.name().name(), Function::from(var.clone()));
                }
                QuantifiedVariable::Unbound(unbound) => {
                    let resolved = self.resolve(&unbound.sort, Role::Sort, pool)?;
                    resolved.type_check()?;
                    let sort = Sort::try_from(resolved)?;

                    let var = Variable::new(unbound.name.clone(), sort, unbound.span.clone());

                    variables.push(QuantifiedVariable::Bound(var.clone()));
                    env.functions
                        .add(var.name().name(), Function::from(var.clone()));
                }
            }
        }

        let body = env.resolve(&quant.body, role, pool)?;

        Ok(Quantified {
            quantifier: quant.quantifier,
            variables: Arc::from(variables.into_boxed_slice()),
            body,
            span: quant.span.clone(),
        })
    }

    fn resolve_let(&self, let_: &Let, role: Role, pool: &dyn TermPool) -> Result<Let> {
        let mut env = Env::new().with_parent(self.clone());

        for bind in &*let_.bindings {
            env.functions.add(
                bind.variable.name().name(),
                Function::from(bind.variable.clone()),
            );
        }

        let body = env.resolve(&let_.body, role, pool)?;

        Ok(Let {
            bindings: let_.bindings.clone(),
            body,
            span: let_.span.clone(),
        })
    }
}
