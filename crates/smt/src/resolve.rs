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
use std::{collections::HashMap, iter::zip};

impl Env {
    /// Perform *name resolution*.
    ///
    /// Name resolution is the process of replacing all the [unbound atoms][UnboundAtom] in a term
    /// with [bound](BoundAtom) ones, i.e. replacing raw names with entities. This function should
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
    pub fn resolve<P: TermPool>(&self, term: &Term, role: Role, pool: &P) -> Result<Term>
    {
        Ok(match term.kind() {
            TermKind::Constant(_) => term.clone(),
            TermKind::Atom(Atom::Bound(atom)) => pool.term(TermKind::Atom(Atom::Bound(
                self.resolve_bound(atom, pool)?,
            ))),
            TermKind::Atom(Atom::Unbound(unbound)) => pool.term(TermKind::Atom(Atom::Bound(
                self.resolve_unbound(unbound, role, pool)?,
            ))),
        })
    }

    fn resolve_bound<P: TermPool>(&self, atom: &BoundAtom, pool: &P) -> Result<BoundAtom>
    {
        let domain = atom.domain();

        if domain.len() != atom.arguments.len() {
            error!(
                atom.span(),
                "applied {} arguments to a function of {} parameters",
                atom.arguments.len(),
                domain.len(),
            );
            return Err(DiagnosticEmitted);
        }

        let mut resolved = Vec::new();
        for (sort, arg) in zip(domain, &atom.arguments) {
            if Sort::equal(&sort, &Sort::sort()) {
                resolved.push(self.resolve(arg, Role::Sort, pool)?);
            } else {
                resolved.push(self.resolve(arg, Role::Function, pool)?);
            }
        }

        Ok(BoundAtom {
            head: atom.head.clone(),
            arguments: resolved,
            span: atom.span.clone(),
        })
    }

    fn resolve_unbound<P: TermPool>(&self, unbound: &UnboundAtom, role: Role, pool: &P) -> Result<BoundAtom>
    {
        let head = Identifier::from(unbound.head.name()).over(unbound.head.span());

        self.lookup(head.clone(), role)
            .filter_map(move |f| {
                let atom = BoundAtom {
                    head: Reference {
                        function: f.clone(),
                        span: head.span(),
                    },
                    arguments: unbound.arguments.clone(),
                    span: unbound.span(),
                };
                let atom = Diagnostic::with(
                    NullEmitter,
                    AssertUnwindSafe(|| self.resolve_bound(&atom, pool)),
                )
                .ok()?;

                let mut arguments = Vec::new();
                for arg in &atom.arguments {
                    arguments.push(Sort::of(arg).ok()?);
                }

                let mut matches = HashMap::new();
                for (sort, arg) in zip(atom.domain(), &arguments) {
                    if !sort.matches_with(arg, &mut matches) {
                        return None;
                    }
                }

                Some(atom)
            })
            .one()
    }
}
