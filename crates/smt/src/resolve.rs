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

use std::{collections::HashMap, iter::zip};

impl BoundAtom {
    fn resolve(&self, env: &Env) -> Result<BoundAtom> {
        let domain = self.domain();

        if domain.len() != self.arguments.len() {
            error!(
                &env.context(),
                self.span(),
                "applied {} arguments to a function of {} parameters",
                self.arguments.len(),
                domain.len(),
            );
            return Err(DiagnosticEmitted);
        }

        let mut resolved = Vec::new();
        for (sort, arg) in zip(domain, &self.arguments) {
            if Sort::equal(&sort, &Sort::sort()) {
                resolved.push(arg.resolve(env, Role::Sort)?);
            } else {
                resolved.push(arg.resolve(env, Role::Function)?);
            }
        }

        Ok(BoundAtom {
            head: self.head.clone(),
            arguments: resolved,
            span: self.span.clone(),
        })
    }
}

impl UnboundAtom {
    fn resolve(&self, env: &Env, role: Role) -> Result<BoundAtom> {
        let head = Identifier::from(self.head.name()).over(self.head.span());

        env.lookup(head.clone(), role)
            .filter_map(move |f| {
                let atom = BoundAtom {
                    head: Reference {
                        function: f.clone(),
                        span: head.span(),
                    },
                    arguments: self.arguments.clone(),
                    span: self.span(),
                };
                let silent = env.clone().with_emitter(NullEmitter);
                let atom = atom.resolve(&silent).ok()?;

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

impl Term {
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
    pub fn resolve(&self, env: &Env, role: Role) -> Result<Term> {
        Ok(match self.kind() {
            TermKind::Constant(_) => self.clone(),
            TermKind::Atom(Atom::Bound(atom)) => {
                pool.term(&TermKind::Atom(Atom::Bound(atom.resolve(env)?)))
            }
            TermKind::Atom(Atom::Unbound(unbound)) => {
                pool.term(&TermKind::Atom(Atom::Bound(unbound.resolve(env, role)?)))
            }
        })
    }
}
