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

pub trait Resolve: Sized {
    fn resolve(&self, env: &Env, pool: &dyn TermPool, role: Role) -> Result<Self>;
}

impl Resolve for Term {
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
    fn resolve(&self, env: &Env, pool: &dyn TermPool, role: Role) -> Result<Term> {
        if self.is_resolved() {
            return Ok(self.clone());
        }

        Ok(match self.kind() {
            TermKind::Constant(_) => self.clone(),
            TermKind::Atom(atom) => Self::resolve_atom(atom, env, role, pool)?.into_term_in(pool),
            TermKind::Quantified(quant) => {
                TermKind::Quantified(Self::resolve_quant(quant, env, role, pool)?)
                    .into_term_in(pool)
            }
            TermKind::Let(let_) => {
                TermKind::Let(Self::resolve_let(let_, env, role, pool)?).into_term_in(pool)
            }
        })
    }
}

impl Term {
    fn resolve_atom(atom: &Atom, env: &Env, role: Role, pool: &dyn TermPool) -> Result<Atom> {
        match &atom.head {
            FunctionRef::Bound(bound) => Self::resolve_bound(bound, env, &atom.arguments, pool),
            FunctionRef::Unbound(unbound) => {
                Self::resolve_unbound(unbound, env, &atom.arguments, role, pool)
            }
        }
    }

    fn resolve_bound(
        head: &BoundRef,
        env: &Env,
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
                resolved.push(arg.resolve(env, pool, Role::Sort)?);
            } else {
                resolved.push(arg.resolve(env, pool, Role::Function)?);
            }
        }

        Ok(Atom {
            head: FunctionRef::Bound(head.clone()),
            arguments: Arc::from(resolved.into_boxed_slice()),
            span: head.span.clone(),
        })
    }

    fn resolve_unbound(
        unbound: &UnboundRef,
        env: &Env,
        arguments: &[Term],
        role: Role,
        pool: &dyn TermPool,
    ) -> Result<Atom> {
        let head = Identifier::from(unbound.name.name()).over(unbound.name.span());

        let mut resolved = Vec::with_capacity(arguments.len());
        let mut argsorts = Vec::with_capacity(arguments.len());
        for arg in arguments {
            let t = arg.resolve(env, pool, role)?;
            argsorts.push(Sort::of(&t)?);
            resolved.push(t);
        }

        env.lookup(head.clone(), role)
            .filter_map(move |f| Self::candidate(f, env, &head, &argsorts, &resolved, pool))
            .one()
    }

    fn candidate(
        f: &Function,
        env: &Env,
        head: &Identifier<'_>,
        argsorts: &[Sort],
        arguments: &[Term],
        pool: &dyn TermPool,
    ) -> Option<Atom> {
        let bound = BoundRef {
            function: f.clone(),
            span: head.span(),
        };
        let atom = Diagnostic::with(
            NullEmitter,
            AssertUnwindSafe(|| Self::resolve_bound(&bound, env, arguments, pool)),
        )
        .ok()?;

        #[allow(clippy::mutable_key_type)]
        let mut matches = HashMap::new();
        let domain = bound.domain(arguments.len());
        for (sort, arg) in zip(domain, argsorts) {
            if !sort.matches_with(arg, &mut matches) {
                return None;
            }
        }

        Some(atom)
    }

    fn resolve_quant(
        quant: &Quantified,
        env: &Env,
        role: Role,
        pool: &dyn TermPool,
    ) -> Result<Quantified> {
        let mut nested = Env::new().with_parent(env.clone());

        let mut variables = Vec::with_capacity(quant.variables.len());
        for var in &*quant.variables {
            let var = var.resolve(env, pool, role)?;
            variables.push(var.clone());
            nested
                .functions
                .add(var.name().name(), Function::from(var.clone()));
        }

        let body = quant.body.resolve(&nested, pool, role)?;

        Ok(Quantified {
            quantifier: quant.quantifier,
            variables: Arc::from(variables.into_boxed_slice()),
            body,
            span: quant.span.clone(),
        })
    }

    fn resolve_let(let_: &Let, env: &Env, role: Role, pool: &dyn TermPool) -> Result<Let> {
        let mut nested = Env::new().with_parent(env.clone());

        for bind in &*let_.bindings {
            nested.functions.add(
                bind.variable.name().name(),
                Function::from(bind.variable.clone()),
            );
        }

        let body = let_.body.resolve(&nested, pool, role)?;

        Ok(Let {
            bindings: let_.bindings.clone(),
            body,
            span: let_.span.clone(),
        })
    }
}

impl Resolve for Variable {
    fn resolve(&self, env: &Env, pool: &dyn TermPool, _role: Role) -> Result<Self> {
        Ok(Variable::new(
            self.name().clone(),
            self.sort().resolve(env, pool, Role::Sort)?,
        )
        .over(self.span()))
    }
}

impl Resolve for Sort {
    fn resolve(&self, env: &Env, pool: &dyn TermPool, role: Role) -> Result<Self> {
        if role == Role::Function {
            internal!(None, "cannot resolve a sort with Role::Function");
            return Err(DiagnosticEmitted);
        }

        let term = self.to_term_in(pool);
        let resolved = term.resolve(env, pool, Role::Sort)?;
        let sort = Sort::try_from(resolved).ok().unwrap();

        Ok(sort)
    }
}

impl Resolve for Declared {
    fn resolve(&self, _env: &Env, _pool: &dyn TermPool, _role: Role) -> Result<Self> {
        Ok(self.clone())
    }
}

impl Resolve for Defined {
    fn resolve(&self, _env: &Env, _pool: &dyn TermPool, _role: Role) -> Result<Self> {
        Ok(self.clone())
    }
}
