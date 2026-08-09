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

impl Term {
    /// Check the well-formedness of the term by performing name resolution and type checking
    /// together.
    ///
    /// The resolved term is returned.
    pub fn validated(self, env: &Env) -> Result<Self> {
        let resolved = self.resolve(env, Role::Function)?;
        let _ = Sort::of(&resolved, env.context())?;
        Ok(resolved)
    }
}

impl Sort {
    /// Check the well-formedness of the sort.
    pub fn validate(&self, env: &Env) -> Result<()> {
        let _ = Sort::evaluate(&TermKind::from(self), env.context())?;
        Ok(())
    }
}

impl Declaration {
    /// Check the well-formedness of the sorts involved in the declaration.
    ///
    /// The returned [Declaration] is equal to `self`.
    pub fn validated(self, env: &Env) -> Result<Declaration> {
        for sort in &self.domain {
            sort.validate(env)?;
        }
        self.range.validate(env)?;

        Ok(self)
    }
}

impl Definition<Term> {
    /// Check the well-formedness of the sorts and the terms involved in the declaration.
    ///
    /// The terms involved in the given definition are [resolved](Term::resolve()) and the result
    /// is returned.
    pub fn validated(mut self, env: &Env) -> Result<Self> {
        for param in &self.domain {
            param.sort().validate(env)?;
        }
        self.body = self.body.validated(env)?;

        let inferred = Sort::of(&self.body, env.context())?;
        if !Sort::equal(&inferred, &self.range) {
            error!(&env.context(), self.span, "sort mismatch in definition");
            note!(
                &env.context(),
                self.range.span(),
                "expected term of sort `{}`",
                self.range
            );
            note!(
                &env.context(),
                self.body.span(),
                "found term of sort `{}`",
                inferred
            );

            return Err(DiagnosticEmitted);
        }

        Ok(self)
    }
}
