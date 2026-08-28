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
use formally::{smt::backends::*, support::*};
use itertools::Itertools;

use linkme::distributed_slice;
use thiserror::Error;

#[doc(hidden)]
#[distributed_slice]
pub static BACKENDS: [&'static dyn Backend];

/// Type that collects the available SMT backends.
///
/// This type provides access to the SMT backends registered using the
/// [backend](smt::backend) attribute. The type is not supposed to be instantiated, it just provides
/// associated functions.
pub struct Register;

/// Error type for the methods of the [Register] type.
///
/// This error type is [Diagnosable], meaning that you can convert it to [DiagnosticEmitted] with
/// the `?` operator and it emits itself as diagnostics automatically when this happens.
#[derive(Debug, Error, Located)]
#[error("SMT backend `{0}` not found")]
pub struct BackendNotFound<'s>(pub Identifier<'s>);

impl Diagnosable for BackendNotFound<'_> {
    fn notes(&self) -> DiagnosticEmitted {
        let mut backends = Vec::new();
        for backend in Register::backends() {
            if let Ok(backend) = backend.name() {
                backends.push(backend)
            }
        }

        note!(
            self.0.span(),
            "available backends: {}",
            backends.into_iter().join(", ")
        );
        DiagnosticEmitted
    }
}

pub struct Default;

impl Backend for Default {
    fn name(&self) -> Result<&str, Error> {
        Register::default_backend()?.name()
    }

    fn manager(&self) -> Result<Box<dyn Manager>, Error> {
        Register::default_backend()?.manager()
    }

    fn solver(&self, config: &Config, manager: Rc<dyn Manager>) -> Result<Box<dyn Solver>, Error> {
        Register::default_backend()?.solver(config, manager)
    }
}

impl Register {
    /// Return the default backend.
    pub fn default_backend() -> Result<&'static dyn Backend, BackendNotFound<'static>> {
        if cfg!(feature = "cvc5") {
            Self::backend("cvc5")
        } else if cfg!(feature = "z3") {
            Self::backend("z3")
        } else {
            Err(BackendNotFound(Identifier::from("default")))
        }
    }

    /// Return the registered backend that goes after the give name, if it exists.
    pub fn backend<'a>(
        name: impl Into<Identifier<'a>>,
    ) -> Result<&'static dyn Backend, BackendNotFound<'a>> {
        let name = name.into();
        for b in BACKENDS {
            if let Ok(bname) = b.name() && bname == name.name() {
                return Ok(*b);
            }
        }
        Err(BackendNotFound(name))
    }

    /// Return a slice of all the currently registered backends.
    pub fn backends() -> &'static [&'static dyn Backend] {
        &BACKENDS
    }
}
