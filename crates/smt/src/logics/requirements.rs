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
// AUTHORS OR COPYRIGHT HOLDERS BE IntsBLE FOR ANY CLAIM, DAMAGES OR OTHER
// IntsBILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
// OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
// SOFTWARE.
//

//! Requirements imposed by standard SMT-LIBv2 logics with the [logic] macro.
//!
//! This module declares common requirements imposed by standard SMT-LIBv2 logics and used
//! by the declaration of those standard logics with the [logic] macro.
//!
//! A logic requirement is a type implementing the [LogicRequirement] trait.
//!
//! These requirements can be used in custom invocations of the [logic] macros when declaring
//! new logics, as well as other, custom requirements.

use crate::*;

use formally::smt::logics::*;
use formally::support::*;

/// A requirement imposed by an SMT-LIBv2 logic.
///
/// Types implementing [LogicRequirement] tell how to restrict the syntax of terms and the
/// admitted declarations and definitions as specified by some logic. Requirements are used
/// in the [logic] macro to specify how the logic restricts its syntax and semantics.
///
/// The trait provides two methods, both with a do-nothing default implementation.
/// 1. [check_term()](LogicRequirement::check_term()) is invoked by [Logic::check_term()] to check
///    terms asserted to a [Solver] or used in function definitions.
/// 2. [check_function()](LogicRequirement::check_function()) checks some requirements on each
///    [UserFunction] that is being added to a [Solver].
///
/// By their `context` arguments, these methods have the ability to emit detailed diagnostics about
/// why a given term or function is being forbidden by the current logic.
pub trait LogicRequirement {
    /// Check a term.
    #[allow(unused)]
    fn check_term(logic: &dyn Logic, term: &Term) -> Result<()> {
        Ok(())
    }

    /// Check a user function to be declared or defined.
    #[allow(unused)]
    fn check_function(logic: &dyn Logic, function: &UserFunction) -> Result<()> {
        Ok(())
    }
}

/// [Logic requirement](LogicRequirement) mandating the *linearity* of terms.
///
/// Linearity is defined by the SMT-LIBv2 logics LIA and LRA as the absence of the operators
/// `*`, `/`, `mod` and `abs`, except when used with at most a single non-constant argument.
pub struct Linear;

/// [Logic requirement](LogicRequirement) mandating the *absence of quantifiers* from terms.
pub struct QuantifierFree;

/// [Logic requirement](LogicRequirement) mandating the *absence of uninterpreted functions*.
///
/// When [NoUF] is active, function declarations (as done with [Solver::declare()]) are forbidden.
/// Definitions are still possible.
pub struct NoUF;

impl LogicRequirement for Linear {
    fn check_term(logic: &dyn Logic, term: &Term) -> Result<()> {
        match term.kind() {
            TermKind::Constant(_) => Ok(()),
            TermKind::Atom(atom) => {
                if let FunctionRef::Bound(bound) = &atom.head {
                    use theories::Ints;
                    use theories::Reals;

                    let forbidden = [
                        Ints::mult(),
                        Reals::mult(),
                        Ints::div(),
                        Reals::div(),
                        Ints::mod_(),
                        Ints::abs(),
                    ];
                    if let Function::Primitive(prim) = &bound.function
                        && forbidden.contains(prim)
                    {
                        let nonlinear = atom
                            .arguments
                            .iter()
                            .filter(|arg| {
                                !matches!(
                                    arg.kind(),
                                    TermKind::Constant(
                                        Constant::Integer { .. } | Constant::Rational { .. }
                                    )
                                )
                            })
                            .count();
                        if nonlinear > 1 {
                            error!(
                                term.span(),
                                "non-linear terms are not admitted in logic `{}`",
                                logic.name()
                            );
                            note!(
                                bound.span,
                                "function `{}` can only be used with a single non-constant argument, found {}",
                                bound.function.name(),
                                nonlinear
                            );
                            return Err(DiagnosticEmitted);
                        }
                    }
                }
                for arg in &*atom.arguments {
                    Linear::check_term(logic, arg)?;
                }
                Ok(())
            }
            TermKind::Quantified(quant) => Linear::check_term(logic, &quant.body),
            TermKind::Let(let_) => {
                for bind in &*let_.bindings {
                    Linear::check_term(logic, &bind.def)?
                }
                Linear::check_term(logic, &let_.body)
            }
        }
    }
}

impl LogicRequirement for QuantifierFree {
    fn check_term(logic: &dyn Logic, term: &Term) -> Result<()> {
        match term.kind() {
            TermKind::Constant(_) => Ok(()),
            TermKind::Atom(atom) => {
                for arg in &*atom.arguments {
                    QuantifierFree::check_term(logic, arg)?;
                }
                Ok(())
            }
            TermKind::Quantified(_) => {
                error!(
                    term.span(),
                    "quantified formulas are not admitted in logic `{}`",
                    logic.name()
                );
                Err(DiagnosticEmitted)
            }
            TermKind::Let(let_) => {
                for bind in &*let_.bindings {
                    QuantifierFree::check_term(logic, &bind.def)?
                }
                QuantifierFree::check_term(logic, &let_.body)
            }
        }
    }
}

impl LogicRequirement for NoUF {
    fn check_function(logic: &dyn Logic, function: &UserFunction) -> Result<()> {
        match function {
            UserFunction::Declared(decl) if !decl.domain.is_empty() => {
                error!(
                    decl.span(),
                    "uninterpreted functions are not allowed in logic `{}`",
                    logic.name()
                );
                Err(DiagnosticEmitted)
            }
            _ => Ok(()),
        }
    }
}
