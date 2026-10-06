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

use crate::formally;

use formally::smt::{Rational, theories::*};

use std::collections::{HashMap, HashSet};

#[allow(clippy::mutable_key_type)]
impl Simplify for Core {
    fn simplify(&self, term: &Term, pool: &dyn TermPool) -> Term {
        let Ok(atom) = CoreAtom::try_from(term) else {
            return term.to_term_in(pool);
        };

        match atom {
            CoreAtom::Not(arg) if let Ok(arg) = CoreAtom::try_from(arg) => match arg {
                CoreAtom::True => Core::False().into_term_in(pool),
                CoreAtom::False => Core::True().into_term_in(pool),
                CoreAtom::Not(arg) => arg.clone(),
                _ => term.clone(),
            },
            CoreAtom::And(args) => {
                let mut arguments = Vec::with_capacity(args.len());
                for arg in args {
                    if *arg == false {
                        return Core::False().into_term_in(pool);
                    }
                    if *arg != true {
                        arguments.push(arg.clone())
                    }
                }

                if arguments.is_empty() {
                    Core::True().into_term_in(pool)
                } else if arguments.len() == 1 {
                    arguments[0].clone()
                } else {
                    Core::and().call(arguments).into_term_in(pool)
                }
            }
            CoreAtom::Or(args) => {
                let mut arguments = Vec::with_capacity(args.len());
                for arg in args {
                    if *arg == true {
                        return Core::True().into_term_in(pool);
                    }
                    if *arg != false {
                        arguments.push(arg.clone())
                    }
                }
                if arguments.is_empty() {
                    Core::False().into_term_in(pool)
                } else if arguments.len() == 1 {
                    arguments[0].clone()
                } else {
                    Core::or().call(arguments).into_term_in(pool)
                }
            }
            CoreAtom::Equals(args) => {
                let arguments: HashSet<_> = args.iter().cloned().collect();
                if arguments.len() == 1 {
                    Core::True().into_term_in(pool)
                } else {
                    Core::equals().call(arguments).into_term_in(pool)
                }
            }
            CoreAtom::Distinct(args) => {
                let arguments: HashSet<_> = args.iter().cloned().collect();
                if arguments.len() < args.len() {
                    Core::False().into_term_in(pool)
                } else {
                    Core::equals().call(arguments).into_term_in(pool)
                }
            }
            CoreAtom::Ite(guard, high, low) => {
                if *guard == true {
                    high.clone()
                } else if *guard == false {
                    low.clone()
                } else if *high == *low {
                    high.clone()
                } else if *high == true && *low == false {
                    guard.clone()
                } else if *high == false && *low == true {
                    Core::not()
                        .call([guard.clone()])
                        .into_term_in(pool)
                        .simplified(pool)
                } else {
                    term.clone()
                }
            }
            _ => term.clone(), // TODO: Boolean constant propagation for implications and xors
        }
    }
}

impl Simplify for Reals {
    fn simplify(&self, term: &Term, pool: &dyn TermPool) -> Term {
        let Ok(atom) = RealsAtom::try_from(term) else {
            return term.to_term_in(pool);
        };

        match atom {
            RealsAtom::Unary_minus(arg) => {
                match RealsAtom::try_from(arg) {
                    // - (- x) = x
                    Ok(RealsAtom::Unary_minus(arg)) => arg.clone(),
                    Ok(RealsAtom::Plus(args)) => {
                        let mut arguments = Vec::with_capacity(args.len());
                        for arg in args {
                            arguments.push(Reals.simplify(
                                &Reals::unary_minus().call([arg.clone()]).into_term_in(pool),
                                pool,
                            ));
                        }
                        Reals::plus().call(arguments).into_term_in(pool)
                    }
                    Ok(RealsAtom::Mult(args)) => {
                        let mut arguments = args.iter().cloned().collect_vec();
                        arguments[0] = Reals::unary_minus()
                            .call([arguments[0].clone()])
                            .into_term_in(pool)
                            .simplified(pool);

                        Reals::mult()
                            .call(arguments)
                            .into_term_in(pool)
                            .simplified(pool)
                    }
                    // - (- 42) = 42
                    _ if let TermKind::Constant(cnst) = arg.kind() => match cnst {
                        Constant::Integer { .. } => {
                            let value = cnst.to_integer().unwrap();
                            if value <= 0 {
                                Constant::from(-value).into_term_in(pool)
                            } else {
                                term.clone()
                            }
                        }
                        Constant::Rational { .. } => {
                            let value = cnst.to_rational();
                            if value <= 0 {
                                Constant::from(-value).into_term_in(pool)
                            } else {
                                term.clone()
                            }
                        }
                    },
                    _ => term.clone(),
                }
            }
            RealsAtom::Minus(args) => {
                // x - y - z = x + (- y) + (- z)
                let mut arguments = Vec::with_capacity(args.len());
                for (i, arg) in args.iter().enumerate() {
                    if i == 0 {
                        arguments.push(arg.clone());
                    } else {
                        arguments.push(Reals.simplify(
                            &Reals::unary_minus().call([arg.clone()]).into_term_in(pool),
                            pool,
                        ))
                    }
                }
                Reals::plus()
                    .call(arguments)
                    .into_term_in(pool)
                    .simplified(pool)
            }
            // collect scaled common factors together
            RealsAtom::Plus(args) => {
                #[allow(clippy::mutable_key_type)]
                let mut factors = HashMap::new();
                let mut arguments = Vec::with_capacity(args.len());
                for arg in args {
                    let (coefficient, factor) = self.coefficient(arg, pool);
                    if let Some(c) = factors.get_mut(&factor) {
                        *c += coefficient;
                    } else {
                        factors.insert(factor, coefficient);
                    }
                }

                for (factor, coefficient) in factors {
                    if coefficient == 1 {
                        if !matches!(factor.kind(), TermKind::Constant(cnst) if cnst.to_rational() == 0)
                        {
                            arguments.push(factor)
                        }
                    } else {
                        let coefficient = Constant::from(coefficient).into_term_in(pool);
                        arguments.push(
                            Reals::mult()
                                .call([factor, coefficient])
                                .into_term_in(pool)
                                .simplified(pool),
                        );
                    }
                }

                let arguments = arguments.into_iter().filter(
                    |arg| !matches!(arg.kind(), TermKind::Constant(cnst) if cnst.to_rational() == 0),
                ).collect_vec();

                if arguments.is_empty() {
                    Constant::from(Rational::from(0)).into_term_in(pool)
                } else if arguments.len() == 1 {
                    arguments[0].clone()
                } else {
                    Reals::plus().call(arguments).into_term_in(pool)
                }
            }
            RealsAtom::Mult(args) => {
                let mut coefficient = Rational::from(1);
                let mut arguments = Vec::with_capacity(args.len());
                for arg in args {
                    if let TermKind::Constant(cnst) = arg.kind() {
                        coefficient *= cnst.to_rational();
                    } else {
                        arguments.push(arg.clone())
                    }
                }
                if coefficient != 1 {
                    arguments.push(Constant::from(coefficient).into_term_in(pool))
                }

                let arguments = arguments.into_iter().filter(
                    |arg| !matches!(arg.kind(), TermKind::Constant(cnst) if cnst.to_rational() == 1),
                ).collect_vec();

                if arguments.is_empty() {
                    Constant::from(Rational::from(1)).into_term_in(pool)
                } else if arguments.len() == 1 {
                    arguments[0].clone()
                } else {
                    Reals::mult().call(arguments).into_term_in(pool)
                }
            }
            // lhs <= rhs ---> lhs - rhs <= 0
            RealsAtom::Le(args) => match args {
                [left, right] => {
                    let lhs = Reals::minus()
                        .call([left.clone(), right.clone()])
                        .into_term_in(pool)
                        .simplified(pool);
                    let zero = Constant::from(Rational::from(0)).into_term_in(pool);
                    Reals::le().call([lhs, zero]).into_term_in(pool)
                }
                _ => term.clone(),
            },
            // lhs < rhs ---> lhs - rhs < 0
            RealsAtom::Lt(args) => match args {
                [left, right] => {
                    let lhs = Reals::minus()
                        .call([left.clone(), right.clone()])
                        .into_term_in(pool)
                        .simplified(pool);
                    let zero = Constant::from(Rational::from(0)).into_term_in(pool);
                    Reals::lt().call([lhs, zero]).into_term_in(pool)
                }
                _ => term.clone(),
            },
            // lhs >= rhs ---> rhs <= lhs
            RealsAtom::Ge(args) => match args {
                [left, right] => Reals.simplify(
                    &Reals::le()
                        .call([right.clone(), left.clone()])
                        .into_term_in(pool),
                    pool,
                ),
                _ => term.clone(),
            },
            // lhs > rhs ---> rhs < lhs
            RealsAtom::Gt(args) => match args {
                [left, right] => Reals.simplify(
                    &Reals::lt()
                        .call([right.clone(), left.clone()])
                        .into_term_in(pool),
                    pool,
                ),
                _ => term.clone(),
            },
            RealsAtom::Div(_) => term.clone(),
        }
    }
}

impl Reals {
    // this assumes there's a single constant factor in a multiplication because earlier
    // simplification recursive pass has collapsed multiple constant factors together already.
    fn coefficient(&self, term: &Term, pool: &dyn TermPool) -> (Rational, Term) {
        let Ok(RealsAtom::Mult(args)) = RealsAtom::try_from(term) else {
            return (Rational::from(1), term.clone());
        };

        let mut coefficient = None;
        let mut arguments = Vec::with_capacity(args.len());
        for arg in args {
            if let TermKind::Constant(cnst) = arg.kind() {
                coefficient = Some(cnst.to_rational());
            } else {
                arguments.push(arg.clone());
            }
        }

        (
            coefficient.unwrap_or(Rational::from(1)),
            Reals::mult()
                .call(arguments)
                .into_term_in(pool)
                .simplified(pool),
        )
    }
}
