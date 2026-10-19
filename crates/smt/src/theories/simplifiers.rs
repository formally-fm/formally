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

use formally::smt::theories::*;

use std::collections::HashSet;

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
                } else if *low == true {
                    Core::implies()
                        .call([guard.clone(), high.clone()])
                        .into_term_in(pool)
                        .simplified(pool)
                } else if *low == false {
                    Core::and()
                        .call([guard.clone(), high.clone()])
                        .into_term_in(pool)
                        .simplified(pool)
                } else if *high == true {
                    Core::or()
                        .call([guard.clone(), low.clone()])
                        .into_term_in(pool)
                        .simplified(pool)
                } else if *high == false {
                    Core::and()
                        .call([
                            Core::not().call([guard.clone()]).into_term_in(pool),
                            low.clone(),
                        ])
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
