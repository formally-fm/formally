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
use formally::smt::{
    self,
    backend::{
        self, Backend as _,
        z3::{Z3, Z3ALL, bindings as z3},
    },
    logics::LogicEx,
    theories::TheoryEx as _,
};

use itertools::*;

use crate::backend::z3::Z3ALLAtom;
use crate::theories::{ArraysAtom, CoreAtom, IntsAtom, Reals_IntsAtom, RealsAtom};
use std::{collections::HashMap, rc::Rc};

type Result<T, E = backend::Error> = std::result::Result<T, E>;

pub struct Z3Manager {
    z3context: Rc<z3::Context>,
    functions: HashMap<smt::Declared, z3::FuncDecl>,
    sorts: HashMap<smt::Declared, z3::Sort>,
    terms: HashMap<smt::Term, z3::Ast>,
}

impl backend::Term for z3::Ast {}

impl Z3Manager {
    pub fn new() -> Z3Manager {
        Z3Manager {
            z3context: z3::Context::new(&z3::Config::new()),
            functions: HashMap::new(),
            sorts: HashMap::new(),
            terms: HashMap::new(),
        }
    }
}

impl Default for Z3Manager {
    fn default() -> Self {
        Z3Manager::new()
    }
}

impl backend::Manager for Z3Manager {
    fn backend(&self) -> &dyn backend::Backend {
        &Z3
    }

    fn import(&self, term: &smt::Term) -> Result<&dyn backend::Term> {
        todo!()
    }

    fn export(&self, term: &dyn backend::Term, pool: &smt::TermPool) -> Result<smt::Term> {
        todo!()
    }
}

type ArgMap = rpds::HashTrieMap<smt::Parameter, smt::Term>;

impl Z3Manager {
    fn term_to_z3(&self, argmap: &ArgMap, term: &smt::Term) -> Result<z3::Ast> {
        match term.kind() {
            smt::TermKind::Constant(cnst) => self.constant_to_z3(cnst),
            smt::TermKind::Atom(atom) => self.atom_to_z3(argmap, atom),
        }
    }

    fn terms_to_z3(&self, argmap: &ArgMap, terms: &[smt::Term]) -> Result<Vec<z3::Ast>> {
        terms
            .iter()
            .map(|arg| self.term_to_z3(argmap, arg))
            .process_results(|c| c.collect_vec())
    }

    fn constant_to_z3(&self, cnst: &smt::Constant) -> Result<z3::Ast> {
        match cnst {
            smt::Constant::Integer { value, .. } => {
                Ok(self.z3context.mk_numeral(&value.to_string_radix(10)))
            }
            smt::Constant::Rational { value, .. } => {
                Ok(self.z3context.mk_numeral(&value.to_string_radix(10)))
            }
        }
    }

    fn atom_to_z3(&self, argmap: &ArgMap, atom: &smt::Atom) -> Result<z3::Ast> {
        match atom {
            smt::Atom::Bound(atom) => match &atom.head.function {
                smt::Function::Parameter(param) => self.param_to_z3(argmap, param),
                smt::Function::Primitive(prim) => self.prim_to_z3(argmap, atom),
                smt::Function::User(user) => self.userfunc_to_z3(argmap, user, &atom.arguments),
            },
            smt::Atom::Unbound(smt::UnboundAtom { head, .. }) => Err(backend::Error::new(
                Z3.name(),
                backend::ErrorKind::ViolatedPrecondition(format!(
                    "unbound variable in term: `{head}`"
                )),
            )),
        }
    }

    fn param_to_z3(&self, argmap: &ArgMap, param: &smt::Parameter) -> Result<z3::Ast> {
        match argmap.get(param) {
            Some(arg) => self.term_to_z3(argmap, arg),
            None => Err(backend::Error::new(
                Z3.name(),
                backend::ErrorKind::ViolatedPrecondition(format!(
                    "unbound parameter in term: `{}`",
                    param.name()
                )),
            )),
        }
    }

    fn prim_to_z3(&self, argmap: &ArgMap, atom: &smt::BoundAtom) -> Result<z3::Ast> {
        match Z3ALLAtom::try_from(atom) {
            Ok(atom) => self.z3atom_to_z3(argmap, &atom),
            Err(_) => Err(backend::Error::new(
                Z3.name(),
                backend::ErrorKind::ViolatedPrecondition(format!(
                    "unknown primitive symbol or mismatching arguments: `{}`",
                    atom.head.function.name()
                )),
            )),
        }
    }

    fn z3atom_to_z3(&self, argmap: &ArgMap, atom: &Z3ALLAtom) -> Result<z3::Ast> {
        match atom {
            Z3ALLAtom::Core(atom) => self.core_atom_to_z3(argmap, atom),
            Z3ALLAtom::Ints(atom) => self.ints_atom_to_z3(argmap, atom),
            Z3ALLAtom::Reals(atom) => self.reals_atom_to_z3(argmap, atom),
            Z3ALLAtom::Reals_Ints(atom) => self.reals_int_atom_to_z3(argmap, atom),
            Z3ALLAtom::Arrays(atom) => self.arrays_atom_to_z3(argmap, atom),
        }
    }

    fn core_atom_to_z3(&self, argmap: &ArgMap, atom: &CoreAtom) -> Result<z3::Ast> {
        Ok(match atom {
            CoreAtom::True => self.z3context.mk_true(),
            CoreAtom::False => self.z3context.mk_false(),
            CoreAtom::Not(arg) => self.z3context.mk_not(&self.term_to_z3(argmap, arg)?),
            CoreAtom::Implies(args) => {
                let args = self.terms_to_z3(argmap, args)?;

                let mut result = self
                    .z3context
                    .mk_implies(&args[args.len() - 2], &args[args.len() - 1]);
                for i in (0..args.len() - 2).rev() {
                    result = self.z3context.mk_implies(&args[i], &result)
                }

                result
            }
            CoreAtom::And(args) => {
                let args = self.terms_to_z3(argmap, args)?;
                self.z3context.mk_and(&args)
            }
            CoreAtom::Or(args) => {
                let args = self.terms_to_z3(argmap, args)?;
                self.z3context.mk_or(&args)
            }
            CoreAtom::Xor(args) => {
                let args = self.terms_to_z3(argmap, args)?;

                let mut result = self.z3context.mk_implies(&args[0], &args[1]);
                for i in 2..args.len() {
                    result = self.z3context.mk_xor(&result, &args[i])
                }

                result
            }
            CoreAtom::Equals(args) => {
                let args = self.terms_to_z3(argmap, args)?;

                let mut partials = Vec::new();
                for i in 0..args.len() - 1 {
                    partials.push(self.z3context.mk_eq(&args[i], &args[i + 1]));
                }
                self.z3context.mk_and(&partials)
            }
            CoreAtom::Distinct(args) => {
                let args = self.terms_to_z3(argmap, args)?;
                self.z3context.mk_distinct(&args)
            }
            CoreAtom::Ite(cond, then, else_) => {
                let cond = self.term_to_z3(argmap, cond)?;
                let then = self.term_to_z3(argmap, then)?;
                let else_ = self.term_to_z3(argmap, else_)?;

                self.z3context.mk_ite(&cond, &then, &else_)
            }
        })
    }

    fn ints_atom_to_z3(&self, argmap: &ArgMap, atom: &IntsAtom) -> Result<z3::Ast> {
        match atom {
            IntsAtom::Unary_minus(_) => todo!(),
            IntsAtom::Minus(_) => todo!(),
            IntsAtom::Plus(_) => todo!(),
            IntsAtom::Mult(_) => todo!(),
            IntsAtom::Div(_) => todo!(),
            IntsAtom::Mod_(_, _) => todo!(),
            IntsAtom::Abs(_, _) => todo!(),
            IntsAtom::Le(_) => todo!(),
            IntsAtom::Lt(_) => todo!(),
            IntsAtom::Ge(_) => todo!(),
            IntsAtom::Gt(_) => todo!(),
        }
    }

    fn reals_atom_to_z3(&self, argmap: &ArgMap, atom: &RealsAtom) -> Result<z3::Ast> {
        match atom {
            RealsAtom::Unary_minus(_) => todo!(),
            RealsAtom::Minus(_) => todo!(),
            RealsAtom::Plus(_) => todo!(),
            RealsAtom::Mult(_) => todo!(),
            RealsAtom::Div(_) => todo!(),
            RealsAtom::Le(_) => todo!(),
            RealsAtom::Lt(_) => todo!(),
            RealsAtom::Ge(_) => todo!(),
            RealsAtom::Gt(_) => todo!(),
        }
    }

    fn reals_int_atom_to_z3(&self, argmap: &ArgMap, atom: &Reals_IntsAtom) -> Result<z3::Ast> {
        match atom {
            Reals_IntsAtom::To_real(_) => todo!(),
            Reals_IntsAtom::To_int(_) => todo!(),
            Reals_IntsAtom::Is_int(_) => todo!(),
        }
    }

    fn arrays_atom_to_z3(&self, argmap: &ArgMap, atom: &ArraysAtom) -> Result<z3::Ast> {
        match atom {
            ArraysAtom::Select(_, _) => todo!(),
            ArraysAtom::Store(_, _, _) => todo!(),
        }
    }

    fn userfunc_to_z3(
        &self,
        argmap: &ArgMap,
        user: &smt::UserFunction,
        arguments: &[smt::Term],
    ) -> Result<z3::Ast> {
        match user {
            smt::UserFunction::Declared(decl) => self.declared_to_z3(argmap, decl, arguments),
            smt::UserFunction::Defined(def) => self.defined_to_z3(argmap, def, arguments),
        }
    }

    fn declared_to_z3(
        &self,
        argmap: &ArgMap,
        decl: &smt::Declared,
        arguments: &[smt::Term],
    ) -> Result<z3::Ast> {
        let args = arguments
            .iter()
            .map(|arg| self.term_to_z3(argmap, arg))
            .process_results(|c| c.collect_vec())?;

        let func = self.functions.get(decl).ok_or_else(|| {
            backend::Error::new(
                Z3.name(),
                backend::ErrorKind::ViolatedPrecondition(format!(
                    "use of unadopted function declaration: `{}`",
                    decl.name
                )),
            )
        })?;

        Ok(self.z3context.mk_app(func, &args))
    }

    fn defined_to_z3(
        &self,
        argmap: &ArgMap,
        def: &smt::Defined,
        arguments: &[smt::Term],
    ) -> Result<z3::Ast> {
        let mut argmap = argmap.clone();
        for (param, arg) in std::iter::zip(def.domain.iter(), arguments.iter()) {
            argmap.insert_mut(param.clone(), arg.clone())
        }

        self.term_to_z3(&argmap, &def.body)
    }
}
