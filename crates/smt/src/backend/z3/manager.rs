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
        z3::{Z3, Z3ALLAtom, Z3ALLSort, bindings as z3},
    },
    theories::{
        ArraysAtom, ArraysSort, CoreAtom, CoreSort, IntsAtom, IntsSort, Reals_IntsAtom, RealsAtom,
        RealsSort,
    },
};

use itertools::*;

use std::{cell::RefCell, collections::HashMap, rc::Rc};

type Result<T, E = backend::Error> = std::result::Result<T, E>;

pub struct Z3Manager {
    pub z3context: Rc<z3::Context>,
    decls: RefCell<HashMap<smt::Declared, z3::FuncDecl>>,
    defs: RefCell<HashMap<smt::Defined, z3::FuncDecl>>,
    sorts: RefCell<HashMap<smt::Declared, z3::Sort>>,
    terms: RefCell<HashMap<smt::Term, z3::Ast>>,
    bindings: RefCell<HashMap<smt::Binding, z3::Ast>>,
}

impl Z3Manager {
    pub fn new() -> Z3Manager {
        Z3Manager {
            z3context: z3::Context::new(&z3::Config::new()),
            decls: RefCell::default(),
            defs: RefCell::default(),
            sorts: RefCell::default(),
            terms: RefCell::default(),
            bindings: RefCell::default(),
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
}

impl Z3Manager {
    pub fn sort_to_z3(&self, sort: &smt::Sort) -> Result<z3::Sort> {
        match Z3ALLSort::try_from(sort) {
            Ok(sort) => self.z3sort_to_z3(sort),
            Err(_) => Err(backend::Error::new(
                Z3.name(),
                backend::ErrorKind::ViolatedPrecondition(format!(
                    "unknown primitive sort or mismatching arguments: `{}`",
                    sort.head.name()
                )),
            )),
        }
    }

    pub fn term_to_z3(&self, term: &smt::Term) -> Result<z3::Ast> {
        if let Some(ast) = self.terms.borrow().get(term) {
            return Ok(ast.clone());
        }

        let ast = match term.kind() {
            smt::TermKind::Constant(cnst) => self.constant_to_z3(cnst)?,
            smt::TermKind::Atom(atom) => self.atom_to_z3(atom)?,
        };

        self.terms.borrow_mut().insert(term.clone(), ast.clone());

        Ok(ast)
    }

    pub fn declare(&self, decl: smt::Declared) -> Result<()> {
        if smt::Sort::equal(&decl.range, &smt::Sort::sort()) {
            self.declare_sort(decl)
        } else {
            self.declare_fun(decl)
        }
    }

    fn declare_sort(&self, decl: smt::Declared) -> Result<()> {
        if self.sorts.borrow().contains_key(&decl) {
            return Ok(());
        }

        let sort = if decl.domain.is_empty() {
            self.z3context.mk_uninterpreted_sort(decl.name.name())
        } else {
            todo!()
        };

        self.sorts.borrow_mut().insert(decl, sort);

        Ok(())
    }

    fn declare_fun(&self, decl: smt::Declared) -> Result<()> {
        if self.decls.borrow().contains_key(&decl) {
            return Ok(());
        }

        let range = self.sort_to_z3(&decl.range)?;
        let mut sorts = Vec::new();
        for sort in &decl.domain {
            sorts.push(self.sort_to_z3(sort)?);
        }

        let z3decl = self
            .z3context
            .mk_func_decl(decl.name.name(), &sorts, &range);

        self.decls.borrow_mut().insert(decl, z3decl);

        Ok(())
    }

    pub fn define(&self, _def: smt::Defined) -> Result<()> {
        todo!()
    }

    fn terms_to_z3(&self, terms: &[smt::Term]) -> Result<Vec<z3::Ast>> {
        terms
            .iter()
            .map(|arg| self.term_to_z3(arg))
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

    fn atom_to_z3(&self, atom: &smt::Atom) -> Result<z3::Ast> {
        match atom {
            smt::Atom::Bound(atom) => match &atom.head.function {
                smt::Function::Binding(bind) => self.binding_to_z3(bind),
                smt::Function::Primitive(_) => self.prim_to_z3(atom),
                smt::Function::User(user) => self.userfunc_to_z3(user, &atom.arguments),
            },
            smt::Atom::Unbound(smt::UnboundAtom { head, .. }) => Err(backend::Error::new(
                Z3.name(),
                backend::ErrorKind::ViolatedPrecondition(format!(
                    "unbound variable in term: `{head}`"
                )),
            )),
        }
    }

    fn binding_to_z3(&self, binding: &smt::Binding) -> Result<z3::Ast> {
        if let Some(ast) = self.bindings.borrow().get(binding) {
            return Ok(ast.clone());
        }

        let ast = self
            .z3context
            .mk_const(binding.name().name(), self.sort_to_z3(binding.sort())?);

        self.bindings
            .borrow_mut()
            .insert(binding.clone(), ast.clone());

        Ok(ast)
    }

    fn prim_to_z3(&self, atom: &smt::BoundAtom) -> Result<z3::Ast> {
        match Z3ALLAtom::try_from(atom) {
            Ok(atom) => self.z3atom_to_z3(&atom),
            Err(_) => Err(backend::Error::new(
                Z3.name(),
                backend::ErrorKind::ViolatedPrecondition(format!(
                    "unknown primitive symbol or mismatching arguments: `{}`",
                    atom.head.function.name()
                )),
            )),
        }
    }

    fn userfunc_to_z3(&self, user: &smt::UserFunction, arguments: &[smt::Term]) -> Result<z3::Ast> {
        match user {
            smt::UserFunction::Declared(decl) => self.declared_to_z3(decl, arguments),
            smt::UserFunction::Defined(def) => self.defined_to_z3(def, arguments),
        }
    }

    fn declared_to_z3(&self, decl: &smt::Declared, arguments: &[smt::Term]) -> Result<z3::Ast> {
        let args = arguments
            .iter()
            .map(|arg| self.term_to_z3(arg))
            .process_results(|c| c.collect_vec())?;

        if let Some(func) = self.decls.borrow().get(decl) {
            return Ok(self.z3context.mk_app(func, &args));
        }

        Err(backend::Error::new(
            Z3.name(),
            backend::ErrorKind::ViolatedPrecondition(format!(
                "use of unknown function declaration: `{}`",
                decl.name
            )),
        ))
    }

    fn defined_to_z3(&self, def: &smt::Defined, arguments: &[smt::Term]) -> Result<z3::Ast> {
        let args = arguments
            .iter()
            .map(|arg| self.term_to_z3(arg))
            .process_results(|c| c.collect_vec())?;

        if let Some(func) = self.defs.borrow().get(def) {
            return Ok(self.z3context.mk_app(func, &args));
        }

        Err(backend::Error::new(
            Z3.name(),
            backend::ErrorKind::ViolatedPrecondition(format!(
                "use of unknown function definition: `{}`",
                def.name
            )),
        ))
    }

    fn sort_argument_to_sort<'s>(&self, arg: &'s smt::SortArgument) -> Result<&'s smt::Sort> {
        match arg {
            smt::SortArgument::Sort(sort) => Ok(sort),
            smt::SortArgument::Value(_) => Err(backend::Error::new(
                Z3.name(),
                backend::ErrorKind::ViolatedPrecondition("expected sort, found a value".into()),
            )),
        }
    }

    fn z3sort_to_z3(&self, sort: Z3ALLSort) -> Result<z3::Sort> {
        Ok(match sort {
            Z3ALLSort::Core(sort) => match sort {
                CoreSort::Bool => self.z3context.mk_bool_sort(),
            },
            Z3ALLSort::Ints(sort) => match sort {
                IntsSort::Int => self.z3context.mk_int_sort(),
            },
            Z3ALLSort::Reals(sort) => match sort {
                RealsSort::Real => self.z3context.mk_real_sort(),
            },
            Z3ALLSort::Reals_Ints(_) => unreachable!(),
            Z3ALLSort::Arrays(sort) => match sort {
                ArraysSort::Array(index, range) => {
                    let index = self.sort_to_z3(self.sort_argument_to_sort(index)?)?;
                    let range = self.sort_to_z3(self.sort_argument_to_sort(range)?)?;

                    self.z3context.mk_array_sort(&[index], &range)
                }
            },
        })
    }

    fn z3atom_to_z3(&self, atom: &Z3ALLAtom) -> Result<z3::Ast> {
        match atom {
            Z3ALLAtom::Core(atom) => self.core_atom_to_z3(atom),
            Z3ALLAtom::Ints(atom) => self.ints_atom_to_z3(atom),
            Z3ALLAtom::Reals(atom) => self.reals_atom_to_z3(atom),
            Z3ALLAtom::Reals_Ints(atom) => self.reals_int_atom_to_z3(atom),
            Z3ALLAtom::Arrays(atom) => self.arrays_atom_to_z3(atom),
        }
    }

    fn core_atom_to_z3(&self, atom: &CoreAtom) -> Result<z3::Ast> {
        Ok(match atom {
            CoreAtom::True => self.z3context.mk_true(),
            CoreAtom::False => self.z3context.mk_false(),
            CoreAtom::Not(arg) => self.z3context.mk_not(&self.term_to_z3(arg)?),
            CoreAtom::Implies(args) => {
                let args = self.terms_to_z3(args)?;

                let mut result = self
                    .z3context
                    .mk_implies(&args[args.len() - 2], &args[args.len() - 1]);
                for i in (0..args.len() - 2).rev() {
                    result = self.z3context.mk_implies(&args[i], &result)
                }

                result
            }
            CoreAtom::And(args) => {
                let args = self.terms_to_z3(args)?;
                self.z3context.mk_and(&args)
            }
            CoreAtom::Or(args) => {
                let args = self.terms_to_z3(args)?;
                self.z3context.mk_or(&args)
            }
            CoreAtom::Xor(args) => {
                let args = self.terms_to_z3(args)?;

                let mut result = self.z3context.mk_implies(&args[0], &args[1]);
                for i in 2..args.len() {
                    result = self.z3context.mk_xor(&result, &args[i])
                }

                result
            }
            CoreAtom::Equals(args) => {
                let args = self.terms_to_z3(args)?;

                let mut partials = Vec::new();
                for i in 0..args.len() - 1 {
                    partials.push(self.z3context.mk_eq(&args[i], &args[i + 1]));
                }
                self.z3context.mk_and(&partials)
            }
            CoreAtom::Distinct(args) => {
                let args = self.terms_to_z3(args)?;
                self.z3context.mk_distinct(&args)
            }
            CoreAtom::Ite(cond, then, else_) => {
                let cond = self.term_to_z3(cond)?;
                let then = self.term_to_z3(then)?;
                let else_ = self.term_to_z3(else_)?;

                self.z3context.mk_ite(&cond, &then, &else_)
            }
        })
    }

    fn ints_atom_to_z3(&self, atom: &IntsAtom) -> Result<z3::Ast> {
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

    fn reals_atom_to_z3(&self, atom: &RealsAtom) -> Result<z3::Ast> {
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

    fn reals_int_atom_to_z3(&self, atom: &Reals_IntsAtom) -> Result<z3::Ast> {
        match atom {
            Reals_IntsAtom::To_real(_) => todo!(),
            Reals_IntsAtom::To_int(_) => todo!(),
            Reals_IntsAtom::Is_int(_) => todo!(),
        }
    }

    fn arrays_atom_to_z3(&self, atom: &ArraysAtom) -> Result<z3::Ast> {
        match atom {
            ArraysAtom::Select(_, _) => todo!(),
            ArraysAtom::Store(_, _, _) => todo!(),
        }
    }
}
