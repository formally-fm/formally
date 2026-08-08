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

//! The Z3 backend.

#![allow(clippy::type_complexity)]

mod bindings;

use bindings as z3;

use crate::formally;
use formally::{
    smt::{backend::*, logics::*, theories::SortConstructor},
    support::{Context, Contextual},
};

use itertools::Itertools;
use std::{collections::HashMap, iter::zip, rc::Rc, sync::LazyLock};
use z3_sys::AstKind;

/// The Z3 backend.
///
/// This backend is based on the C API of [Z3](https://github.com/Z3Prover/z3) from Microsoft
/// Research, accessed via the [z3_sys] crate.
#[derive(Clone, Copy, Default)]
pub struct Z3;

#[derive(Contextual)]
struct Z3Instance {
    context: Context,
    logic: &'static dyn Logic,
    z3context: Rc<z3::Context>,
    z3solver: z3::Solver,
    functions: HashMap<Declared, z3::FuncDecl>,
    sorts: HashMap<Declared, z3::Sort>,
    result: Option<bool>,
}

struct Model<'z> {
    backend: &'z Z3Instance,
}

logic! {
    name: Z3ALL,
    theories: [ theories::Core, theories::Reals_Ints, theories::Arrays ],
    requirements: [ ]
}

impl Backend for Z3 {
    fn name(&self) -> &str {
        "Z3"
    }

    fn solver(&self, config: &Config) -> Result<Box<dyn Solver>, BackendError> {
        Ok(Box::new(Z3Instance::new(config)?))
    }
}

impl Z3Instance {
    pub fn new(config: &Config) -> Result<Z3Instance, BackendError> {
        let z3config = z3::Config::new();
        if config.produce_models {
            z3config.set_param_value(c"model", c"true");
        }

        let z3context = z3::Context::new(&z3config);

        let z3solver;
        let logic: &dyn Logic;
        match &config.logic {
            Some(name) => match standard_logic(name, &Z3ALL) {
                Some(found) => {
                    z3solver = z3::Solver::new_for_logic(z3context.clone(), name);
                    logic = found;
                }
                None => {
                    return Err(BackendError {
                        kind: Box::new(BackendErrorKind::UnsupportedLogic(
                            name.clone().into_owned(),
                        )),
                        context: config.context(),
                        backend: "Z3".to_string(),
                    });
                }
            },
            None => {
                z3solver = z3::Solver::new(z3context.clone());
                logic = &Z3ALL;
            }
        }

        Ok(Z3Instance {
            context: config.context(),
            logic,
            z3context,
            z3solver,
            functions: HashMap::new(),
            sorts: HashMap::new(),
            result: None,
        })
    }
}

impl Solver for Z3Instance {
    fn backend(&self) -> &dyn Backend {
        &Z3
    }

    fn logic(&self) -> &dyn Logic {
        self.logic
    }

    fn declare(&mut self, decl: Declared) -> Result<(), BackendError> {
        let mut sorts = Vec::new();
        for sort in &decl.domain {
            sorts.push(self.sort(sort)?);
        }

        if Sort::equal(&decl.range, &Sort::sort()) {
            let z3sort = self.z3context.mk_uninterpreted_sort(&decl.name);
            self.sorts.insert(decl.clone(), z3sort);
        } else {
            let range = self.sort(&decl.range)?;
            let func = self.z3context.mk_func_decl(&decl.name, &sorts, &range);
            self.functions.insert(decl.clone(), func.clone());
        }

        Ok(())
    }

    fn define(&mut self, _def: Defined) -> Result<(), BackendError> {
        Ok(())
    }

    fn require(&mut self, term: &Term) -> Result<(), BackendError> {
        let term = self.term_to_z3(&rpds::HashTrieMap::new(), term)?;

        self.z3solver.assert(&term);

        Ok(())
    }

    fn push(&mut self) -> Result<(), BackendError> {
        self.z3solver.push();
        Ok(())
    }

    fn pop_n(&mut self, n: usize) -> Result<(), BackendError> {
        self.z3solver.pop(n);
        Ok(())
    }

    fn check(&mut self) -> Result<Option<bool>, BackendError> {
        self.result = match self.z3solver.check() {
            z3::Z3_L_FALSE => Some(false),
            z3::Z3_L_TRUE => Some(true),
            _ => None,
        };

        Ok(self.result)
    }

    fn model(&self) -> Result<Option<Box<dyn '_ + ModelProvider>>, BackendError> {
        match self.result {
            Some(true) => Ok(Some(Box::new(Model { backend: self }))),
            _ => Ok(None),
        }
    }
}

impl ModelProvider for Model<'_> {
    fn value(&self, decl: &Declared) -> Option<ModelValue> {
        let func = self.backend.functions.get(decl)?;
        let ast = self.backend.z3solver.get_model()?.get_const_interp(func)?;

        self.backend.z3_to_value(&ast)
    }
}

enum Z3SortArgument {
    Value(z3::Ast),
    Sort(z3::Sort),
}

impl Z3SortArgument {
    pub fn as_sort(&self) -> Option<&z3::Sort> {
        match self {
            Z3SortArgument::Value(_) => None,
            Z3SortArgument::Sort(sort) => Some(sort),
        }
    }

    #[expect(unused)]
    pub fn as_value(&self) -> Option<&z3::Ast> {
        match self {
            Z3SortArgument::Value(value) => Some(value),
            Z3SortArgument::Sort(_) => None,
        }
    }
}

static THEORY_SORTS: LazyLock<
    HashMap<Function, fn(&z3::Context, &[Z3SortArgument]) -> Option<z3::Sort>>,
> = LazyLock::new(|| {
    let mut map: HashMap<Function, fn(&z3::Context, &[Z3SortArgument]) -> Option<z3::Sort>> =
        HashMap::new();

    map.insert(theories::Core::Bool.to_constructor(), |ctx, _| {
        Some(ctx.mk_bool_sort())
    });
    map.insert(theories::Ints::Int.to_constructor(), |ctx, _| {
        Some(ctx.mk_int_sort())
    });
    map.insert(theories::Reals::Real.to_constructor(), |ctx, _| {
        Some(ctx.mk_real_sort())
    });
    map.insert(
        theories::Arrays::Array.to_constructor(),
        |ctx, args| match args {
            [index, value] => {
                Some(ctx.mk_array_sort(&[index.as_sort()?.clone()], value.as_sort()?))
            }
            _ => None,
        },
    );

    map
});

static THEORY_FUNCS: LazyLock<HashMap<Primitive, fn(&z3::Context, &[z3::Ast]) -> Option<z3::Ast>>> =
    LazyLock::new(|| {
        let mut map: HashMap<Primitive, fn(&z3::Context, &[z3::Ast]) -> Option<z3::Ast>> =
            HashMap::new();

        map.insert(theories::Core::True(), |ctx, _| Some(ctx.mk_true()));
        map.insert(theories::Core::False(), |ctx, _| Some(ctx.mk_false()));
        map.insert(theories::Core::not(), |ctx, args| match args {
            [arg] => Some(ctx.mk_not(arg)),
            _ => None,
        });
        map.insert(theories::Core::implies(), |ctx, args| match args {
            [_, _, ..] => {
                let mut result = ctx.mk_implies(&args[args.len() - 2], &args[args.len() - 1]);
                for i in (0..args.len() - 2).rev() {
                    result = ctx.mk_implies(&args[i], &result)
                }
                Some(result)
            }
            _ => None,
        });
        map.insert(theories::Core::and(), |ctx, args| Some(ctx.mk_and(args)));
        map.insert(theories::Core::or(), |ctx, args| Some(ctx.mk_or(args)));
        map.insert(theories::Core::xor(), |ctx, args| match args {
            [left, right] => Some(ctx.mk_xor(left, right)),
            _ => None,
        });
        map.insert(theories::Core::equals(), |ctx, args| {
            let mut partials = Vec::new();
            for i in 0..args.len() - 1 {
                partials.push(ctx.mk_eq(&args[i], &args[i + 1]));
            }
            Some(ctx.mk_and(&partials))
        });
        map.insert(theories::Core::distinct(), |ctx, args| {
            Some(ctx.mk_distinct(args))
        });
        map.insert(theories::Core::ite(), |ctx, args| match args {
            [cond, then, else_] => Some(ctx.mk_ite(cond, then, else_)),
            _ => None,
        });

        map.insert(theories::Ints::unary_minus(), |ctx, args| match args {
            [arg] => Some(ctx.mk_unary_minus(arg)),
            _ => None,
        });
        map.insert(theories::Ints::minus(), |ctx, args| Some(ctx.mk_sub(args)));
        map.insert(theories::Ints::plus(), |ctx, args| Some(ctx.mk_add(args)));
        map.insert(theories::Ints::mult(), |ctx, args| Some(ctx.mk_mul(args)));
        map.insert(theories::Ints::div(), |ctx, args| match args {
            [left, right] => Some(ctx.mk_div(left, right)),
            _ => None,
        });
        map.insert(theories::Ints::mod_(), |ctx, args| match args {
            [left, right] => Some(ctx.mk_mod(left, right)),
            _ => None,
        });
        map.insert(theories::Ints::abs(), |ctx, args| match args {
            [arg] => Some(ctx.mk_ite(
                &ctx.mk_ge(arg, &ctx.mk_int(0)),
                arg,
                &ctx.mk_unary_minus(arg),
            )),
            _ => None,
        });
        map.insert(theories::Ints::le(), |ctx, args| {
            let mut partials = Vec::new();
            for i in 0..args.len() - 1 {
                partials.push(ctx.mk_le(&args[i], &args[i + 1]));
            }
            Some(ctx.mk_and(&partials))
        });
        map.insert(theories::Ints::lt(), |ctx, args| {
            let mut partials = Vec::new();
            for i in 0..args.len() - 1 {
                partials.push(ctx.mk_lt(&args[i], &args[i + 1]));
            }
            Some(ctx.mk_and(&partials))
        });
        map.insert(theories::Ints::ge(), |ctx, args| {
            let mut partials = Vec::new();
            for i in 0..args.len() - 1 {
                partials.push(ctx.mk_ge(&args[i], &args[i + 1]));
            }
            Some(ctx.mk_and(&partials))
        });
        map.insert(theories::Ints::gt(), |ctx, args| {
            let mut partials = Vec::new();
            for i in 0..args.len() - 1 {
                partials.push(ctx.mk_gt(&args[i], &args[i + 1]));
            }
            Some(ctx.mk_and(&partials))
        });
        map.insert(theories::Arrays::select(), |ctx, args| match args {
            [array, index] => Some(ctx.mk_select_n(array, std::slice::from_ref(index))),
            _ => None,
        });
        map.insert(theories::Arrays::store(), |ctx, args| match args {
            [array, index, value] => {
                Some(ctx.mk_store_n(array, std::slice::from_ref(index), value))
            }
            _ => None,
        });

        map
    });

impl Z3Instance {
    fn theory_sort(
        &mut self,
        ctor: &Function,
        args: &[Z3SortArgument],
    ) -> Result<Option<z3::Sort>, BackendError> {
        Ok(THEORY_SORTS
            .get(ctor)
            .and_then(|f| f(&self.z3context, args)))
    }

    fn theory_atom(&self, func: &Primitive, args: &[z3::Ast]) -> Option<z3::Ast> {
        THEORY_FUNCS
            .get(&func.clone())
            .and_then(|f| f(&self.z3context, args))
    }

    fn sort(&mut self, sort: &Sort) -> Result<z3::Sort, BackendError> {
        match &sort.head {
            Function::Parameter(_) => todo!(),
            Function::Primitive(_) => {
                let mut args = Vec::new();
                for arg in &sort.arguments {
                    match arg {
                        SortArgument::Value(value) => {
                            args.push(Z3SortArgument::Value(self.constant_to_z3(value)?));
                        }
                        SortArgument::Sort(sort) => {
                            args.push(Z3SortArgument::Sort(self.sort(sort)?));
                        }
                    }
                }

                if let Some(z3sort) = self.theory_sort(&sort.head, &args)? {
                    Ok(z3sort.clone())
                } else {
                    Err(BackendError::new(
                        self,
                        BackendErrorKind::ViolatedPrecondition(format!(
                            "unknown primitive symbol or mismatching arguments: `{}`",
                            sort
                        )),
                    ))
                }
            }
            Function::User(UserFunction::Declared(decl)) => {
                if !sort.arguments.is_empty() {
                    todo!()
                }
                self.sorts.get(decl).cloned().ok_or_else(|| {
                    BackendError::new(
                        self,
                        BackendErrorKind::ViolatedPrecondition(format!(
                            "use of unadopted sort declaration: `{}`",
                            decl.name
                        )),
                    )
                })
            }
            Function::User(UserFunction::Defined(_)) => todo!(),
        }
    }

    fn atom_to_z3(
        &mut self,
        argset: &rpds::HashTrieMap<Parameter, Term>,
        atom: &Atom,
    ) -> Result<z3::Ast, BackendError> {
        match atom {
            Atom::Bound(BoundAtom {
                head, arguments, ..
            }) => match &head.function {
                Function::Parameter(param) => {
                    if let Some(arg) = argset.get(param) {
                        self.term_to_z3(argset, arg)
                    } else {
                        Err(BackendError::new(
                            self,
                            BackendErrorKind::ViolatedPrecondition(format!(
                                "unbound parameter in term: `{}`",
                                param.name()
                            )),
                        ))
                    }
                }
                Function::Primitive(primitive) => {
                    let args = arguments
                        .iter()
                        .map(|arg| self.term_to_z3(argset, arg))
                        .process_results(|c| c.collect_vec())?;

                    self.theory_atom(primitive, &args).ok_or_else(|| {
                        BackendError::new(
                            self,
                            BackendErrorKind::ViolatedPrecondition(format!(
                                "unknown primitive symbol or mismatching arguments: `{}`",
                                head.function.name()
                            )),
                        )
                    })
                }
                Function::User(UserFunction::Declared(decl)) => {
                    let args = arguments
                        .iter()
                        .map(|arg| self.term_to_z3(argset, arg))
                        .process_results(|c| c.collect_vec())?;

                    let func = self.functions.get(decl).ok_or_else(|| {
                        BackendError::new(
                            self,
                            BackendErrorKind::ViolatedPrecondition(format!(
                                "use of unadopted function declaration: `{}`",
                                decl.name
                            )),
                        )
                    })?;

                    Ok(self.z3context.mk_app(func, &args))
                }
                Function::User(UserFunction::Defined(def)) => {
                    let mut argset = argset.clone();
                    for (param, arg) in zip(def.domain.iter(), arguments.iter()) {
                        argset.insert_mut(param.clone(), arg.clone())
                    }

                    self.term_to_z3(&argset, &def.body)
                }
            },
            Atom::Unbound(UnboundAtom { head, .. }) => Err(BackendError::new(
                self,
                BackendErrorKind::ViolatedPrecondition(format!(
                    "unbound variable in term: `{head}`"
                )),
            )),
        }
    }

    fn term_to_z3(
        &mut self,
        argset: &rpds::HashTrieMap<Parameter, Term>,
        term: &Term,
    ) -> Result<z3::Ast, BackendError> {
        match term.kind() {
            TermKind::Constant(cnst) => self.constant_to_z3(cnst),
            TermKind::Atom(atom) => self.atom_to_z3(argset, atom),
        }
    }

    fn constant_to_z3(&self, cnst: &Constant) -> Result<z3::Ast, BackendError> {
        match cnst {
            Constant::Integer { value, .. } => {
                Ok(self.z3context.mk_numeral(&value.to_string_radix(10)))
            }
            Constant::Rational { value, .. } => {
                Ok(self.z3context.mk_numeral(&value.to_string_radix(10)))
            }
        }
    }

    fn z3_to_value(&self, ast: &z3::Ast) -> Option<ModelValue> {
        match self.z3context.get_bool_value(ast) {
            z3::Z3_L_FALSE => {
                return Some(ModelValue::from(false));
            }
            z3::Z3_L_TRUE => {
                return Some(ModelValue::from(true));
            }
            _ => {}
        }

        if ast.kind() != AstKind::Numeral {
            return None;
        }

        let string = ast.get_numeral_string();

        match rug::Integer::from_str_radix(&string, 10) {
            Ok(int) => Some(ModelValue::from(Constant::from(int))),
            Err(_) => match rug::Rational::from_str_radix(&string, 10) {
                Ok(rat) => Some(ModelValue::from(Constant::from(rat))),
                Err(_) => None,
            },
        }
    }
}
