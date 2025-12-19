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

use z3_sys::*;

use itertools::Itertools;
use std::{
    ffi::*,
    hash::{Hash, Hasher},
    rc::{Rc, Weak},
};

pub use z3_sys::Z3_L_FALSE;
pub use z3_sys::Z3_L_TRUE;

pub use z3_sys::AstKind;

#[repr(transparent)]
pub struct Config {
    pub config: Z3_config,
}

pub struct Context {
    pub this: Weak<Context>,
    pub ctx: Z3_context,
}

pub struct Solver {
    pub ctx: Rc<Context>,
    pub slv: Z3_solver,
    pub model: Option<Z3_model>,
}

pub struct Ast {
    pub ctx: Rc<Context>,
    pub ast: Z3_ast,
}

pub struct FuncDecl {
    pub ctx: Rc<Context>,
    pub decl: Z3_func_decl,
}

pub struct Sort {
    pub ctx: Rc<Context>,
    pub sort: Z3_sort,
}

pub struct Model {
    pub ctx: Rc<Context>,
    pub model: Z3_model,
}

impl Config {
    pub fn new() -> Config {
        Config {
            config: unsafe { Z3_mk_config().unwrap() },
        }
    }

    pub fn set_param_value(&self, param: &CStr, value: &CStr) {
        unsafe { Z3_set_param_value(self.config, param.as_ptr(), value.as_ptr()) }
    }
}

impl Default for Config {
    fn default() -> Self {
        Config::new()
    }
}

impl Drop for Config {
    fn drop(&mut self) {
        unsafe { Z3_del_config(self.config) }
    }
}

impl Context {
    pub fn new(config: &Config) -> Rc<Context> {
        Rc::new_cyclic(|weak| Context {
            this: weak.clone(),
            ctx: unsafe { Z3_mk_context_rc(config.config).unwrap() },
        })
    }

    pub fn mk_uninterpreted_sort(&self, name: &str) -> Sort {
        let name = CString::new(name.as_bytes()).unwrap();
        Sort::new(self, unsafe {
            Z3_mk_uninterpreted_sort(
                self.ctx,
                Z3_mk_string_symbol(self.ctx, name.as_ptr()).unwrap(),
            )
            .unwrap()
        })
    }

    pub fn mk_bool_sort(&self) -> Sort {
        Sort::new(self, unsafe { Z3_mk_bool_sort(self.ctx).unwrap() })
    }

    pub fn mk_int_sort(&self) -> Sort {
        Sort::new(self, unsafe { Z3_mk_int_sort(self.ctx).unwrap() })
    }

    pub fn mk_real_sort(&self) -> Sort {
        Sort::new(self, unsafe { Z3_mk_real_sort(self.ctx).unwrap() })
    }

    pub fn mk_array_sort(&self, sorts: &[Sort], range: &Sort) -> Sort {
        let sorts = sorts.iter().map(|s| s.sort).collect_vec();

        Sort::new(self, unsafe {
            Z3_mk_array_sort_n(self.ctx, sorts.len() as c_uint, sorts.as_ptr(), range.sort).unwrap()
        })
    }

    pub fn mk_true(&self) -> Ast {
        Ast::new(self, unsafe { Z3_mk_true(self.ctx).unwrap() })
    }

    pub fn mk_false(&self) -> Ast {
        Ast::new(self, unsafe { Z3_mk_true(self.ctx).unwrap() })
    }

    pub fn get_bool_value(&self, ast: &Ast) -> Z3_lbool {
        unsafe { Z3_get_bool_value(self.ctx, ast.ast) }
    }

    pub fn mk_int(&self, value: c_int) -> Ast {
        Ast::new(self, unsafe {
            Z3_mk_int(self.ctx, value, Z3_mk_int_sort(self.ctx).unwrap()).unwrap()
        })
    }

    pub fn mk_numeral(&self, value: &str) -> Ast {
        let numeral = CString::new(value.as_bytes()).unwrap();
        Ast::new(self, unsafe {
            Z3_mk_numeral(
                self.ctx,
                numeral.as_ptr(),
                Z3_mk_int_sort(self.ctx).unwrap(),
            )
            .unwrap()
        })
    }

    pub fn mk_func_decl(&self, name: &str, sorts: &[Sort], range: &Sort) -> FuncDecl {
        let name = CString::new(name.as_bytes()).unwrap();
        let sorts = sorts.iter().map(|s| s.sort).collect_vec();
        FuncDecl::new(self, unsafe {
            Z3_mk_func_decl(
                self.ctx,
                Z3_mk_string_symbol(self.ctx, name.as_ptr()).unwrap(),
                sorts.len() as c_uint,
                sorts.as_ptr(),
                range.sort,
            )
            .unwrap()
        })
    }

    pub fn mk_app(&self, func: &FuncDecl, args: &[Ast]) -> Ast {
        let args = args.iter().map(|ast| ast.ast).collect_vec();
        Ast::new(self, unsafe {
            Z3_mk_app(self.ctx, func.decl, args.len() as c_uint, args.as_ptr()).unwrap()
        })
    }

    pub fn mk_select_n(&self, array: &Ast, args: &[Ast]) -> Ast {
        let args = args.iter().map(|ast| ast.ast).collect_vec();
        Ast::new(self, unsafe {
            Z3_mk_select_n(self.ctx, array.ast, args.len() as c_uint, args.as_ptr()).unwrap()
        })
    }

    pub fn mk_store_n(&self, array: &Ast, args: &[Ast], value: &Ast) -> Ast {
        let args = args.iter().map(|ast| ast.ast).collect_vec();
        Ast::new(self, unsafe {
            Z3_mk_store_n(
                self.ctx,
                array.ast,
                args.len() as c_uint,
                args.as_ptr(),
                value.ast,
            )
            .unwrap()
        })
    }

    pub fn mk_not(&self, arg: &Ast) -> Ast {
        Ast::new(self, unsafe { Z3_mk_not(self.ctx, arg.ast).unwrap() })
    }

    pub fn mk_implies(&self, left: &Ast, right: &Ast) -> Ast {
        Ast::new(self, unsafe {
            Z3_mk_implies(self.ctx, left.ast, right.ast).unwrap()
        })
    }

    pub fn mk_and(&self, args: &[Ast]) -> Ast {
        let args = args.iter().map(|ast| ast.ast).collect_vec();
        Ast::new(self, unsafe {
            Z3_mk_and(self.ctx, args.len() as c_uint, args.as_ptr()).unwrap()
        })
    }

    pub fn mk_or(&self, args: &[Ast]) -> Ast {
        let args = args.iter().map(|ast| ast.ast).collect_vec();
        Ast::new(self, unsafe {
            Z3_mk_or(self.ctx, args.len() as c_uint, args.as_ptr()).unwrap()
        })
    }

    pub fn mk_xor(&self, left: &Ast, right: &Ast) -> Ast {
        Ast::new(self, unsafe {
            Z3_mk_xor(self.ctx, left.ast, right.ast).unwrap()
        })
    }

    pub fn mk_eq(&self, left: &Ast, right: &Ast) -> Ast {
        Ast::new(self, unsafe {
            Z3_mk_eq(self.ctx, left.ast, right.ast).unwrap()
        })
    }

    pub fn mk_distinct(&self, args: &[Ast]) -> Ast {
        let args = args.iter().map(|ast| ast.ast).collect_vec();
        Ast::new(self, unsafe {
            Z3_mk_distinct(self.ctx, args.len() as c_uint, args.as_ptr()).unwrap()
        })
    }

    pub fn mk_ite(&self, cond: &Ast, then: &Ast, otherwise: &Ast) -> Ast {
        Ast::new(self, unsafe {
            Z3_mk_ite(self.ctx, cond.ast, then.ast, otherwise.ast).unwrap()
        })
    }

    pub fn mk_unary_minus(&self, arg: &Ast) -> Ast {
        Ast::new(self, unsafe {
            Z3_mk_unary_minus(self.ctx, arg.ast).unwrap()
        })
    }

    pub fn mk_sub(&self, args: &[Ast]) -> Ast {
        let args = args.iter().map(|ast| ast.ast).collect_vec();
        Ast::new(self, unsafe {
            Z3_mk_sub(self.ctx, args.len() as c_uint, args.as_ptr()).unwrap()
        })
    }

    pub fn mk_add(&self, args: &[Ast]) -> Ast {
        let args = args.iter().map(|ast| ast.ast).collect_vec();
        Ast::new(self, unsafe {
            Z3_mk_add(self.ctx, args.len() as c_uint, args.as_ptr()).unwrap()
        })
    }

    pub fn mk_mul(&self, args: &[Ast]) -> Ast {
        let args = args.iter().map(|ast| ast.ast).collect_vec();
        Ast::new(self, unsafe {
            Z3_mk_mul(self.ctx, args.len() as c_uint, args.as_ptr()).unwrap()
        })
    }

    pub fn mk_div(&self, left: &Ast, right: &Ast) -> Ast {
        Ast::new(self, unsafe {
            Z3_mk_div(self.ctx, left.ast, right.ast).unwrap()
        })
    }

    pub fn mk_mod(&self, left: &Ast, right: &Ast) -> Ast {
        Ast::new(self, unsafe {
            Z3_mk_mod(self.ctx, left.ast, right.ast).unwrap()
        })
    }

    pub fn mk_le(&self, left: &Ast, right: &Ast) -> Ast {
        Ast::new(self, unsafe {
            Z3_mk_le(self.ctx, left.ast, right.ast).unwrap()
        })
    }

    pub fn mk_lt(&self, left: &Ast, right: &Ast) -> Ast {
        Ast::new(self, unsafe {
            Z3_mk_lt(self.ctx, left.ast, right.ast).unwrap()
        })
    }

    pub fn mk_ge(&self, left: &Ast, right: &Ast) -> Ast {
        Ast::new(self, unsafe {
            Z3_mk_ge(self.ctx, left.ast, right.ast).unwrap()
        })
    }

    pub fn mk_gt(&self, left: &Ast, right: &Ast) -> Ast {
        Ast::new(self, unsafe {
            Z3_mk_gt(self.ctx, left.ast, right.ast).unwrap()
        })
    }
}

impl Drop for Context {
    fn drop(&mut self) {
        unsafe { Z3_del_context(self.ctx) }
    }
}

impl Solver {
    pub fn new(ctx: Rc<Context>) -> Solver {
        Solver {
            slv: unsafe {
                let slv = Z3_mk_solver(ctx.ctx).unwrap();
                Z3_solver_inc_ref(ctx.ctx, slv);
                slv
            },
            ctx,
            model: None,
        }
    }

    pub fn new_for_logic(ctx: Rc<Context>, logic: &str) -> Solver {
        let logic = CString::new(logic.as_bytes()).unwrap();
        Solver {
            slv: unsafe {
                let slv = Z3_mk_solver_for_logic(
                    ctx.ctx,
                    Z3_mk_string_symbol(ctx.ctx, logic.as_ptr()).unwrap(),
                )
                .unwrap();
                Z3_solver_inc_ref(ctx.ctx, slv);
                slv
            },
            ctx,
            model: None,
        }
    }

    pub fn push(&self) {
        unsafe { Z3_solver_push(self.ctx.ctx, self.slv) }
    }

    pub fn pop(&self, n: usize) {
        unsafe { Z3_solver_pop(self.ctx.ctx, self.slv, n as c_uint) }
    }

    pub fn assert(&self, ast: &Ast) {
        unsafe { Z3_solver_assert(self.ctx.ctx, self.slv, ast.ast) }
    }

    pub fn check(&mut self) -> Z3_lbool {
        let answer = unsafe { Z3_solver_check(self.ctx.ctx, self.slv) };

        if answer == Z3_L_TRUE {
            let model = unsafe { Z3_solver_get_model(self.ctx.ctx, self.slv).unwrap() };
            unsafe {
                Z3_model_inc_ref(self.ctx.ctx, model);
            }
            self.model = Some(model);
        } else {
            self.model = None;
        }

        answer
    }

    pub fn get_model(&self) -> Option<Model> {
        self.model.map(|m| Model::new(self.ctx.clone(), m))
    }
}

impl Drop for Solver {
    fn drop(&mut self) {
        unsafe { Z3_solver_dec_ref(self.ctx.ctx, self.slv) }
    }
}

impl Model {
    pub fn new(ctx: Rc<Context>, model: Z3_model) -> Model {
        unsafe {
            Z3_model_inc_ref(ctx.ctx, model);
        }
        Model {
            ctx: ctx.this.upgrade().unwrap(),
            model,
        }
    }

    pub fn get_const_interp(&self, decl: &FuncDecl) -> Option<Ast> {
        Some(Ast::new(&self.ctx, unsafe {
            Z3_model_get_const_interp(self.ctx.ctx, self.model, decl.decl)?
        }))
    }
}

impl Drop for Model {
    fn drop(&mut self) {
        unsafe { Z3_model_dec_ref(self.ctx.ctx, self.model) }
    }
}

impl Ast {
    fn new(ctx: &Context, ast: Z3_ast) -> Ast {
        Ast {
            ctx: ctx.this.upgrade().unwrap(),
            ast: unsafe {
                Z3_inc_ref(ctx.ctx, ast);
                ast
            },
        }
    }

    pub fn kind(&self) -> AstKind {
        unsafe { Z3_get_ast_kind(self.ctx.ctx, self.ast) }
    }

    pub fn get_numeral_string(&self) -> String {
        assert_eq!(self.kind(), AstKind::Numeral);

        unsafe {
            let string = Z3_get_numeral_string(self.ctx.ctx, self.ast);
            CString::from(CStr::from_ptr(string)).into_string().unwrap()
        }
    }
}

impl Clone for Ast {
    fn clone(&self) -> Self {
        unsafe { Z3_inc_ref(self.ctx.ctx, self.ast) }
        Ast {
            ctx: self.ctx.clone(),
            ast: self.ast,
        }
    }
}

impl Hash for Ast {
    fn hash<H: Hasher>(&self, state: &mut H) {
        Hash::hash(&self.ast, state)
    }
}

impl From<FuncDecl> for Ast {
    fn from(app: FuncDecl) -> Self {
        Ast {
            ctx: app.ctx.clone(),
            ast: app.decl.cast::<_Z3_ast>(),
        }
    }
}

impl From<Sort> for Ast {
    fn from(sort: Sort) -> Self {
        Ast {
            ctx: sort.ctx.clone(),
            ast: sort.sort.cast::<_Z3_ast>(),
        }
    }
}

impl FuncDecl {
    pub fn new(ctx: &Context, decl: Z3_func_decl) -> FuncDecl {
        FuncDecl {
            ctx: ctx.this.upgrade().unwrap(),
            decl: unsafe {
                Z3_inc_ref(ctx.ctx, decl.cast::<_Z3_ast>());
                decl
            },
        }
    }
}

impl Clone for FuncDecl {
    fn clone(&self) -> Self {
        unsafe { Z3_inc_ref(self.ctx.ctx, self.decl.cast::<_Z3_ast>()) }
        FuncDecl {
            ctx: self.ctx.clone(),
            decl: self.decl,
        }
    }
}

impl Drop for FuncDecl {
    fn drop(&mut self) {
        unsafe { Z3_dec_ref(self.ctx.ctx, self.decl.cast::<_Z3_ast>()) }
    }
}

impl Hash for FuncDecl {
    fn hash<H: Hasher>(&self, state: &mut H) {
        Hash::hash(&self.decl, state)
    }
}

impl Sort {
    pub fn new(ctx: &Context, sort: Z3_sort) -> Sort {
        Sort {
            ctx: ctx.this.upgrade().unwrap(),
            sort: unsafe {
                Z3_inc_ref(ctx.ctx, sort.cast::<_Z3_ast>());
                sort
            },
        }
    }
}

impl Clone for Sort {
    fn clone(&self) -> Self {
        unsafe { Z3_inc_ref(self.ctx.ctx, self.sort.cast::<_Z3_ast>()) }
        Sort {
            ctx: self.ctx.clone(),
            sort: self.sort,
        }
    }
}

impl Drop for Sort {
    fn drop(&mut self) {
        unsafe { Z3_dec_ref(self.ctx.ctx, self.sort.cast::<_Z3_ast>()) }
    }
}

impl Hash for Sort {
    fn hash<H: Hasher>(&self, state: &mut H) {
        Hash::hash(&self.sort, state)
    }
}
