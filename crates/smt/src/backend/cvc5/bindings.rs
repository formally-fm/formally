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

use cvc5_sys as cvc5;

use std::{
    ffi::{CStr, CString},
    ptr::NonNull,
    rc::Rc,
};

pub use cvc5::Kind;

pub type Sort = NonNull<cvc5::cvc5_sort_t>;
pub type Term = NonNull<cvc5::cvc5_term_t>;

pub struct TermManager {
    manager: *mut cvc5::TermManager,
}

impl TermManager {
    pub fn new() -> TermManager {
        TermManager {
            manager: unsafe { cvc5::term_manager_new() },
        }
    }

    pub fn get_boolean_sort(&self) -> Sort {
        unsafe { NonNull::new(cvc5::get_boolean_sort(self.manager)).unwrap() }
    }

    pub fn get_integer_sort(&self) -> Sort {
        unsafe { NonNull::new(cvc5::get_integer_sort(self.manager)).unwrap() }
    }

    pub fn get_real_sort(&self) -> Sort {
        unsafe { NonNull::new(cvc5::get_real_sort(self.manager)).unwrap() }
    }

    pub fn mk_array_sort(&self, index: Sort, element: Sort) -> Sort {
        unsafe {
            NonNull::new(cvc5::mk_array_sort(
                self.manager,
                index.as_ptr(),
                element.as_ptr(),
            ))
            .unwrap()
        }
    }

    pub fn mk_term(&self, kind: Kind, children: &[Term]) -> Term {
        unsafe {
            NonNull::new(cvc5::mk_term(
                self.manager,
                kind,
                children.len(),
                children.as_ptr().cast(),
            ))
            .unwrap()
        }
    }

    pub fn mk_boolean(&self, value: bool) -> Term {
        unsafe { NonNull::new(cvc5::mk_boolean(self.manager, value)).unwrap() }
    }

    pub fn mk_integer(&self, value: &str) -> Term {
        let value = CString::new(value.as_bytes()).unwrap();
        unsafe { NonNull::new(cvc5::mk_integer(self.manager, value.as_ptr())).unwrap() }
    }

    pub fn mk_real(&self, value: &str) -> Term {
        let value = CString::new(value.as_bytes()).unwrap();
        unsafe { NonNull::new(cvc5::mk_real(self.manager, value.as_ptr())).unwrap() }
    }

    pub fn mk_uninterpreted_sort(&self, name: &str) -> Sort {
        let name = CString::new(name.as_bytes()).unwrap();
        unsafe { NonNull::new(cvc5::mk_uninterpreted_sort(self.manager, name.as_ptr())).unwrap() }
    }
}

impl Default for TermManager {
    fn default() -> Self {
        TermManager::new()
    }
}

impl Drop for TermManager {
    fn drop(&mut self) {
        unsafe { cvc5::term_manager_delete(self.manager) }
    }
}

pub struct Solver {
    manager: Rc<TermManager>,
    solver: *mut cvc5::Solver,
}

impl Solver {
    pub fn new(manager: Rc<TermManager>) -> Solver {
        Solver {
            manager: manager.clone(),
            solver: unsafe { cvc5::new(manager.manager) },
        }
    }

    pub fn set_option(&self, option: &str, value: &str) {
        let option = CString::new(option.as_bytes()).unwrap();
        let value = CString::new(value.as_bytes()).unwrap();
        unsafe { cvc5::set_option(self.solver, option.as_ptr(), value.as_ptr()) }
    }

    pub fn set_logic(&self, logic: &str) {
        let logic = CString::new(logic.as_bytes()).unwrap();
        unsafe { cvc5::set_logic(self.solver, logic.as_ptr()) }
    }

    pub fn declare_fun(&self, name: &str, sorts: &[Sort], range: Sort, fresh: bool) -> Term {
        let name = CString::new(name.as_bytes()).unwrap();
        unsafe {
            NonNull::new(cvc5::declare_fun(
                self.solver,
                name.as_ptr(),
                sorts.len(),
                sorts.as_ptr().cast(),
                range.as_ptr(),
                fresh,
            ))
            .unwrap()
        }
    }

    pub fn define_fun(
        &self,
        name: &str,
        vars: &[Term],
        range: Sort,
        body: Term,
        global: bool,
    ) -> Term {
        let name = CString::new(name.as_bytes()).unwrap();
        unsafe {
            NonNull::new(cvc5::define_fun(
                self.solver,
                name.as_ptr(),
                vars.len(),
                vars.as_ptr().cast(),
                range.as_ptr(),
                body.as_ptr(),
                global,
            ))
            .unwrap()
        }
    }

    pub fn assert_formula(&self, term: Term) {
        unsafe { cvc5::assert_formula(self.solver, term.as_ptr()) }
    }

    pub fn check_sat(&self) -> Result {
        Result::new(unsafe { cvc5::check_sat(self.solver) })
    }

    pub fn push(&self) {
        unsafe { cvc5::push(self.solver, 1) }
    }

    pub fn pop(&self, n: u32) {
        unsafe { cvc5::pop(self.solver, n) }
    }
}

impl Drop for Solver {
    fn drop(&mut self) {
        unsafe { cvc5::delete(self.solver) }
    }
}

pub struct Result {
    result: cvc5::Result,
}

impl Clone for Result {
    fn clone(&self) -> Self {
        Result {
            result: unsafe { cvc5::result_copy(self.result) },
        }
    }
}

impl Drop for Result {
    fn drop(&mut self) {
        unsafe { cvc5::result_release(self.result) }
    }
}

impl Result {
    fn new(result: cvc5::Result) -> Result {
        Result { result }
    }

    pub fn is_sat(&self) -> bool {
        unsafe { cvc5::result_is_sat(self.result) }
    }

    pub fn is_unsat(&self) -> bool {
        unsafe { cvc5::result_is_unsat(self.result) }
    }

    pub fn is_unknown(&self) -> bool {
        unsafe { cvc5::result_is_unknown(self.result) }
    }
}
