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

//! Handling of SMT-LIBv2 logics.
//!
//! This module contains what is needed to declare and use *logics* as in the terminology of
//! SMT-LIBv2.
//!
//! An SMT-LIBv2 logic combines a set of [theories] with a set of syntactic requirements
//! (such as the linerity of terms) and restrictions on the allowed signatures (such as
//! the absence of uninterpreted functions).
//!
//! In `::formally`, logics are types implementing the [Logic] trait. Most of the types in this
//! module are logics declared using the [logic] macro. The types in this module are, however,
//! usually not necessary during common usage of the framework, since logics are usually set *by
//! name* by configuring the [logic](Config::logic) field of the [Config] object used when
//! instantiating a [Solver].
//!
//! The contents of this module are instead most useful when implementing new backends, so we
//! refer to the documentation on [how to write new backends](backend).

#![allow(non_camel_case_types)]

mod macros;
mod standard;

pub mod requirements;

pub use standard::*;

use crate::*;
use formally::support::*;

use linkme::distributed_slice;
use std::{collections::HashMap, sync::LazyLock};

/// Trait for types representing SMT-LIBv2 logics.
///
/// Types implementing this trait are usually not declared by hand but by using the [logic] macro.
pub trait Logic {
    /// Return the name of the logic.
    fn name(&self) -> &str;

    /// Return the background theory of the logic.
    fn theory(&self) -> &dyn theories::Theory;

    /// Check the syntactic requirements of this logic on terms.
    fn check_term(&self, context: &Context, term: &Term) -> Result<()>;

    /// Check the requirements of this logic on the functions added to the current signature.
    fn check_function(&self, context: &Context, func: &UserFunction) -> Result<()>;
}

#[distributed_slice]
static STANDARD_LOGICS: [&'static (dyn Logic + Send + Sync)];

static STANDARD_LOGICS_MAP: LazyLock<HashMap<&str, &'static (dyn Logic + Send + Sync)>> =
    LazyLock::new(|| {
        let mut map = HashMap::new();
        for logic in STANDARD_LOGICS {
            map.insert(logic.name(), *logic);
        }
        map
    });

/// Return an iterator over all the standard SMT-LIBv2 logics declared in the module.
pub fn standard_logics() -> impl Iterator<Item = &'static dyn Logic> {
    STANDARD_LOGICS.iter().map(|v| *v as &dyn Logic)
}

/// Lookup a logic by name among the standard SMT-LIBv2 logics declared in the module.
///
/// The function returns `None` if the logic of the given name is not found, and returns
/// the second argument `all` if `logic` is equal to `"ALL"`.
pub fn standard_logic<'b>(logic: &str, all: &'b dyn Logic) -> Option<&'b dyn Logic> {
    match logic {
        "ALL" => Some(all),
        _ => STANDARD_LOGICS_MAP.get(logic).map(|v| *v as &dyn Logic),
    }
}
