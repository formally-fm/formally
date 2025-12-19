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

use crate::diagnostics::*;

use dashmap::DashMap;

use perfect_derive::perfect_derive;
use std::{
    any::{Any, TypeId},
    fmt::{Debug, Formatter},
    hash::Hash,
    ops::Deref,
    sync::Arc,
};

///
/// Centralized store for data shared between components.
///
/// In many places in `::formally`, different components need to access shared data in a controlled
/// way. For example, the SMT type checker needs a global cache to save the results of invocations
/// to save time when the sort of the same term is asked for twice. Furthermore, all the compontents
/// of `::formally` needs access to a common [Emitter] to emit errors, warnings, etc.
///
/// The [Context] type provides access to this sort of shared data in a well-defined way.
/// A [Context] provide access to a common [Emitter] by implementing [Emitter] on its own,
/// delegating to the one selected at instantiation with the [Context::with_emitter]
/// method.
///
/// The common pattern to start using any `::formally` component is to create a [Context], set an
/// emitter (if the default is not desired), and then pass the context to the constructor of the
/// component.
///
/// Example:
/// ```rust,no_run
/// # use formally_support::*;
/// # use formally_smt::*;
/// # fn main() -> Result<()> {
/// let ctx = Context::new().with_emitter(StdErrEmitter::new());
/// let config = Config::default().with_context(ctx);
/// let slv = Solver::new(&config);
/// # Ok(())
/// # }
/// ```
///
/// [Context] can hold arbitrary data in the form of a [DataPool] object (obtained by
/// [Context::data_pool],which is basically a hash map [DashMap] indexed by `TypeId`. [DataPool] is
/// used by the [Context::cache] method to provide a general key-value cache for arbitrary pairs of
/// key and value types (see the [Context::cache] method for details).
///
/// Note that [Context] is [Clone] and the clone is *shallow*, so each clone will share the same
/// [Emitter] and the same [DataPool].
///
/// The [Contextual] trait is for types which know their [Context].
/// Many types in `formally` are [Contextual] and, by convention, usually a [Contextual] type
/// implements [Emitter] as well relaying the diagnostics to the [Context].
#[derive(Clone)]
pub struct Context {
    emitter: Arc<dyn Emitter + Send + Sync>,
    data: Arc<DataPool>,
}

impl Default for Context {
    /// Equivalent to [Context::new]
    fn default() -> Self {
        Context::new()
    }
}

impl Context {
    ///
    /// Creates a default [Context] with the default [Emitter] (currently a `StdErrEmitter`) and an
    /// empty [DataPool].
    pub fn new() -> Self {
        Context {
            emitter: Arc::new(StdErrEmitter::new()),
            data: Arc::new(DataPool::new()),
        }
    }

    /// Function to get a new context with a different [Emitter].
    pub fn with_emitter(self, emitter: impl 'static + Emitter + Send + Sync) -> Context {
        Context {
            emitter: Arc::new(emitter),
            data: self.data.clone(),
        }
    }

    /// Retrieves a shared reference to the internal [DataPool] of the context.
    /// Note that since [Context] is meant to be shared between different components, [DataPool]
    /// uses interior mutability so a shared reference is sufficient to write to it safely.
    pub fn data_pool(&self) -> Arc<DataPool> {
        self.data.clone()
    }

    /// Access to the shared key/value cache of the [Context].
    ///
    /// [Context] stores different caches in its data pool identified by a different [CacheTag]
    /// type. The [CacheTag] trait defines the type of the keys and values of the cache, and
    /// [Context::cache] returns an object dereferencing to a [DashMap] of the approriate type.
    ///
    /// The [CacheTag] system allows us to have different independent caches with the same key/value
    /// types, which otherwise would be confused together if [Context::cache] was paramterized
    /// directly by the type of keys and values.
    ///
    /// Example:
    /// ```
    /// # use formally_support::{Context,CacheTag};
    /// # let context = Context::new();
    /// struct MyCacheTag;
    ///
    /// impl CacheTag for MyCacheTag {
    ///     type Key = String;
    ///     type Value = usize;
    /// }
    ///
    /// let cache = context.cache::<MyCacheTag>();
    ///
    /// let string = "hello".to_string();
    /// let len = string.len();
    /// cache.insert(string, len);
    /// ```
    pub fn cache<T: CacheTag>(
        &self,
    ) -> impl Deref<Target: Deref<Target = DashMap<T::Key, T::Value>>> {
        self.data.get::<CacheSlot<T>>()
    }
}

impl Emitter for Context {
    ///
    /// Emits the diagnostic through the underlying [Emitter]
    fn emit(&self, level: Level, diag: Diagnostic) {
        self.emitter.emit(level, diag)
    }

    ///
    /// Emits the note through the underlying [Emitter]
    fn note(&self, kind: NoteKind, note: Diagnostic) {
        self.emitter.note(kind, note)
    }
}

impl Debug for Context {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "Context {{ .. }}")
    }
}

/// Types that hold a shared reference to the a [Context].
///
/// A [Contextual] type holds a shared [Context] instance. The trait also defines how to change the
/// contained [Context], through the [Contextual::set_context] method, and the builder function
/// [Contextual::with_context] to help select the context when instantiating a [Contextual] object.
///
/// Since [Context] holds a reference to the currently selected [Emitter], [Contextual] types
/// automatically implement [Emitter] as well.
///
/// This trait can be automatically derived (see the corresponding proc-macro for details).
pub trait Contextual {
    /// Retrieves the shared reference to the [Context].
    fn context(&self) -> Context;

    /// Sets a new shared reference to a [Context].
    ///
    /// It is expected for implementors to start using the new [Context] as the [Emitter] after this
    /// change.
    fn set_context(&mut self, ctx: Context);

    ///
    /// Builder method to set a new [Context] after creation.
    ///
    /// Example:
    /// ```rust,no_run
    /// # use formally_support::*;
    /// # use formally_smt::*;
    /// # fn main() -> Result<()> {
    /// let ctx = Context::new().with_emitter(StdErrEmitter::new());
    /// let config = Config::default().with_context(ctx);
    /// let slv = Solver::new(&config);
    /// # Ok(())
    /// # }
    /// ```
    fn with_context(mut self, ctx: Context) -> Self
    where
        Self: Sized,
    {
        self.set_context(ctx);
        self
    }

    /// Returns a new instance with the same [Context] holding a different [Emitter].
    fn with_emitter(self, emitter: impl 'static + Emitter + Send + Sync) -> Self
    where
        Self: Sized,
    {
        let ctx = self.context().with_emitter(emitter);
        self.with_context(ctx)
    }
}

impl<T: Contextual> Emitter for T {
    fn emit(&self, level: Level, diag: Diagnostic) {
        self.context().emit(level, diag)
    }

    fn note(&self, kind: NoteKind, note: Diagnostic) {
        self.context().note(kind, note)
    }
}

///
/// Trait to define tag types for usage with the [Context::cache] method.
pub trait CacheTag: 'static {
    /// The type of keys of the cache
    type Key: 'static + Hash + Eq + Clone + Send + Sync;

    /// The type of values held by the cache
    type Value: 'static + Clone + Send + Sync;
}

#[perfect_derive(Default)]
struct CacheSlot<T: CacheTag> {
    map: DashMap<T::Key, T::Value>,
}

impl<T: CacheTag> Deref for CacheSlot<T> {
    type Target = DashMap<T::Key, T::Value>;

    fn deref(&self) -> &Self::Target {
        &self.map
    }
}

/// Shared data indexed by TypeId.
///
/// [DataPool] holds a collection of objects of different arbitrary types, indexed by their
/// [TypeId].
///
/// The only access to these data is the [DataPool::get] method which creates a default object of
/// the given type if not present, or retrieves the existing one otherwise.
///
/// Since [DataPool] is meant to be used inside a [Context], which is meant to be used through
/// shared references, [DataPool::get] returns a shared reference to the underlying data. This means
/// the mechanism is only useful when the stored types use interior mutability.
#[derive(Default)]
pub struct DataPool {
    pool: DashMap<TypeId, Box<dyn Any + Send + Sync>>,
}

impl DataPool {
    /// Creates a default [DataPool]
    pub fn new() -> DataPool {
        DataPool::default()
    }

    // Retrieves and/or creates a reference to an object of type `T`
    pub fn get<T: 'static + Default + Send + Sync>(&self) -> impl Deref<Target = T> {
        let tid = TypeId::of::<T>();
        if !self.pool.contains_key(&tid) {
            self.pool
                .insert(tid, Box::new(T::default()) as Box<dyn Any + Send + Sync>);
        }

        self.pool
            .get(&tid)
            .unwrap()
            .map(|m| m.downcast_ref::<T>().unwrap())
    }
}
