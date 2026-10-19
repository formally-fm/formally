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

use oxidd::{HasWorkers as _, WorkerPool, bcdd::BCDDManagerRef};

use async_task::{Runnable, Task as AsyncTask};

use std::future::Future;
use std::pin::Pin;
use std::task::{Context, Poll};

pub trait Executor {
    fn spawn<F>(&self, future: F) -> Task<F::Output>
    where
        F: 'static + Future + Send,
        F::Output: 'static + Send;
}

pub struct Task<T>(Option<AsyncTask<T>>);

impl<T> Task<T> {
    fn new(task: AsyncTask<T>) -> Self {
        Task(Some(task))
    }
}

impl<T> Future for Task<T> {
    type Output = T;

    fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        Pin::new(&mut self.0.as_mut().unwrap()).poll(cx)
    }
}

impl<T> Drop for Task<T> {
    fn drop(&mut self) {
        self.0.take().unwrap().detach()
    }
}

impl Executor for BCDDManagerRef {
    fn spawn<F>(&self, future: F) -> Task<F::Output>
    where
        F: 'static + Future + Send,
        F::Output: 'static + Send,
    {
        let manager = self.clone();

        let (runnable, task) = async_task::Builder::new().propagate_panic(true).spawn(
            move |_| future,
            move |runnable: Runnable| {
                manager.workers().install(move || {
                    rayon::spawn(move || {
                        runnable.run();
                    })
                })
            },
        );
        runnable.schedule();

        Task::new(task)
    }
}
