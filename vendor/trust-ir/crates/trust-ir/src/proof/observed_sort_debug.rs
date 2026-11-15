// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Original default ClauseSort Debug spelling, never a canonical identity.
use super::ClauseSort;
use crate::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
use core::mem::{size_of, take};
mod queue;
mod storage;
#[cfg(test)]
mod tests;
mod walk;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;

// Every descriptor owns only fixed or borrowed headers. Copy prevents a future
// owned field from silently entering the fixed retirement path.
#[derive(Clone, Copy)]
enum Task<'a> {
    Sort(&'a ClauseSort),
    Text(&'static str),
    Ctors(&'a [(String, Vec<(String, ClauseSort)>)], usize),
    Fields(&'a [(String, ClauseSort)], usize),
}
#[derive(Default)]
struct State<'a> {
    tasks: Vec<Task<'a>>,
    pending: Option<Task<'a>>,
    output: String,
}

impl ClauseSort {
    /// Render the exact ordinary `{:?}` diagnostic, including malformed sort
    /// numbers, duplicate names and all physical datatype rows. This does not
    /// validate, normalize, authenticate or prove anything about the sort.
    ///
    /// The supplied session/site is reused inside the actual iterative walk,
    /// scalar Debug escapes and bounded text copies. Returned String and input
    /// disposal remain caller-owned. No physical allocator, std table search,
    /// machine-work, panic/OOM/unwind or hard-time bound is claimed.
    pub fn debug_observed<O: ExecutionObserver>(
        &self,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<String> {
        session.admit(ExecutionProgress {
            phase: ExecutionPhase::Validation,
            site,
            work: 1,
            copy_bytes: size_of::<State<'_>>() + size_of::<Work<'_, '_, O>>(),
        })?;
        let mut state = State::default();
        let mut work = Work { session, site };
        let result = state.walk(self, &mut work);
        state.finish(result, &mut work)
    }
}
impl State<'_> {
    fn retire_tasks<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        // Remove each held header only after the corresponding retirement step.
        work.step(size_of::<Option<Task<'_>>>().saturating_add(1));
        work.fixed(take(&mut self.pending));
        work.retire_fixed_vec(&mut self.tasks);
    }
    fn finish<O: ExecutionObserver>(&mut self, result: R, work: &mut Work<'_, '_, O>) -> R<String> {
        // Output remains owned while every pending/queued descriptor retires.
        self.retire_tasks(work);
        match result.and_then(|()| work.publication(1, size_of::<String>())) {
            Ok(()) => Ok(take(&mut self.output)),
            Err(error) => {
                work.retire_text(&mut self.output);
                Err(work.terminal(error))
            }
        }
    }
}
