// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Exact no-op-drop type predicate under the original caller operation.
use super::*;
use crate::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
use core::mem::{size_of, take};
mod storage;
#[cfg(test)]
mod tests;
mod walk;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;
#[derive(Clone, Copy)]
enum Frame<'a> {
    Visit(&'a Ty),
    Tail(&'a [Ty]),
    Exit(u32),
}
#[derive(Clone, Copy, PartialEq, Eq)]
enum Mark {
    OnPath,
    Done,
}
#[derive(Default)]
struct State<'a> {
    stack: Vec<Frame<'a>>,
    marks: Vec<(u32, Mark)>,
}
impl Ty {
    /// Same documented table, reverse tuple traversal, array memoization and
    /// cyclic/out-of-range false answer as is_trivially_droppable. Pointer and
    /// Vector payloads stay opaque; zero-length arrays never read their element.
    /// Actual frame/mark work and requested storage use the same supplied
    /// original session/site; both boolean outcomes require final publication
    /// after all scratch retirement. A typed operational stop is never false.
    /// This diagnostic predicate grants no type/layout/drop/proof authority.
    pub fn is_trivially_droppable_observed<O: ExecutionObserver>(
        &self,
        types: &[Ty],
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<bool> {
        let mut work = Work { session, site };
        work.admit(1, size_of::<State<'_>>() + size_of::<Work<'_, '_, O>>())?;
        let mut state = State::default();
        let result = state.run(self, types, &mut work);
        work.drain(&mut state.stack);
        work.drain(&mut state.marks);
        result
            .and_then(|answer| {
                work.publication()?;
                Ok(answer)
            })
            .map_err(|error| work.terminal(error))
    }
}
impl State<'_> {
    fn find<O: ExecutionObserver>(&self, id: u32, work: &mut Work<'_, '_, O>) -> R<Option<usize>> {
        let mut index = 0usize;
        loop {
            work.admit(1, size_of::<Option<&(u32, Mark)>>())?;
            let Some((candidate, _)) = self.marks.get(index) else {
                return Ok(None);
            };
            work.admit(1, 2 * size_of::<u32>())?;
            if *candidate == id {
                return Ok(Some(index));
            }
            work.admit(1, size_of::<usize>())?;
            index = index
                .checked_add(1)
                .ok_or(ObservedValueError::CapacityOverflow)?;
        }
    }
}
// Borrowed input disposal and physical std/allocator/deallocator/OOM/panic/
// unwind/RSS/machinework/hard-time guarantees remain separate obligations.
