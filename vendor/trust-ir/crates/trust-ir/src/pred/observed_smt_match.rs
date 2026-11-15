// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Actual original predicate SMT text equality, without an expanded DAG String.
use super::*;
use crate::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
use core::mem::{size_of, take};
mod cardinality;
mod storage;
#[cfg(test)]
mod tests;
mod walk;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;
#[derive(Clone, Copy)]
enum Task<'a> {
    Pred(PredId, u32),
    Children(&'a [PredId], usize, u32),
    Members(&'a [Constant], usize),
    Constant(&'a Constant),
    Text(&'static str),
    Signed(i128),
    Unsigned(u128),
}
#[derive(Default)]
struct State<'a> {
    tasks: Vec<Task<'a>>,
    pending: Option<String>,
    cursor: usize,
}
impl<'a> PredTable<'a> {
    /// Whether the exact original `smtlib_of_within(id, text.len())` is Some(text).
    /// Traversal, source references, decimal spelling, complete Constant child
    /// output, requested scratch and comparison all use this same original
    /// session/site. The existing depth64 boundary is preserved. No schema,
    /// predicate validity, source/proof authority or owner is established.
    ///
    /// A mismatching/too-long prefix proves inequality without expanding a DAG
    /// tail. Matching text must finish every actual task; dangling/depth/cardinality
    /// failure is unequal as in the original. The existing Constant Display
    /// Float primitive still returns UnsupportedValue rather than opaque std
    /// formatting, and remains explicitly OPEN. Successful input disposal and
    /// physical std/allocator/deallocator/OOM/panic/unwind/RSS/hardtime are OPEN.
    pub fn smtlib_matches_observed<O: ExecutionObserver>(
        &self,
        id: PredId,
        text: &str,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<bool> {
        let mut work = Work { session, site };
        work.admit(1, size_of::<State<'_>>() + size_of::<Work<'_, '_, O>>())?;
        let mut state = State::default();
        let result = state.run(self, id, text, &mut work);
        state.finish(result, &mut work)
    }
}
impl State<'_> {
    fn finish<O: ExecutionObserver>(
        &mut self,
        result: R<bool>,
        work: &mut Work<'_, '_, O>,
    ) -> R<bool> {
        self.retire(work);
        let answer = result.map_err(|error| work.terminal(error))?;
        work.publish(answer)
    }
    fn retire<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        self.retire_pending(work);
        loop {
            work.step(size_of::<Option<Task<'_>>>().saturating_add(1));
            let Some(_) = self.tasks.pop() else { break };
            work.step(size_of::<Task<'_>>().saturating_add(1));
        }
        work.step(size_of::<Vec<Task<'_>>>().saturating_add(1));
        drop(take(&mut self.tasks));
        work.poll();
    }
    fn retire_pending<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        work.step(size_of::<Option<String>>().saturating_add(1));
        if let Some(text) = self.pending.take() {
            work.flat(text);
        }
        work.poll();
    }
}
fn text<O: ExecutionObserver>(
    expected: &str,
    cursor: &mut usize,
    source: &str,
    work: &mut Work<'_, '_, O>,
) -> R<bool> {
    work.admit(3, 3 * size_of::<usize>())?;
    let end = cursor
        .checked_add(source.len())
        .ok_or(ObservedValueError::CapacityOverflow)?;
    if end > expected.len() {
        return Ok(false);
    }
    let mut at = 0usize;
    while at < source.len() {
        work.admit(4, 2 * size_of::<&[u8]>() + 2 * size_of::<usize>())?;
        let next = at.saturating_add(1024).min(source.len());
        work.admit(next - at, 0)?;
        if source.as_bytes()[at..next] != expected.as_bytes()[*cursor + at..*cursor + next] {
            return Ok(false);
        }
        work.admit(1, size_of::<usize>())?;
        at = next;
    }
    work.admit(1, size_of::<usize>())?;
    *cursor = end;
    Ok(true)
}
