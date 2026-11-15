// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
impl<'a> State<'a> {
    fn descriptor<O: ExecutionObserver>(&self, work: &mut Work<'_, '_, O>) -> R {
        // This occurs before constructing any actual Task/Some header.
        work.admit(2, size_of::<Option<Task<'_>>>())?;
        if self.pending.is_some() {
            return Err(ObservedValueError::InvalidRange);
        }
        Ok(())
    }
    pub(super) fn enqueue<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) -> R {
        // The new descriptor is already held by State through both fallible
        // capacity admission and the final move/header admission.
        work.reserve(&mut self.tasks)?;
        work.admit(1, size_of::<Task<'_>>() + size_of::<Option<Task<'_>>>())?;
        let task = self
            .pending
            .take()
            .ok_or(ObservedValueError::InvalidRange)?;
        self.tasks.push(task);
        Ok(())
    }
    pub(super) fn sort<O: ExecutionObserver>(
        &mut self,
        value: &'a ClauseSort,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        self.descriptor(work)?;
        self.pending = Some(Task::Sort(value));
        self.enqueue(work)
    }
    pub(super) fn text<O: ExecutionObserver>(
        &mut self,
        value: &'static str,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        self.descriptor(work)?;
        self.pending = Some(Task::Text(value));
        self.enqueue(work)
    }
    pub(super) fn ctors<O: ExecutionObserver>(
        &mut self,
        rows: &'a [(String, Vec<(String, ClauseSort)>)],
        index: usize,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        self.descriptor(work)?;
        self.pending = Some(Task::Ctors(rows, index));
        self.enqueue(work)
    }
    pub(super) fn fields<O: ExecutionObserver>(
        &mut self,
        rows: &'a [(String, ClauseSort)],
        index: usize,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        self.descriptor(work)?;
        self.pending = Some(Task::Fields(rows, index));
        self.enqueue(work)
    }
}
