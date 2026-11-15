// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;

pub(super) struct Work<'s, 'o, O: ExecutionObserver> {
    pub(super) session: &'s mut ObservedSession<'o, O>,
    pub(super) site: ExecutionSite,
}

impl<O: ExecutionObserver> Work<'_, '_, O> {
    pub(super) fn step(&mut self, work: usize) {
        // The original observer still sees every actual retirement after a
        // refusal. No admission here can return early with owned input live.
        self.session.retirement_step(self.site, work);
    }
    pub(super) fn poll(&mut self) {
        self.session.retirement_poll(self.site);
    }
    pub(super) fn fixed<T: Copy>(&mut self, value: T) {
        // Future owned payload cannot be silently consumed by this route.
        self.step(size_of::<T>().saturating_add(1));
        let _ = value;
    }
    pub(super) fn arc<T>(&mut self) {
        self.step(
            size_of::<Arc<T>>()
                .saturating_add(size_of::<Option<T>>())
                .saturating_add(2 * size_of::<usize>())
                .saturating_add(1),
        );
    }
    pub(super) fn text(&mut self, text: String) {
        // Actual UTF8 byte length is charged before releasing the allocation;
        // physical allocator/deallocator work is outside this logical receipt.
        self.step(
            text.len()
                .saturating_add(size_of::<String>())
                .saturating_add(1),
        );
        drop(text);
        self.poll();
    }
    pub(super) fn scalars<T: Copy>(&mut self, mut rows: Vec<T>) {
        loop {
            self.step(size_of::<Option<T>>().saturating_add(1));
            let Some(value) = rows.pop() else { break };
            self.fixed(value);
        }
        self.empty(rows);
    }
    pub(super) fn empty<T>(&mut self, rows: Vec<T>) {
        // Private callers have explicitly popped every owned child first.
        // No ordinary variable-payload Drop is hidden in an empty buffer.
        self.step(size_of::<Vec<T>>().saturating_add(1));
        drop(rows);
        self.poll();
    }
    pub(super) fn finish(&mut self) -> R {
        // All ownership has already been consumed. A sticky original refusal
        // rejects this terminal receipt without renewing normal admission.
        self.session
            .admit(ExecutionProgress {
                phase: ExecutionPhase::Publication,
                site: self.site,
                work: 0,
                copy_bytes: 0,
            })
            .map_err(Into::into)
    }
}
