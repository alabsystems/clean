// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
pub(super) fn key<O: ExecutionObserver>(key: Option<Key<'_>>, work: &mut Work<'_, '_, O>) {
    work.step(size_of::<Option<Key<'_>>>().saturating_add(1));
    if let Some(Key::Composite { children, .. }) = key {
        work.rows(children);
    }
    work.poll();
}
impl State<'_> {
    pub(super) fn retire_scratch<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        key(self.building.take(), work);
        key(self.pending_key.take(), work);
        work.rows(take(&mut self.pending_bucket));
        work.retire(self.current.take());
        loop {
            work.step(size_of::<Option<Frame<'_>>>().saturating_add(1));
            let Some(frame) = self.stack.pop() else {
                break;
            };
            work.retire(frame);
        }
        work.retire(take(&mut self.stack));
        work.rows(take(&mut self.results));
        loop {
            work.step(size_of::<Option<Key<'_>>>().saturating_add(1));
            let Some(row) = self.classes.pop() else {
                break;
            };
            key(Some(row), work);
        }
        work.retire(take(&mut self.classes));
        while !self.buckets.is_empty() {
            work.step(self.buckets.len().saturating_add(1).saturating_mul(64));
            if let Some((fp, rows)) = self.buckets.pop_first() {
                work.rows(rows);
                work.retire(fp);
            }
        }
        work.retire(take(&mut self.buckets));
    }
}
