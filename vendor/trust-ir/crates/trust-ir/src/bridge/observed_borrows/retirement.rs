// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
use super::*;
impl<O: ExecutionObserver> Work<'_, '_, O> {
    fn flat<T>(&mut self, value: T) {
        self.session.retirement_step(self.site, 1);
        drop(value);
        self.session.retirement_poll(self.site);
    }
    pub(super) fn retire_pending(&mut self, pending: &mut Option<Ty>) {
        self.session.retirement_step(self.site, 1);
        if let Some(ty) = pending.take() {
            // The public consuming helper always finishes actual cleanup,
            // including when this original session has already refused.
            let _ = ty.retire_observed(self.session, self.site);
        }
        self.session.retirement_poll(self.site);
    }
}
impl State {
    pub(super) fn retire_scratch<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        work.retire_pending(&mut self.pending);
        while !self.operands.is_empty() {
            work.session.retirement_step(work.site, 1);
            self.operands.pop();
        }
        work.flat(take(&mut self.operands));
    }
    pub(super) fn retire_resolved<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        while !self.resolved.is_empty() {
            work.session.retirement_step(work.site, 1);
            if let Some((_, ty)) = self.resolved.pop() {
                let _ = ty.retire_observed(work.session, work.site);
            }
        }
        work.flat(take(&mut self.resolved));
    }
}
