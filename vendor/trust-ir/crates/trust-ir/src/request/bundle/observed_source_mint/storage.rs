// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
pub(super) struct Work<'s, 'o, O: ExecutionObserver> {
    pub(super) session: &'s mut ObservedSession<'o, O>,
    pub(super) site: ExecutionSite,
}
impl<O: ExecutionObserver> Work<'_, '_, O> {
    pub(super) fn admit(&mut self, work: usize, copy_bytes: usize) -> R {
        self.session
            .admit(ExecutionProgress {
                phase: ExecutionPhase::Validation,
                site: self.site,
                work,
                copy_bytes,
            })
            .map_err(Into::into)
    }
    pub(super) fn terminal(&mut self) -> R {
        self.session
            .admit(ExecutionProgress {
                phase: ExecutionPhase::Publication,
                site: self.site,
                work: 0,
                copy_bytes: 0,
            })
            .map_err(Into::into)
    }
    pub(super) fn publication(&mut self) -> R {
        self.session
            .admit(ExecutionProgress {
                phase: ExecutionPhase::Publication,
                site: self.site,
                work: 1,
                copy_bytes: size_of::<Mint>()
                    + size_of::<Option<Mint>>()
                    + size_of::<SourceGenerationLiveMarker>()
                    + size_of::<Option<SourceGenerationLiveMarker>>(),
            })
            .map_err(Into::into)
    }
    pub(super) fn record(&mut self, work: usize, copy_bytes: usize) {
        self.session.retirement_record(self.site, work, copy_bytes);
    }
    pub(super) fn poll(&mut self) {
        self.session.retirement_poll(self.site);
    }
    pub(super) fn release(&mut self, nonce: Arc<SourceGenerationNonce>) {
        // Only this private nonce type reaches here: a fresh candidate or its
        // installed non-Clone authority, at most two refs. Bounded releases, zero-sized user
        // payload and one fixed ArcInner allocation; no arbitrary graph Drop.
        // Actual std allocator/deallocator/atomic latency remains OPEN.
        self.record(
            4,
            size_of::<Arc<SourceGenerationNonce>>() + 2 * size_of::<usize>(),
        );
        drop(nonce);
        self.poll();
    }
}
