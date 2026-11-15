// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
impl State {
    pub(super) fn retire_scratch<O: ExecutionObserver>(&mut self, w: &mut Work<'_, '_, O>) {
        self.retire_batch(w);
        w.record(1, size_of::<Option<E>>());
        if let Some(error) = self.pending.take() {
            let _ = error.retire_observed(w.session, w.site);
        }
        w.poll();
    }
    pub(super) fn retire_errors<O: ExecutionObserver>(&mut self, w: &mut Work<'_, '_, O>) {
        w.record(1, size_of::<Vec<E>>());
        let _ = retire_native_bundle_errors_observed(take(&mut self.errors), w.session, w.site);
    }
    pub(super) fn retire_output<O: ExecutionObserver>(&mut self, w: &mut Work<'_, '_, O>) {
        w.record(1, size_of::<Option<Validation>>() + size_of::<Validation>());
        if let Some(Err(rows)) = self.output.take() {
            let _ = retire_native_bundle_errors_observed(rows, w.session, w.site);
        }
        w.poll();
    }
}
