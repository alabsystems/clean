// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
#[derive(Clone, Copy)]
pub(super) enum Group {
    Prefix,
    Requests,
    Evidence,
}
impl State {
    pub(super) fn run<O: ExecutionObserver>(
        &mut self,
        b: &NativeVerificationBundle,
        w: &mut Work<'_, '_, O>,
    ) -> R {
        self.child(b, Group::Prefix, w)?;
        self.child(b, Group::Requests, w)?;
        self.child(b, Group::Evidence, w)
    }
    pub(super) fn child<O: ExecutionObserver>(
        &mut self,
        b: &NativeVerificationBundle,
        group: Group,
        w: &mut Work<'_, '_, O>,
    ) -> R {
        self.prepare(w)?;
        w.admit(3, size_of::<Group>())?;
        let rows = match group {
            Group::Prefix => b.pre_request_errors_observed(w.session, w.site)?,
            Group::Requests => b.request_errors_kernel_less_observed(w.session, w.site)?,
            Group::Evidence => b.evidence_errors_observed(w.session, w.site)?,
        };
        self.capture(rows);
        self.flush(w)
    }
}
