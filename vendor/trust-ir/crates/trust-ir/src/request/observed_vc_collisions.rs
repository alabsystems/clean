// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Complete cross-request import/discharge ambiguity diagnostics.
use super::{
    NativeRequestId, NativeVerificationBundle, NativeVerificationBundleError as E,
    NativeVerificationRequest, TrustVcVerificationMode as Mode,
    retire_native_bundle_errors_observed,
};
use crate::ProofId;
use crate::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
use core::mem::{size_of, take};
mod scan;
mod storage;
#[cfg(test)]
mod tests;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;
#[derive(Default)]
struct State {
    ids: Vec<ProofId>,
    pending: Option<E>,
    errors: Vec<E>,
}
impl NativeVerificationBundle {
    /// Complete original final cross-request collision guard. Only the first
    /// physical importing/merging and discharging request for each obligation
    /// are named, and all collisions retain unsigned ascending obligation order.
    /// This DATA leaf neither replays nor admits any certificate or request.
    pub fn trust_vc_mode_collision_errors_observed<O: ExecutionObserver>(
        &self,
        s: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<Vec<E>> {
        let mut w = Work { session: s, site };
        w.admit(1, size_of::<State>() + size_of::<Work<'_, '_, O>>())?;
        let mut st = State::default();
        let result = st.run(&self.requests, &mut w);
        st.finish(result, &mut w)
    }
}
impl State {
    fn retire_scratch<O: ExecutionObserver>(&mut self, w: &mut Work<'_, '_, O>) {
        w.record(1, size_of::<Vec<ProofId>>());
        let mut ids = take(&mut self.ids);
        loop {
            w.record(1, size_of::<Option<ProofId>>());
            if ids.pop().is_none() {
                break;
            }
        }
        w.record(1, ids.capacity().saturating_mul(size_of::<ProofId>()));
        drop(ids);
        w.record(1, size_of::<Option<E>>());
        if let Some(e) = self.pending.take() {
            let _ = e.retire_observed(w.session, w.site);
        }
        w.poll();
    }
    fn finish<O: ExecutionObserver>(&mut self, result: R, w: &mut Work<'_, '_, O>) -> R<Vec<E>> {
        self.retire_scratch(w);
        match result.and_then(|()| w.publication(size_of::<Vec<E>>())) {
            Ok(()) => Ok(take(&mut self.errors)),
            Err(error) => {
                w.record(1, size_of::<Vec<E>>());
                let _ =
                    retire_native_bundle_errors_observed(take(&mut self.errors), w.session, w.site);
                Err(error)
            }
        }
    }
}
