// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Exact verifier/solver-multiset/optional-replay DATA binding diagnostics.
use super::{
    NativeEvidenceBundle, NativeRequestId, NativeToolIdentity, NativeVerificationBundleError as E,
    NativeVerificationRequest, retire_native_bundle_errors_observed,
};
use crate::ProofReplayIdentity;
use crate::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
use core::mem::{size_of, take};
mod multiset;
mod storage;
#[cfg(test)]
mod tests;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;
#[derive(Default)]
struct State {
    pending: Option<E>,
    errors: Vec<E>,
}
impl NativeEvidenceBundle {
    /// Complete original provenance-binding errors. Verifier and optional
    /// replay use raw whole-record Eq; solver order is ignored but duplicate
    /// multiplicity is preserved. This does not execute/authenticate a tool,
    /// compare request digests or perform transcript replay.
    pub fn provenance_binding_errors_observed<O: ExecutionObserver>(
        &self,
        request: &NativeVerificationRequest,
        s: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<Vec<E>> {
        let mut w = Work { session: s, site };
        w.admit(1, size_of::<State>() + size_of::<Work<'_, '_, O>>())?;
        let mut st = State::default();
        let result = st.run(request, self, &mut w);
        st.finish(result, &mut w)
    }
}
impl State {
    pub(super) fn run<O: ExecutionObserver>(
        &mut self,
        request: &NativeVerificationRequest,
        evidence: &NativeEvidenceBundle,
        w: &mut Work<'_, '_, O>,
    ) -> R {
        w.admit(
            3,
            size_of::<NativeRequestId>()
                + 2 * size_of::<&NativeToolIdentity>()
                + size_of::<R<bool>>(),
        )?;
        let id = request.id();
        if !evidence.verifier().structural_eq_observed(
            request.expected_verifier_identity(),
            w.session,
            w.site,
        )? {
            self.mismatch(id, "verifier", w)?;
        }
        w.admit(
            2,
            2 * size_of::<&[NativeToolIdentity]>() + size_of::<R<bool>>(),
        )?;
        if !w.multiset(request.solver_identities(), evidence.solvers())? {
            self.mismatch(id, "solvers", w)?;
        }
        w.admit(
            2,
            size_of::<Option<&ProofReplayIdentity>>()
                + 2 * size_of::<&ProofReplayIdentity>()
                + size_of::<R<bool>>(),
        )?;
        if let Some(expected) = request.provenance().replay_identity()
            && !evidence
                .replay()
                .structural_eq_observed(expected, w.session, w.site)?
        {
            self.mismatch(id, "replay", w)?;
        }
        Ok(())
    }
    fn mismatch<O: ExecutionObserver>(
        &mut self,
        request: NativeRequestId,
        field: &'static str,
        w: &mut Work<'_, '_, O>,
    ) -> R {
        w.admit(1, size_of::<E>() + size_of::<Option<E>>())?;
        self.pending = Some(E::EvidenceProvenanceMismatch { request, field });
        w.reserve(&mut self.errors)?;
        w.admit(1, size_of::<E>() + size_of::<Option<E>>())?;
        self.errors.push(
            self.pending
                .take()
                .ok_or(ObservedValueError::InvalidRange)?,
        );
        Ok(())
    }
    fn retire_scratch<O: ExecutionObserver>(&mut self, w: &mut Work<'_, '_, O>) {
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
