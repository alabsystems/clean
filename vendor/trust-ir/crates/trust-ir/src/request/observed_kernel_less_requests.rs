// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Complete original request checks ONLY in the actual kernel-less build.
//! No enabled-kernel API or candidate replay currency is supplied here.
use super::{
    NativeVerificationBundle, NativeVerificationBundleError as E, NativeVerificationRequest,
    TrustVcNativeRequest, TrustVcTrustedEvidencePolicy, retire_native_bundle_errors_observed,
};
use crate::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
use crate::{ProofCertificateRef, ProofId, ProofStatus};
use core::mem::{size_of, take};
use std::vec::IntoIter;
mod authority;
mod batch;
mod known;
mod scan;
mod storage;
#[cfg(test)]
mod tests;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;
struct Known {
    reference: ProofCertificateRef,
    trusted: bool,
}
#[derive(Default)]
struct State {
    known: Vec<Known>,
    reference: Option<ProofCertificateRef>,
    text: String,
    batch: Option<IntoIter<E>>,
    batch_capacity: usize,
    pending: Option<E>,
    errors: Vec<E>,
}
impl NativeVerificationBundle {
    /// Complete ordinary `validate_requests` diagnostics when `clean-expr` is
    /// disabled. That original build's NativeProofAuthority ALWAYS rejects,
    /// irrespective of status, non-empty kernel terms or self-bound metadata.
    /// This method does not exist in a kernel-enabled build. It never supplies
    /// full bundle/module/source admission or changes the ordinary validator.
    pub fn request_errors_kernel_less_observed<O: ExecutionObserver>(
        &self,
        s: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<Vec<E>> {
        let mut w = Work { session: s, site };
        w.admit(1, size_of::<State>() + size_of::<Work<'_, '_, O>>())?;
        let mut st = State::default();
        let result = st.run(self, &mut w);
        st.finish(result, &mut w)
    }
}
impl State {
    fn emit<O: ExecutionObserver>(&mut self, w: &mut Work<'_, '_, O>) -> R {
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
        self.retire_batch(w);
        w.record(1, size_of::<Option<ProofCertificateRef>>());
        if let Some(reference) = self.reference.take() {
            let _ = reference.retire_observed(w.session, w.site);
        }
        loop {
            w.record(1, size_of::<Option<Known>>() + size_of::<Known>());
            let Some(row) = self.known.pop() else { break };
            let _ = row.reference.retire_observed(w.session, w.site);
            w.record(1, size_of::<bool>());
        }
        w.record(1, size_of::<Vec<Known>>());
        let known = take(&mut self.known);
        w.record(1, known.capacity().saturating_mul(size_of::<Known>()));
        drop(known);
        w.record(1, size_of::<String>());
        w.text_drop(take(&mut self.text));
        w.record(1, size_of::<Option<E>>());
        if let Some(error) = self.pending.take() {
            let _ = error.retire_observed(w.session, w.site);
        }
        w.poll();
    }
    fn finish<O: ExecutionObserver>(&mut self, result: R, w: &mut Work<'_, '_, O>) -> R<Vec<E>> {
        self.retire_scratch(w);
        // Never replace an already-held local error with a later cleanup stop.
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
