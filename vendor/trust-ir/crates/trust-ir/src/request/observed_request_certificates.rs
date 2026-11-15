// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Complete original request-certificate attachment DATA diagnostic loop.
use super::{
    NativeRequestId, NativeRequestLineage, NativeVerificationBundle,
    NativeVerificationBundleError as E, NativeVerificationRequest, NativeVerifierSuite as Suite,
    retire_native_bundle_errors_observed,
};
use crate::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
use crate::{ProofCertificateRef, ProofId};
use core::mem::{size_of, take};
use std::vec::IntoIter;
mod batch;
mod known;
mod names;
mod scan;
mod storage;
#[cfg(test)]
mod tests;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;
#[derive(Default)]
struct State<'m> {
    lineage: Option<NativeRequestLineage<'m>>,
    known: Vec<ProofCertificateRef>,
    reference: Option<ProofCertificateRef>,
    text: String,
    pending: Option<E>,
    errors: Vec<E>,
    batch: Option<IntoIter<E>>,
    batch_capacity: usize,
}
impl NativeVerificationBundle {
    /// Complete actual per-request certificate DATA loop selected by physical
    /// request index. Module selectors are recomputed by the actual observed
    /// canonical evidence child; this never replays or admits a certificate.
    /// VC strong-status/trusted-evidence/kernel checks remain separate.
    pub fn request_certificate_errors_observed<'m, O: ExecutionObserver>(
        &'m self,
        index: usize,
        s: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<Vec<E>> {
        let mut w = Work { session: s, site };
        w.admit(1, size_of::<State<'m>>() + size_of::<Work<'_, '_, O>>())?;
        let mut st = State::default();
        let result = st.run(self, index, &mut w);
        st.finish(result, &mut w)
    }
}
impl State<'_> {
    fn fixed<O: ExecutionObserver>(
        &mut self,
        make: impl FnOnce() -> E,
        w: &mut Work<'_, '_, O>,
    ) -> R {
        w.admit(1, size_of::<E>() + size_of::<Option<E>>())?;
        self.pending = Some(make());
        self.emit(w)
    }
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
        w.record(
            1,
            size_of::<Option<ProofCertificateRef>>() + size_of::<ProofCertificateRef>(),
        );
        if let Some(reference) = self.reference.take() {
            let _ = reference.retire_observed(w.session, w.site);
        }
        loop {
            w.record(
                1,
                size_of::<Option<ProofCertificateRef>>() + size_of::<ProofCertificateRef>(),
            );
            let Some(reference) = self.known.pop() else {
                break;
            };
            let _ = reference.retire_observed(w.session, w.site);
        }
        w.record(1, size_of::<Vec<ProofCertificateRef>>());
        let known = take(&mut self.known);
        w.record(
            1,
            known
                .capacity()
                .saturating_mul(size_of::<ProofCertificateRef>()),
        );
        drop(known);
        w.record(
            1,
            size_of::<Option<NativeRequestLineage<'_>>>() + size_of::<NativeRequestLineage<'_>>(),
        );
        if let Some(lineage) = self.lineage.take() {
            let _ = lineage.retire_observed(w.session, w.site);
        }
        w.record(1, size_of::<String>());
        w.text_drop(take(&mut self.text));
        w.record(1, size_of::<Option<E>>());
        if let Some(e) = self.pending.take() {
            let _ = e.retire_observed(w.session, w.site);
        }
        self.retire_batch(w);
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
