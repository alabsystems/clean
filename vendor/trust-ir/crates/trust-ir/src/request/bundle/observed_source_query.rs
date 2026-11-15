// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Query ONLY an existing sealed source capability; no mint/constructor.
use super::{NativeVerificationBundle, SourceGenerationAuthority};
use crate::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
use crate::{ProofDigest, request::NativeVerificationBundleError};
use core::mem::size_of;
mod storage;
#[cfg(test)]
mod tests;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;
type Validation = Result<(), Vec<NativeVerificationBundleError>>;
#[derive(Default)]
struct State {
    digest: Option<ProofDigest>,
    validation: Option<Validation>,
    answer: Option<bool>,
}
impl SourceGenerationAuthority {
    /// Exact ordinary authorizes_bundle query for an EXISTING sealed capability
    /// in a genuinely kernel-less core. Private nonce identity short-circuits
    /// before hashing; whole canonical bundle digest short-circuits before full
    /// actual validation. All three checks are required in that order.
    /// This method cannot construct, clone, transfer or mint authority. The
    /// caller still must establish the existing capability's trusted origin.
    /// No API is supplied in a clean-expr build pending real observed replay.
    pub fn authorizes_bundle_kernel_less_observed<O: ExecutionObserver>(
        &self,
        bundle: &NativeVerificationBundle,
        s: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<bool> {
        let mut w = Work { session: s, site };
        w.admit(1, size_of::<State>() + size_of::<Work<'_, '_, O>>())?;
        let mut st = State::default();
        let result = st.run(self, bundle, &mut w);
        st.finish(result, &mut w)
    }
}
impl State {
    fn run<O: ExecutionObserver>(
        &mut self,
        a: &SourceGenerationAuthority,
        b: &NativeVerificationBundle,
        w: &mut Work<'_, '_, O>,
    ) -> R {
        w.admit(
            4,
            size_of::<super::SourceGenerationLiveMarker>()
                + 2 * size_of::<&super::Arc<super::SourceGenerationNonce>>()
                + size_of::<bool>(),
        )?;
        if !b.source_generation_live.matches(&a.nonce) {
            self.set(false, w)?;
            return Ok(());
        }
        w.admit(
            1,
            size_of::<R<ProofDigest>>() + size_of::<Option<ProofDigest>>(),
        )?;
        self.digest = Some(b.stable_digest_observed(w.session, w.site)?);
        w.admit(34, 2 * size_of::<ProofDigest>() + size_of::<bool>())?;
        if self.digest != Some(a.bundle_digest) {
            self.set(false, w)?;
            return Ok(());
        }
        w.admit(
            1,
            size_of::<R<Validation>>() + size_of::<Option<Validation>>(),
        )?;
        self.validation = Some(b.validate_kernel_less_observed(w.session, w.site)?);
        w.admit(1, size_of::<bool>())?;
        self.set(matches!(&self.validation, Some(Ok(()))), w)
    }
    fn set<O: ExecutionObserver>(&mut self, answer: bool, w: &mut Work<'_, '_, O>) -> R {
        w.admit(1, size_of::<Option<bool>>())?;
        if self.answer.is_some() {
            return Err(ObservedValueError::InvalidRange);
        }
        self.answer = Some(answer);
        Ok(())
    }
    fn retire_scratch<O: ExecutionObserver>(&mut self, w: &mut Work<'_, '_, O>) {
        w.record(1, size_of::<Option<ProofDigest>>());
        let _ = self.digest.take();
        w.record(1, size_of::<Option<Validation>>() + size_of::<Validation>());
        if let Some(result) = self.validation.take() {
            let _ = NativeVerificationBundle::retire_kernel_less_validation_observed(
                result, w.session, w.site,
            );
        }
        w.poll();
    }
    fn finish<O: ExecutionObserver>(&mut self, result: R, w: &mut Work<'_, '_, O>) -> R<bool> {
        self.retire_scratch(w);
        match result.and_then(|()| w.publication()) {
            Ok(()) => self.answer.take().ok_or(ObservedValueError::InvalidRange),
            Err(error) => {
                w.record(1, size_of::<Option<bool>>());
                let _ = self.answer.take();
                Err(error)
            }
        }
    }
}
