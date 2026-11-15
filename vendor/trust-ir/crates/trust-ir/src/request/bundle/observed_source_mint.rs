// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Same conspicuous trusted-live-source issuer, kernel-less build only.
//! The candidate marker is never installed before the last fallible callback.
use super::{
    Arc, NativeVerificationBundle, SourceGenerationAuthority,
    SourceGenerationAuthorityMintError as MintError, SourceGenerationLiveMarker,
    SourceGenerationNonce,
};
use crate::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
use crate::{ProofDigest, request::NativeVerificationBundleError};
use core::mem::size_of;
mod issue;
mod retirement;
mod storage;
#[cfg(test)]
mod tests;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;
type Validation = Result<(), Vec<NativeVerificationBundleError>>;
type Mint = Result<SourceGenerationAuthority, MintError>;
#[derive(Default)]
struct State {
    validation: Option<Validation>,
    digest: Option<ProofDigest>,
    nonce: Option<Arc<SourceGenerationNonce>>,
    marker: Option<SourceGenerationLiveMarker>,
    output: Option<Mint>,
}
impl SourceGenerationAuthority {
    /// Consume this existing capability without resetting the bundle's private
    /// one-shot marker. The private zero-sized nonce has at most its original
    /// marker reference plus this non-Clone capability reference.
    pub fn retire_observed<O: ExecutionObserver>(
        self,
        s: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R {
        let mut w = Work { session: s, site };
        w.record(1, size_of::<Self>() + size_of::<Work<'_, '_, O>>());
        let Self {
            nonce,
            bundle_digest,
        } = self;
        w.release(nonce);
        w.record(1, size_of::<ProofDigest>());
        let _ = bundle_digest;
        w.terminal()
    }
    /// Observed counterpart of the SAME explicit semantic TCB issuer.
    ///
    /// # Trust boundary
    /// The caller MUST be the audited live compiler-source lowering boundary,
    /// exactly as required by mint_from_live_lowering. Never call for decoded,
    /// IPC, cached or otherwise unauthenticated bundles. This conspicuous safe
    /// method is an authority issuer and must be included in the same callsite
    /// gate; its observed validator does not establish live-source origin.
    ///
    /// Only available without clean-expr. Complete original validation and
    /// canonical digest precede a fresh private nonce. All candidates stay
    /// uninstalled through final publication. Refusal fully retires candidates
    /// and leaves the live bundle's one-shot marker untouched. After the final
    /// successful callback, only infallible private marker/capability transfer
    /// remains. Existing issuer and all enabled-kernel behavior are unchanged.
    pub fn mint_from_live_lowering_kernel_less_observed<O: ExecutionObserver>(
        bundle: &mut NativeVerificationBundle,
        s: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<Mint> {
        let mut w = Work { session: s, site };
        w.admit(1, size_of::<State>() + size_of::<Work<'_, '_, O>>())?;
        let mut st = State::default();
        let result = st.run(bundle, &mut w);
        st.finish(bundle, result, &mut w)
    }
}
impl State {
    fn ready<O: ExecutionObserver>(&self, w: &mut Work<'_, '_, O>) -> R {
        w.admit(
            8,
            size_of::<Option<Mint>>()
                + size_of::<Option<SourceGenerationLiveMarker>>()
                + size_of::<Option<Arc<SourceGenerationNonce>>>()
                + 4 * size_of::<bool>(),
        )?;
        if self.nonce.is_some() {
            return Err(ObservedValueError::InvalidRange);
        }
        match &self.output {
            Some(Ok(authority)) => {
                let Some(marker) = &self.marker else {
                    return Err(ObservedValueError::InvalidRange);
                };
                if !marker.matches(&authority.nonce) {
                    return Err(ObservedValueError::InvalidRange);
                }
                w.admit(
                    34,
                    2 * size_of::<ProofDigest>()
                        + size_of::<Option<ProofDigest>>()
                        + size_of::<bool>(),
                )?;
                if self.digest != Some(authority.bundle_digest) {
                    return Err(ObservedValueError::InvalidRange);
                }
            }
            Some(Err(_)) if self.marker.is_none() => {}
            _ => return Err(ObservedValueError::InvalidRange),
        }
        Ok(())
    }
    fn finish<O: ExecutionObserver>(
        &mut self,
        b: &mut NativeVerificationBundle,
        result: R,
        w: &mut Work<'_, '_, O>,
    ) -> R<Mint> {
        let result = result.and_then(|()| self.ready(w));
        self.retire_transient(w);
        let result = result.and_then(|()| w.publication());
        match result {
            Ok(()) => {
                // ready verified exact owning shapes before the final callback.
                // No observer/fallible operation separates install and return.
                if let Some(marker) = self.marker.take() {
                    b.source_generation_live = marker;
                }
                self.output.take().ok_or(ObservedValueError::InvalidRange)
            }
            Err(error) => {
                self.retire_candidates(w);
                Err(error)
            }
        }
    }
}
