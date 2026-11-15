// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
impl State {
    pub(super) fn retire_transient<O: ExecutionObserver>(&mut self, w: &mut Work<'_, '_, O>) {
        w.record(1, size_of::<Option<Validation>>() + size_of::<Validation>());
        if let Some(result) = self.validation.take() {
            let _ = NativeVerificationBundle::retire_kernel_less_validation_observed(
                result, w.session, w.site,
            );
        }
        w.record(1, size_of::<Option<ProofDigest>>());
        let _ = self.digest.take();
        w.poll();
    }
    pub(super) fn retire_candidates<O: ExecutionObserver>(&mut self, w: &mut Work<'_, '_, O>) {
        w.record(1, size_of::<Option<Mint>>() + size_of::<Mint>());
        if let Some(result) = self.output.take() {
            match result {
                Err(MintError::InvalidBundle(rows)) => {
                    let _ = crate::request::retire_native_bundle_errors_observed(
                        rows, w.session, w.site,
                    );
                }
                Err(MintError::AlreadyMinted) => {}
                Ok(SourceGenerationAuthority {
                    nonce,
                    bundle_digest,
                }) => {
                    w.release(nonce);
                    w.record(1, size_of::<ProofDigest>());
                    let _ = bundle_digest;
                }
            }
        }
        w.record(
            1,
            size_of::<Option<SourceGenerationLiveMarker>>()
                + size_of::<SourceGenerationLiveMarker>(),
        );
        if let Some(SourceGenerationLiveMarker(nonce)) = self.marker.take() {
            w.record(1, size_of::<Option<Arc<SourceGenerationNonce>>>());
            if let Some(nonce) = nonce {
                w.release(nonce);
            }
        }
        w.record(1, size_of::<Option<Arc<SourceGenerationNonce>>>());
        if let Some(nonce) = self.nonce.take() {
            w.release(nonce);
        }
        w.poll();
    }
}

impl MintError {
    /// Consume the whole ordinary inner issuance error, including all invalid
    /// bundle diagnostics, under the same original owner. No marker is reset.
    pub fn retire_observed<O: ExecutionObserver>(
        self,
        s: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R {
        let mut w = Work { session: s, site };
        w.record(1, size_of::<Self>() + size_of::<Work<'_, '_, O>>());
        match self {
            Self::InvalidBundle(rows) => {
                crate::request::retire_native_bundle_errors_observed(rows, w.session, w.site)
            }
            Self::AlreadyMinted => w.terminal(),
        }
    }
}
