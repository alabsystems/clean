// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
impl State {
    pub(super) fn run<O: ExecutionObserver>(
        &mut self,
        b: &NativeVerificationBundle,
        w: &mut Work<'_, '_, O>,
    ) -> R {
        w.admit(
            1,
            size_of::<SourceGenerationLiveMarker>() + size_of::<bool>(),
        )?;
        if b.source_generation_live.0.is_some() {
            w.admit(1, size_of::<Mint>() + size_of::<Option<Mint>>())?;
            self.output = Some(Err(MintError::AlreadyMinted));
            return Ok(());
        }
        w.admit(
            1,
            size_of::<R<Validation>>() + size_of::<Option<Validation>>(),
        )?;
        self.validation = Some(b.validate_kernel_less_observed(w.session, w.site)?);
        w.admit(
            2,
            size_of::<bool>()
                + size_of::<Mint>()
                + size_of::<Option<Mint>>()
                + size_of::<Validation>(),
        )?;
        if let Err(rows) = self
            .validation
            .take()
            .ok_or(ObservedValueError::InvalidRange)?
        {
            self.output = Some(Err(MintError::InvalidBundle(rows)));
            return Ok(());
        }
        w.admit(
            1,
            size_of::<R<ProofDigest>>() + size_of::<Option<ProofDigest>>(),
        )?;
        self.digest = Some(b.stable_digest_observed(w.session, w.site)?);
        // Pinned std ArcInner<ZST> is repr(C,align(2)), two Atomic<usize>
        // headers plus this zero-sized private token. Logical fixed allocation
        // is prepaid; allocator/OOM/atomic physical latency is not bounded here.
        w.admit(
            8,
            2 * size_of::<usize>()
                + size_of::<SourceGenerationNonce>()
                + size_of::<Arc<SourceGenerationNonce>>()
                + size_of::<Option<Arc<SourceGenerationNonce>>>(),
        )?;
        self.nonce = Some(Arc::new(SourceGenerationNonce));
        w.admit(
            4,
            size_of::<SourceGenerationLiveMarker>()
                + size_of::<Option<SourceGenerationLiveMarker>>()
                + size_of::<Arc<SourceGenerationNonce>>(),
        )?;
        self.marker = Some(SourceGenerationLiveMarker(Some(Arc::clone(
            self.nonce
                .as_ref()
                .ok_or(ObservedValueError::InvalidRange)?,
        ))));
        w.admit(
            3,
            size_of::<SourceGenerationAuthority>()
                + size_of::<Mint>()
                + size_of::<Option<Mint>>()
                + size_of::<Option<Arc<SourceGenerationNonce>>>(),
        )?;
        let bundle_digest = self.digest.ok_or(ObservedValueError::InvalidRange)?;
        let nonce = self.nonce.take().ok_or(ObservedValueError::InvalidRange)?;
        self.output = Some(Ok(SourceGenerationAuthority {
            nonce,
            bundle_digest,
        }));
        Ok(())
    }
}
