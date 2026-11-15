// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
impl State {
    pub(super) fn run<O: ExecutionObserver>(
        &mut self,
        b: &NativeVerificationBundle,
        w: &mut Work<'_, '_, O>,
    ) -> R {
        let mut at = 0;
        while let Some(e) = w.at(&b.evidence_bundles, at)? {
            self.row(b, e, at, w)?;
            w.next(&mut at)?;
        }
        Ok(())
    }
    fn row<O: ExecutionObserver>(
        &mut self,
        b: &NativeVerificationBundle,
        e: &NativeEvidenceBundle,
        at: usize,
        w: &mut Work<'_, '_, O>,
    ) -> R {
        w.admit(
            64,
            size_of::<NativeRequestId>() + size_of::<Suite>() + 2 * size_of::<u8>(),
        )?;
        let id = e.request();
        let suite = e.verifier_suite();
        if self.duplicate(b, e, at, w)? {
            self.fixed(|| E::DuplicateEvidenceBundle { request: id, suite }, w)?;
        }
        let Some(request) = self.last_request(b, id, w)? else {
            self.fixed(|| E::EvidenceRequestUnknown { request: id, suite }, w)?;
            return Ok(());
        };
        w.admit(
            64,
            2 * size_of::<Suite>() + 2 * size_of::<u8>() + size_of::<bool>(),
        )?;
        let expected = request.verifier_suite();
        if expected != suite
            || native_request_mode_tag(request) != native_evidence_bundle_mode_tag(e)
        {
            self.fixed(
                || E::EvidenceRequestMismatch {
                    request: id,
                    expected,
                    actual: suite,
                },
                w,
            )?;
        }
        w.admit(
            2 * size_of::<crate::ProofDigest>() + 2,
            2 * size_of::<crate::ProofDigest>() + size_of::<bool>(),
        )?;
        let actual = e.trust_ir_module_digest();
        let expected = b.trust_ir_module_digest;
        if actual != expected {
            self.fixed(
                || E::EvidenceTrustIrModuleDigestMismatch {
                    request: id,
                    expected,
                    actual,
                },
                w,
            )?;
        }
        w.admit(
            1,
            size_of::<R<crate::ProofDigest>>() + size_of::<crate::ProofDigest>(),
        )?;
        let expected = request.stable_digest_observed(w.session, w.site)?;
        w.admit(
            2 * size_of::<crate::ProofDigest>() + 2,
            2 * size_of::<crate::ProofDigest>() + size_of::<bool>(),
        )?;
        let actual = e.request_digest();
        if actual != expected {
            self.fixed(
                || E::EvidenceRequestDigestMismatch {
                    request: id,
                    expected,
                    actual,
                },
                w,
            )?;
        }
        self.children(request, e, w)
    }
    fn duplicate<O: ExecutionObserver>(
        &self,
        b: &NativeVerificationBundle,
        e: &NativeEvidenceBundle,
        end: usize,
        w: &mut Work<'_, '_, O>,
    ) -> R<bool> {
        w.admit(64, size_of::<NativeRequestId>() + 2 * size_of::<u8>())?;
        let key = (
            e.request(),
            native_evidence_bundle_variant_tag(e),
            native_evidence_bundle_mode_tag(e),
        );
        let mut at = 0;
        while at < end {
            let old = w
                .at(&b.evidence_bundles, at)?
                .ok_or(ObservedValueError::InvalidRange)?;
            w.admit(
                64,
                size_of::<NativeRequestId>() + 2 * size_of::<u8>() + size_of::<bool>(),
            )?;
            if (
                old.request(),
                native_evidence_bundle_variant_tag(old),
                native_evidence_bundle_mode_tag(old),
            ) == key
            {
                return Ok(true);
            }
            w.next(&mut at)?;
        }
        Ok(false)
    }
    fn last_request<'a, O: ExecutionObserver>(
        &self,
        b: &'a NativeVerificationBundle,
        id: NativeRequestId,
        w: &mut Work<'_, '_, O>,
    ) -> R<Option<&'a NativeVerificationRequest>> {
        w.admit(1, size_of::<usize>())?;
        let mut at = b.requests.len();
        loop {
            w.admit(1, size_of::<bool>())?;
            if at == 0 {
                return Ok(None);
            }
            w.admit(1, size_of::<usize>())?;
            at -= 1;
            let request = w
                .at(&b.requests, at)?
                .ok_or(ObservedValueError::InvalidRange)?;
            w.admit(8, size_of::<NativeRequestId>() + size_of::<bool>())?;
            if request.id() == id {
                return Ok(Some(request));
            }
        }
    }
}
