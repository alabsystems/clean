// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
impl State {
    pub(super) fn setup<O: ExecutionObserver>(
        &mut self,
        b: &NativeVerificationBundle,
        w: &mut Work<'_, '_, O>,
    ) -> R {
        w.admit(2, 2 * size_of::<bool>())?;
        if self.reference.is_some() || self.known.capacity() != 0 {
            return Err(ObservedValueError::InvalidRange);
        }
        let mut at = 0;
        while let Some(certificate) = w.at(&b.module.proof_certificates, at)? {
            w.admit(
                1,
                size_of::<R<ProofCertificateRef>>() + size_of::<Option<ProofCertificateRef>>(),
            )?;
            // Whole real evidence digest + prover is captured before any fee.
            self.reference = Some(certificate.lineage_ref_observed(w.session, w.site)?);
            w.admit(1, size_of::<bool>())?;
            let trusted = certificate.uses_trusted_evidence(); // actual fixed enum-tag test
            w.reserve(&mut self.known)?;
            w.admit(
                1,
                size_of::<Known>() + size_of::<Option<ProofCertificateRef>>(),
            )?;
            self.known.push(Known {
                reference: self
                    .reference
                    .take()
                    .ok_or(ObservedValueError::InvalidRange)?,
                trusted,
            });
            w.next(&mut at)?;
        }
        Ok(())
    }
    pub(super) fn last_known<O: ExecutionObserver>(
        &self,
        reference: &ProofCertificateRef,
        w: &mut Work<'_, '_, O>,
    ) -> R<Option<bool>> {
        w.admit(1, size_of::<usize>())?;
        let mut at = self.known.len();
        loop {
            w.admit(1, size_of::<bool>())?;
            if at == 0 {
                return Ok(None);
            }
            w.admit(1, size_of::<usize>())?;
            at -= 1;
            let row = w
                .at(&self.known, at)?
                .ok_or(ObservedValueError::InvalidRange)?;
            if w.reference_equal(&row.reference, reference)? {
                w.admit(1, size_of::<Option<bool>>())?;
                return Ok(Some(row.trusted));
            }
        }
    }
}
impl<O: ExecutionObserver> Work<'_, '_, O> {
    pub(super) fn reference_equal(
        &mut self,
        a: &ProofCertificateRef,
        b: &ProofCertificateRef,
    ) -> R<bool> {
        let ProofCertificateRef {
            obligation: ao,
            prover: ap,
            evidence_digest: ad,
        } = a;
        let ProofCertificateRef {
            obligation: bo,
            prover: bp,
            evidence_digest: bd,
        } = b;
        self.admit(1, 2 * size_of::<ProofId>() + size_of::<bool>())?;
        if ao != bo || !self.text_equal(ap, bp)? {
            return Ok(false);
        }
        self.admit(34, 2 * size_of::<crate::ProofDigest>() + size_of::<bool>())?;
        Ok(ad == bd)
    }
    fn text_equal(&mut self, a: &str, b: &str) -> R<bool> {
        self.admit(1, 2 * size_of::<usize>())?;
        if a.len() != b.len() {
            return Ok(false);
        }
        let mut at = 0;
        loop {
            self.admit(1, size_of::<bool>())?;
            if at == a.len() {
                return Ok(true);
            }
            self.admit(1, 2 * size_of::<&[u8]>() + size_of::<usize>())?;
            let end = at.saturating_add(1024).min(a.len());
            self.admit(
                (end - at)
                    .checked_mul(2)
                    .ok_or(ObservedValueError::CapacityOverflow)?,
                0,
            )?;
            if a.as_bytes()[at..end] != b.as_bytes()[at..end] {
                return Ok(false);
            }
            self.admit(1, size_of::<usize>())?;
            at = end;
        }
    }
}
