// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
impl<'m> State<'m> {
    pub(super) fn setup<O: ExecutionObserver>(
        &mut self,
        b: &'m NativeVerificationBundle,
        r: &NativeVerificationRequest,
        w: &mut Work<'_, '_, O>,
    ) -> R {
        w.admit(3, 3 * size_of::<bool>())?;
        if self.reference.is_some() || !self.known.is_empty() || self.lineage.is_some() {
            return Err(ObservedValueError::InvalidRange);
        }
        let mut at = 0;
        while let Some(certificate) = w.at(&b.module.proof_certificates, at)? {
            w.admit(
                1,
                size_of::<R<ProofCertificateRef>>() + size_of::<Option<ProofCertificateRef>>(),
            )?;
            // Mandatory actual corrected bc661 child, DATA only. Capture the
            // whole owning reference before allocation/transport callbacks.
            self.reference = Some(certificate.lineage_ref_observed(w.session, w.site)?);
            w.reserve(&mut self.known)?;
            w.admit(
                1,
                size_of::<ProofCertificateRef>() + size_of::<Option<ProofCertificateRef>>(),
            )?;
            self.known.push(
                self.reference
                    .take()
                    .ok_or(ObservedValueError::InvalidRange)?,
            );
            w.next(&mut at)?;
        }
        w.admit(
            1,
            size_of::<R<NativeRequestLineage<'m>>>()
                + size_of::<Option<NativeRequestLineage<'m>>>()
                + size_of::<Option<crate::ProofDigest>>()
                + size_of::<&[crate::ProofLineageId]>(),
        )?;
        self.lineage = Some(b.lineage.request_lineage_observed(
            r.lineage_roots(),
            b.source_digest(),
            w.session,
            w.site,
        )?);
        Ok(())
    }
    pub(super) fn known<O: ExecutionObserver>(
        &self,
        c: &ProofCertificateRef,
        pair: Match,
        w: &mut Work<'_, '_, O>,
    ) -> R<bool> {
        let mut at = 0;
        while let Some(row) = w.at(&self.known, at)? {
            let found = match pair {
                Match::Full => w.reference_equal(row, c)?,
                Match::ObligationAndProver => w.pair_equal(row, c)?,
            };
            if found {
                return Ok(true);
            }
            w.next(&mut at)?;
        }
        Ok(false)
    }
}
#[derive(Clone, Copy)]
pub(super) enum Match {
    Full,
    ObligationAndProver,
}
