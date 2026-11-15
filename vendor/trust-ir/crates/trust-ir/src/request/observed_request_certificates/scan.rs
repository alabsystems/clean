// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::known::Match;
use super::*;
impl<'m> State<'m> {
    pub(super) fn run<O: ExecutionObserver>(
        &mut self,
        b: &'m NativeVerificationBundle,
        index: usize,
        w: &mut Work<'_, '_, O>,
    ) -> R {
        let r = w
            .at(&b.requests, index)?
            .ok_or(ObservedValueError::InvalidRange)?;
        self.setup(b, r, w)?;
        w.admit(
            3,
            size_of::<NativeRequestId>()
                + size_of::<Suite>()
                + size_of::<&[ProofCertificateRef]>()
                + size_of::<&[ProofId]>(),
        )?;
        let id = r.id();
        let suite = r.verifier_suite();
        let certificates = r.certificates();
        let obligations = r.obligations();
        let mut at = 0;
        while let Some(c) = w.at(certificates, at)? {
            if Self::duplicate(certificates, at, c, w)? {
                self.named(id, c, names::Kind::Duplicate, w)?;
            }
            if !self.known(c, Match::Full, w)? {
                if self.known(c, Match::ObligationAndProver, w)? {
                    self.named(id, c, names::Kind::DigestMismatch, w)?;
                } else {
                    self.named(id, c, names::Kind::Missing, w)?;
                }
            }
            if !Self::requested(obligations, &c.obligation, w)? {
                self.fixed(
                    || E::CertificateObligationNotRequested {
                        request: id,
                        obligation: c.obligation,
                    },
                    w,
                )?;
            }
            w.admit(1, size_of::<R<bool>>())?;
            let bound = self
                .lineage
                .as_ref()
                .ok_or(ObservedValueError::InvalidRange)?
                .source_bound_certificate_contains_observed(c, w.session, w.site)?;
            if !bound {
                self.named(id, c, names::Kind::NotInLineage, w)?;
            }
            self.prepare(w)?;
            self.capture(c.verifier_suite_errors_observed(id, suite, w.session, w.site)?);
            self.flush(w)?;
            w.next(&mut at)?;
        }
        Ok(())
    }
    fn duplicate<O: ExecutionObserver>(
        rows: &[ProofCertificateRef],
        end: usize,
        c: &ProofCertificateRef,
        w: &mut Work<'_, '_, O>,
    ) -> R<bool> {
        let mut at = 0;
        loop {
            w.admit(1, size_of::<bool>())?;
            if at == end {
                return Ok(false);
            }
            let prior = w.at(rows, at)?.ok_or(ObservedValueError::InvalidRange)?;
            if w.pair_equal(prior, c)? {
                return Ok(true);
            }
            w.next(&mut at)?;
        }
    }
    fn requested<O: ExecutionObserver>(
        rows: &[ProofId],
        id: &ProofId,
        w: &mut Work<'_, '_, O>,
    ) -> R<bool> {
        let mut at = 0;
        while let Some(prior) = w.at(rows, at)? {
            w.admit(1, 2 * size_of::<ProofId>() + size_of::<bool>())?;
            if prior == id {
                return Ok(true);
            }
            w.next(&mut at)?;
        }
        Ok(false)
    }
}
