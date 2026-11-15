// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
impl<'m> Members<'m> {
    pub(super) fn node<O: ExecutionObserver>(
        &mut self,
        node: &'m ProofLineageNode,
        w: &mut Work<'_, '_, O>,
    ) -> R {
        let mut at = 0;
        while let Some(id) = w.at(&node.obligations, at)? {
            w.insert(&mut self.obligations, id)?;
            w.next(&mut at)?;
        }
        at = 0;
        while let Some(reference) = w.at(&node.certificates, at)? {
            w.insert_certificate(&mut self.certificates, reference)?;
            w.next(&mut at)?;
        }
        w.insert(&mut self.sources, &node.source_module)?;
        Ok(())
    }
    pub(super) fn merge<O: ExecutionObserver>(
        &mut self,
        other: &Self,
        w: &mut Work<'_, '_, O>,
    ) -> R {
        let mut at = 0;
        while let Some(id) = w.at(&other.obligations, at)? {
            w.insert(&mut self.obligations, id)?;
            w.next(&mut at)?;
        }
        at = 0;
        while let Some(reference) = w.at(&other.certificates, at)? {
            w.insert_certificate(&mut self.certificates, reference)?;
            w.next(&mut at)?;
        }
        // Source-bound callers use only obligation/certificate memberships;
        // original source_bound_lineage_membership returns no source set.
        Ok(())
    }
    pub(super) fn retire<O: ExecutionObserver>(&mut self, w: &mut Work<'_, '_, O>) {
        w.rows(&mut self.obligations);
        w.rows(&mut self.certificates);
        w.rows(&mut self.sources);
    }
}
impl<O: ExecutionObserver> Work<'_, '_, O> {
    pub(super) fn has_certificate(
        &mut self,
        rows: &[&ProofCertificateRef],
        needle: &ProofCertificateRef,
    ) -> R<bool> {
        let mut at = 0;
        while let Some(row) = self.at(rows, at)? {
            if self.certificate(row, needle)? {
                return Ok(true);
            }
            self.next(&mut at)?;
        }
        Ok(false)
    }
    pub(super) fn insert_certificate<'m>(
        &mut self,
        rows: &mut Vec<&'m ProofCertificateRef>,
        reference: &'m ProofCertificateRef,
    ) -> R {
        if !self.has_certificate(rows, reference)? {
            self.push(rows, &reference)?;
        }
        Ok(())
    }
    fn certificate(&mut self, a: &ProofCertificateRef, b: &ProofCertificateRef) -> R<bool> {
        // Whole structural patterns intentionally fail compilation if the
        // actual raw reference schema gains a field. No normalized identity.
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
        Ok(self.equal(ao, bo)? && self.text_equal(ap, bp)? && self.equal(ad, bd)?)
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
            let bytes = end - at;
            self.admit(
                bytes
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
