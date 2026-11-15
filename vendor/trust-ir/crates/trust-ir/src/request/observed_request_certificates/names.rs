// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
#[derive(Clone, Copy)]
pub(super) enum Kind {
    Duplicate,
    DigestMismatch,
    Missing,
    NotInLineage,
}
impl State<'_> {
    pub(super) fn named<O: ExecutionObserver>(
        &mut self,
        id: NativeRequestId,
        c: &ProofCertificateRef,
        kind: Kind,
        w: &mut Work<'_, '_, O>,
    ) -> R {
        w.text(&c.prover, &mut self.text)?;
        w.admit(
            1,
            size_of::<String>() + size_of::<E>() + size_of::<Option<E>>(),
        )?;
        let prover = take(&mut self.text);
        self.pending = Some(match kind {
            Kind::Duplicate => E::DuplicateRequestCertificate {
                request: id,
                obligation: c.obligation,
                prover,
            },
            Kind::DigestMismatch => E::CertificateDigestMismatch {
                request: id,
                obligation: c.obligation,
                prover,
            },
            Kind::Missing => E::MissingCertificate {
                request: id,
                obligation: c.obligation,
                prover,
            },
            Kind::NotInLineage => E::CertificateNotInLineage {
                request: id,
                obligation: c.obligation,
                prover,
            },
        });
        self.emit(w)
    }
}
impl<O: ExecutionObserver> Work<'_, '_, O> {
    pub(super) fn pair_equal(
        &mut self,
        a: &ProofCertificateRef,
        b: &ProofCertificateRef,
    ) -> R<bool> {
        self.admit(1, 2 * size_of::<ProofId>() + size_of::<bool>())?;
        Ok(a.obligation == b.obligation && self.text_equal(&a.prover, &b.prover)?)
    }
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
