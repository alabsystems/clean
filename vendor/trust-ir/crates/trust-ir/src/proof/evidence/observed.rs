// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Actual complete canonical certificate identity, never replay authority.
use super::{
    CertificateBinding, CleanCicKernelRecheck, ProofCertificate, ProofCertificateRef, ProofDigest,
    ProofDigestAlgorithm, ProofEvidence,
};
use crate::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
use core::mem::{size_of, take};
mod binding;
mod encode;
#[cfg(test)]
mod error_precedence_tests;
mod lineage;
mod module_floor;
mod storage;
#[cfg(test)]
mod tests;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;
#[derive(Default)]
struct State {
    bytes: Vec<u8>,
    prover: String,
    reference: Option<ProofCertificateRef>,
}
impl ProofCertificate {
    /// Exact existing obligation/prover/evidence selector, not certification.
    /// Complete prover and returned reference stay parent-owned before every
    /// next admission, including cleanup and final publication. Both complete
    /// and partial output is drained after the original first refusal.
    pub fn lineage_ref_observed<O: ExecutionObserver>(
        &self,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<ProofCertificateRef> {
        let mut work = Work { session, site };
        work.admit(1, size_of::<State>() + size_of::<Work<'_, '_, O>>())?;
        let mut state = State::default();
        let result = state.reference(self, &mut work);
        state.finish_reference(result, &mut work)
    }
}
impl State {
    fn finish_reference<O: ExecutionObserver>(
        &mut self,
        result: R,
        work: &mut Work<'_, '_, O>,
    ) -> R<ProofCertificateRef> {
        self.retire_bytes(work);
        match result.and_then(|()| work.publication()) {
            Ok(()) => self
                .reference
                .take()
                .ok_or(ObservedValueError::InvalidRange),
            Err(error) => {
                self.retire(work);
                Err(work.terminal(error))
            }
        }
    }

    fn digest<O: ExecutionObserver>(
        &mut self,
        evidence: &ProofEvidence,
        work: &mut Work<'_, '_, O>,
    ) -> R<ProofDigest> {
        self.evidence(evidence, work)?;
        ProofDigest::sha256_domain_observed(
            "trust_ir.proof.evidence.v2",
            &self.bytes,
            work.session,
            work.site,
        )
    }
    fn reference<O: ExecutionObserver>(
        &mut self,
        certificate: &ProofCertificate,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(1, size_of::<ProofDigest>())?;
        let digest = self.digest(&certificate.evidence, work)?;
        work.text(&certificate.prover, &mut self.prover)?;
        work.admit(3, size_of::<ProofCertificateRef>() + size_of::<String>())?;
        self.reference = Some(ProofCertificateRef {
            obligation: certificate.obligation,
            prover: take(&mut self.prover),
            evidence_digest: digest,
        });
        Ok(())
    }
    fn retire_bytes<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        work.bytes(take(&mut self.bytes));
    }
    fn retire<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        self.retire_bytes(work);
        work.string(take(&mut self.prover));
        work.step(size_of::<Option<ProofCertificateRef>>().saturating_add(1));
        if let Some(reference) = self.reference.take() {
            work.step(size_of::<ProofCertificateRef>().saturating_add(1));
            work.string(reference.prover);
        }
        work.poll();
    }
}

impl ProofCertificateRef {
    /// Consume this exact data selector under its original caller. This does
    /// not revoke or establish proof authority; it retires owned text even
    /// after sticky refusal, then checks the original terminal publication.
    pub fn retire_observed<O: ExecutionObserver>(
        self,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R {
        let mut w = Work { session, site };
        w.step(size_of::<Self>().saturating_add(1));
        w.string(self.prover);
        w.session
            .admit(ExecutionProgress {
                phase: ExecutionPhase::Publication,
                site,
                work: 0,
                copy_bytes: 0,
            })
            .map_err(Into::into)
    }
}
