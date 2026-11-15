// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
#[derive(Clone, Copy)]
enum Issue {
    NotDischarged(ProofStatus),
    Trusted,
}
impl State {
    pub(super) fn vc<O: ExecutionObserver>(
        &mut self,
        b: &NativeVerificationBundle,
        r: &TrustVcNativeRequest,
        w: &mut Work<'_, '_, O>,
    ) -> R {
        let mut at = 0;
        while let Some(reference) = w.at(&r.certificates, at)? {
            if let Some(trusted) = self.last_known(reference, w)? {
                if let Some(status) = Self::last_status(b, reference.obligation, w)? {
                    // cfg(not(clean-expr)): actual NativeProofAuthority replays
                    // NOTHING, even for strong public labels. No candidate set.
                    self.named(r, reference, Issue::NotDischarged(status), w)?;
                }
                w.admit(
                    2,
                    size_of::<TrustVcTrustedEvidencePolicy>() + 2 * size_of::<bool>(),
                )?;
                if r.options.trusted_evidence == TrustVcTrustedEvidencePolicy::Reject && trusted {
                    self.named(r, reference, Issue::Trusted, w)?;
                }
            }
            w.next(&mut at)?;
        }
        Ok(())
    }
    pub(super) fn last_status<O: ExecutionObserver>(
        b: &NativeVerificationBundle,
        id: ProofId,
        w: &mut Work<'_, '_, O>,
    ) -> R<Option<ProofStatus>> {
        w.admit(1, size_of::<usize>())?;
        let mut at = b.module.proof_obligations.len();
        loop {
            w.admit(1, size_of::<bool>())?;
            if at == 0 {
                return Ok(None);
            }
            w.admit(1, size_of::<usize>())?;
            at -= 1;
            let row = w
                .at(&b.module.proof_obligations, at)?
                .ok_or(ObservedValueError::InvalidRange)?;
            w.admit(1, 2 * size_of::<ProofId>() + size_of::<bool>())?;
            if row.id == id {
                w.admit(1, size_of::<Option<ProofStatus>>())?;
                return Ok(Some(row.status));
            }
        }
    }
    fn named<O: ExecutionObserver>(
        &mut self,
        r: &TrustVcNativeRequest,
        reference: &ProofCertificateRef,
        issue: Issue,
        w: &mut Work<'_, '_, O>,
    ) -> R {
        w.text(&reference.prover, &mut self.text)?;
        w.admit(
            1,
            size_of::<String>() + size_of::<E>() + size_of::<Option<E>>() + size_of::<Issue>(),
        )?;
        let prover = take(&mut self.text);
        self.pending = Some(match issue {
            Issue::NotDischarged(status) => E::TrustVcCertificateNotDischarged {
                request: r.id,
                obligation: reference.obligation,
                prover,
                status,
            },
            Issue::Trusted => E::TrustedCertificateRejected {
                request: r.id,
                obligation: reference.obligation,
                prover,
            },
        });
        self.emit(w)
    }
}
