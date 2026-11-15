// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[derive(Clone, Copy)]
enum Match {
    Complete,
    ObligationProver,
}

impl<'a> Checking<'a> {
    pub(super) fn against<O: ExecutionObserver>(
        &mut self,
        manifest: &ProofLineageManifest,
        obligations: &[ProofObligation],
        certificates: &'a [ProofCertificate],
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R {
        for obligation in obligations {
            admit(session, site, 1, 0)?;
            set_insert(&mut self.obligations, obligation.id, session, site)?;
        }
        for certificate in certificates {
            admit(session, site, 1, 0)?;
            let digest = certificate.evidence_digest_observed(session, site)?;
            push(&mut self.certificates, (certificate, digest), session, site)?;
        }
        for node in &manifest.nodes {
            admit(session, site, 1, 0)?;
            for obligation in &node.obligations {
                lookup(self.obligations.len(), session, site)?;
                if !self.obligations.contains(obligation) {
                    self.error(
                        ProofLineageError::UnknownObligation {
                            node: node.id,
                            obligation: *obligation,
                        },
                        session,
                        site,
                    )?;
                }
            }
            for certificate in &node.certificates {
                admit(session, site, 1, 0)?;
                if self.certificate_present(certificate, Match::Complete, session, site)? {
                    continue;
                }
                let identity =
                    self.certificate_present(certificate, Match::ObligationProver, session, site)?;
                let prover = copy_text(&certificate.prover, session, site)?;
                let error = if identity {
                    ProofLineageError::CertificateDigestMismatch {
                        node: node.id,
                        obligation: certificate.obligation,
                        prover,
                    }
                } else {
                    ProofLineageError::MissingCertificate {
                        node: node.id,
                        obligation: certificate.obligation,
                        prover,
                    }
                };
                self.error(error, session, site)?;
            }
        }
        Ok(())
    }
    fn certificate_present<O: ExecutionObserver>(
        &self,
        reference: &ProofCertificateRef,
        matching: Match,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<bool> {
        for (certificate, digest) in &self.certificates {
            admit(session, site, 1, 0)?;
            if certificate.obligation == reference.obligation
                && text_equal(&certificate.prover, &reference.prover, session, site)?
                && (matches!(matching, Match::ObligationProver)
                    || *digest == reference.evidence_digest)
            {
                return Ok(true);
            }
        }
        Ok(false)
    }
}
