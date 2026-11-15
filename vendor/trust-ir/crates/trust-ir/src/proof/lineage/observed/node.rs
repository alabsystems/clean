// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;

impl Checking<'_> {
    pub(super) fn node<O: ExecutionObserver>(
        &mut self,
        node: &ProofLineageNode,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R {
        for (field, value) in [
            ("name", &node.transform.name),
            ("producer", &node.transform.producer),
            ("version", &node.transform.version),
        ] {
            admit(session, site, 1, 0)?;
            if value.is_empty() {
                self.error(
                    ProofLineageError::EmptyTransformField {
                        node: node.id,
                        field,
                    },
                    session,
                    site,
                )?;
            }
        }
        for (field, digest) in [
            ("source_module", node.source_module),
            ("target_module", node.target_module),
        ] {
            admit(session, site, 1, 0)?;
            if digest.is_zero() {
                self.error(
                    ProofLineageError::EmptyDigest {
                        node: node.id,
                        field,
                    },
                    session,
                    site,
                )?;
            }
            if digest.algorithm != ProofDigestAlgorithm::Sha256 {
                self.error(
                    ProofLineageError::NonCryptographicDigest {
                        node: node.id,
                        field,
                    },
                    session,
                    site,
                )?;
            }
        }
        if node.transform.stage == ProofTransformStage::Replay && node.replay.is_none() {
            self.error(
                ProofLineageError::MissingReplayIdentity(node.id),
                session,
                site,
            )?;
        }
        if let Some(replay) = &node.replay {
            self.replay(node.id, replay, session, site)?;
        }
        if node.obligations.is_empty() {
            self.error(ProofLineageError::EmptyObligations(node.id), session, site)?;
        }
        for obligation in &node.obligations {
            admit(session, site, 1, 0)?;
            if !set_insert(&mut self.obligations, *obligation, session, site)? {
                self.error(
                    ProofLineageError::DuplicateObligation {
                        node: node.id,
                        obligation: *obligation,
                    },
                    session,
                    site,
                )?;
            }
        }
        self.certificates(node, session, site)?;
        retire_set(&mut self.obligations, session, site);
        admit(session, site, 1, 0)
    }
    fn certificates<O: ExecutionObserver>(
        &mut self,
        node: &ProofLineageNode,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R {
        for (position, certificate) in node.certificates.iter().enumerate() {
            admit(session, site, 1, 0)?;
            if certificate.evidence_digest.algorithm != ProofDigestAlgorithm::Sha256 {
                self.error(
                    ProofLineageError::NonCryptographicDigest {
                        node: node.id,
                        field: "certificate.evidence_digest",
                    },
                    session,
                    site,
                )?;
            }
            lookup(self.obligations.len(), session, site)?;
            if !self.obligations.contains(&certificate.obligation) {
                self.error(
                    ProofLineageError::CertificateObligationNotBound {
                        node: node.id,
                        obligation: certificate.obligation,
                    },
                    session,
                    site,
                )?;
            }
            let (mut identity, mut exact) = (false, false);
            for previous in &node.certificates[..position] {
                admit(session, site, 1, 0)?;
                if previous.obligation == certificate.obligation
                    && text_equal(&previous.prover, &certificate.prover, session, site)?
                {
                    identity = true;
                    exact |= previous.evidence_digest == certificate.evidence_digest;
                }
            }
            if identity {
                let prover = copy_text(&certificate.prover, session, site)?;
                self.error(
                    ProofLineageError::DuplicateCertificateIdentity {
                        node: node.id,
                        obligation: certificate.obligation,
                        prover,
                    },
                    session,
                    site,
                )?;
            }
            if exact {
                let prover = copy_text(&certificate.prover, session, site)?;
                self.error(
                    ProofLineageError::DuplicateCertificate {
                        node: node.id,
                        obligation: certificate.obligation,
                        prover,
                    },
                    session,
                    site,
                )?;
            }
        }
        Ok(())
    }
    fn replay<O: ExecutionObserver>(
        &mut self,
        id: ProofLineageId,
        replay: &ProofReplayIdentity,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R {
        for (field, value) in [
            ("engine", &replay.engine),
            ("invocation", &replay.invocation),
        ] {
            if blank(value, session, site)? {
                self.error(
                    ProofLineageError::InvalidReplayIdentity { node: id, field },
                    session,
                    site,
                )?;
            }
        }
        if let Some(digest) = replay.transcript_digest {
            admit(session, site, 1, 0)?;
            if digest.is_zero() {
                self.error(
                    ProofLineageError::InvalidReplayIdentity {
                        node: id,
                        field: "transcript_digest",
                    },
                    session,
                    site,
                )?;
            }
            if digest.algorithm != ProofDigestAlgorithm::Sha256 {
                self.error(
                    ProofLineageError::NonCryptographicDigest {
                        node: id,
                        field: "replay.transcript_digest",
                    },
                    session,
                    site,
                )?;
            }
        }
        Ok(())
    }
}
