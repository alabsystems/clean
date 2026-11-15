// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
#[derive(Clone, Copy)]
pub(super) enum Fault {
    Invalid(&'static str),
    Duplicate,
}
impl State {
    pub(super) fn run<O: ExecutionObserver>(
        &mut self,
        evidence: &NativeEvidenceBundle,
        w: &mut Work<'_, '_, O>,
    ) -> R {
        w.admit(
            3,
            size_of::<super::super::NativeRequestId>()
                + size_of::<super::super::NativeVerifierSuite>()
                + size_of::<&[NativeEvidenceArtifact]>(),
        )?;
        let request = evidence.request();
        let suite = evidence.verifier_suite();
        let artifacts = evidence.artifacts();
        w.admit(1, size_of::<bool>())?;
        if artifacts.is_empty() {
            w.admit(1, size_of::<E>() + size_of::<Option<E>>())?;
            self.pending = Some(E::MissingEvidenceArtifacts { request, suite });
            self.emit(w)?;
        }
        let mut at = 0;
        while let Some(artifact) = w.at(artifacts, at)? {
            self.row(evidence, artifacts, at, artifact, w)?;
            w.next(&mut at)?;
        }
        Ok(())
    }
    fn row<O: ExecutionObserver>(
        &mut self,
        evidence: &NativeEvidenceBundle,
        artifacts: &[NativeEvidenceArtifact],
        at: usize,
        artifact: &NativeEvidenceArtifact,
        w: &mut Work<'_, '_, O>,
    ) -> R {
        if w.blank(&artifact.name)? {
            self.named(evidence, artifact, Fault::Invalid("name"), w)?;
        }
        w.admit(40, size_of::<bool>())?;
        if artifact.digest.is_zero() {
            self.named(evidence, artifact, Fault::Invalid("digest"), w)?;
        }
        w.admit(1, size_of::<bool>())?;
        if artifact.digest.algorithm != ProofDigestAlgorithm::Sha256 {
            self.named(evidence, artifact, Fault::Invalid("digest.algorithm"), w)?;
        }
        if self.earlier(artifacts, at, &artifact.name, w)? {
            self.named(evidence, artifact, Fault::Duplicate, w)?;
        }
        // The retained ordinary helper is a complete finite match over three
        // bundle variants, three modes each and fixed artifact-kind tags. It
        // never reads strings, bytes, lists or any external authority.
        w.admit(512, size_of::<bool>())?;
        if !evidence_artifact_matches_bundle(evidence, artifact.kind) {
            w.admit(1, size_of::<E>() + size_of::<Option<E>>())?;
            self.pending = Some(E::EvidenceArtifactSuiteMismatch {
                request: evidence.request(),
                suite: evidence.verifier_suite(),
                kind: artifact.kind,
            });
            self.emit(w)?;
        }
        Ok(())
    }
    fn earlier<O: ExecutionObserver>(
        &mut self,
        artifacts: &[NativeEvidenceArtifact],
        end: usize,
        name: &str,
        w: &mut Work<'_, '_, O>,
    ) -> R<bool> {
        let mut at = 0;
        while at < end {
            let old = w
                .at(artifacts, at)?
                .ok_or(ObservedValueError::InvalidRange)?;
            if w.equal(&old.name, name)? {
                return Ok(true);
            }
            w.next(&mut at)?;
        }
        Ok(false)
    }
    pub(super) fn named<O: ExecutionObserver>(
        &mut self,
        evidence: &NativeEvidenceBundle,
        artifact: &NativeEvidenceArtifact,
        fault: Fault,
        w: &mut Work<'_, '_, O>,
    ) -> R {
        w.text(&artifact.name, &mut self.text)?;
        w.admit(
            1,
            size_of::<E>() + size_of::<Option<E>>() + size_of::<String>(),
        )?;
        let name = take(&mut self.text);
        let request = evidence.request();
        self.pending = Some(match fault {
            Fault::Invalid(field) => E::InvalidEvidenceArtifact {
                request,
                name,
                field,
            },
            Fault::Duplicate => E::DuplicateEvidenceArtifact { request, name },
        });
        self.emit(w)
    }
}
