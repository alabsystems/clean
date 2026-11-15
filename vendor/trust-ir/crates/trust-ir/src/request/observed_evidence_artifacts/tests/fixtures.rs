// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
#[derive(Clone, Copy)]
pub(super) enum Mode {
    Vc(Vc),
    Mc(Mc),
    Wp(Wp),
}
pub(super) fn modes() -> [Mode; 9] {
    [
        Mode::Vc(Vc::ImportProofCertificates),
        Mode::Vc(Vc::DischargeProofObligations),
        Mode::Vc(Vc::MergeProofCertificates),
        Mode::Mc(Mc::BoundedModelCheck),
        Mode::Mc(Mc::Chc),
        Mode::Mc(Mc::Pdr),
        Mode::Wp(Wp::WeakestPrecondition),
        Mode::Wp(Wp::StrongestPostcondition),
        Mode::Wp(Wp::Abduction),
    ]
}
pub(super) fn kinds() -> [Kind; 14] {
    use Kind::*;
    [
        TrustVcCertificateImport,
        TrustVcMergedCertificate,
        TrustMcHornClauses,
        TrustMcPdrTrace,
        TrustMcModel,
        TrustWpVerificationCondition,
        TrustWpReplayTrace,
        TrustWpAbducedPrecondition,
        ReplayTranscript,
        Other,
        Btor2Trace,
        Btor2Proof,
        NativeCompiledArtifact,
        BackendCapabilityMetadata,
    ]
}
pub(super) fn evidence(mode: Mode, artifacts: Vec<NativeEvidenceArtifact>) -> NativeEvidenceBundle {
    let request = NativeRequestId::new(19);
    let obligations = vec![];
    let verifier = NativeToolIdentity::new("not authenticated by this leaf");
    let solvers = vec![];
    let replay = ProofReplayIdentity::new("raw", "invocation");
    let trust_ir_module_digest = ProofDigest::sha256([3; 32]);
    let request_digest = ProofDigest::sha256([4; 32]);
    match mode {
        Mode::Vc(mode) => NativeEvidenceBundle::TrustVc(TrustVcNativeEvidenceBundle {
            request,
            mode,
            obligations,
            verifier,
            solvers,
            replay,
            trust_ir_module_digest,
            request_digest,
            artifacts,
        }),
        Mode::Mc(mode) => NativeEvidenceBundle::TrustMc(TrustMcNativeEvidenceBundle {
            request,
            mode,
            obligations,
            verifier,
            solvers,
            replay,
            trust_ir_module_digest,
            request_digest,
            artifacts,
        }),
        Mode::Wp(mode) => NativeEvidenceBundle::TrustWp(TrustWpNativeEvidenceBundle {
            request,
            mode,
            obligations,
            verifier,
            solvers,
            replay,
            trust_ir_module_digest,
            request_digest,
            artifacts,
        }),
    }
}
pub(super) fn artifact(name: impl Into<String>, kind: Kind) -> NativeEvidenceArtifact {
    NativeEvidenceArtifact::new(name, kind, ProofDigest::sha256([7; 32]))
}
pub(super) fn fixture() -> NativeEvidenceBundle {
    let mut bad = artifact(
        " \u{2003}\u{3000}\t".repeat(500),
        Kind::TrustVcCertificateImport,
    );
    bad.digest = ProofDigest {
        algorithm: ProofDigestAlgorithm::TrustIrStableV1,
        bytes: [0; 32],
    };
    let mut other = artifact("raw'\0λ🦀".repeat(700), Kind::TrustMcModel);
    other.digest = bad.digest;
    evidence(
        Mode::Vc(Vc::DischargeProofObligations),
        vec![bad.clone(), other.clone(), bad, other],
    )
}
