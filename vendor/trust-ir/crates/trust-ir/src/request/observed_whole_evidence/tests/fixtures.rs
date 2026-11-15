// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
pub(super) fn provenance(r: &mut NativeVerificationRequest) -> &mut NativeRequestProvenance {
    match r {
        NativeVerificationRequest::TrustVc(r) => &mut r.provenance,
        NativeVerificationRequest::TrustMc(r) => &mut r.provenance,
        NativeVerificationRequest::TrustWp(r) => &mut r.provenance,
    }
}
pub(super) fn evidence(r: &NativeVerificationRequest, digest: ProofDigest) -> NativeEvidenceBundle {
    let request = r.id();
    let obligations = r.obligations().to_vec();
    let verifier = r.expected_verifier_identity().clone();
    let solvers = r.solver_identities().to_vec();
    let replay = r
        .provenance()
        .replay_identity()
        .cloned()
        .unwrap_or_else(|| ProofReplayIdentity::new("unknown", "invoke"));
    let trust_ir_module_digest = digest;
    let request_digest = r.stable_digest();
    let artifacts = vec![NativeEvidenceArtifact::new(
        "packet",
        NativeEvidenceArtifactKind::Other,
        ProofDigest::sha256([7; 32]),
    )];
    match r {
        NativeVerificationRequest::TrustVc(r) => {
            NativeEvidenceBundle::TrustVc(TrustVcNativeEvidenceBundle {
                request,
                mode: r.mode,
                obligations,
                verifier,
                solvers,
                replay,
                trust_ir_module_digest,
                request_digest,
                artifacts,
            })
        }
        NativeVerificationRequest::TrustMc(r) => {
            NativeEvidenceBundle::TrustMc(TrustMcNativeEvidenceBundle {
                request,
                mode: r.mode,
                obligations,
                verifier,
                solvers,
                replay,
                trust_ir_module_digest,
                request_digest,
                artifacts,
            })
        }
        NativeVerificationRequest::TrustWp(r) => {
            NativeEvidenceBundle::TrustWp(TrustWpNativeEvidenceBundle {
                request,
                mode: r.mode,
                obligations,
                verifier,
                solvers,
                replay,
                trust_ir_module_digest,
                request_digest,
                artifacts,
            })
        }
    }
}
pub(super) fn good() -> NativeVerificationBundle {
    let mut b = crate::request::tests::native_bundle();
    b.evidence_bundles = b
        .requests
        .iter()
        .map(|r| evidence(r, b.trust_ir_module_digest))
        .collect();
    b
}
pub(super) fn minimal() -> NativeVerificationBundle {
    let mut b = crate::request::tests::native_bundle();
    let mut r = b.requests.remove(1);
    let p = provenance(&mut r);
    p.expected_verifier = NativeToolIdentity::new("m");
    p.solvers = vec![NativeToolIdentity::new("s")];
    p.replay = Some(
        ProofReplayIdentity::new("m", "i").with_transcript_digest(ProofDigest::sha256([1; 32])),
    );
    b.requests = vec![r];
    b.evidence_bundles = vec![evidence(&b.requests[0], b.trust_ir_module_digest)];
    b
}
pub(super) fn mc(e: &mut NativeEvidenceBundle) -> &mut TrustMcNativeEvidenceBundle {
    match e {
        NativeEvidenceBundle::TrustMc(e) => e,
        _ => panic!("fixture is MC"),
    }
}
pub(super) fn bad() -> NativeVerificationBundle {
    let mut b = good();
    let m = mc(&mut b.evidence_bundles[1]);
    m.mode = TrustMcVerificationMode::Pdr;
    m.trust_ir_module_digest = ProofDigest::sha256([71; 32]);
    m.request_digest = ProofDigest::sha256([72; 32]);
    m.verifier.name = "WRONG.Native".into();
    m.verifier.version = Some(" ".into());
    m.solvers.clear();
    m.replay =
        ProofReplayIdentity::new("wrong", " ").with_transcript_digest(ProofDigest::sha256([0; 32]));
    m.obligations = vec![crate::ProofId::new(99)];
    m.artifacts = vec![
        NativeEvidenceArtifact::new(
            " ",
            NativeEvidenceArtifactKind::TrustVcMergedCertificate,
            ProofDigest {
                algorithm: crate::ProofDigestAlgorithm::TrustIrStableV1,
                bytes: [0; 32]
            }
        );
        2
    ];
    b.evidence_bundles.push(b.evidence_bundles[0].clone());
    b
}
pub(super) fn all_modes() -> Vec<NativeVerificationRequest> {
    let base = crate::request::tests::native_bundle();
    let mut out = Vec::new();
    for r in base.requests {
        match r {
            NativeVerificationRequest::TrustVc(r) => {
                for mode in [
                    TrustVcVerificationMode::ImportProofCertificates,
                    TrustVcVerificationMode::DischargeProofObligations,
                    TrustVcVerificationMode::MergeProofCertificates,
                ] {
                    let mut r = r.clone();
                    r.mode = mode;
                    out.push(NativeVerificationRequest::TrustVc(r));
                }
            }
            NativeVerificationRequest::TrustMc(r) => {
                for mode in [
                    TrustMcVerificationMode::BoundedModelCheck,
                    TrustMcVerificationMode::Chc,
                    TrustMcVerificationMode::Pdr,
                ] {
                    let mut r = r.clone();
                    r.mode = mode;
                    out.push(NativeVerificationRequest::TrustMc(r));
                }
            }
            NativeVerificationRequest::TrustWp(r) => {
                for mode in [
                    TrustWpVerificationMode::WeakestPrecondition,
                    TrustWpVerificationMode::StrongestPostcondition,
                    TrustWpVerificationMode::Abduction,
                ] {
                    let mut r = r.clone();
                    r.mode = mode;
                    out.push(NativeVerificationRequest::TrustWp(r));
                }
            }
        }
    }
    out
}
