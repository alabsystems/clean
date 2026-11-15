// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
pub(super) fn fixture() -> NativeVerificationBundle {
    let mut b = crate::request::tests::native_bundle();
    b.module.proof_certificates.clear();
    for o in &mut b.module.proof_obligations {
        o.status = ProofStatus::Pending;
    }
    b
}
pub(super) fn provenance(r: &mut NativeVerificationRequest) -> &mut NativeRequestProvenance {
    match r {
        NativeVerificationRequest::TrustVc(r) => &mut r.provenance,
        NativeVerificationRequest::TrustMc(r) => &mut r.provenance,
        NativeVerificationRequest::TrustWp(r) => &mut r.provenance,
    }
}
pub(super) fn ids(r: &mut NativeVerificationRequest) -> &mut Vec<ProofId> {
    match r {
        NativeVerificationRequest::TrustVc(r) => &mut r.obligations,
        NativeVerificationRequest::TrustMc(r) => &mut r.obligations,
        NativeVerificationRequest::TrustWp(r) => &mut r.obligations,
    }
}
pub(super) fn bad() -> NativeVerificationBundle {
    let mut b = fixture();
    let r = match &mut b.requests[1] {
        NativeVerificationRequest::TrustMc(r) => r,
        _ => panic!("MC"),
    };
    r.id = NativeRequestId::new(0);
    r.lineage_roots.clear();
    r.obligations = vec![ProofId::new(99), ProofId::new(1), ProofId::new(99)];
    r.diagnostics.include_source_spans = false;
    r.diagnostics.include_lineage = false;
    r.diagnostics.emit_counterexamples = true;
    r.diagnostics.max_counterexamples = 0;
    r.provenance.verifier_suite = Suite::TrustWp;
    r.provenance.expected_verifier = NativeToolIdentity::new("wrong").with_version(" ");
    r.provenance.solvers = vec![
        NativeToolIdentity::new(" "),
        NativeToolIdentity::new("\u{2003}"),
    ];
    r.provenance.replay = Some(
        ProofReplayIdentity::new("trust_vc", " ")
            .with_transcript_digest(ProofDigest::sha256([0; 32])),
    );
    let mut atom = NativeReplayAtom::assertion(
        NativeReplayAtomId::new(0),
        ProofFormula::smtlib2("true", "Bool"),
    );
    atom.formula.smtlib = Some("false".into());
    atom.payload_digest = ProofDigest::sha256([0; 32]);
    r.provenance.replay_context.atoms = vec![atom];
    r.provenance.replay_context.unsupported_modes = vec![NativeUnsupportedMode::new(
        NativeUnsupportedModeReason::Other,
        "actual unsupported",
    )];
    b
}
