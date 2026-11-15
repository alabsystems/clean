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
pub(super) fn matched() -> (NativeVerificationRequest, NativeEvidenceBundle) {
    let r = crate::request::tests::native_bundle().requests.remove(1);
    let e = NativeEvidenceBundle::TrustMc(TrustMcNativeEvidenceBundle {
        request: r.id(),
        mode: TrustMcVerificationMode::Chc,
        obligations: vec![],
        verifier: r.expected_verifier_identity().clone(),
        solvers: r.solver_identities().to_vec(),
        replay: r.provenance().replay_identity().unwrap().clone(),
        trust_ir_module_digest: ProofDigest::sha256([1; 32]),
        request_digest: ProofDigest::sha256([2; 32]),
        artifacts: vec![],
    });
    (r, e)
}
pub(super) fn payload(e: &mut NativeEvidenceBundle) -> &mut TrustMcNativeEvidenceBundle {
    match e {
        NativeEvidenceBundle::TrustMc(b) => b,
        _ => panic!("fixture is MC"),
    }
}
pub(super) fn bad() -> (NativeVerificationRequest, NativeEvidenceBundle) {
    let (mut r, mut e) = matched();
    let p = provenance(&mut r);
    p.solvers = vec![
        NativeToolIdentity::new("a"),
        NativeToolIdentity::new("a"),
        NativeToolIdentity::new("b"),
    ];
    let b = payload(&mut e);
    b.verifier.name = "wrong".into();
    b.solvers = vec![
        NativeToolIdentity::new("a"),
        NativeToolIdentity::new("b"),
        NativeToolIdentity::new("b"),
    ];
    b.replay.invocation = "different".into();
    (r, e)
}
