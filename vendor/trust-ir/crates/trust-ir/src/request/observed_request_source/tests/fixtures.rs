// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
pub(super) fn fixture() -> (NativeVerificationBundle, NativeVerificationRequest) {
    let mut b = crate::request::tests::native_bundle();
    b.module.proof_certificates.clear();
    for o in &mut b.module.proof_obligations {
        o.status = ProofStatus::Pending;
    }
    let mut r = b.requests.remove(1);
    *ids(&mut r) = vec![ProofId::new(0), ProofId::new(1)];
    (b, r)
}
pub(super) fn ids(r: &mut NativeVerificationRequest) -> &mut Vec<ProofId> {
    match r {
        NativeVerificationRequest::TrustVc(r) => &mut r.obligations,
        NativeVerificationRequest::TrustMc(r) => &mut r.obligations,
        NativeVerificationRequest::TrustWp(r) => &mut r.obligations,
    }
}
pub(super) fn roots(r: &mut NativeVerificationRequest) -> &mut Vec<ProofLineageId> {
    match r {
        NativeVerificationRequest::TrustVc(r) => &mut r.lineage_roots,
        NativeVerificationRequest::TrustMc(r) => &mut r.lineage_roots,
        NativeVerificationRequest::TrustWp(r) => &mut r.lineage_roots,
    }
}
pub(super) fn function(r: &mut NativeVerificationRequest, id: Option<FuncId>) {
    match r {
        NativeVerificationRequest::TrustVc(r) => r.function = id,
        NativeVerificationRequest::TrustMc(r) => r.function = id.unwrap(),
        NativeVerificationRequest::TrustWp(r) => r.function = id.unwrap(),
    }
}
pub(super) fn bad() -> (NativeVerificationBundle, NativeVerificationRequest) {
    let (mut b, mut r) = fixture();
    *ids(&mut r) = vec![
        ProofId::new(1),
        ProofId::new(0),
        ProofId::new(1),
        ProofId::new(77),
    ];
    *roots(&mut r) = vec![
        ProofLineageId::new(0),
        ProofLineageId::new(99),
        ProofLineageId::new(0),
    ];
    function(&mut r, Some(FuncId::new(777)));
    b.input = NativeAdapterInput::RustMir {
        body_digest: ProofDigest::sha256([55; 32]),
    };
    let mut node = b.lineage.nodes[0].clone();
    node.target_module = ProofDigest::sha256([56; 32]);
    b.lineage.nodes.push(node);
    for source in &mut b.compiler_facts.obligation_sources {
        source.span = None;
        source.assertion_id = None;
        source.function = None;
    }
    (b, r)
}
