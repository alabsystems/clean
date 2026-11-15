// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
pub(super) fn good() -> NativeVerificationBundle {
    let mut b = crate::request::tests::native_bundle();
    b.requests.retain(|r| r.id() != NativeRequestId::new(0));
    b.evidence_bundles
        .retain(|e| e.request() != NativeRequestId::new(0));
    let digest = b.module.stable_digest();
    b.trust_ir_module_digest = digest;
    for n in &mut b.lineage.nodes {
        if b.lineage.roots.contains(&n.id) {
            n.target_module = digest;
        }
    }
    for e in &mut b.evidence_bundles {
        match e {
            NativeEvidenceBundle::TrustVc(e) => e.trust_ir_module_digest = digest,
            NativeEvidenceBundle::TrustMc(e) => e.trust_ir_module_digest = digest,
            NativeEvidenceBundle::TrustWp(e) => e.trust_ir_module_digest = digest,
        }
    }
    b
}
pub(super) fn bad() -> NativeVerificationBundle {
    let mut b = good();
    b.schema_version = u32::MAX;
    b.provenance.producer_version.clear();
    b.serialization.canonical_order = false;
    b
}
pub(super) fn private_bound(b: &NativeVerificationBundle) -> usize {
    let mut o = Observer::default();
    let c = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut st = State::default();
    st.run(b, &mut w).unwrap();
    let end = c.get();
    st.retire_transient(&mut w);
    st.retire_candidates(&mut w);
    end
}
