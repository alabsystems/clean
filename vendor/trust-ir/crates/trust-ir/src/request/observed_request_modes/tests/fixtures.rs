// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

#![allow(
    clippy::field_reassign_with_default,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
pub(super) fn mc() -> TrustMcNativeRequest {
    match crate::request::tests::native_bundle().requests.remove(1) {
        NativeVerificationRequest::TrustMc(r) => r,
        _ => panic!("MC fixture"),
    }
}
pub(super) fn wp() -> TrustWpNativeRequest {
    match crate::request::tests::native_bundle().requests.remove(2) {
        NativeVerificationRequest::TrustWp(r) => r,
        _ => panic!("WP fixture"),
    }
}
pub(super) fn atom(kind: NativeReplayAtomKind, sited: bool) -> NativeReplayAtom {
    NativeReplayAtom {
        id: NativeReplayAtomId::new(0),
        kind,
        formula: ProofFormula::smtlib2("ignored", "Bool"),
        payload_digest: ProofDigest::sha256([0; 32]),
        obligation: None,
        assertion_id: sited.then(|| NativeAssertionId::new(u32::MAX)),
        span: None,
    }
}
pub(super) fn bad() -> Input {
    let mut r = mc();
    r.mode = McMode::Pdr;
    r.options.chc.pdr.enabled = false;
    r.options.chc.emit_horn_clauses = false;
    r.options.chc.pdr.max_frames = Some(0);
    Input::Mc(r)
}
pub(super) fn bad_wp() -> Input {
    let mut r = wp();
    r.mode = WpMode::StrongestPostcondition;
    r.provenance.replay_context.atoms = vec![atom(NativeReplayAtomKind::Assertion, false); 12];
    r.options.emit_verification_conditions = false;
    Input::Wp(r)
}
pub(super) fn bad_diagnostics() -> Input {
    let mut p = NativeDiagnosticsPolicy::default();
    p.include_source_spans = false;
    p.include_lineage = false;
    p.emit_counterexamples = true;
    p.max_counterexamples = 0;
    Input::Diagnostics(NativeRequestId::new(u32::MAX), p)
}
