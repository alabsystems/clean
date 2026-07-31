// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the `CertifiedPayload` → `CleanCic` converter.

use super::super::certified_proof::{certify_kernel_term, false_expr, CertifiedPayload};
use super::{to_clean_cic, CleanCicLineage};
use clean_kernel::bitvec_slice;
use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Environment, Expr, FVarId, LocalContext};

/// Mint a genuinely authority-audited payload without smuggling the old
/// domain-axiom-based BV fixture through the certification gate.
///
/// The converter test is about byte preservation, so a bound local assumption
/// is the smallest honest source payload: the context-closing audit turns this
/// into `False -> False`, whose proof is foundational. The BV reconstruction
/// and kernel-reflection paths have their own dedicated tests.
fn certify_bound_false() -> (CertifiedPayload, Expr) {
    let mut env = Environment::new();
    env.init_true_false().expect("init_true_false");
    let goal = false_expr();
    let hypothesis = FVarId::new(700);
    let mut ctx = LocalContext::new();
    ctx.push_with_id(
        hypothesis,
        Name::from_string("h_false"),
        goal.clone(),
        BinderInfo::Default,
    );
    let payload = certify_kernel_term(&Expr::fvar(hypothesis), &goal, &env, &ctx)
        .expect("bound foundational judgment certifies");
    (payload, goal)
}

#[test]
fn test_to_clean_cic_carries_certified_bytes() {
    let (payload, goal) = certify_bound_false();
    let lineage = CleanCicLineage::stable(
        "clean.bv.slice.v1",
        &bincode::serde::encode_to_vec(&goal, bincode::config::standard()).expect("ser goal"),
    );
    let cic = to_clean_cic(&payload, lineage);
    assert_eq!(cic.term, payload.term_bytes, "term bytes carried verbatim");
    assert_eq!(
        cic.context, payload.context_bytes,
        "context bytes carried verbatim"
    );
    assert_eq!(cic.lineage.algorithm, CleanCicLineage::TAG_STABLE_V1);
    assert_ne!(
        cic.lineage.bytes, [0u8; 32],
        "lineage digest is non-trivial"
    );
}

#[test]
fn test_lineage_binds_to_goal() {
    // Different goals ⇒ different lineage digests (a CleanCic minted for one
    // obligation cannot masquerade as another's).
    let g1 = {
        let a = Expr::const_str("a");
        let b = Expr::const_str("b");
        bitvec_slice::negated_goal(
            bitvec_slice::bv_binop(false, a.clone(), b.clone()),
            bitvec_slice::bv_binop(false, a, b),
        )
    };
    let g2 = {
        let a = Expr::const_str("a");
        let b = Expr::const_str("b");
        bitvec_slice::negated_goal(
            bitvec_slice::bv_binop(false, a.clone(), b.clone()),
            bitvec_slice::bv_binop(false, b, a),
        )
    };
    let d1 = CleanCicLineage::stable(
        "clean.bv.slice.v1",
        &bincode::serde::encode_to_vec(&g1, bincode::config::standard()).unwrap(),
    );
    let d2 = CleanCicLineage::stable(
        "clean.bv.slice.v1",
        &bincode::serde::encode_to_vec(&g2, bincode::config::standard()).unwrap(),
    );
    assert_ne!(
        d1.bytes, d2.bytes,
        "distinct obligations ⇒ distinct lineage"
    );
}

#[test]
fn test_lineage_deterministic() {
    let d1 = CleanCicLineage::stable("dom", b"payload");
    let d2 = CleanCicLineage::stable("dom", b"payload");
    assert_eq!(d1, d2, "lineage digest is deterministic across runs");
}
