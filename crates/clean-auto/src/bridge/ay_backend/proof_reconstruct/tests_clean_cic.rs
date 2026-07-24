// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the `CertifiedPayload` → `CleanCic` converter.

use super::super::certified_proof::{certify_reconstruction, CertifiedPayload};
use super::super::theory_lemma_bv::reconstruct_bv_bitblast;
use super::super::ReconstructionResult;
use super::super::ReconstructionStats;
use super::{to_clean_cic, CleanCicLineage};
use ay_proof::bv_blast_export::{export_bv_blast_proof, BvOp, SliceObligation};
use clean_kernel::bitvec_slice;
use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Declaration, Environment, Expr, FVarId, LocalContext};

fn slice_env() -> Environment {
    let mut env = Environment::new();
    env.init_bv_slice().expect("init_bv_slice");
    env.init_classical().expect("init_classical");
    let bv = Expr::const_str(bitvec_slice::names::BV);
    for n in ["a", "b"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(n),
            level_params: vec![],
            type_: bv.clone(),
        })
        .expect("operand");
    }
    env
}

fn certify_sub() -> (CertifiedPayload, Expr) {
    let env = slice_env();
    let proof = export_bv_blast_proof(SliceObligation::identical(BvOp::Sub)).unwrap();
    let neg = FVarId::new(700);
    let rec = reconstruct_bv_bitblast(&proof, neg).expect("reconstruct");
    let mut ctx = LocalContext::new();
    ctx.push_with_id(
        neg,
        Name::from_string("h_neg"),
        rec.negated_goal.clone(),
        BinderInfo::Default,
    );
    let result = ReconstructionResult {
        proof_term: Some(rec.proof_term),
        negated_goal_fvar: Some(neg),
        compound_witness_fvars: Vec::new(),
        derives_empty_clause: true,
        trust_subterm_count: 0,
        residual: crate::bridge::ay_backend::reconstruction_quality::ResidualTrustSummary::empty(),
        stats: ReconstructionStats::default(),
    };
    let payload = certify_reconstruction(&result, &env, &ctx).expect("certify");
    (payload, rec.negated_goal)
}

#[test]
fn test_to_clean_cic_carries_certified_bytes() {
    let (payload, goal) = certify_sub();
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
