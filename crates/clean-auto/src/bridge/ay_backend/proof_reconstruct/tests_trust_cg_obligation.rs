// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Clean-side audit of the historical TrustCG overflow-carrier reflexivity
//! fragment.
//!
//! The reconstructed ay proof is a valid kernel term for the tautology
//! `not (= (bvadd a b) (bvadd a b)) -> False`.  That is deliberately not enough
//! to mint `CleanCic`: the C1 slice semantics (`Clean.BV`, `bvAdd`, and
//! `getBit`) are axiomatic and therefore outside the foundational authority
//! closure.  The rooted certification gate must reject the payload.  This
//! mirrors TrustCG production, where guard-replay authority remains unavailable
//! and the carrier rewrite stays disabled.

use super::certified_proof::{certify_reconstruction, false_expr, NotCertified};
use super::clean_cic::CleanCicLineage;
use super::theory_lemma_bv::reconstruct_bv_bitblast;
use super::{ReconstructionResult, ReconstructionStats};
use ay_proof::bv_blast_export::{export_bv_blast_proof, BvOp, SliceObligation};
use clean_kernel::bitvec_slice;
use clean_kernel::name::Name;
use clean_kernel::{
    BinderInfo, CertificationIssue, Declaration, Environment, Expr, FVarId, LocalContext,
    TypeChecker,
};

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
        .expect("slice operand");
    }
    env
}

fn lowering_add_reflexivity_reconstruction(
) -> (Environment, ReconstructionResult, LocalContext, Expr) {
    let env = slice_env();
    let proof = export_bv_blast_proof(SliceObligation::identical(BvOp::Add))
        .expect("identical bvadd reflexivity goal is UNSAT");
    let neg = FVarId::new(900);
    let rec = reconstruct_bv_bitblast(&proof, neg).expect("reconstruct add reflexivity");

    let mut ctx = LocalContext::new();
    ctx.push_with_id(
        neg,
        Name::from_string("h_neg"),
        rec.negated_goal.clone(),
        BinderInfo::Default,
    );

    let goal = rec.negated_goal;
    let result = ReconstructionResult {
        proof_term: Some(rec.proof_term),
        negated_goal_fvar: Some(neg),
        compound_witness_fvars: Vec::new(),
        derives_empty_clause: true,
        trust_subterm_count: 0,
        residual: crate::bridge::ay_backend::reconstruction_quality::ResidualTrustSummary::empty(),
        stats: ReconstructionStats::default(),
    };
    (env, result, ctx, goal)
}

#[test]
fn trust_cg_overflow_reflexivity_fails_closed_at_authority_boundary() {
    let (env, result, ctx, _goal) = lowering_add_reflexivity_reconstruction();
    let term = result.proof_term.as_ref().expect("reconstructed term");

    // The proof checker accepts the term at False in its local hypothesis
    // context.  Certification nevertheless requires foundational authority.
    let tc = TypeChecker::with_context(&env, ctx.clone());
    tc.check_type(term, &false_expr())
        .expect("reconstructed reflexivity refutation kernel-checks");

    let err = certify_reconstruction(&result, &env, &ctx)
        .expect_err("axiomatic BV semantics must not become CleanCic authority");
    assert!(matches!(
        err,
        NotCertified::AuthorityRejected { ref issues }
            if issues.iter().any(|issue| matches!(
                issue,
                CertificationIssue::NonFoundationalAxiom { name }
                    if name.to_string().starts_with("Clean.BV")
            ))
    ));
}

/// Lineage still distinguishes descriptor bytes, but remains diagnostic
/// metadata: no certified payload is minted and no consumer may treat this hash
/// as proof authority.
#[test]
fn trust_cg_lineage_digest_is_diagnostic_only() {
    let add_goal = {
        let a = Expr::const_str("a");
        let b = Expr::const_str("b");
        bitvec_slice::negated_goal(
            bitvec_slice::bv_binop(true, a.clone(), b.clone()),
            bitvec_slice::bv_binop(true, a, b),
        )
    };
    let sub_goal = {
        let a = Expr::const_str("a");
        let b = Expr::const_str("b");
        bitvec_slice::negated_goal(
            bitvec_slice::bv_binop(false, a.clone(), b.clone()),
            bitvec_slice::bv_binop(false, a, b),
        )
    };

    let encode = |goal: &Expr| {
        bincode::serde::encode_to_vec(goal, bincode::config::standard()).expect("serialize goal")
    };
    let add_lineage =
        CleanCicLineage::stable("trust_cg.overflow.signed_add.v1", &encode(&add_goal));
    let sub_lineage =
        CleanCicLineage::stable("trust_cg.overflow.signed_add.v1", &encode(&sub_goal));

    assert_ne!(
        add_lineage.bytes, sub_lineage.bytes,
        "different op descriptors must have different diagnostic lineage"
    );
}
