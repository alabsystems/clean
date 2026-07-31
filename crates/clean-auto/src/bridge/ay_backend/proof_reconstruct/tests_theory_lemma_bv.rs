// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end zero-trust tests for the C1 `bvsub`/`bvadd` equality slice.
//!
//! POSITIVE: a real `BvBlastProof` from `ay_proof::export_bv_blast_proof`
//! reconstructs to a kernel `False` proof that `check_type`s against the negated
//! slice goal.  The slice layer is axiomatic, so the rooted authority gate must
//! reject promotion to `Certified`; kernel type checking alone is not proof
//! authority.
//!
//! M2 (operand swap): the correct proof term, certified against the WRONG
//! (operand-swapped) obligation goal, is REJECTED by the kernel.
//!
//! Regression anchor: the existing gate-(d) trust-smuggling reject still holds
//! (covered in `tests_certified_proof.rs`; re-asserted here in miniature).

use super::super::certified_proof::{
    certify_reconstruction, deserialize_term, false_expr, CertifiedPayload, NotCertified,
};
use super::super::ReconstructionResult;
use super::{reconstruct_bv_bitblast, reconstruct_bv_compute_identity, BvComputeIdentity};
use ay_proof::bv_blast_export::{export_bv_blast_proof, BvOp, SliceObligation};
use clean_kernel::bitvec_compute;
use clean_kernel::bitvec_slice;
use clean_kernel::name::Name;
use clean_kernel::{
    BinderInfo, CertificationIssue, Declaration, Environment, Expr, FVarId, LocalContext,
    TypeChecker,
};

/// Fresh env with the slice layer + two free `BV` operands `a`, `b`.
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

/// Build a closed reconstruction result + context for an identical-operand op.
fn reconstruct_and_close(op: BvOp) -> (Environment, ReconstructionResult, LocalContext, Expr) {
    let env = slice_env();
    let ob = SliceObligation::identical(op);
    let proof = export_bv_blast_proof(ob).expect("producer emits proof for identical slice");

    let neg_fvar = FVarId::new(500);
    let rec = reconstruct_bv_bitblast(&proof, neg_fvar)
        .unwrap_or_else(|e| panic!("reconstruct_bv_bitblast: {e}"));

    // Sanity on the honesty report.
    assert_eq!(rec.resolution_steps, proof.refutation.steps.len());
    assert!(
        rec.xnor_lemmas_proved >= 1,
        "at least one XnorEq lemma must be proved by refl"
    );

    let mut ctx = LocalContext::new();
    ctx.push_with_id(
        neg_fvar,
        Name::from_string("h_neg"),
        rec.negated_goal.clone(),
        BinderInfo::Default,
    );

    let result = ReconstructionResult {
        proof_term: Some(rec.proof_term.clone()),
        negated_goal_fvar: Some(neg_fvar),
        compound_witness_fvars: Vec::new(),
        derives_empty_clause: true,
        trust_subterm_count: 0,
        residual: crate::bridge::ay_backend::reconstruction_quality::ResidualTrustSummary::empty(),
        stats: super::super::ReconstructionStats::default(),
    };

    (env, result, ctx, rec.negated_goal)
}

#[test]
fn test_bvsub_identical_slice_reconstructs_to_false() {
    let (env, _result, ctx, goal) = reconstruct_and_close(BvOp::Sub);
    let term = {
        let ob = SliceObligation::identical(BvOp::Sub);
        let proof = export_bv_blast_proof(ob).unwrap();
        reconstruct_bv_bitblast(&proof, FVarId::new(500))
            .unwrap()
            .proof_term
    };
    // Directly: the proof term type-checks to False in the closing context.
    let tc = TypeChecker::with_context(&env, ctx);
    tc.check_type(&term, &false_expr())
        .expect("bvsub identical-slice proof term must kernel-check to False");
    // And the goal really is Not (bvEq ...).
    assert!(goal.is_app(), "goal is an application of Not");
}

#[test]
fn test_bvsub_identical_slice_is_authority_rejected() {
    let (env, result, ctx, _goal) = reconstruct_and_close(BvOp::Sub);

    let err = certify_reconstruction(&result, &env, &ctx)
        .expect_err("axiomatic BV slice semantics must not certify");
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

#[test]
fn test_bvadd_identical_slice_is_authority_rejected() {
    let (env, result, ctx, _goal) = reconstruct_and_close(BvOp::Add);
    let err = certify_reconstruction(&result, &env, &ctx)
        .expect_err("axiomatic BV slice semantics must not certify");
    assert!(matches!(err, NotCertified::AuthorityRejected { .. }));
}

/// MUTATION M2: take the CORRECT proof term, attempt to certify it against the
/// WRONG (operand-swapped) obligation goal — the kernel must REJECT it.
#[test]
fn test_m2_operand_swap_goal_is_rejected_by_kernel() {
    // Correct proof for bvsub(a,b) == bvsub(a,b).
    let (env, mut result, _ctx, _goal) = reconstruct_and_close(BvOp::Sub);

    // Build the WRONG goal: Not (bvEq (bvSub a b) (bvSub b a)).
    let a = Expr::const_str("a");
    let b = Expr::const_str("b");
    let lhs = bitvec_slice::bv_binop(false, a.clone(), b.clone()); // bvSub a b
    let rhs = bitvec_slice::bv_binop(false, b, a); // bvSub b a (swapped)
    let wrong_goal = bitvec_slice::negated_goal(lhs, rhs);

    // Close against the WRONG goal in the same FVar slot.
    let neg_fvar = result.negated_goal_fvar.expect("has neg fvar");
    let mut wrong_ctx = LocalContext::new();
    wrong_ctx.push_with_id(
        neg_fvar,
        Name::from_string("h_neg_wrong"),
        wrong_goal,
        BinderInfo::Default,
    );
    // Keep all other gates satisfied so only the kernel can reject.
    result.derives_empty_clause = true;
    result.trust_subterm_count = 0;
    result.compound_witness_fvars = Vec::new();

    match certify_reconstruction(&result, &env, &wrong_ctx) {
        Err(NotCertified::KernelRejected { .. }) => {}
        Ok(_) => panic!("M2: correct proof must NOT certify against swapped goal"),
        other => panic!("M2: expected KernelRejected, got {other:?}"),
    }
}

/// Producer refuses the genuinely-SAT swapped obligation; reconstructor never
/// sees a bogus proof (no proof to smuggle).
#[test]
fn test_swapped_obligation_has_no_producer_proof() {
    let ob = SliceObligation {
        width: bitvec_slice::BV_SLICE_WIDTH,
        op: BvOp::Sub,
        lhs_args: [
            ay_proof::bv_blast_export::OperandRef::A,
            ay_proof::bv_blast_export::OperandRef::B,
        ],
        rhs_args: [
            ay_proof::bv_blast_export::OperandRef::B,
            ay_proof::bv_blast_export::OperandRef::A,
        ],
    };
    assert!(
        export_bv_blast_proof(ob).is_err(),
        "non-identical obligation must yield NoRefutation, not a proof"
    );
}

// ────────────────────────────────────────────────────────────────────────────
// Path-b NON-REFLEXIVE computational layer (`clean_kernel::bitvec_compute`).
// No ay/SAT: the `False` proof is the negated goal applied to a PROVED kernel
// theorem (`Clean.BV4.bvSub_self`), whose axiom closure is ⊆ foundational.
// ────────────────────────────────────────────────────────────────────────────

/// Fresh env with the COMPUTATIONAL bv layer + a local symbolic `Clean.BV4`
/// operand.  The operand is a context binder, not an environment axiom, so the
/// rooted authority audit closes it into the certified judgment.
fn compute_env() -> (Environment, LocalContext, Expr) {
    let mut env = Environment::with_prelude();
    env.init_bv_compute().expect("init_bv_compute");
    env.init_classical().expect("init_classical");
    let a_id = FVarId::new(650);
    let mut ctx = LocalContext::new();
    ctx.push_with_id(
        a_id,
        Name::from_string("a"),
        Expr::const_str(bitvec_compute::names::BV),
        BinderInfo::Default,
    );
    (env, ctx, Expr::fvar(a_id))
}

#[test]
fn test_bvsub_self_nonreflexive_certifies_zero_trust() {
    let (env, mut ctx, a) = compute_env();
    let neg_fvar = FVarId::new(700);
    let rec = reconstruct_bv_compute_identity(BvComputeIdentity::SubSelf, &a, neg_fvar);
    assert_eq!(rec.theorem, "Clean.BV4.bvSub_self");

    // The LHS (bvSub a a) and RHS (bvZero) inside the goal are DISTINCT terms.
    let lhs = Expr::apps(
        Expr::const_str(bitvec_compute::names::BV_SUB),
        [a.clone(), a.clone()],
    );
    let rhs = Expr::const_str(bitvec_compute::names::BV_ZERO);
    assert_ne!(lhs, rhs, "non-reflexive: bvSub a a != bvZero syntactically");

    ctx.push_with_id(
        neg_fvar,
        Name::from_string("h_neg"),
        rec.negated_goal.clone(),
        BinderInfo::Default,
    );

    // Directly: the proof term kernel-checks to False.
    let tc = TypeChecker::with_context(&env, ctx.clone());
    tc.check_type(&rec.proof_term, &false_expr())
        .expect("path-b non-reflexive proof term must kernel-check to False");

    // And it certifies zero-trust through the same gate as the slice path.
    let result = ReconstructionResult {
        proof_term: Some(rec.proof_term.clone()),
        negated_goal_fvar: Some(neg_fvar),
        compound_witness_fvars: Vec::new(),
        derives_empty_clause: true,
        trust_subterm_count: 0,
        residual: crate::bridge::ay_backend::reconstruction_quality::ResidualTrustSummary::empty(),
        stats: super::super::ReconstructionStats::default(),
    };
    let payload: CertifiedPayload = certify_reconstruction(&result, &env, &ctx)
        .expect("non-reflexive bvSub_self identity must certify zero-trust");
    assert_eq!(payload.trust_count, 0, "trust_count == 0 (no ay)");

    // Round-trip.
    let term = deserialize_term(&payload.term_bytes).expect("term deserializes");
    let tc = TypeChecker::with_context(&env, ctx);
    tc.check_type(&term, &false_expr())
        .expect("deserialized non-reflexive term still checks to False");

    // The backing theorem's transitive axiom closure is ⊆ foundational.
    let deps = env
        .axiom_deps(&Name::from_string("Clean.BV4.bvSub_self"))
        .expect("bvSub_self registered");
    assert!(
        deps.is_empty(),
        "bvSub_self axiom closure must be ⊆ foundational, got {deps:?}"
    );
}

#[test]
fn test_bvadd_zero_nonreflexive_certifies_zero_trust() {
    let (env, mut ctx, a) = compute_env();
    let neg_fvar = FVarId::new(701);
    let rec = reconstruct_bv_compute_identity(BvComputeIdentity::AddZero, &a, neg_fvar);

    ctx.push_with_id(
        neg_fvar,
        Name::from_string("h_neg"),
        rec.negated_goal.clone(),
        BinderInfo::Default,
    );
    let result = ReconstructionResult {
        proof_term: Some(rec.proof_term.clone()),
        negated_goal_fvar: Some(neg_fvar),
        compound_witness_fvars: Vec::new(),
        derives_empty_clause: true,
        trust_subterm_count: 0,
        residual: crate::bridge::ay_backend::reconstruction_quality::ResidualTrustSummary::empty(),
        stats: super::super::ReconstructionStats::default(),
    };
    let payload = certify_reconstruction(&result, &env, &ctx)
        .expect("non-reflexive bvAdd_zero identity must certify zero-trust");
    assert_eq!(payload.trust_count, 0);
}

/// MUTATION: a FALSE computational identity (`bvSub a a == a`) must NOT certify.
/// We build the `False` proof using the genuine `bvSub_self` term but close it
/// against the BOGUS negated goal `Not (bvEq (bvSub a a) a)`; the kernel rejects
/// it (the proof's actual conclusion is `bvEq (bvSub a a) bvZero`, not the bogus
/// goal), so certification fails closed.
#[test]
fn test_false_compute_identity_bvsub_self_eq_a_is_rejected() {
    let (env, mut ctx, a) = compute_env();
    let neg_fvar = FVarId::new(702);
    let rec = reconstruct_bv_compute_identity(BvComputeIdentity::SubSelf, &a, neg_fvar);

    // Bogus negated goal: Not (bvEq (bvSub a a) a).
    let lhs = Expr::apps(
        Expr::const_str(bitvec_compute::names::BV_SUB),
        [a.clone(), a.clone()],
    );
    let bogus_goal = Expr::app(
        Expr::const_str("Not"),
        bitvec_compute::bv_eq(lhs, a.clone()),
    );

    ctx.push_with_id(
        neg_fvar,
        Name::from_string("h_neg_bogus"),
        bogus_goal,
        BinderInfo::Default,
    );
    let result = ReconstructionResult {
        proof_term: Some(rec.proof_term.clone()),
        negated_goal_fvar: Some(neg_fvar),
        compound_witness_fvars: Vec::new(),
        derives_empty_clause: true,
        trust_subterm_count: 0,
        residual: crate::bridge::ay_backend::reconstruction_quality::ResidualTrustSummary::empty(),
        stats: super::super::ReconstructionStats::default(),
    };
    match certify_reconstruction(&result, &env, &ctx) {
        Err(NotCertified::KernelRejected { .. }) => {}
        other => panic!("false identity bvSub a a == a must be kernel-rejected, got {other:?}"),
    }
}

/// Regression anchor (gate d): a trust-bearing result never certifies, even if
/// every other gate passes — re-asserted on the real BV reconstruction.
#[test]
fn test_gate_d_trust_smuggle_still_rejected_on_bv() {
    let (env, mut result, ctx, _goal) = reconstruct_and_close(BvOp::Sub);
    result.trust_subterm_count = 1; // smuggle one trustedAy
    match certify_reconstruction(&result, &env, &ctx) {
        Err(NotCertified::TrustedSubterms { count }) => assert_eq!(count, 1),
        other => panic!("expected TrustedSubterms, got {other:?}"),
    }
}
