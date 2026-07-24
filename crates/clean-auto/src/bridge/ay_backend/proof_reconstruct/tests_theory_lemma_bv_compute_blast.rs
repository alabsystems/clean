// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end zero-trust tests for the SOLVER-BACKED width-4 commutativity
//! refutation reconstructed over the computational `Clean.BV4` layer.
//!
//! THE HEADLINE: ay produces the width-4 `not(bvAdd(a,b) == bvAdd(b,a))`
//! refutation (~520 real resolution steps over SEPARATE output vars) → this
//! module reconstructs it to a kernel `False` proof with EVERY gate clause
//! kernel-PROVED from the BV4 definitions → `certify_reconstruction` yields
//! `trust_count == 0` → `check_type(_, False)` passes and round-trips.
//!
//! MUTATIONS: a FALSE identity (producer `NoRefutation`); and a tampered proof
//! closed against the WRONG goal (kernel rejects).

use super::{bv4_binop, reconstruct_bv_compute_blast};
use crate::bridge::ay_backend::proof_reconstruct::certified_proof::{
    certify_reconstruction, deserialize_term, false_expr, CertifiedPayload, NotCertified,
};
use crate::bridge::ay_backend::proof_reconstruct::ReconstructionResult;
use ay_proof::bv_blast_export::BvOp;
use ay_proof::bv_blast_solver::{export_bv_blast_proof_solved, SolvedObligation};
use clean_kernel::bitvec_compute;
use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Declaration, Environment, Expr, FVarId, LocalContext, TypeChecker};

/// Fresh env with the COMPUTATIONAL bv layer + two symbolic `Clean.BV4` operands.
fn compute_env() -> (Environment, Expr, Expr) {
    let mut env = Environment::with_prelude();
    env.init_bv_compute().expect("init_bv_compute");
    env.init_classical().expect("init_classical");
    for n in ["a", "b"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(n),
            level_params: vec![],
            type_: Expr::const_str(bitvec_compute::names::BV),
        })
        .expect("operand");
    }
    (env, Expr::const_str("a"), Expr::const_str("b"))
}

fn lhs_rhs(proof: &ay_proof::bv_blast_export::BvBlastProof, a: &Expr, b: &Expr) -> (Expr, Expr) {
    let ob = &proof.obligation;
    let lhs = bv4_binop(ob.op, ob.lhs_args, a, b);
    let rhs = bv4_binop(ob.op, ob.rhs_args, a, b);
    (lhs, rhs)
}

#[test]
fn headline_width4_commutativity_certifies_zero_trust_and_roundtrips() {
    let (env, a, b) = compute_env();
    let proof = export_bv_blast_proof_solved(SolvedObligation::AddCommutes { width: 4 })
        .expect("width-4 commutativity is UNSAT, producer must export");
    proof.validate().expect("producer proof validates");
    // Real non-reflexive refutation: separate output vars, many steps.
    assert!(!proof.obligation.is_identical());
    assert!(
        proof.refutation.steps.len() > 100,
        "real bit-blast, not a shortcut"
    );

    let (lhs, rhs) = lhs_rhs(&proof, &a, &b);
    // Non-reflexive: bvAdd a b and bvAdd b a are DISTINCT kernel terms.
    assert_ne!(lhs, rhs, "operand-swapped sides are syntactically distinct");

    let neg_fvar = FVarId::new(900);
    let rec = reconstruct_bv_compute_blast(&env, &proof, &lhs, &rhs, &a, &b, neg_fvar)
        .unwrap_or_else(|e| panic!("reconstruct_bv_compute_blast: {e}"));
    eprintln!("{}", rec.report());

    // Every gate clause kernel-proved (none assumed).
    let gate_clauses = proof
        .clauses
        .iter()
        .filter(|c| {
            matches!(
                c.provenance,
                ay_proof::bv_blast_export::ClauseProvenance::BitLemmaCnf { .. }
            )
        })
        .count();
    assert_eq!(
        rec.gate_clauses_proved, gate_clauses,
        "every BitLemmaCnf clause is kernel-justified"
    );
    assert!(rec.xor3_lemmas >= 1 && rec.maj_lemmas >= 1 && rec.xnor_lemmas >= 1);

    // The certified term is a GENUINE bit-blast resolution, NOT the wholesale
    // `h (bvAdd_comm a b)` shortcut: it must contain the disequality-clause
    // resolution structure (`litClash` discharging each pivot, `eqImpXnorTrue`
    // building the per-bit units, `boolEm`/`xnorTrueImpEq`/`notFalseImpTrue` in
    // the kernel-proved disequality clause). If a future refactor regresses to the
    // `bvAdd_comm`-only shortcut, these consts vanish and this assertion fails.
    let consts = collect_const_names(&rec.proof_term);
    for needed in [
        bitvec_compute::names::LIT_CLASH,
        bitvec_compute::names::EQ_IMP_XNOR_TRUE,
        bitvec_compute::names::BOOL_EM,
        bitvec_compute::names::XNOR_TRUE_IMP_EQ,
        bitvec_compute::names::BV_ADD_COMM,
    ] {
        assert!(
            consts.contains(needed),
            "certified term must consume the bit-blast resolution structure ({needed})"
        );
    }

    let mut ctx = LocalContext::new();
    ctx.push_with_id(
        neg_fvar,
        Name::from_string("h_neg"),
        rec.negated_goal.clone(),
        BinderInfo::Default,
    );

    // (e) Directly: the proof term kernel-checks to False.
    let tc = TypeChecker::with_context(&env, ctx.clone());
    tc.check_type(&rec.proof_term, &false_expr())
        .expect("solver-backed width-4 proof term must kernel-check to False");

    // Certify zero-trust through the same gate as every other path.
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
        .expect("width-4 commutativity must certify zero-trust");
    assert_eq!(payload.trust_count, 0, "CertifiedPayload trust_count == 0");

    // Round-trip.
    let term = deserialize_term(&payload.term_bytes).expect("term deserializes");
    let tc = TypeChecker::with_context(&env, ctx);
    tc.check_type(&term, &false_expr())
        .expect("deserialized term still kernel-checks to False");
}

/// MUTATION 1: a FALSE identity yields NO producer proof (nothing to reconstruct).
#[test]
fn mutation_false_identity_has_no_producer_proof() {
    let err = export_bv_blast_proof_solved(SolvedObligation::SubAntiCommutesFalse { width: 4 })
        .expect_err("anti-commutativity of bvsub is SAT; producer must refuse");
    assert_eq!(
        err,
        ay_proof::bv_blast_solver::BvSolvedExportError::NoRefutation
    );
}

/// MUTATION 2: the CORRECT proof term certified against the WRONG (operand order
/// preserved, i.e. non-commuted) goal is REJECTED by the kernel.
#[test]
fn mutation_wrong_goal_is_kernel_rejected() {
    let (env, a, b) = compute_env();
    let proof = export_bv_blast_proof_solved(SolvedObligation::AddCommutes { width: 4 }).unwrap();
    let (lhs, rhs) = lhs_rhs(&proof, &a, &b);
    let neg_fvar = FVarId::new(901);
    let rec = reconstruct_bv_compute_blast(&env, &proof, &lhs, &rhs, &a, &b, neg_fvar).unwrap();

    // WRONG goal: Not (bvEq (bvAdd a b) (bvAdd a b)) — a reflexive (always-true)
    // equality, so its negation is unprovable and the proof (which discharges the
    // real swapped goal) does not type-check against it.
    let wrong_goal = Expr::app(
        Expr::const_str("Not"),
        bitvec_compute::bv_eq(lhs.clone(), lhs.clone()),
    );
    let mut ctx = LocalContext::new();
    ctx.push_with_id(
        neg_fvar,
        Name::from_string("h_neg_wrong"),
        wrong_goal,
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
        other => panic!("wrong goal must be kernel-rejected, got {other:?}"),
    }
}

/// Collect the set of constant names referenced anywhere in `e`.
fn collect_const_names(e: &Expr) -> std::collections::HashSet<String> {
    use clean_kernel::ExprKind;
    let mut out = std::collections::HashSet::new();
    fn go(e: &Expr, out: &mut std::collections::HashSet<String>) {
        match e.kind() {
            ExprKind::Const(name, _) => {
                out.insert(name.to_string());
            }
            ExprKind::App(f, a) => {
                go(f, out);
                go(a, out);
            }
            ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
                go(ty, out);
                go(body, out);
            }
            ExprKind::Let(_, ty, val, body, _) => {
                go(ty, out);
                go(val, out);
                go(body, out);
            }
            ExprKind::Proj(_, _, inner) => go(inner, out),
            ExprKind::MData(_, inner) => go(inner, out),
            _ => {}
        }
    }
    go(e, &mut out);
    out
}
