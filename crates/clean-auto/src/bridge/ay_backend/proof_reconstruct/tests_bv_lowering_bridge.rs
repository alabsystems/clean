// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! THE HEADLINE: the COMPLETE fully-zero-trust lowering certificate. The real
//! width-4 commutativity `BvBlastProof` (28 vars, 131 clauses, 520 steps) yields a
//! kernel proof of `bvEq (bvAdd a b) (bvAdd b a)` (symbolic 4-bit a,b) whose
//! transitive axiom closure is ⊆ FOUNDATIONAL — assembled from the PROVED `Unsat`
//! reflection cert + the PROVED encoding-fidelity bridge (gate clauses + the
//! disequality clause routed through `xnorTrueImpEq` over the bit-blast OUTPUT
//! terms, NOT `bvAdd_comm`).

use super::certify_lowering_by_reflection;
use crate::bridge::ay_backend::proof_reconstruct::theory_lemma_bv_compute_blast::bv4_binop;
use ay_proof::bv_blast_export::Lit;
use ay_proof::bv_blast_solver::{export_bv_blast_proof_solved, SolvedObligation};
use clean_kernel::name::Name;
use clean_kernel::{bitvec_compute, Declaration, Environment, Expr, TypeChecker};

/// The width-4 lowering cert is a large reflection proof whose kernel `check_type`
/// retains tens of GB of `Definition` values. `cargo test` runs the crate's tests on
/// parallel threads in ONE process, so two of these heavy tests overlapping would sum
/// their footprints and OOM. This lock serializes them — each runs at one cert's peak.
static HEAVY_CERT_LOCK: std::sync::Mutex<()> = std::sync::Mutex::new(());

/// Env with the computational BV4 layer + Boolean model + classical, and two
/// symbolic `Clean.BV4` operands `a`, `b`.
fn bridge_env() -> (Environment, Expr, Expr) {
    let mut env = Environment::with_prelude();
    env.init_bv_compute().expect("init_bv_compute");
    env.init_bool_model().expect("init_bool_model");
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
    (
        bv4_binop(ob.op, ob.lhs_args, a, b),
        bv4_binop(ob.op, ob.rhs_args, a, b),
    )
}

#[test]
fn headline_width4_lowering_cert_is_fully_zero_trust() {
    let _guard = HEAVY_CERT_LOCK
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    let (env, a, b) = bridge_env();
    let proof = export_bv_blast_proof_solved(SolvedObligation::AddCommutes { width: 4 })
        .expect("width-4 commutativity is UNSAT, producer must export");
    proof.validate().expect("producer validates");
    // Genuine non-reflexive bit-blast: distinct output vars, full refutation.
    assert!(!proof.obligation.is_identical());
    assert!(
        proof.refutation.steps.len() > 100,
        "real ~520-step refutation"
    );

    let (lhs, rhs) = lhs_rhs(&proof, &a, &b);
    assert_ne!(lhs, rhs, "operand-swapped sides are syntactically distinct");

    let mut env = env;
    let bridge = certify_lowering_by_reflection(
        &mut env,
        &proof,
        &lhs,
        &rhs,
        &a,
        &b,
        "Clean.Demo.bvAddComm",
    )
    .unwrap_or_else(|e| panic!("lowering cert must kernel-check: {e}"));

    // The assembled term inhabits `bvEq (bvAdd a b) (bvAdd b a)` (re-check).
    {
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&bridge.bv_eq_term, &bridge.bv_eq_goal)
            .expect("re-check: assembled lowering cert type-checks");
    }

    // Register the assembled cert as a Theorem so we can audit its axiom closure.
    let cert_name = Name::from_string("Clean.Demo.bvAddCommLoweringCert");
    env.add_decl(Declaration::Theorem {
        name: cert_name.clone(),
        level_params: vec![],
        type_: bridge.bv_eq_goal.clone(),
        value: bridge.bv_eq_term.clone(),
    })
    .expect("assembled lowering cert must register as a kernel Theorem");
    let info = env.get_const(&cert_name).expect("registered");
    assert!(
        matches!(info.kind, clean_kernel::ConstantKind::Theorem),
        "lowering cert is a PROVED Theorem"
    );

    // HEADLINE: the assembled cert's transitive axiom closure is ⊆ FOUNDATIONAL.
    // `axiom_deps` returns only DOMAIN axioms (foundational ones are filtered out);
    // the symbolic operands `a`/`b` are the parameters being quantified, not
    // soundness axioms, so they are excluded from the soundness claim.
    let domain = env.axiom_deps(&cert_name).expect("axiom_deps");
    let non_foundational: Vec<String> = domain
        .iter()
        .map(std::string::ToString::to_string)
        .filter(|n| n != "a" && n != "b" && !is_foundational(n))
        .collect();
    assert!(
        non_foundational.is_empty(),
        "lowering cert must carry ZERO domain axioms; non-foundational: {non_foundational:?}"
    );

    eprintln!(
        "LOWERING CERT (width-4 commutativity): bvEq (bvAdd a b)(bvAdd b a) PROVED \
         zero-trust; gate clauses justified = {}",
        bridge.gate_clauses_proved
    );
    assert!(
        bridge.gate_clauses_proved > 0,
        "gate clauses kernel-justified"
    );
}

/// FOUNDATIONAL axioms: propext, Quot.sound, Classical.choice, plus the `Eq`/`Acc`
/// recursor built-ins. Anything else is a residual DOMAIN axiom.
fn is_foundational(n: &str) -> bool {
    matches!(
        n,
        "propext" | "Quot.sound" | "Classical.choice" | "Eq.refl" | "Eq.rec" | "Acc.rec"
    ) || n.starts_with("Quot.")
}

#[test]
fn fidelity_allsat_only_kernel_checks() {
    // Isolate + time the encoding-fidelity half: allSat (boolModel f_ab) <clauses>
    // kernel-type-checks (gate clauses from BV4 defs + disequality from Not(bvEq)).
    let _guard = HEAVY_CERT_LOCK
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    let (mut env, a, b) = bridge_env();
    let proof =
        export_bv_blast_proof_solved(SolvedObligation::AddCommutes { width: 4 }).expect("export");
    let (lhs, rhs) = lhs_rhs(&proof, &a, &b);
    let t0 = std::time::Instant::now();
    let (_p, _ty, _h) =
        super::build_and_check_all_sat(&mut env, &proof, &lhs, &rhs, &a, &b, "Clean.Demo.fidelity")
            .unwrap_or_else(|e| panic!("allSat fidelity proof must kernel-check: {e}"));
    eprintln!("FIDELITY allSat check time = {:?}", t0.elapsed());
}

#[test]
fn tampered_gate_clause_is_rejected_fail_closed() {
    // Flip one literal of a GATE (Tseitin) clause so it is no longer a tautology of its
    // gate. The input-split gate prover must refuse (`NotAGateTautology`) BEFORE the
    // heavy reduction — never fabricating a `clauseOr` proof. Exercises the new
    // gate-clause path's fail-closed guard directly (fast: fails at the gate clause).
    use ay_proof::bv_blast_export::ClauseProvenance;
    let (mut env, a, b) = bridge_env();
    let mut proof =
        export_bv_blast_proof_solved(SolvedObligation::AddCommutes { width: 4 }).expect("export");
    let (lhs, rhs) = lhs_rhs(&proof, &a, &b);
    // Find a gate clause and negate its first literal (breaks the gate tautology).
    let gate_idx = proof
        .clauses
        .iter()
        .position(|c| {
            matches!(c.provenance, ClauseProvenance::BitLemmaCnf { .. }) && !c.lits.is_empty()
        })
        .expect("a gate clause exists");
    proof.clauses[gate_idx].lits[0].neg = !proof.clauses[gate_idx].lits[0].neg;
    let msg = match certify_lowering_by_reflection(
        &mut env,
        &proof,
        &lhs,
        &rhs,
        &a,
        &b,
        "Clean.Demo.gatetamper",
    ) {
        Ok(_) => panic!("tampered gate clause must not yield a cert"),
        Err(e) => e.to_string(),
    };
    assert!(
        msg.contains("tautology") || msg.contains("rejected") || msg.contains("validate"),
        "rejection must cite the broken gate clause / validation, got: {msg}"
    );
}

#[test]
fn wrong_lowering_sat_obligation_yields_no_cert() {
    // A SAT obligation (sub anti-commutes is FALSE) must NOT produce a lowering cert:
    // the producer refuses to fabricate a refutation, so the bridge cannot be built.
    let res = export_bv_blast_proof_solved(SolvedObligation::SubAntiCommutesFalse { width: 4 });
    assert!(
        res.is_err(),
        "a SAT (false) obligation must yield NoRefutation, not a proof"
    );
}

#[test]
fn tampered_proof_is_rejected_no_cert() {
    // Corrupt a recorded resolvent so the Unsat reflection step no longer reduces to
    // true; the bridge must fail (producer validate or kernel rejection), never
    // emitting a bogus `bvEq` cert.
    let (mut env, a, b) = bridge_env();
    let mut proof =
        export_bv_blast_proof_solved(SolvedObligation::AddCommutes { width: 4 }).expect("export");
    let (lhs, rhs) = lhs_rhs(&proof, &a, &b);
    let mid = proof.refutation.steps.len() / 2;
    let bogus_var = proof.vars.roles.len() as u32 + 100;
    proof.refutation.steps[mid].clause = vec![Lit {
        var: bogus_var,
        neg: false,
    }];
    assert!(
        certify_lowering_by_reflection(&mut env, &proof, &lhs, &rhs, &a, &b, "Clean.Demo.tampered")
            .is_err(),
        "tampered proof must not yield a lowering cert"
    );
}
