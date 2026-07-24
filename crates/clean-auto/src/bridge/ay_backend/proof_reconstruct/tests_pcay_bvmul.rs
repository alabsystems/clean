// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Milestone-2 e2e: a real `bvmul` UNSAT obligation passes the kernel's exact
//! rooted certification authority, NATIVELY (Clean kernel reflection of the
//! array-multiplier bit-blast; no Carcara; no `bvMul_comm` axiom shortcut), plus
//! the fail-closed negative controls.

use super::*;
use ay_proof::bv_blast_solver::BvExpr;

/// The width the mul obligations bit-blast at. Width 8 = the gate leaf width the
/// existing mul-headline re-check uses; keeps the native kernel re-check tractable
/// (the shared gate cache fuses the widened readout to the bare multiply's output
/// bits, so the refutation is the short empty-clause derivation).
const W: u32 = 8;

/// MILESTONE 2 (positive): a real, gate-shaped `bvmul` widening no-overflow VC is
/// kernel-CERTIFIED under rooted authority, natively, with `trust_count == 0`. The FULL
/// shift-and-add array multiplier (partial-product `And2` + adder-tree
/// `Xor3`/`FullAdderCarry` gates) is bit-blasted and its refutation re-checked by
/// the Clean kernel; the certified `Unsat` judgment's complete dependency
/// closure passes exact foundation and declaration-provenance checks.
#[test]
fn bvmul_widening_no_overflow_is_kernel_certified_zero_trust() {
    let env = bvmul_certify_env().expect("env setup");
    let (lhs, rhs) = bvmul_widening_no_overflow_obligation("A0", "B0", W);
    let certified = certify_bvmul_unsat(&env, &lhs, &rhs)
        .expect("a real bvmul UNSAT VC must be kernel-Certified via native reflection");

    assert_eq!(
        certified.payload.trust_count, 0,
        "milestone-2 bvmul UNSAT must certify with ZERO trust in ay"
    );
    assert!(
        !certified.payload.term_bytes.is_empty(),
        "Certified payload must carry the serialized kernel Unsat term"
    );
    // The whole multiplier is materialised — a genuine gate-tree bit-blast, not a
    // 1-clause shortcut.
    assert!(
        certified.num_clauses > 100,
        "the full array multiplier must be bit-blasted (got {} clauses)",
        certified.num_clauses
    );
    assert!(
        certified.num_resolution_steps >= 1,
        "the refutation must carry at least one resolution step"
    );
}

/// Independently replay the exact rooted authority audit on the serialized term.
/// This checks much more than an axiom-name residue: goal inhabitation, full
/// declaration provenance/recheck state, exact canonical foundations, and the
/// complete type/value dependency closure.
#[test]
fn bvmul_certified_term_passes_rooted_authority() {
    let env = bvmul_certify_env().expect("env");
    let (lhs, rhs) = bvmul_widening_no_overflow_obligation("A0", "B0", W);
    let certified = certify_bvmul_unsat(&env, &lhs, &rhs).expect("must certify");

    let term = super::super::certified_proof::deserialize_term(&certified.payload.term_bytes)
        .expect("deserialize certified Unsat term");
    let goal = clean_kernel::TypeChecker::new(&env)
        .infer_type(&term)
        .expect("infer serialized certificate goal");
    let audit = env.audit_certification(&goal, &term);
    assert!(
        audit.is_certified(),
        "serialized bvmul certificate must pass exact rooted authority: {audit:#?}"
    );
}

/// A bvmul EQUALITY that is UNSAT for a different reason — `mul(X0, const 0)`
/// must equal `const 0` (multiply by zero), so `not(mul(X0,0) == 0)` is UNSAT —
/// also kernel-certifies natively. Exercises a second, distinct multiplier shape.
#[test]
fn bvmul_by_zero_identity_is_kernel_certified() {
    let env = bvmul_certify_env().expect("env");
    let x = BvExpr::leaf("X0", W);
    let lhs = BvExpr::Mul(Box::new(x), Box::new(BvExpr::const_val(0, W)));
    let rhs = BvExpr::const_val(0, W);
    let certified = certify_bvmul_unsat(&env, &lhs, &rhs)
        .expect("mul-by-zero identity is UNSAT and must kernel-certify");
    assert_eq!(certified.payload.trust_count, 0);
}

/// FAIL-CLOSED negative control (never false-PROVE): a SATISFIABLE bvmul
/// obligation — `not(mul(A0,B0) == add(A0,B0))` is SAT (multiply is genuinely
/// distinct from add) — must be DECLINED with `NoRefutation`, never certified.
/// This is the exact anti-vacuity guard: ay finds a model and refuses to
/// fabricate a proof, so the caller keeps the honest pre-certification verdict.
#[test]
fn satisfiable_bvmul_is_declined_fail_closed() {
    let env = bvmul_certify_env().expect("env");
    let a = BvExpr::leaf("A0", W);
    let b = BvExpr::leaf("B0", W);
    let lhs = BvExpr::Mul(Box::new(a.clone()), Box::new(b.clone()));
    let rhs = BvExpr::Add(Box::new(a), Box::new(b)); // mul != add ⇒ SATISFIABLE disequality.
    let outcome = certify_bvmul_unsat(&env, &lhs, &rhs);
    assert!(
        matches!(outcome, Err(BvMulCertifyError::NoRefutation)),
        "a satisfiable bvmul obligation must be declined (NoRefutation), never certified; \
         got {outcome:?}"
    );
}

/// FAIL-CLOSED negative control: an off-by-one scale (`mul(X0,2) == mul(X0,4)`)
/// is SATISFIABLE (they differ for most X0), so it must be declined — a wrong
/// bvmul relationship never certifies.
#[test]
fn wrong_bvmul_scale_is_declined_fail_closed() {
    let env = bvmul_certify_env().expect("env");
    let x = BvExpr::leaf("X0", W);
    let lhs = BvExpr::Mul(Box::new(x.clone()), Box::new(BvExpr::const_val(2, W)));
    let rhs = BvExpr::Mul(Box::new(x), Box::new(BvExpr::const_val(4, W)));
    let outcome = certify_bvmul_unsat(&env, &lhs, &rhs);
    assert!(
        matches!(outcome, Err(BvMulCertifyError::NoRefutation)),
        "a wrong bvmul scale relationship must be declined, got {outcome:?}"
    );
}
