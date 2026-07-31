// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Milestone-3 e2e: a real `bvshl` / `bvlshr` / `bvashr` UNSAT obligation is
//! kernel-CERTIFIED under exact rooted authority, NATIVELY (Clean kernel reflection of the
//! barrel-shifter bit-blast; no Carcara; no shift axiom), plus the fail-closed
//! negative controls (satisfiable, wrong-shift, and the signed-vs-unsigned bug
//! class). Reuses the OP-AGNOSTIC reflection family — the same reflection
//! milestone 2's bvmul certification uses (here the sub-quadratic trie variant).

use super::super::pcay_bvmul::bvmul_certify_env;
use super::*;
use ay_proof::bv_blast_solver::BvExpr;

/// The always-on HEADLINE operand width for shift certification. A width-4
/// variable barrel shift exercises the full gate tree through the sub-quadratic
/// trie reflection (`checkRefutes3_sound`).
const W: u32 = 4;

/// A LIGHTER width for the second/third shift-kind positives (`bvlshr`/`bvashr`),
/// so the three heavy kernel reflections don't OOM when the harness runs them
/// concurrently. A width-2 barrel shift is the same genuine gate tree over a
/// smaller operand.
const W_LIGHT: u32 = 2;

/// The reused resolution-soundness environment (identical layer to milestone 2).
fn env() -> Environment {
    bvmul_certify_env().expect("env setup")
}

/// MILESTONE 3 (positive HEADLINE, `bvshl` @ width 4): a real, gate-shaped
/// logical-shift-left identity VC is kernel-CERTIFIED under rooted authority,
/// natively, with `trust_count == 0`. The FULL barrel shifter (conditional constant-shift layers +
/// over-shift saturation mux) is bit-blasted and its refutation re-checked by the
/// Clean kernel via the OP-AGNOSTIC reflection. (~30 s single-threaded.)
#[test]
fn bvshl_identity_is_kernel_certified_zero_trust() {
    let env = env();
    let (lhs, rhs) = bvshift_identity_obligation(
        |value, amount| BvExpr::Shl(Box::new(value), Box::new(amount)),
        "V0",
        "S0",
        W,
    );
    let certified = certify_bvshift_unsat(&env, &lhs, &rhs)
        .expect("a real bvshl UNSAT VC must be kernel-Certified via native reflection");

    assert_eq!(
        certified.payload.trust_count, 0,
        "milestone-3 bvshl UNSAT must certify with ZERO trust in ay"
    );
    assert!(
        !certified.payload.term_bytes.is_empty(),
        "Certified payload must carry the serialized kernel Unsat term"
    );
    // The whole barrel shifter is materialised — a genuine gate-tree bit-blast.
    assert!(
        certified.num_clauses > 50,
        "the full barrel shifter must be bit-blasted (got {} clauses)",
        certified.num_clauses
    );
    assert!(
        certified.num_resolution_steps >= 1,
        "the refutation must carry at least one resolution step"
    );

    // Independently replay the exact rooted authority check inline so the heavy
    // width-4 reflection runs only once. This checks the complete type/value
    // dependency closure, provenance, and exact canonical foundations.
    let term = super::super::certified_proof::deserialize_term(&certified.payload.term_bytes)
        .expect("deserialize certified Unsat term");
    let goal = clean_kernel::TypeChecker::new(&env)
        .infer_type(&term)
        .expect("infer serialized certificate goal");
    let audit = env.audit_certification(&goal, &term);
    assert!(
        audit.is_certified(),
        "serialized bvshift certificate must pass exact rooted authority: {audit:#?}"
    );
}

/// MILESTONE 3 (positive, `bvlshr` @ width 2): logical (zero-filling) shift-right
/// identity certifies natively under rooted authority.
#[test]
fn bvlshr_identity_is_kernel_certified_zero_trust() {
    let env = env();
    let (lhs, rhs) = bvshift_identity_obligation(BvExpr::lshr, "V0", "S0", W_LIGHT);
    let certified = certify_bvshift_unsat(&env, &lhs, &rhs)
        .expect("a real bvlshr UNSAT VC must kernel-certify via native reflection");
    assert_eq!(certified.payload.trust_count, 0);
}

/// MILESTONE 3 (positive, `bvashr` @ width 2): arithmetic (sign-filling)
/// shift-right identity. Distinct gate topology from `lshr` (the fill is the sign
/// bit), so this exercises the signed shift path — still certifies natively.
#[test]
fn bvashr_identity_is_kernel_certified_zero_trust() {
    let env = env();
    let (lhs, rhs) = bvshift_identity_obligation(BvExpr::ashr, "V0", "S0", W_LIGHT);
    let certified = certify_bvshift_unsat(&env, &lhs, &rhs)
        .expect("a real bvashr UNSAT VC must kernel-certify via native reflection");
    assert_eq!(certified.payload.trust_count, 0);
}

/// FAIL-CLOSED negative control (never false-PROVE): the SIGNED-vs-UNSIGNED bug
/// class — `not( ashr(V,S) == lshr(V,S) )` is SATISFIABLE (a negative value
/// shifted right differs under sign-fill vs zero-fill) — must be DECLINED with
/// `NoRefutation`, never certified. This is the exact miscompile
/// (signed-shift-lowered-as-unsigned) the campaign caught: ay finds a model and
/// refuses to fabricate a proof.
#[test]
fn ashr_vs_lshr_is_declined_fail_closed() {
    let env = env();
    let v = BvExpr::leaf("V0", W);
    let s = BvExpr::leaf("S0", W);
    let lhs = BvExpr::ashr(v.clone(), s.clone());
    let rhs = BvExpr::lshr(v, s); // ashr != lshr ⇒ SATISFIABLE disequality.
    let outcome = certify_bvshift_unsat(&env, &lhs, &rhs);
    assert!(
        matches!(outcome, Err(BvShiftCertifyError::NoRefutation)),
        "ashr-vs-lshr is SAT and must be declined (NoRefutation), never certified; got {outcome:?}"
    );
}

/// FAIL-CLOSED negative control: `not( shl(V,S) == lshr(V,S) )` is SATISFIABLE
/// (left vs right shift differ), so it must be declined — a wrong shift direction
/// never certifies.
#[test]
fn shl_vs_lshr_is_declined_fail_closed() {
    let env = env();
    let v = BvExpr::leaf("V0", W);
    let s = BvExpr::leaf("S0", W);
    let lhs = BvExpr::Shl(Box::new(v.clone()), Box::new(s.clone()));
    let rhs = BvExpr::lshr(v, s);
    let outcome = certify_bvshift_unsat(&env, &lhs, &rhs);
    assert!(
        matches!(outcome, Err(BvShiftCertifyError::NoRefutation)),
        "shl-vs-lshr is SAT and must be declined, got {outcome:?}"
    );
}

/// AY 0e35 reduced the width-8 identity trace to 430 clauses / 266 resolution
/// steps. It is now within the operational ceiling and must kernel-certify
/// rather than being rejected by a stale width-based expectation.
#[test]
fn bvshift_width8_is_kernel_certified_zero_trust() {
    let env = env();
    let (lhs, rhs) = bvshift_identity_obligation(
        |value, amount| BvExpr::Shl(Box::new(value), Box::new(amount)),
        "V0",
        "S0",
        8,
    );
    let certified = certify_bvshift_unsat(&env, &lhs, &rhs)
        .expect("the current width-8 trace is within budget and must certify");
    assert_eq!(certified.payload.trust_count, 0);
    assert_eq!(certified.num_clauses, 430);
    assert!(
        certified.num_resolution_steps <= MAX_REFLECTION_STEPS,
        "certified trace must be within the enforced cap"
    );
}

/// The cap itself remains fail-closed independent of proof-producer shape.
#[test]
fn reflection_step_cap_declines_before_kernel_recheck() {
    let steps = MAX_REFLECTION_STEPS + 1;
    assert_eq!(
        enforce_reflection_step_cap(steps),
        Err(BvShiftCertifyError::RefutationTooLarge {
            steps,
            cap: MAX_REFLECTION_STEPS,
        })
    );
}
