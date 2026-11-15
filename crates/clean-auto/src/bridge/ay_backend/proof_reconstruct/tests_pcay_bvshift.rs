// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Milestone-3 e2e: a real `bvshl` / `bvlshr` / `bvashr` UNSAT obligation is
//! kernel-CERTIFIED under exact rooted authority, NATIVELY (Clean kernel reflection of the
//! barrel-shifter bit-blast; no Carcara; no shift axiom), plus the fail-closed
//! negative controls (satisfiable, wrong-shift, and the signed-vs-unsigned bug
//! class). Reuses the OP-AGNOSTIC reflection family — the same reflection
//! milestone 2's bvmul certification uses (here the sub-quadratic trie variant).
//!
//! The identity positives certify the lane end to end, but since ay 8d72a7b97
//! their refutations do not resolve through the shifter (see the NON-IDENTITY
//! section note). The non-identity positives in that section are the ones whose
//! certificates must reason through the barrel shifter and the adder.

use super::super::bv_blast_reflection::check_refutes3_sound_name;
use super::super::certified_proof::deserialize_term;
use super::super::pcay_bvmul::bvmul_certify_env;
use super::super::tests_support::{assert_refutation_resolves_through, refutation_core_gate_kinds};
use super::*;
use ay_proof::bv_blast_export::BitLemmaKind;
use ay_proof::bv_blast_solver::BvExpr;
use clean_kernel::name::Name;

/// The always-on HEADLINE operand width for shift certification: a width-4
/// variable barrel shift is two constant-shift mux layers plus the over-shift
/// mux, reflected through the sub-quadratic trie checker (`checkRefutes3_sound`).
const W: u32 = 4;

/// A LIGHTER width for the second/third shift-kind positives (`bvlshr`/`bvashr`),
/// chosen when their traces were heavy enough to OOM if the harness ran three
/// concurrently, and for the adder-plus-shifter positive, whose width-4
/// certificate measured 1908 steps / 86 s. A width-2 barrel shift is the same
/// gate structure (one constant-shift layer plus the over-shift mux) over a
/// smaller operand.
const W_LIGHT: u32 = 2;

/// The reused resolution-soundness environment (identical layer to milestone 2).
fn env() -> Environment {
    bvmul_certify_env().expect("env setup")
}

/// MILESTONE 3 (positive HEADLINE, `bvshl` @ width 4): a real, gate-shaped
/// logical-shift-left identity VC is kernel-CERTIFIED under rooted authority,
/// natively, with `trust_count == 0`. The FULL barrel shifter (conditional constant-shift layers +
/// over-shift saturation mux) is bit-blasted into the CNF the Clean kernel
/// reflects. Since ay 8d72a7b97 both sides blast to the same output bits, so the
/// refutation is the per-bit `XnorEq` derivation plus the disequality and uses no
/// shifter clause (148 clauses / 9 steps at AY 0.27.0@f28345ff);
/// `bvshl_constant_and_variable_shifts_commute_certified_through_the_shifter` is
/// the width-4 positive whose refutation does resolve through the shifter.
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

    // Independently replay the exact rooted authority check inline so the
    // width-4 certification runs only once. This checks the complete type/value
    // dependency closure, provenance, and exact canonical foundations.
    let term =
        deserialize_term(&certified.payload.term_bytes).expect("deserialize certified Unsat term");
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
/// bit), blasted into the reflected CNF; as for every identity here, the
/// refutation does not resolve through it. The sign-fill semantics are what
/// `ashr_vs_lshr_is_declined_fail_closed` exercises.
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

/// The width-8 `bvshl` identity kernel-certifies under rooted authority with
/// `trust_count == 0`, within the enforced cap — and, at the SAME width, the
/// wrong-direction obligation (`shl` vs `lshr`) is declined, so the width-8
/// shift encoding the certificate rests on is not vacuous.
///
/// WHY NO SHAPE PIN. This test used to assert `num_clauses == 430`, the clause
/// count recorded when AY 0e35 first brought the width-8 trace under the cap
/// (430 clauses / 266 steps; 5356 steps before that). A clause or step count is a
/// producer-shape fact, not a soundness property, and it moves with benign
/// producer changes: since ay 8d72a7b97 the exporter folds `or(const 0, x)` to
/// `x`'s own wires, so both sides of the identity blast to the same output bits
/// and at AY 0.27.0@f28345ff this trace is 382 clauses / 17 steps (= 2·8 + 1:
/// the per-bit `XnorEq` derivation plus the disequality). The drift that matters
/// is guarded directly instead: an over-cap trace is `RefutationTooLarge` (the
/// `expect` fails before any reduction), certification and `trust_count == 0`
/// are asserted, and a producer that collapsed width-8 shift semantics (say,
/// blasting `shl` and `lshr` alike) would certify the wrong-direction obligation
/// below instead of declining it.
#[test]
fn bvshift_width8_is_kernel_certified_zero_trust() {
    const W8: u32 = 8;
    let env = env();
    let (lhs, rhs) = bvshift_identity_obligation(
        |value, amount| BvExpr::Shl(Box::new(value), Box::new(amount)),
        "V0",
        "S0",
        W8,
    );
    let certified = certify_bvshift_unsat(&env, &lhs, &rhs)
        .expect("the width-8 trace must be within the cap and kernel-certify");
    eprintln!(
        "[CERTIFIED] bvshl identity w8: clauses={} steps={}",
        certified.num_clauses, certified.num_resolution_steps
    );
    assert_eq!(certified.payload.trust_count, 0);
    assert!(
        certified.num_resolution_steps <= MAX_REFLECTION_STEPS,
        "certified trace must be within the enforced cap"
    );

    // Non-vacuity at the certified width: a genuinely different shift over the
    // same width-8 operands is SATISFIABLE and must be declined.
    let v = BvExpr::leaf("V0", W8);
    let s = BvExpr::leaf("S0", W8);
    let wrong = certify_bvshift_unsat(
        &env,
        &BvExpr::Shl(Box::new(v.clone()), Box::new(s.clone())),
        &BvExpr::lshr(v, s),
    );
    assert!(
        matches!(wrong, Err(BvShiftCertifyError::NoRefutation)),
        "width-8 shl-vs-lshr is SAT and must be declined (NoRefutation), got {wrong:?}"
    );
}

// ===========================================================================
// NON-IDENTITY SHIFT POSITIVES: certificates that must resolve through the
// barrel shifter's (and the adder's) clauses.
//
// Every shift positive above is `or(const 0, shift) == shift`. Since ay 8d72a7b97
// AY folds `or(const 0, x)` to x's own wires, so both sides blast to the same
// output bits and the certificate is the 2·w + 1-step per-bit `XnorEq`
// derivation: the barrel shifter's clauses are in the CNF, and no step uses them.
// Those tests still certify the lane end to end, but none of them re-checks a
// SHIFT refutation. The two positives below are valid but are NOT identities
// after AY's preprocessing (a literal shift amount blasts to wiring, a variable
// one to a barrel shifter, and the gate cache shares only gates with identical
// ordered inputs), so the two sides blast to different output bits and the
// refutation must go through the shifter's mux gates, whose kinds here are
// exactly `Not` / `And2` / `Or2` (nothing else in these obligations emits them).
//
// Measured at AY 0.27.0@f28345ff (clauses / steps; input clauses the refutation
// resolves on, of those in the CNF):
//   shl by 1 commutes with shl by S, width 4    193 / 305
//       And2 34/100, Or2 15/72, Not 4/6
//   shl distributes over doubling, width 2      118 / 371
//       And2 38/48, Or2 15/32, Not 4/4, Xor3 12/16, FullAdderCarry 4/8
// ===========================================================================

/// The barrel shifter's gate kinds: each mux bit is `(sel ∧ t) ∨ (¬sel ∧ f)`.
const BARREL_SHIFTER: [BitLemmaKind; 3] =
    [BitLemmaKind::Not, BitLemmaKind::And2, BitLemmaKind::Or2];

/// Certify a NON-identity obligation through the production lane
/// ([`certify_bvshift_unsat`]) and show that the certificate reasons through
/// `circuit`.
///
/// Before any kernel work, AY's proof of `lhs == rhs` must self-validate and pass
/// [`assert_refutation_resolves_through`]: within [`MAX_REFLECTION_STEPS`],
/// longer than the identity shape, and resolving on every gate kind in
/// `circuit`. Then `certify_bvshift_unsat` must certify it (it enforces the same
/// cap before its own kernel re-check, then runs the rooted authority audit), the
/// certificate must be of that same proof, `trust_count` must be 0, and the
/// certified term must rest on the PROVED `checkRefutes3_sound` bridge, whose
/// axiom closure contains zero domain axioms.
fn certify_non_identity_through(
    env: &Environment,
    lhs: &BvExpr,
    rhs: &BvExpr,
    width: u32,
    circuit: &[BitLemmaKind],
    label: &str,
) {
    let proof = export_bv_blast_proof_expr(lhs, rhs)
        .unwrap_or_else(|e| panic!("{label}: a valid obligation must export: {e}"));
    proof
        .validate()
        .unwrap_or_else(|e| panic!("{label}: producer proof must self-validate: {e}"));
    let core = assert_refutation_resolves_through(&proof, width, circuit, label);

    let certified = certify_bvshift_unsat(env, lhs, rhs)
        .unwrap_or_else(|e| panic!("{label}: must kernel-certify natively: {e}"));
    eprintln!(
        "[CERTIFIED] {label}: clauses={} steps={} core clauses by gate kind: {core:?}",
        certified.num_clauses, certified.num_resolution_steps
    );
    assert_eq!(
        (certified.num_clauses, certified.num_resolution_steps),
        (proof.clauses.len(), proof.refutation.steps.len()),
        "{label}: the certificate must be of the proof whose core was inspected"
    );
    assert_eq!(
        certified.payload.trust_count, 0,
        "{label}: must certify with ZERO trust in ay"
    );
    let term = deserialize_term(&certified.payload.term_bytes)
        .unwrap_or_else(|e| panic!("{label}: deserialize certified Unsat term: {e}"));
    assert!(
        format!("{term:?}").contains("checkRefutes3_sound"),
        "{label}: the certificate must apply the PROVED checkRefutes3_sound bridge"
    );
    let domain: Vec<String> = env
        .axiom_deps(&Name::from_string(check_refutes3_sound_name()))
        .expect("checkRefutes3_sound registered")
        .iter()
        .map(ToString::to_string)
        .collect();
    assert!(
        domain.is_empty(),
        "{label}: the certificate must carry ZERO domain axioms; got {domain:?}"
    );
}

/// The pre-kernel shape guard is not vacuous: on the width-4 IDENTITY positive
/// above (`or(const 0, shl(V, S)) == shl(V, S)`), whose refutation resolves on no
/// shifter clause, it must REFUSE, and on its load-bearing gate-kind check. This
/// is the regression the guard exists for: a producer change that made a
/// non-identity positive's sides fuse the same way would be refused like this,
/// before any kernel work.
#[test]
fn shape_guard_refuses_the_identity_refutation() {
    let (lhs, rhs) = bvshift_identity_obligation(BvExpr::shl, "V0", "S0", W);
    let proof = export_bv_blast_proof_expr(&lhs, &rhs).expect("the identity must export");
    proof.validate().expect("producer proof must self-validate");
    let core = refutation_core_gate_kinds(&proof);
    assert!(
        BARREL_SHIFTER.iter().all(|kind| !core.contains_key(kind)),
        "the width-4 identity's refutation was measured to resolve on no shifter clause; \
         core is now {core:?}, so the identity doc comments in this file are stale"
    );
    let guard = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        assert_refutation_resolves_through(&proof, W, &BARREL_SHIFTER, "identity (must refuse)")
    }));
    let refusal = match guard {
        Ok(_) => panic!("the shape guard accepted an identity refutation (core {core:?})"),
        Err(payload) => payload
            .downcast_ref::<String>()
            .cloned()
            .unwrap_or_default(),
    };
    assert!(
        refusal.contains("never resolves on a"),
        "the shape guard must refuse on its gate-kind check; it said: {refusal:?}"
    );
}

/// A constant shift commutes with a variable one: `shl(shl(V, 1), S) ==
/// shl(shl(V, S), 1)` at width 4. Each side has ONE barrel shifter keyed on `S`,
/// but over different inputs (`V` moved up one place, vs `V` itself), so the two
/// shifters share no gate and the certificate must resolve through their muxes.
#[test]
fn bvshl_constant_and_variable_shifts_commute_certified_through_the_shifter() {
    let env = env();
    let (v, s, one) = (
        BvExpr::leaf("V0", W),
        BvExpr::leaf("S0", W),
        BvExpr::const_val(1, W),
    );
    certify_non_identity_through(
        &env,
        &BvExpr::shl(BvExpr::shl(v.clone(), one.clone()), s.clone()),
        &BvExpr::shl(BvExpr::shl(v, s), one),
        W,
        &BARREL_SHIFTER,
        "shl1-shlS-commute-w4",
    );
}

/// ANTI-VACUITY for the commuting shifts: the same obligation with the outer
/// constant shift turned right, `shl(shl(V, 1), S) == lshr(shl(V, S), 1)`, is
/// SATISFIABLE (`V = 1, S = 0` gives 2 vs 0) and must be declined.
#[test]
fn bvshl_then_lshr_does_not_commute_declined_fail_closed() {
    let env = env();
    let (v, s, one) = (
        BvExpr::leaf("V0", W),
        BvExpr::leaf("S0", W),
        BvExpr::const_val(1, W),
    );
    let outcome = certify_bvshift_unsat(
        &env,
        &BvExpr::shl(BvExpr::shl(v.clone(), one.clone()), s.clone()),
        &BvExpr::lshr(BvExpr::shl(v, s), one),
    );
    assert!(
        matches!(outcome, Err(BvShiftCertifyError::NoRefutation)),
        "shl-then-lshr is SAT and must be declined (NoRefutation), got {outcome:?}"
    );
}

/// A left shift distributes over doubling: `shl(V, S) + shl(V, S) ==
/// shl(V + V, S)` at width 2. The left side adds two copies of one shifter's
/// output; the right side shifts an adder's output through a second shifter. The
/// certificate must resolve through BOTH circuits: the shifters' muxes and the
/// adders' sums and carries.
#[test]
fn bvshl_distributes_over_doubling_certified_through_adder_and_shifter() {
    let env = env();
    let (v, s) = (BvExpr::leaf("V0", W_LIGHT), BvExpr::leaf("S0", W_LIGHT));
    let shifted = BvExpr::shl(v.clone(), s.clone());
    let mut circuit = BARREL_SHIFTER.to_vec();
    circuit.extend([BitLemmaKind::Xor3, BitLemmaKind::FullAdderCarry]);
    certify_non_identity_through(
        &env,
        &BvExpr::add(shifted.clone(), shifted),
        &BvExpr::shl(BvExpr::add(v.clone(), v), s),
        W_LIGHT,
        &circuit,
        "shl-over-doubling-w2",
    );
}

/// ANTI-VACUITY for distributivity: a LOGICAL RIGHT shift does not distribute
/// over addition (low bits each addend loses to the shift can carry into bits the
/// shift keeps), so `lshr(V, S) + lshr(V, S) == lshr(V + V, S)` is SATISFIABLE
/// (`V = 1, S = 1` gives 0 vs 1) and must be declined.
#[test]
fn bvlshr_does_not_distribute_over_doubling_declined_fail_closed() {
    let env = env();
    let (v, s) = (BvExpr::leaf("V0", W_LIGHT), BvExpr::leaf("S0", W_LIGHT));
    let shifted = BvExpr::lshr(v.clone(), s.clone());
    let outcome = certify_bvshift_unsat(
        &env,
        &BvExpr::add(shifted.clone(), shifted),
        &BvExpr::lshr(BvExpr::add(v.clone(), v), s),
    );
    assert!(
        matches!(outcome, Err(BvShiftCertifyError::NoRefutation)),
        "lshr-over-doubling is SAT and must be declined (NoRefutation), got {outcome:?}"
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
