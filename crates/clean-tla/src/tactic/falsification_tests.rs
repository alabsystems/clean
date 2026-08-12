// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Falsification suite for the TLA+ tactic engine.
//!
//! # Purpose
//!
//! This module is the standing soundness regression suite for `clean-tla`.
//! Each `false_*` test constructs a genuinely-FALSE TLA+ obligation that a
//! prior version of the heuristic tactic engine reported as PROVED (see
//! `docs/SOUNDNESS_FINDINGS_CLEAN_TLA_2026-07.md`, 15 confirmed holes), and
//! asserts that the PUBLIC entry [`prove_tla_obligation`] now returns
//! `proved == false`.
//!
//! The `true_*` tests are correct-path guards: genuinely-TRUE properties the
//! engine legitimately proves must keep proving after the fail-closed fixes,
//! so that over-conservatism does not silently turn the engine into a no-op.
//!
//! # Soundness contract
//!
//! A heuristic shortcut that can fire on a false goal is unsound. When a
//! tactic cannot genuinely discharge its side-condition it must return
//! not-proved / continue-search — never accept. These tests pin that
//! contract at the observable (public-entry) boundary.

use super::prove_tla_obligation;
use crate::encoding::{TlaArithOp, TlaCmpOp, TlaExpr};
use crate::obligation::TlaObligation;
use crate::TlaFormula;

// ---------------------------------------------------------------------------
// Small builders (keep the test bodies readable and faithful to the encoder).
// ---------------------------------------------------------------------------

fn var(name: &str) -> TlaExpr {
    TlaExpr::Var(name.to_string())
}

fn int(n: i64) -> TlaExpr {
    TlaExpr::Int(n)
}

fn add(a: TlaExpr, b: TlaExpr) -> TlaExpr {
    TlaExpr::Arith(TlaArithOp::Add, Box::new(a), Box::new(b))
}

fn sub(a: TlaExpr, b: TlaExpr) -> TlaExpr {
    TlaExpr::Arith(TlaArithOp::Sub, Box::new(a), Box::new(b))
}

fn mul(a: TlaExpr, b: TlaExpr) -> TlaExpr {
    TlaExpr::Arith(TlaArithOp::Mul, Box::new(a), Box::new(b))
}

fn div(a: TlaExpr, b: TlaExpr) -> TlaExpr {
    TlaExpr::Arith(TlaArithOp::Div, Box::new(a), Box::new(b))
}

fn modulo(a: TlaExpr, b: TlaExpr) -> TlaExpr {
    TlaExpr::Arith(TlaArithOp::Mod, Box::new(a), Box::new(b))
}

fn eq(a: TlaExpr, b: TlaExpr) -> TlaFormula {
    TlaFormula::Eq(Box::new(a), Box::new(b))
}

fn forall_nat(v: &str, body: TlaFormula) -> TlaFormula {
    TlaFormula::ForallIn(v.to_string(), Box::new(TlaExpr::Nat), Box::new(body))
}

/// Convenience: build an induction-hinted obligation from a goal formula.
fn induction(goal: TlaFormula) -> TlaObligation {
    TlaObligation::new(goal).with_tactic("induction")
}

/// Assert a genuinely-false obligation is NOT reported proved.
fn assert_not_proved(ob: &TlaObligation, label: &str) {
    let r = prove_tla_obligation(ob);
    assert!(
        !r.proved,
        "SOUNDNESS: false property `{label}` must NOT be proved, but engine reported \
         proved=true with certificate {:?}",
        r.certificate
    );
}

/// Assert a genuinely-true obligation IS reported proved (correct-path guard).
fn assert_proved(ob: &TlaObligation, label: &str) {
    let r = prove_tla_obligation(ob);
    assert!(
        r.proved,
        "REGRESSION: true property `{label}` should still prove, but engine reported \
         proved=false (error {:?}, tactics {:?})",
        r.error, r.tactics_tried
    );
}

// ===========================================================================
// FALSE properties — every one of these was a confirmed false-proof hole.
// ===========================================================================

/// induction.rs check_shifted_equality: `∀n,m: (m+n) = (m+n*n)`
/// (false at n=2, m=0: 2 ≠ 4).
#[test]
fn false_shifted_equality_m_plus_n_eq_m_plus_n_sq() {
    let goal = forall_nat(
        "n",
        forall_nat(
            "m",
            eq(
                add(var("m"), var("n")),
                add(var("m"), mul(var("n"), var("n"))),
            ),
        ),
    );
    assert_not_proved(&induction(goal), "∀n,m: (m+n)=(m+n*n)");
}

/// induction.rs try_nested_forall_step_case sibling: `∀n,m: (n+m) = (n+m+m)`
/// (false at n=0, m=1: 1 ≠ 2).
#[test]
fn false_nested_forall_n_plus_m_eq_n_plus_m_plus_m() {
    let goal = forall_nat(
        "n",
        forall_nat(
            "m",
            eq(
                add(var("n"), var("m")),
                add(add(var("n"), var("m")), var("m")),
            ),
        ),
    );
    assert_not_proved(&induction(goal), "∀n,m: (n+m)=(n+m+m)");
}

/// arith.rs normalize_arith div: `∀v: (0 ÷ v) = 0`
/// (false — division by 0 is unspecified in TLA+).
#[test]
fn false_zero_div_v_eq_zero() {
    let goal = forall_nat("v", eq(div(int(0), var("v")), int(0)));
    assert_not_proved(&induction(goal), "∀v: (0÷v)=0");
}

/// arith.rs normalize_arith mod: `∀v: (0 % v) = 0`
/// (false — modulo by 0 is unspecified in TLA+).
#[test]
fn false_zero_mod_v_eq_zero() {
    let goal = forall_nat("v", eq(modulo(int(0), var("v")), int(0)));
    assert_not_proved(&induction(goal), "∀v: (0%v)=0");
}

/// arith.rs try_arith_step_case add_zero_succ: `∀n: (n+0) = (2*n)`
/// (false at n=1: 1 ≠ 2).
#[test]
fn false_n_plus_zero_eq_two_n() {
    let goal = forall_nat("n", eq(add(var("n"), int(0)), mul(int(2), var("n"))));
    assert_not_proved(&induction(goal), "∀n: (n+0)=(2*n)");
}

/// arith.rs try_arith_step_case mul_one_succ: `∀n: (n*1) = (n+n)`
/// (false at n=1: 1 ≠ 2).
#[test]
fn false_n_times_one_eq_n_plus_n() {
    let goal = forall_nat("n", eq(mul(var("n"), int(1)), add(var("n"), var("n"))));
    assert_not_proved(&induction(goal), "∀n: (n*1)=(n+n)");
}

/// ring.rs Nat.sub encoding: `∀n: (2-5)+5 = 2`
/// (false over TLA+/Nat monus at the constant, and false when routed via the
/// n-independent body whose step is trivially P→P).
#[test]
fn false_two_minus_five_plus_five_eq_two() {
    let goal = forall_nat("n", eq(add(sub(int(2), int(5)), int(5)), int(2)));
    assert_not_proved(&induction(goal), "(2-5)+5=2");
}

/// ring.rs TLA.mul coefficient overflow: `∀n: 3037000500² = 4000000000²`
/// (both products exceed i64::MAX; saturation used to alias them).
#[test]
fn false_squared_product_overflow_collision() {
    let goal = forall_nat(
        "n",
        eq(
            mul(int(3_037_000_500), int(3_037_000_500)),
            mul(int(4_000_000_000), int(4_000_000_000)),
        ),
    );
    assert_not_proved(&induction(goal), "3037000500²=4000000000²");
}

/// induction.rs try_lex_induction: `∀p ∈ Nat×Nat: 0 = 1`.
#[test]
fn false_lex_induction_zero_eq_one_over_product() {
    let prod = TlaExpr::OpApply("Prod".to_string(), vec![TlaExpr::Nat, TlaExpr::Nat]);
    let goal = TlaFormula::ForallIn(
        "p".to_string(),
        Box::new(prod),
        Box::new(eq(int(0), int(1))),
    );
    assert_not_proved(&induction(goal), "∀p∈Nat×Nat: 0=1");
}

/// Retired lattice-decomposition heuristic: false liveness `(x<5) ~> FALSE`.
#[test]
fn false_liveness_x_lt_5_leads_to_false() {
    let p = TlaFormula::Expr(TlaExpr::Cmp(
        TlaCmpOp::Lt,
        Box::new(var("x")),
        Box::new(int(5)),
    ));
    let goal = TlaFormula::LeadsTo(Box::new(p), Box::new(TlaFormula::False));
    assert_not_proved(&TlaObligation::new(goal), "(x<5)~>FALSE");
}

/// progress.rs try_progress_measure Pattern 4 (name-based): false liveness
/// `(counter=0) ~> (counter=5)` with no fairness / action.
#[test]
fn false_liveness_counter_0_leads_to_counter_5() {
    let p = eq(var("counter"), int(0));
    let q = eq(var("counter"), int(5));
    let goal = TlaFormula::LeadsTo(Box::new(p), Box::new(q));
    assert_not_proved(&TlaObligation::new(goal), "(counter=0)~>(counter=5)");
}

/// progress.rs try_progress_measure Pattern 2 (countdown): false liveness
/// `(n>0) ~> (n=0)` with no fairness / action.
#[test]
fn false_liveness_n_gt_0_leads_to_n_0() {
    let p = TlaFormula::Expr(TlaExpr::Cmp(
        TlaCmpOp::Gt,
        Box::new(var("n")),
        Box::new(int(0)),
    ));
    let q = eq(var("n"), int(0));
    let goal = TlaFormula::LeadsTo(Box::new(p), Box::new(q));
    assert_not_proved(&TlaObligation::new(goal), "(n>0)~>(n=0)");
}

/// mod.rs / expr_utils is_trivially_true: unconstrained `x >= 0`.
/// `x` ranges over the untyped TLA+ value universe (incl. negatives), so this
/// is not a theorem.
#[test]
fn false_unconstrained_x_ge_zero() {
    let goal = TlaFormula::Expr(TlaExpr::Cmp(
        TlaCmpOp::Ge,
        Box::new(var("x")),
        Box::new(int(0)),
    ));
    assert_not_proved(&TlaObligation::new(goal), "x>=0 (unconstrained)");
}

/// rewrite.rs verify_sum_formula_step: false closed form
/// `∀n: sum(n) = (n*(n+3))/2` under the correct recursive hypotheses
/// (sum(0)=0, sum(k+1)=sum(k)+(k+1)). The true closed form is n*(n+1)/2.
#[test]
fn false_sum_closed_form_n_times_n_plus_3_over_2() {
    // sum(n) as an opaque unary application.
    let sum = |arg: TlaExpr| TlaExpr::OpApply("sum".to_string(), vec![arg]);

    // Hypotheses: sum(0) = 0 and ∀k∈Nat: sum(k+1) = sum(k) + (k+1).
    let hyp0 = eq(sum(int(0)), int(0));
    let hyp_succ = forall_nat(
        "k",
        eq(
            sum(add(var("k"), int(1))),
            add(sum(var("k")), add(var("k"), int(1))),
        ),
    );

    // Goal: ∀n∈Nat: sum(n) = (n*(n+3))/2.
    let goal = forall_nat(
        "n",
        eq(
            sum(var("n")),
            div(mul(var("n"), add(var("n"), int(3))), int(2)),
        ),
    );

    let ob = TlaObligation::new(goal)
        .with_hypothesis("sum_def_0", hyp0)
        .with_hypothesis("sum_def_succ", hyp_succ)
        .with_tactic("induction");
    assert_not_proved(&ob, "∀n: sum(n)=(n*(n+3))/2");
}

// ===========================================================================
// TRUE properties — correct-path guards (must still prove).
// ===========================================================================

/// `∀n∈Nat: n+0 = n` (add-zero identity).
#[test]
fn true_n_plus_zero_eq_n() {
    let goal = forall_nat("n", eq(add(var("n"), int(0)), var("n")));
    assert_proved(&induction(goal), "∀n: n+0=n");
}

/// `∀n∈Nat: n*1 = n` (mul-one identity).
#[test]
fn true_n_times_one_eq_n() {
    let goal = forall_nat("n", eq(mul(var("n"), int(1)), var("n")));
    assert_proved(&induction(goal), "∀n: n*1=n");
}

/// `∀n,m∈Nat: (m+n)+0 = (m+n)` — a genuinely-true NESTED induction identity
/// that the sound engine discharges via the RHS-inspecting `normalize_both`
/// path (both sides normalize to `m+n`). This is the correct-path guard for
/// nested foralls after the unsound count-based shifted-equality branch was
/// removed.
///
/// NOTE: `∀n,m: (m+n)=(n+m)` (commutativity) is intentionally NOT used as a
/// guard: it was previously "proved" ONLY by the unsound succ-count
/// `equality_preservation` branch (see the findings doc), and the sound engine
/// has no commutative canonicalization, so it now correctly reports Unknown
/// rather than a heuristic PROVED. That is acceptable over-conservatism.
#[test]
fn true_nested_identity_m_plus_n_plus_zero() {
    let goal = forall_nat(
        "n",
        forall_nat(
            "m",
            eq(
                add(add(var("m"), var("n")), int(0)),
                add(var("m"), var("n")),
            ),
        ),
    );
    assert_proved(&induction(goal), "∀n,m: (m+n)+0=(m+n)");
}

/// `∀n∈Nat: 2*sum(n) = n*(n+1)` given the recursive hyps sum(0)=0,
/// sum(k+1)=sum(k)+(k+1). This is the genuinely-TRUE triangle-number induction
/// (the correct closed form), discharged soundly via the recursive-rewrite +
/// ring step-case path. It is the true counterpart to the false
/// `sum(n)=(n*(n+3))/2` closed form above.
#[test]
fn true_sum_closed_form_two_sum_eq_n_times_n_plus_1() {
    let sum = |arg: TlaExpr| TlaExpr::OpApply("sum".to_string(), vec![arg]);

    let hyp0 = eq(sum(int(0)), int(0));
    let hyp_succ = forall_nat(
        "k",
        eq(
            sum(add(var("k"), int(1))),
            add(sum(var("k")), add(var("k"), int(1))),
        ),
    );

    let goal = forall_nat(
        "n",
        eq(
            mul(int(2), sum(var("n"))),
            mul(var("n"), add(var("n"), int(1))),
        ),
    );

    let ob = TlaObligation::new(goal)
        .with_hypothesis("sum_def_0", hyp0)
        .with_hypothesis("sum_def_succ", hyp_succ)
        .with_tactic("induction");
    assert_proved(&ob, "∀n: 2*sum(n)=n*(n+1)");
}

/// `∀n∈Nat: (a+b)+c = a+(b+c)` — ring associativity over opaque atoms, routed
/// through the induction base case so it reaches the sound polynomial (ring)
/// path. The body ignores `n`; the point is that the ring equality is genuine.
#[test]
fn true_add_associativity() {
    let goal = forall_nat(
        "n",
        eq(
            add(add(var("a"), var("b")), var("c")),
            add(var("a"), add(var("b"), var("c"))),
        ),
    );
    assert_proved(&induction(goal), "∀n: (a+b)+c=a+(b+c)");
}

/// `∀n∈Nat: 0 ÷ 1 = 0` — division by a provably-nonzero divisor (1) is fine to
/// simplify, so the `0/b → 0` rewrite must still fire when b is nonzero.
#[test]
fn true_zero_div_one_eq_zero() {
    let goal = forall_nat("n", eq(div(int(0), int(1)), int(0)));
    assert_proved(&induction(goal), "∀n: 0÷1=0");
}

/// True liveness by reflexivity: `P ~> P`.
#[test]
fn true_liveness_reflexivity() {
    let p = eq(var("state"), int(3));
    let goal = TlaFormula::LeadsTo(Box::new(p.clone()), Box::new(p));
    assert_proved(&TlaObligation::new(goal), "P~>P");
}

/// True liveness from `□(P → Q)` hypothesis: `P ~> Q`.
#[test]
fn true_liveness_from_always_implication() {
    let p = eq(var("s"), int(1));
    let q = eq(var("s"), int(1));
    // Reflexivity already covers P==Q; use a from-always hypothesis for a
    // distinct P/Q that is genuinely entailed.
    let p2 = eq(var("s"), int(1));
    let q2 = TlaFormula::True;
    let hyp = TlaFormula::Always(Box::new(TlaFormula::Implies(
        Box::new(p2.clone()),
        Box::new(q2.clone()),
    )));
    let goal = TlaFormula::LeadsTo(Box::new(p2), Box::new(q2));
    let ob = TlaObligation::new(goal).with_hypothesis("box_impl", hyp);
    assert_proved(&ob, "□(P→Q) ⊢ P~>Q");
    // Silence unused warnings for the illustrative p/q pair.
    let _ = (p, q);
}
