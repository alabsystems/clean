// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end tests for the general Farkas-with-goal omega reconstruction.
//!
//! Closes the `farkas_replay_gap`: omega now proves linear Nat inequality goals
//! whose UNSAT certificate mixes the hypotheses AND the negated goal (the goal
//! slot the certified-mathverse replay previously dropped). The builder is in
//! [`crate::tactic::arith_linarith_farkas_goal`].
//!
//! Soundness teeth:
//! - PROVE: `(h1 : a + b ≤ c)(h2 : c ≤ a) ⊢ b ≤ 0` and the `<` variant
//!   `(h1 : a + b < c)(h2 : c ≤ a) ⊢ b < 0` both close with a kernel-checked,
//!   axiom-free term (`close_goal` re-checks; zero trustedAy/trustedArith/sorry).
//! - NEGATIVE (fail-closed): the FALSE goals `(h1 : a ≤ b)(h2 : b ≤ c) ⊢ c ≤ a`
//!   and `(h : a ≤ b) ⊢ b ≤ a` and `(h : a ≤ b) ⊢ a + 1 ≤ b` must STILL be
//!   rejected — omega must never prove a false (SAT) goal.

use super::*;
use crate::tactic::tc_app::{nat_le_tc, nat_lt_tc};
use crate::tactic::LocalDecl;
use clean_kernel::Expr;
use serial_test::serial;

fn nat_type() -> Expr {
    Expr::const_(Name::from_string("Nat"), vec![])
}

fn nat_fvar(id: u64) -> Expr {
    Expr::fvar(FVarId::new(id))
}

fn nat_local(id: u64, name: &str) -> LocalDecl {
    LocalDecl {
        fvar: FVarId::new(id),
        name: name.to_string(),
        ty: nat_type(),
        value: None,
    }
}

fn nat_add(lhs: Expr, rhs: Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("Nat.add"), vec![]), lhs),
        rhs,
    )
}

/// `@GE.ge Nat instLENat a b` (`a ≥ b`).
fn nat_ge(a: Expr, b: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("GE.ge"), vec![Level::zero()]),
        [
            nat_type(),
            Expr::const_(Name::from_string("instLENat"), vec![]),
            a,
            b,
        ],
    )
}

/// `@Eq Nat l r` (`l = r`).
fn nat_eq(l: Expr, r: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [nat_type(), l, r],
    )
}

fn hyp(id: u64, name: &str, ty: Expr) -> LocalDecl {
    LocalDecl {
        fvar: FVarId::new(id),
        name: name.to_string(),
        ty,
        value: None,
    }
}

/// Build a state with locals `decls` and goal `goal_target`.
fn state_with(decls: Vec<LocalDecl>, goal_target: Expr) -> ProofState {
    ProofState::with_context(Environment::with_prelude(), goal_target, decls)
}

/// Run omega and assert it closes the goal with a real, axiom-free proof term.
fn assert_omega_proves(mut state: ProofState, label: &str) {
    reset_all_counters();
    let axiom_before = axiom_snapshot();
    let result = omega(&mut state);
    assert!(
        result.is_ok(),
        "omega should prove `{label}`, got: {result:?}"
    );
    assert!(
        state.is_complete(),
        "goal `{label}` should be closed after omega succeeds"
    );
    assert_no_trusted_axiom_usage("omega", label, axiom_before);
    let ledger = state.trust_ledger();
    assert_eq!(
        ledger.trusted_arith_count, 0,
        "`{label}`: omega must not use trustedArith"
    );
    assert_eq!(
        ledger.trusted_ay_count, 0,
        "`{label}`: omega must not use trustedAy"
    );
    assert_eq!(
        ledger.sorry_count, 0,
        "`{label}`: omega must produce a real proof term (no sorry)"
    );
}

/// Run omega and assert it does NOT close (false / SAT goal — fail closed).
fn assert_omega_rejects(mut state: ProofState, label: &str) {
    reset_all_counters();
    let result = omega(&mut state);
    assert!(
        result.is_err() && !state.is_complete(),
        "omega must REJECT the false goal `{label}`, but it closed: {result:?}"
    );
}

#[test]
#[serial]
fn test_farkas_goal_proves_b_le_zero_from_hyp_chain() {
    // (a b c : Nat)(h1 : a + b ≤ c)(h2 : c ≤ a) ⊢ b ≤ 0  — t1.
    let a = nat_fvar(0);
    let b = nat_fvar(1);
    let c = nat_fvar(2);
    let h1 = nat_le_tc(nat_add(a.clone(), b.clone()), c.clone());
    let h2 = nat_le_tc(c, a);
    let goal = nat_le_tc(b, Expr::nat_lit(0));
    let state = state_with(
        vec![
            nat_local(0, "a"),
            nat_local(1, "b"),
            nat_local(2, "c"),
            LocalDecl {
                fvar: FVarId::new(3),
                name: "h1".into(),
                ty: h1,
                value: None,
            },
            LocalDecl {
                fvar: FVarId::new(4),
                name: "h2".into(),
                ty: h2,
                value: None,
            },
        ],
        goal,
    );
    assert_omega_proves(state, "(h1 : a + b ≤ c)(h2 : c ≤ a) ⊢ b ≤ 0");
}

#[test]
#[serial]
fn test_farkas_goal_proves_b_lt_zero_from_lt_hyp_chain() {
    // (a b c : Nat)(h1 : a + b < c)(h2 : c ≤ a) ⊢ b < 0  — t5.
    let a = nat_fvar(0);
    let b = nat_fvar(1);
    let c = nat_fvar(2);
    let h1 = nat_lt_tc(nat_add(a.clone(), b.clone()), c.clone());
    let h2 = nat_le_tc(c, a);
    let goal = nat_lt_tc(b, Expr::nat_lit(0));
    let state = state_with(
        vec![
            nat_local(0, "a"),
            nat_local(1, "b"),
            nat_local(2, "c"),
            LocalDecl {
                fvar: FVarId::new(3),
                name: "h1".into(),
                ty: h1,
                value: None,
            },
            LocalDecl {
                fvar: FVarId::new(4),
                name: "h2".into(),
                ty: h2,
                value: None,
            },
        ],
        goal,
    );
    assert_omega_proves(state, "(h1 : a + b < c)(h2 : c ≤ a) ⊢ b < 0");
}

#[test]
#[serial]
fn test_farkas_goal_rejects_false_c_le_a() {
    // FALSE: (a b c : Nat)(h1 : a ≤ b)(h2 : b ≤ c) ⊢ c ≤ a.
    let a = nat_fvar(0);
    let b = nat_fvar(1);
    let c = nat_fvar(2);
    let h1 = nat_le_tc(a.clone(), b.clone());
    let h2 = nat_le_tc(b, c.clone());
    let goal = nat_le_tc(c, a);
    let state = state_with(
        vec![
            nat_local(0, "a"),
            nat_local(1, "b"),
            nat_local(2, "c"),
            LocalDecl {
                fvar: FVarId::new(3),
                name: "h1".into(),
                ty: h1,
                value: None,
            },
            LocalDecl {
                fvar: FVarId::new(4),
                name: "h2".into(),
                ty: h2,
                value: None,
            },
        ],
        goal,
    );
    assert_omega_rejects(state, "(h1 : a ≤ b)(h2 : b ≤ c) ⊢ c ≤ a");
}

#[test]
#[serial]
fn test_farkas_goal_rejects_false_b_le_a() {
    // FALSE: (a b : Nat)(h : a ≤ b) ⊢ b ≤ a.
    let a = nat_fvar(0);
    let b = nat_fvar(1);
    let h = nat_le_tc(a.clone(), b.clone());
    let goal = nat_le_tc(b, a);
    let state = state_with(
        vec![
            nat_local(0, "a"),
            nat_local(1, "b"),
            LocalDecl {
                fvar: FVarId::new(2),
                name: "h".into(),
                ty: h,
                value: None,
            },
        ],
        goal,
    );
    assert_omega_rejects(state, "(h : a ≤ b) ⊢ b ≤ a");
}

#[test]
#[serial]
fn test_farkas_goal_rejects_false_a_plus_1_le_b() {
    // FALSE: (a b : Nat)(h : a ≤ b) ⊢ a + 1 ≤ b.
    let a = nat_fvar(0);
    let b = nat_fvar(1);
    let h = nat_le_tc(a.clone(), b.clone());
    let goal = nat_le_tc(nat_add(a, Expr::nat_lit(1)), b);
    let state = state_with(
        vec![
            nat_local(0, "a"),
            nat_local(1, "b"),
            LocalDecl {
                fvar: FVarId::new(2),
                name: "h".into(),
                ty: h,
                value: None,
            },
        ],
        goal,
    );
    assert_omega_rejects(state, "(h : a ≤ b) ⊢ a + 1 ≤ b");
}

// ---------------------------------------------------------------------------
// Implicit Nat non-negativity (`v ≥ 0`) combined with a hypothesis.
//
// These close the `omegabound` gap: omega now combines the implicit `v ≥ 0` of
// each Nat variable with the hypotheses to discharge inequality goals whose
// Farkas witness is `hyp + neg_goal + Σ (0 ≤ vᵢ)`. Each PROVE asserts a
// kernel-checked, axiom-free term; each REJECT asserts fail-closed behaviour
// (the must-fail soundness teeth — omega must NEVER prove a false goal).
// ---------------------------------------------------------------------------

#[test]
#[serial]
fn test_nonneg_le_hyp_proves_b_ge_2() {
    // (a b : Nat)(h : a + 2 ≤ b) ⊢ b ≥ 2.  Needs a ≥ 0: b ≥ a + 2 ≥ 2.
    let a = nat_fvar(0);
    let b = nat_fvar(1);
    let h = nat_le_tc(nat_add(a, Expr::nat_lit(2)), b.clone());
    let goal = nat_ge(b, Expr::nat_lit(2));
    let state = state_with(
        vec![nat_local(0, "a"), nat_local(1, "b"), hyp(2, "h", h)],
        goal,
    );
    assert_omega_proves(state, "(h : a + 2 ≤ b) ⊢ b ≥ 2");
}

#[test]
#[serial]
fn test_nonneg_eq_hyp_proves_b_ge_2() {
    // (a b : Nat)(h : a + 2 = b) ⊢ b ≥ 2.
    let a = nat_fvar(0);
    let b = nat_fvar(1);
    let h = nat_eq(nat_add(a, Expr::nat_lit(2)), b.clone());
    let goal = nat_ge(b, Expr::nat_lit(2));
    let state = state_with(
        vec![nat_local(0, "a"), nat_local(1, "b"), hyp(2, "h", h)],
        goal,
    );
    assert_omega_proves(state, "(h : a + 2 = b) ⊢ b ≥ 2");
}

#[test]
#[serial]
fn test_nonneg_eq_hyp_proves_b_ge_a() {
    // (a b : Nat)(h : a + 2 = b) ⊢ b ≥ a.
    let a = nat_fvar(0);
    let b = nat_fvar(1);
    let h = nat_eq(nat_add(a.clone(), Expr::nat_lit(2)), b.clone());
    let goal = nat_ge(b, a);
    let state = state_with(
        vec![nat_local(0, "a"), nat_local(1, "b"), hyp(2, "h", h)],
        goal,
    );
    assert_omega_proves(state, "(h : a + 2 = b) ⊢ b ≥ a");
}

#[test]
#[serial]
fn test_nonneg_eq_hyp_reversed_proves_b_ge_2() {
    // (a b : Nat)(h : b = a + 2) ⊢ b ≥ 2.  Equality in the other orientation.
    let a = nat_fvar(0);
    let b = nat_fvar(1);
    let h = nat_eq(b.clone(), nat_add(a, Expr::nat_lit(2)));
    let goal = nat_ge(b, Expr::nat_lit(2));
    let state = state_with(
        vec![nat_local(0, "a"), nat_local(1, "b"), hyp(2, "h", h)],
        goal,
    );
    assert_omega_proves(state, "(h : b = a + 2) ⊢ b ≥ 2");
}

#[test]
#[serial]
fn test_nonneg_two_atoms_proves_c_ge_1() {
    // (a b c : Nat)(h : a + b + 1 ≤ c) ⊢ c ≥ 1.  Both a ≥ 0 AND b ≥ 0 needed.
    let a = nat_fvar(0);
    let b = nat_fvar(1);
    let c = nat_fvar(2);
    let lhs = nat_add(nat_add(a, b), Expr::nat_lit(1));
    let h = nat_le_tc(lhs, c.clone());
    let goal = nat_ge(c, Expr::nat_lit(1));
    let state = state_with(
        vec![
            nat_local(0, "a"),
            nat_local(1, "b"),
            nat_local(2, "c"),
            hyp(3, "h", h),
        ],
        goal,
    );
    assert_omega_proves(state, "(h : a + b + 1 ≤ c) ⊢ c ≥ 1");
}

#[test]
#[serial]
fn test_nonneg_le_hyp_rejects_false_b_ge_3() {
    // FALSE (must-fail soundness): (a b : Nat)(h : a + 2 ≤ b) ⊢ b ≥ 3.
    // b could be 2 (a = 0). omega must reject, not over-accept.
    let a = nat_fvar(0);
    let b = nat_fvar(1);
    let h = nat_le_tc(nat_add(a, Expr::nat_lit(2)), b.clone());
    let goal = nat_ge(b, Expr::nat_lit(3));
    let state = state_with(
        vec![nat_local(0, "a"), nat_local(1, "b"), hyp(2, "h", h)],
        goal,
    );
    assert_omega_rejects(state, "(h : a + 2 ≤ b) ⊢ b ≥ 3");
}

#[test]
#[serial]
fn test_nonneg_eq_hyp_rejects_false_b_ge_3() {
    // FALSE (must-fail soundness): (a b : Nat)(h : a + 2 = b) ⊢ b ≥ 3.
    let a = nat_fvar(0);
    let b = nat_fvar(1);
    let h = nat_eq(nat_add(a, Expr::nat_lit(2)), b.clone());
    let goal = nat_ge(b, Expr::nat_lit(3));
    let state = state_with(
        vec![nat_local(0, "a"), nat_local(1, "b"), hyp(2, "h", h)],
        goal,
    );
    assert_omega_rejects(state, "(h : a + 2 = b) ⊢ b ≥ 3");
}

#[test]
#[serial]
fn test_nonneg_le_hyp_rejects_false_a_ge_1() {
    // FALSE (must-fail soundness): (a b : Nat)(h : a + 2 ≤ b) ⊢ a ≥ 1.
    // a could be 0. omega must reject — the implicit `a ≥ 0` does NOT give `a ≥ 1`.
    let a = nat_fvar(0);
    let b = nat_fvar(1);
    let h = nat_le_tc(nat_add(a.clone(), Expr::nat_lit(2)), b);
    let goal = nat_ge(a, Expr::nat_lit(1));
    let state = state_with(
        vec![nat_local(0, "a"), nat_local(1, "b"), hyp(2, "h", h)],
        goal,
    );
    assert_omega_rejects(state, "(h : a + 2 ≤ b) ⊢ a ≥ 1");
}

/// Surface `k * x` as the elaborator produces it: `@HMul.hMul Nat Nat Nat inst k x`
/// with the `Nat.mul`-backed `HMul` instance. Mirrors the shape omega sees for a
/// goal written `2 * a` in Lean source.
fn hmul(k: Expr, x: Expr) -> Expr {
    let z = Level::zero();
    let nat = nat_type;
    // instHMul for Nat: @HMul.mk Nat Nat Nat Nat.mul.
    let inst = Expr::apps(
        Expr::const_(
            Name::from_string("HMul.mk"),
            vec![z.clone(), z.clone(), z.clone()],
        ),
        [
            nat(),
            nat(),
            nat(),
            Expr::const_(Name::from_string("Nat.mul"), vec![]),
        ],
    );
    Expr::apps(
        Expr::const_(
            Name::from_string("HMul.hMul"),
            vec![z.clone(), z.clone(), z],
        ),
        [nat(), nat(), nat(), inst, k, x],
    )
}

/// SCALED monotonicity (the `c*a`-in-the-goal completeness fix): omega proves
/// `(h : a ≤ b) ⊢ 2 * a ≤ 2 * b` with a kernel-checked, trustedAy-free term.
/// The negated goal contributes `2*a` / `2*b`, and the equality synthesizer
/// expands those into `a + a` / `b + b` to match the doubled hypothesis sum.
#[test]
#[serial]
fn test_farkas_goal_proves_two_mul_a_le_two_mul_b_from_a_le_b() {
    let a = nat_fvar(0);
    let b = nat_fvar(1);
    let h = nat_le_tc(a.clone(), b.clone());
    let goal = nat_le_tc(hmul(Expr::nat_lit(2), a), hmul(Expr::nat_lit(2), b));
    let state = state_with(
        vec![nat_local(0, "a"), nat_local(1, "b"), hyp(2, "h", h)],
        goal,
    );
    assert_omega_proves(state, "(h : a ≤ b) ⊢ 2 * a ≤ 2 * b");
}

/// Must-fail counterpart: `2 * a = a + a + 1` is FALSE and omega must reject it
/// (no over-accept via a trusted residual, no panic).
#[test]
#[serial]
fn test_omega_rejects_false_two_mul_a_eq_a_plus_a_plus_1() {
    let a = nat_fvar(0);
    let lhs = hmul(Expr::nat_lit(2), a.clone());
    let rhs = nat_add(nat_add(a.clone(), a), Expr::nat_lit(1));
    let goal = nat_eq(lhs, rhs);
    let state = state_with(vec![nat_local(0, "a")], goal);
    assert_omega_rejects(state, "2 * a = a + a + 1 (FALSE)");
}

/// Genuinely NON-linear goal `a * b = b * a`: omega does not prove nonlinear
/// goals and must fail closed (no acceptance, no panic).
#[test]
#[serial]
fn test_omega_rejects_nonlinear_a_mul_b_eq_b_mul_a() {
    let a = nat_fvar(0);
    let b = nat_fvar(1);
    let goal = nat_eq(hmul(a.clone(), b.clone()), hmul(b, a));
    let state = state_with(vec![nat_local(0, "a"), nat_local(1, "b")], goal);
    assert_omega_rejects(state, "a * b = b * a (nonlinear)");
}
