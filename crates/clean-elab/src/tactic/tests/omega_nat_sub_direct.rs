// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end tests for the omega Nat-**subtraction** direct reconstruction path.
//!
//! `Nat.sub` is truncated subtraction (`a - b = 0` when `b > a`), which the
//! linear-form parser does not model — it would treat `a - b` as one opaque
//! atom (or, worse, as untruncated integer sub). omega now recognizes three
//! common, unconditionally-true Nat-subtraction goal shapes and emits the
//! *registered foundational lemma* for the matched shape, instead of falling
//! through to the decide/ay path (which produced a `trustedAy` residual):
//!
//! - `a - b ≤ a`        →  `@Nat.sub_le a b`
//! - `a - a = 0`        →  `@Nat.sub_self a`
//! - `a + b - b = a`    →  `@Nat.add_sub_cancel a b`
//!
//! Soundness teeth:
//! - PROVE: the three shapes above all close with ZERO trusted axioms.
//! - KERNEL CHECK + AXIOM CLOSURE: the synthesized term for `a - b ≤ a`
//!   type-checks against the goal via a real `clean_kernel::TypeChecker`, and
//!   its constant closure contains ZERO `trustedAy`/`trustedArith`/`sorryAx`.
//! - NEGATIVE: `a - b = a`, `a ≤ a - b`, `a - b ≥ b` are FALSE (for `b > 0`)
//!   and MUST still be rejected. The Int-true/Nat-false shape `a - b + b = a`
//!   must also stay unprovable (the linear parser must not model truncated Nat
//!   sub as integer sub).

use super::*;
use crate::tactic::arith_linarith_nat_direct::try_prove_nat_inequality_direct_with_hyps;
use crate::tactic::tc_app::nat_le_tc;
use clean_kernel::level::Level;
use clean_kernel::tc::TypeChecker;
use clean_kernel::Expr;
use serial_test::serial;
use std::collections::HashSet;

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
    Expr::apps(
        Expr::const_(Name::from_string("Nat.add"), vec![]),
        [lhs, rhs],
    )
}

fn nat_sub(lhs: Expr, rhs: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Nat.sub"), vec![]),
        [lhs, rhs],
    )
}

/// `@Eq Nat l r`.
fn nat_eq(l: Expr, r: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [nat_type(), l, r],
    )
}

fn collect_const_names(e: &Expr, out: &mut HashSet<String>) {
    use clean_kernel::expr::ExprKind;
    match e.kind() {
        ExprKind::Const(name, _) => {
            out.insert(name.to_string());
        }
        ExprKind::App(f, a) => {
            collect_const_names(f, out);
            collect_const_names(a, out);
        }
        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
            collect_const_names(ty, out);
            collect_const_names(body, out);
        }
        ExprKind::Let(_, ty, val, body, _) => {
            collect_const_names(ty, out);
            collect_const_names(val, out);
            collect_const_names(body, out);
        }
        _ => {}
    }
}

fn state_with(goal_target: Expr, ctx: Vec<LocalDecl>) -> ProofState {
    ProofState::with_context(Environment::with_prelude(), goal_target, ctx)
}

fn ctx_ab() -> Vec<LocalDecl> {
    vec![nat_local(0, "a"), nat_local(1, "b")]
}

fn assert_omega_proves(mut state: ProofState, label: &str) {
    reset_all_counters();
    let axiom_before = axiom_snapshot();
    let result = crate::tactic::omega_tactic::omega(&mut state);
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

fn assert_omega_rejects(mut state: ProofState, label: &str) {
    reset_all_counters();
    let result = crate::tactic::omega_tactic::omega(&mut state);
    assert!(
        result.is_err() && !state.is_complete(),
        "omega must REJECT the false sub goal `{label}`, but it closed: {result:?}"
    );
}

// ---- POSITIVE: the three recognized Nat-subtraction shapes ----

#[test]
#[serial]
fn test_omega_proves_a_sub_b_le_a() {
    // a b : Nat ⊢ a - b ≤ a        (Nat.sub_le)
    let a = nat_fvar(0);
    let b = nat_fvar(1);
    let goal = nat_le_tc(nat_sub(a.clone(), b), a);
    assert_omega_proves(state_with(goal, ctx_ab()), "a - b ≤ a");
}

#[test]
#[serial]
fn test_omega_proves_a_sub_a_eq_0() {
    // a : Nat ⊢ a - a = 0          (Nat.sub_self)
    let a = nat_fvar(0);
    let goal = nat_eq(nat_sub(a.clone(), a), Expr::nat_lit(0));
    assert_omega_proves(state_with(goal, vec![nat_local(0, "a")]), "a - a = 0");
}

#[test]
#[serial]
fn test_omega_proves_a_plus_b_sub_b_eq_a() {
    // a b : Nat ⊢ a + b - b = a    (Nat.add_sub_cancel)
    let a = nat_fvar(0);
    let b = nat_fvar(1);
    let goal = nat_eq(nat_sub(nat_add(a.clone(), b.clone()), b), a);
    assert_omega_proves(state_with(goal, ctx_ab()), "a + b - b = a");
}

/// Teeth: the synthesized term for `a - b ≤ a` type-checks against the goal via
/// a real kernel `TypeChecker`, uses `Nat.sub_le`, and references ZERO trust
/// axioms in its closure.
#[test]
#[serial]
fn test_omega_a_sub_b_le_a_term_kernel_checks_and_axiom_closure_clean() {
    let mut env = Environment::with_prelude();
    for nm in ["a", "b"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(nm),
            level_params: vec![],
            type_: nat_type(),
        })
        .expect("axiom should add");
    }
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let goal = nat_le_tc(nat_sub(a.clone(), b), a);

    let term = try_prove_nat_inequality_direct_with_hyps(&goal, &[])
        .expect("direct prover should synthesize a term for `a - b ≤ a`");

    let tc = TypeChecker::with_mode(&env, env.mode());
    tc.check_type(&term, &goal)
        .expect("synthesized term must check at goal `a - b ≤ a`");

    let mut consts = HashSet::new();
    collect_const_names(&term, &mut consts);
    for forbidden in ["trustedAy", "trustedArith", "sorry", "sorryAx"] {
        assert!(
            !consts.contains(forbidden),
            "synthesized term must not reference `{forbidden}`; closure = {consts:?}"
        );
    }
    assert!(
        consts.contains("Nat.sub_le"),
        "term should use Nat.sub_le; closure = {consts:?}"
    );
}

/// Full kernel acceptance for `a + b - b = a` (exercises `Nat.add_sub_cancel`).
#[test]
#[serial]
fn test_omega_add_sub_cancel_term_full_kernel_checks() {
    let mut env = Environment::with_prelude();
    for nm in ["a", "b"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(nm),
            level_params: vec![],
            type_: nat_type(),
        })
        .expect("axiom should add");
    }
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let goal = nat_eq(nat_sub(nat_add(a.clone(), b.clone()), b), a);

    let term = try_prove_nat_inequality_direct_with_hyps(&goal, &[])
        .expect("direct prover should synthesize a term for `a + b - b = a`");
    let tc = TypeChecker::with_mode(&env, env.mode());
    tc.check_type(&term, &goal)
        .expect("FULL kernel check must accept the `a + b - b = a` proof term");
    let mut consts = HashSet::new();
    collect_const_names(&term, &mut consts);
    assert!(
        consts.contains("Nat.add_sub_cancel"),
        "term should use Nat.add_sub_cancel; closure = {consts:?}"
    );
}

// ---- NEGATIVE: false sub goals must be rejected (fail closed) ----

#[test]
#[serial]
fn test_omega_rejects_a_sub_b_eq_a() {
    // a b : Nat ⊢ a - b = a        (FALSE for b > 0)
    let a = nat_fvar(0);
    let b = nat_fvar(1);
    let goal = nat_eq(nat_sub(a.clone(), b), a);
    assert_omega_rejects(state_with(goal, ctx_ab()), "a - b = a");
}

#[test]
#[serial]
fn test_omega_rejects_a_le_a_sub_b() {
    // a b : Nat ⊢ a ≤ a - b        (FALSE for b > 0)
    let a = nat_fvar(0);
    let b = nat_fvar(1);
    let goal = nat_le_tc(a.clone(), nat_sub(a, b));
    assert_omega_rejects(state_with(goal, ctx_ab()), "a ≤ a - b");
}

#[test]
#[serial]
fn test_omega_rejects_a_sub_b_ge_b() {
    // a b : Nat ⊢ a - b ≥ b        (FALSE; e.g. a=1,b=1 gives 0 ≥ 1)
    // `≥` normalizes to `Nat.le b (a - b)`, which is not the `Nat.sub_le` shape.
    let a = nat_fvar(0);
    let b = nat_fvar(1);
    // a - b ≥ b  ==  b ≤ a - b
    let goal = nat_le_tc(b.clone(), nat_sub(a, b));
    assert_omega_rejects(state_with(goal, ctx_ab()), "a - b ≥ b");
}

#[test]
#[serial]
fn test_omega_rejects_a_sub_b_plus_b_eq_a() {
    // a b : Nat ⊢ (a - b) + b = a  (Int-true but Nat-FALSE for b > a)
    // The linear parser must NOT model truncated Nat sub as integer sub, else
    // it would declare this a tautology. Must stay unprovable.
    let a = nat_fvar(0);
    let b = nat_fvar(1);
    let goal = nat_eq(nat_add(nat_sub(a.clone(), b.clone()), b), a);
    assert_omega_rejects(state_with(goal, ctx_ab()), "(a - b) + b = a");
}

// ---- Direct-prover unit teeth: false shapes must yield None ----

#[test]
fn test_direct_sub_prover_returns_none_on_false_shapes() {
    let a = nat_fvar(0);
    let b = nat_fvar(1);

    let false_eq = nat_eq(nat_sub(a.clone(), b.clone()), a.clone());
    assert!(
        try_prove_nat_inequality_direct_with_hyps(&false_eq, &[]).is_none(),
        "direct prover must reject `a - b = a`"
    );

    let false_le = nat_le_tc(a.clone(), nat_sub(a.clone(), b.clone()));
    assert!(
        try_prove_nat_inequality_direct_with_hyps(&false_le, &[]).is_none(),
        "direct prover must reject `a ≤ a - b`"
    );

    let false_ge = nat_le_tc(b.clone(), nat_sub(a.clone(), b.clone()));
    assert!(
        try_prove_nat_inequality_direct_with_hyps(&false_ge, &[]).is_none(),
        "direct prover must reject `a - b ≥ b` (== `b ≤ a - b`)"
    );

    // Int-true/Nat-false: must NOT synthesize a term.
    let int_true_nat_false = nat_eq(nat_add(nat_sub(a.clone(), b.clone()), b.clone()), a.clone());
    assert!(
        try_prove_nat_inequality_direct_with_hyps(&int_true_nat_false, &[]).is_none(),
        "direct prover must reject `(a - b) + b = a` (truncation-unsound on Nat)"
    );

    // `Nat.sub_self` must only fire when both operands match: `a - b = 0` is
    // FALSE in general and must not match the shape.
    let a_sub_b_eq_0 = nat_eq(nat_sub(a.clone(), b), Expr::nat_lit(0));
    assert!(
        try_prove_nat_inequality_direct_with_hyps(&a_sub_b_eq_0, &[]).is_none(),
        "direct prover must reject `a - b = 0` (Nat.sub_self only matches `a - a = 0`)"
    );
}
