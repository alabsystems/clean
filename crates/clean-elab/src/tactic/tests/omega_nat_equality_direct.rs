// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end tests for the omega Nat-**equality** direct reconstruction path.
//!
//! omega now proves linear Nat equality goals such as `a + b = b + a` and
//! `a + b + c = c + b + a` by deciding on the canonical linear form and
//! synthesizing a kernel-checked `Nat.add_comm` / `Nat.add_assoc` rewrite chain
//! (zero domain axioms), instead of failing closed.
//!
//! Soundness teeth:
//! - PROVE: `a + b = b + a`, `a + b + c = c + b + a`, `a + 0 = a`, `2*a = a+a`,
//!   `3*a = a+a+a`, `a*2 = a+a` (literal-coefficient multiplication expansion).
//! - KERNEL CHECK + AXIOM CLOSURE: the synthesized terms for `a + b = b + a` and
//!   `2*a = a+a` type-check against the goal via a real
//!   `clean_kernel::TypeChecker`, and their constant closures contain ZERO
//!   `trustedAy`/`trustedArith`/`sorryAx`.
//! - NEGATIVE: `a + b = a`, `a = b`, `a + b = a + b + 1`, `2*a = a` are FALSE
//!   and MUST be rejected (omega must never prove a false equality).

use super::*;
use crate::tactic::arith_linarith_nat_eq::try_prove_nat_equality_direct;
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

fn nat_mul(lhs: Expr, rhs: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Nat.mul"), vec![]),
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

fn assert_omega_rejects(mut state: ProofState, label: &str) {
    reset_all_counters();
    let result = omega(&mut state);
    assert!(
        result.is_err() && !state.is_complete(),
        "omega must REJECT the false equality `{label}`, but it closed: {result:?}"
    );
}

// ---- POSITIVE: common provable shapes ----

#[test]
#[serial]
fn test_omega_proves_a_plus_b_eq_b_plus_a() {
    // a b : Nat ⊢ a + b = b + a
    let a = nat_fvar(0);
    let b = nat_fvar(1);
    let goal = nat_eq(nat_add(a.clone(), b.clone()), nat_add(b, a));
    assert_omega_proves(
        state_with(goal, vec![nat_local(0, "a"), nat_local(1, "b")]),
        "a + b = b + a",
    );
}

#[test]
#[serial]
fn test_omega_proves_a_plus_b_plus_c_eq_c_plus_b_plus_a() {
    // a b c : Nat ⊢ (a + b) + c = (c + b) + a
    let a = nat_fvar(0);
    let b = nat_fvar(1);
    let c = nat_fvar(2);
    let lhs = nat_add(nat_add(a.clone(), b.clone()), c.clone());
    let rhs = nat_add(nat_add(c, b), a);
    let goal = nat_eq(lhs, rhs);
    assert_omega_proves(
        state_with(
            goal,
            vec![nat_local(0, "a"), nat_local(1, "b"), nat_local(2, "c")],
        ),
        "a + b + c = c + b + a",
    );
}

#[test]
#[serial]
fn test_omega_proves_a_plus_0_eq_a() {
    // a : Nat ⊢ a + 0 = a   (reduce_eq or linear form both handle this)
    let a = nat_fvar(0);
    let goal = nat_eq(nat_add(a.clone(), Expr::nat_lit(0)), a);
    assert_omega_proves(state_with(goal, vec![nat_local(0, "a")]), "a + 0 = a");
}

/// LANDED (literal-coeff expansion): `2 * a = a + a` is TRUE and now proved by
/// the direct synthesizer, which expands the `2 * a` leaf into `a + a` via a
/// `Nat.succ_mul` / `Nat.one_mul` unfolding chain, then closes the residual
/// additive permutation. The term is kernel-checked by omega's `close_goal`.
#[test]
#[serial]
fn test_omega_proves_two_mul_a_eq_a_plus_a() {
    let a = nat_fvar(0);
    let goal = nat_eq(
        nat_mul(Expr::nat_lit(2), a.clone()),
        nat_add(a.clone(), a.clone()),
    );
    assert_omega_proves(state_with(goal, vec![nat_local(0, "a")]), "2 * a = a + a");
}

/// `3 * a = a + a + a` (left literal, k = 3): the succ_mul chain peels two `a`s
/// and closes on `Nat.one_mul`.
#[test]
#[serial]
fn test_omega_proves_three_mul_a_eq_a_plus_a_plus_a() {
    let a = nat_fvar(0);
    let lhs = nat_mul(Expr::nat_lit(3), a.clone());
    let rhs = nat_add(nat_add(a.clone(), a.clone()), a.clone());
    let goal = nat_eq(lhs, rhs);
    assert_omega_proves(
        state_with(goal, vec![nat_local(0, "a")]),
        "3 * a = a + a + a",
    );
}

/// `a * 2 = a + a` (right literal): the `Nat.mul_succ` / `Nat.mul_one` chain
/// expands the right-oriented factor.
#[test]
#[serial]
fn test_omega_proves_a_mul_two_eq_a_plus_a() {
    let a = nat_fvar(0);
    let goal = nat_eq(
        nat_mul(a.clone(), Expr::nat_lit(2)),
        nat_add(a.clone(), a.clone()),
    );
    assert_omega_proves(state_with(goal, vec![nat_local(0, "a")]), "a * 2 = a + a");
}

/// TEETH: the synthesized `2 * a = a + a` term type-checks against the goal via
/// a real kernel `TypeChecker`, and its constant closure contains ZERO trust
/// axioms and only foundational Nat lemmas (`Nat.succ_mul`, `Nat.one_mul`,
/// `Nat.add_comm`/`Nat.add_assoc` as needed).
#[test]
#[serial]
fn test_omega_two_mul_term_kernel_checks_and_axiom_closure_clean() {
    let mut env = Environment::with_prelude();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("a"),
        level_params: vec![],
        type_: nat_type(),
    })
    .expect("axiom should add");
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let goal = nat_eq(nat_mul(Expr::nat_lit(2), a.clone()), nat_add(a.clone(), a));

    let term = try_prove_nat_equality_direct(&goal)
        .expect("direct prover should synthesize a term for `2 * a = a + a`");

    let tc = TypeChecker::with_mode(&env, env.mode());
    let inferred = tc
        .infer_type(&term)
        .expect("synthesized `2 * a = a + a` term must type-check in the kernel");
    tc.check_type(&term, &goal).unwrap_or_else(|err| {
        panic!(
            "synthesized term must check at goal `2 * a = a + a`: {err:?}\n  inferred = {inferred:?}\n  goal = {goal:?}"
        )
    });

    let mut consts = HashSet::new();
    collect_const_names(&term, &mut consts);
    for forbidden in ["trustedAy", "trustedArith", "sorry", "sorryAx"] {
        assert!(
            !consts.contains(forbidden),
            "synthesized term must not reference `{forbidden}`; closure = {consts:?}"
        );
    }
    assert!(
        consts.contains("Nat.succ_mul"),
        "term should use Nat.succ_mul to expand `2 * a`; closure = {consts:?}"
    );
}

/// The teeth: the synthesized term for `a + b = b + a` type-checks against the
/// goal via a real kernel `TypeChecker`, with ZERO trust axioms in its closure.
#[test]
#[serial]
fn test_omega_a_plus_b_eq_b_plus_a_term_kernel_checks_and_axiom_closure_clean() {
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
    let goal = nat_eq(nat_add(a.clone(), b.clone()), nat_add(b, a));

    let term = try_prove_nat_equality_direct(&goal)
        .expect("direct prover should synthesize a term for `a + b = b + a`");

    let tc = TypeChecker::with_mode(&env, env.mode());
    let inferred = tc
        .infer_type(&term)
        .expect("synthesized term for `a + b = b + a` must type-check in the kernel");
    tc.check_type(&term, &goal).unwrap_or_else(|err| {
        panic!(
            "synthesized term must check at goal `a + b = b + a`: {err:?}\n  inferred = {inferred:?}\n  goal = {goal:?}"
        )
    });

    let mut consts = HashSet::new();
    collect_const_names(&term, &mut consts);
    for forbidden in ["trustedAy", "trustedArith", "sorry", "sorryAx"] {
        assert!(
            !consts.contains(forbidden),
            "synthesized term must not reference `{forbidden}`; closure = {consts:?}"
        );
    }
    assert!(
        consts.contains("Nat.add_comm"),
        "term should use Nat.add_comm; closure = {consts:?}"
    );
}

/// Full kernel acceptance for the 3-atom permutation (exercises the
/// add_assoc/congrArg bubble-sort chain at infer_only=false).
#[test]
#[serial]
fn test_omega_3atom_perm_term_full_kernel_checks() {
    let mut env = Environment::with_prelude();
    for nm in ["a", "b", "c"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(nm),
            level_params: vec![],
            type_: nat_type(),
        })
        .expect("axiom should add");
    }
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let c = Expr::const_(Name::from_string("c"), vec![]);
    let lhs = nat_add(nat_add(a.clone(), b.clone()), c.clone());
    let rhs = nat_add(nat_add(c, b), a);
    let goal = nat_eq(lhs, rhs);

    let term = try_prove_nat_equality_direct(&goal)
        .expect("direct prover should synthesize a term for `a + b + c = c + b + a`");
    let tc = TypeChecker::with_mode(&env, env.mode());
    tc.check_type(&term, &goal)
        .expect("FULL kernel check must accept the 3-atom permutation proof term");
}

// ---- NEGATIVE: false equalities must be rejected ----

#[test]
#[serial]
fn test_omega_rejects_a_plus_b_eq_a() {
    // a b : Nat ⊢ a + b = a   (FALSE)
    let a = nat_fvar(0);
    let b = nat_fvar(1);
    let goal = nat_eq(nat_add(a.clone(), b), a);
    assert_omega_rejects(
        state_with(goal, vec![nat_local(0, "a"), nat_local(1, "b")]),
        "a + b = a",
    );
}

#[test]
#[serial]
fn test_omega_rejects_a_eq_b() {
    // a b : Nat ⊢ a = b   (FALSE)
    let a = nat_fvar(0);
    let b = nat_fvar(1);
    let goal = nat_eq(a, b);
    assert_omega_rejects(
        state_with(goal, vec![nat_local(0, "a"), nat_local(1, "b")]),
        "a = b",
    );
}

#[test]
#[serial]
fn test_omega_rejects_a_plus_b_eq_a_plus_b_plus_1() {
    // a b : Nat ⊢ a + b = a + b + 1   (FALSE)
    let a = nat_fvar(0);
    let b = nat_fvar(1);
    let lhs = nat_add(a.clone(), b.clone());
    let rhs = nat_add(nat_add(a, b), Expr::nat_lit(1));
    let goal = nat_eq(lhs, rhs);
    assert_omega_rejects(
        state_with(goal, vec![nat_local(0, "a"), nat_local(1, "b")]),
        "a + b = a + b + 1",
    );
}

#[test]
#[serial]
fn test_omega_rejects_two_mul_a_eq_a() {
    // a : Nat ⊢ 2 * a = a   (FALSE)
    let a = nat_fvar(0);
    let goal = nat_eq(nat_mul(Expr::nat_lit(2), a.clone()), a);
    assert_omega_rejects(state_with(goal, vec![nat_local(0, "a")]), "2 * a = a");
}

/// Direct-prover unit teeth: it must return `None` for false equality goals so
/// omega can fail closed.
#[test]
fn test_direct_eq_prover_returns_none_on_false_goals() {
    let a = nat_fvar(0);
    let b = nat_fvar(1);
    let false_eq = nat_eq(nat_add(a.clone(), b.clone()), a.clone());
    assert!(
        try_prove_nat_equality_direct(&false_eq).is_none(),
        "direct prover must reject `a + b = a`"
    );
    let a_eq_b = nat_eq(a, b);
    assert!(
        try_prove_nat_equality_direct(&a_eq_b).is_none(),
        "direct prover must reject `a = b`"
    );
}

/// A fabricated reflexivity term claiming to prove a FALSE equality must be
/// rejected by the full kernel check.
#[test]
#[serial]
fn test_full_kernel_rejects_fabricated_false_eq_refl() {
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
    // Eq.refl a : a = a. Claim it proves the FALSE goal a = b.
    let bogus = Expr::apps(
        Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        ),
        [nat_type(), a.clone()],
    );
    let false_goal = nat_eq(a, b);
    let tc = TypeChecker::with_mode(&env, env.mode());
    assert!(
        tc.check_type(&bogus, &false_goal).is_err(),
        "kernel must reject `Eq.refl a` claimed at false goal `a = b`"
    );
}
