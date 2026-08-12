// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end tests for the omega **Int** reconstruction path.
//!
//! omega now proves linear `Int` equality goals (`a + 0 = a`, `a + b = b + a`,
//! `-a + a = 0`), `a = b` from `Int` `≤`/`≥` bounds (via `Int.le_antisymm`), and
//! `False` from two contradictory `Int` equality hypotheses (`a + b = 3`,
//! `a + b = 5`), instead of falling through to `linarith`/`ay_lra` and erroring.
//!
//! Soundness teeth:
//! - PROVE: the five achievable positives above.
//! - KERNEL CHECK + AXIOM CLOSURE: the closed goals carry ZERO
//!   `trustedAy`/`trustedArith`/`sorry`, verified via the proof trust ledger and
//!   the axiom-usage snapshot (mirrors the Nat omega teeth).
//! - NEGATIVE: `a + 1 = a`, `a + b = 3 ⊢ a + b = 4`, and `a = b` (no bounds) are
//!   FALSE / unprovable and MUST be rejected.
//! - DEFERRED: `a + a = 2 * a` needs a literal-coefficient-multiplication lemma
//!   (`Int.two_mul` / `Int.mul_comm` / `Int.right_distrib`) that the prelude does
//!   NOT register — a kernel change, out of scope. omega currently fails closed
//!   on it; the direct prover returns `None` (asserted below).

use super::*;
use crate::tactic::arith_linarith_int_eq::try_prove_int_equality;
use clean_kernel::level::Level;
use clean_kernel::Expr;
use serial_test::serial;
use std::collections::HashSet;

fn int_type() -> Expr {
    Expr::const_(Name::from_string("Int"), vec![])
}

fn int_fvar(id: u64) -> Expr {
    Expr::fvar(FVarId::new(id))
}

fn int_local(id: u64, name: &str) -> LocalDecl {
    LocalDecl {
        fvar: FVarId::new(id),
        name: name.to_string(),
        ty: int_type(),
        value: None,
    }
}

/// `Int.add l r` — the CORE head. The real Lean surface `l + r`
/// (`HAdd.hAdd Int Int Int instHAdd l r`) is def-eq to this and closes via the
/// same prover + `close_goal` path (the surface-form coverage is exercised by
/// the `clean check` `.lean` teeth); the unit tests build the core head so the
/// fresh-`ProofState` `is_def_eq` does not depend on reducing a hand-built
/// instance literal.
fn int_add(l: Expr, r: Expr) -> Expr {
    Expr::apps(Expr::const_(Name::from_string("Int.add"), vec![]), [l, r])
}

/// Core `-a` = `Int.neg a`.
fn int_neg(a: Expr) -> Expr {
    Expr::apps(Expr::const_(Name::from_string("Int.neg"), vec![]), [a])
}

/// Int literal `n` as `Int.ofNat n` (the surface elaboration of a nonneg Int
/// literal).
fn int_lit(n: u64) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Int.ofNat"), vec![]),
        [Expr::nat_lit(n)],
    )
}

/// `2 * a` core form `Int.mul 2 a` (the DEFERRED literal-coefficient shape).
fn int_mul(l: Expr, r: Expr) -> Expr {
    Expr::apps(Expr::const_(Name::from_string("Int.mul"), vec![]), [l, r])
}

/// `@Eq Int l r`.
fn int_eq(l: Expr, r: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [int_type(), l, r],
    )
}

/// Core `Int.le a b` (`a ≤ b`). The surface `a ≥ b`
/// (`GE.ge Int instLEInt a b`) reduces to `Int.le b a`; the unit test uses the
/// core head to avoid depending on a hand-built instance literal reducing in a
/// fresh `ProofState` (the surface `≥` form is covered by the `clean check`
/// `.lean` teeth). `a ≥ b` is spelled here as `Int.le b a`.
fn int_le(a: Expr, b: Expr) -> Expr {
    Expr::apps(Expr::const_(Name::from_string("Int.le"), vec![]), [a, b])
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
    // No trusted axiom / no trustedAy — the authoritative trust teeth.
    assert_no_trusted_axiom_usage("omega", label, axiom_before);
    let ledger = state.trust_ledger();
    assert_eq!(
        ledger.trusted_arith_count, 0,
        "`{label}`: omega must not use trustedArith"
    );
    assert_eq!(
        ledger.trusted_ay_count, 0,
        "`{label}`: accepted omega proof must NOT carry trustedAy"
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
        "omega must REJECT `{label}`, but it closed: {result:?}"
    );
}

// ---- POSITIVE: the five achievable Int cases ----

#[test]
#[serial]
fn test_omega_int_a_plus_0_eq_a() {
    // a : Int ⊢ a + 0 = a
    let a = int_fvar(0);
    let goal = int_eq(int_add(a.clone(), int_lit(0)), a);
    assert_omega_proves(state_with(goal, vec![int_local(0, "a")]), "Int a + 0 = a");
}

#[test]
#[serial]
fn test_omega_int_a_plus_b_eq_b_plus_a() {
    // a b : Int ⊢ a + b = b + a
    let a = int_fvar(0);
    let b = int_fvar(1);
    let goal = int_eq(int_add(a.clone(), b.clone()), int_add(b, a));
    assert_omega_proves(
        state_with(goal, vec![int_local(0, "a"), int_local(1, "b")]),
        "Int a + b = b + a",
    );
}

#[test]
#[serial]
fn test_omega_int_neg_a_plus_a_eq_0() {
    // a : Int ⊢ -a + a = 0
    let a = int_fvar(0);
    let goal = int_eq(int_add(int_neg(a.clone()), a), int_lit(0));
    assert_omega_proves(state_with(goal, vec![int_local(0, "a")]), "Int -a + a = 0");
}

#[test]
#[serial]
fn test_omega_int_a_plus_neg_a_eq_0() {
    // a : Int ⊢ a + -a = 0  (mirror; exercises Int.add_neg_self)
    let a = int_fvar(0);
    let goal = int_eq(int_add(a.clone(), int_neg(a.clone())), int_lit(0));
    assert_omega_proves(state_with(goal, vec![int_local(0, "a")]), "Int a + -a = 0");
}

#[test]
#[serial]
fn test_omega_int_eq_from_ge_ge() {
    // a b : Int, h : a ≥ b (= Int.le b a), h2 : b ≥ a (= Int.le a b) ⊢ a = b.
    let a = int_fvar(0);
    let b = int_fvar(1);
    let h = LocalDecl {
        fvar: FVarId::new(2),
        name: "h".into(),
        ty: int_le(b.clone(), a.clone()),
        value: None,
    };
    let h2 = LocalDecl {
        fvar: FVarId::new(3),
        name: "h2".into(),
        ty: int_le(a.clone(), b.clone()),
        value: None,
    };
    let goal = int_eq(a, b);
    assert_omega_proves(
        state_with(goal, vec![int_local(0, "a"), int_local(1, "b"), h, h2]),
        "Int a ≥ b, b ≥ a ⊢ a = b",
    );
}

#[test]
#[serial]
fn test_omega_int_false_from_contradictory_eq_hyps() {
    // a b : Int, h1 : a + b = 3, h2 : a + b = 5 ⊢ False
    let a = int_fvar(0);
    let b = int_fvar(1);
    let ab = int_add(a.clone(), b.clone());
    let h1 = LocalDecl {
        fvar: FVarId::new(2),
        name: "h1".into(),
        ty: int_eq(ab.clone(), int_lit(3)),
        value: None,
    };
    let h2 = LocalDecl {
        fvar: FVarId::new(3),
        name: "h2".into(),
        ty: int_eq(ab, int_lit(5)),
        value: None,
    };
    let goal = Expr::const_(Name::from_string("False"), vec![]);
    assert_omega_proves(
        state_with(goal, vec![int_local(0, "a"), int_local(1, "b"), h1, h2]),
        "Int a+b=3, a+b=5 ⊢ False",
    );
}

// ---- TEETH: kernel check + axiom closure of the free-var equality terms ----

#[test]
#[serial]
fn test_omega_int_eq_term_kernel_checks_and_axiom_closure_clean() {
    use clean_kernel::tc::TypeChecker;
    let mut env = Environment::with_prelude();
    for nm in ["a", "b"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(nm),
            level_params: vec![],
            type_: int_type(),
        })
        .expect("axiom should add");
    }
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let goal = int_eq(int_add(a.clone(), b.clone()), int_add(b, a));

    let term = try_prove_int_equality(&goal)
        .expect("direct Int prover should synthesize a term for `a + b = b + a`");

    let tc = TypeChecker::with_mode(&env, env.mode());
    tc.check_type(&term, &goal)
        .expect("synthesized Int term must check at goal `a + b = b + a`");

    let mut consts = HashSet::new();
    collect_const_names(&term, &mut consts);
    for forbidden in ["trustedAy", "trustedArith", "sorry", "sorryAx"] {
        assert!(
            !consts.contains(forbidden),
            "synthesized Int term must not reference `{forbidden}`; closure = {consts:?}"
        );
    }
    assert!(
        consts.contains("Int.add_comm"),
        "term should use Int.add_comm; closure = {consts:?}"
    );
}

// ---- NEGATIVE: false / unprovable Int goals must be rejected ----

#[test]
#[serial]
fn test_omega_int_rejects_a_plus_1_eq_a() {
    // a : Int ⊢ a + 1 = a   (FALSE)
    let a = int_fvar(0);
    let goal = int_eq(int_add(a.clone(), int_lit(1)), a);
    assert_omega_rejects(state_with(goal, vec![int_local(0, "a")]), "Int a + 1 = a");
}

#[test]
#[serial]
fn test_omega_int_rejects_a_plus_b_eq_4_from_eq_3() {
    // a b : Int, h : a + b = 3 ⊢ a + b = 4   (FALSE)
    let a = int_fvar(0);
    let b = int_fvar(1);
    let ab = int_add(a.clone(), b.clone());
    let h = LocalDecl {
        fvar: FVarId::new(2),
        name: "h".into(),
        ty: int_eq(ab.clone(), int_lit(3)),
        value: None,
    };
    let goal = int_eq(ab, int_lit(4));
    assert_omega_rejects(
        state_with(goal, vec![int_local(0, "a"), int_local(1, "b"), h]),
        "Int a+b=3 ⊢ a+b=4",
    );
}

#[test]
#[serial]
fn test_omega_int_rejects_a_eq_b_no_bounds() {
    // a b : Int ⊢ a = b   (unprovable, no hypotheses)
    let a = int_fvar(0);
    let b = int_fvar(1);
    let goal = int_eq(a, b);
    assert_omega_rejects(
        state_with(goal, vec![int_local(0, "a"), int_local(1, "b")]),
        "Int a = b (no bounds)",
    );
}

// ---- Direct-prover unit teeth: false equalities return None ----

#[test]
fn test_direct_int_eq_prover_returns_none_on_false_goals() {
    let a = int_fvar(0);
    let false_eq = int_eq(int_add(a.clone(), int_lit(1)), a.clone());
    assert!(
        try_prove_int_equality(&false_eq).is_none(),
        "direct Int prover must reject `a + 1 = a`"
    );
    let a_eq_b = int_eq(a, int_fvar(1));
    assert!(
        try_prove_int_equality(&a_eq_b).is_none(),
        "direct Int prover must reject `a = b`"
    );
}

// ---- DEFERRED: literal-coefficient multiplication is out of scope ----

/// `a + a = 2 * a` is TRUE but needs `Int.two_mul` / `Int.mul_comm` /
/// `Int.right_distrib`, none of which the prelude registers. Registering one is a
/// kernel change (out of scope), so the direct Int prover returns `None` and
/// omega fails closed. This asserts the DEFERRAL is explicit and stable (not a
/// silent over-accept).
#[test]
fn test_direct_int_eq_prover_defers_literal_mul() {
    let a = int_fvar(0);
    // a + a = 2 * a
    let goal = int_eq(
        int_add(a.clone(), a.clone()),
        int_mul(int_lit(2), a.clone()),
    );
    assert!(
        try_prove_int_equality(&goal).is_none(),
        "literal-coefficient multiplication `a + a = 2 * a` is DEFERRED (needs an \
         unregistered kernel lemma); the direct prover must return None"
    );
}
