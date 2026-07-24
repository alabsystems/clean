// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end tests for the omega Nat min/max direct reconstruction path.
//!
//! `Nat.min` / `Nat.max` are non-linear `Bool.rec`-over-`Nat.ble` definitions
//! that the linear-form parser does not model — an App-headed `Nat.min a b`
//! falls through to `None`, so the linear/FM path refuses the goal. omega now
//! recognizes the common, unconditionally-true min/max goal shapes and emits the
//! *registered foundational lemma* for the matched shape:
//!
//! Inequality shapes:
//! - `min a b ≤ a`  →  `@Nat.min_le_left a b`
//! - `min a b ≤ b`  →  `@Nat.min_le_right a b`
//! - `a ≤ max a b`  →  `@Nat.le_max_left a b`
//! - `b ≤ max a b`  →  `@Nat.le_max_right a b`
//!
//! Equality shapes:
//! - `min a b = min b a`  →  `@Nat.min_comm a b`
//! - `max a b = max b a`  →  `@Nat.max_comm a b`
//! - `min a a = a`        →  `@Nat.min_self a`
//! - `max a a = a`        →  `@Nat.max_self a`
//!
//! Soundness teeth:
//! - PROVE: each shape above closes with ZERO trusted axioms.
//! - KERNEL CHECK + AXIOM CLOSURE: the synthesized term type-checks against the
//!   goal via a real `clean_kernel::TypeChecker`, and its constant closure
//!   contains ZERO `trustedAy`/`trustedArith`/`sorryAx`.
//! - NEGATIVE: `a ≤ min a b`, `max a b ≤ a`, `min a b = a` (all FALSE for the
//!   relevant witnesses) and `min a b = min b c` with `b ≠ c` MUST be rejected.

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

fn nat_min(lhs: Expr, rhs: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Nat.min"), vec![]),
        [lhs, rhs],
    )
}

fn nat_max(lhs: Expr, rhs: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Nat.max"), vec![]),
        [lhs, rhs],
    )
}

/// The surface-elaborated `min a b` form: `@Min.min Nat instMinNat a b`.
///
/// This is what `clean check` produces for the surface token `min` after the
/// `Min` class + `instMinNat` instance are registered in `with_prelude`. The
/// recognizer must peel the projection head back to `Nat.min` and emit the same
/// foundational lemma it would for the bare op.
fn min_proj(lhs: Expr, rhs: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Min.min"), vec![Level::zero()]),
        [
            nat_type(),
            Expr::const_(Name::from_string("instMinNat"), vec![]),
            lhs,
            rhs,
        ],
    )
}

/// The surface-elaborated `max a b` form: `@Max.max Nat instMaxNat a b`.
fn max_proj(lhs: Expr, rhs: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Max.max"), vec![Level::zero()]),
        [
            nat_type(),
            Expr::const_(Name::from_string("instMaxNat"), vec![]),
            lhs,
            rhs,
        ],
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
        "omega must REJECT the false min/max goal `{label}`, but it closed: {result:?}"
    );
}

/// Build an env with `a`/`b`/`c` registered as opaque Nat constants, plus a
/// kernel type-check that the synthesized term has the goal type and references
/// the expected lemma with a clean axiom closure.
fn assert_term_kernel_checks(goal: &Expr, expected_lemma: &str, label: &str) {
    let mut env = Environment::with_prelude();
    for nm in ["a", "b", "c"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(nm),
            level_params: vec![],
            type_: nat_type(),
        })
        .expect("axiom should add");
    }

    let term = try_prove_nat_inequality_direct_with_hyps(goal, &[])
        .unwrap_or_else(|| panic!("direct prover should synthesize a term for `{label}`"));

    let tc = TypeChecker::with_mode(&env, env.mode());
    tc.check_type(&term, goal)
        .unwrap_or_else(|e| panic!("synthesized term must check at goal `{label}`: {e:?}"));

    let mut consts = HashSet::new();
    collect_const_names(&term, &mut consts);
    for forbidden in ["trustedAy", "trustedArith", "sorry", "sorryAx"] {
        assert!(
            !consts.contains(forbidden),
            "`{label}`: synthesized term must not reference `{forbidden}`; closure = {consts:?}"
        );
    }
    assert!(
        consts.contains(expected_lemma),
        "`{label}`: term should use `{expected_lemma}`; closure = {consts:?}"
    );
}

/// Build the same goal but over the registered constants `a`/`b` (for the
/// kernel-check helper, which needs closed terms).
fn const_a() -> Expr {
    Expr::const_(Name::from_string("a"), vec![])
}
fn const_b() -> Expr {
    Expr::const_(Name::from_string("b"), vec![])
}
fn const_c() -> Expr {
    Expr::const_(Name::from_string("c"), vec![])
}

// ---- POSITIVE: inequality shapes ----

#[test]
#[serial]
fn test_omega_proves_min_a_b_le_a() {
    // a b : Nat ⊢ min a b ≤ a     (Nat.min_le_left)
    let a = nat_fvar(0);
    let b = nat_fvar(1);
    let goal = nat_le_tc(nat_min(a.clone(), b), a);
    assert_omega_proves(state_with(goal, ctx_ab()), "min a b ≤ a");
}

#[test]
#[serial]
fn test_omega_proves_min_a_b_le_b() {
    // a b : Nat ⊢ min a b ≤ b     (Nat.min_le_right)
    let a = nat_fvar(0);
    let b = nat_fvar(1);
    let goal = nat_le_tc(nat_min(a, b.clone()), b);
    assert_omega_proves(state_with(goal, ctx_ab()), "min a b ≤ b");
}

#[test]
#[serial]
fn test_omega_proves_a_le_max_a_b() {
    // a b : Nat ⊢ a ≤ max a b     (Nat.le_max_left)
    let a = nat_fvar(0);
    let b = nat_fvar(1);
    let goal = nat_le_tc(a.clone(), nat_max(a, b));
    assert_omega_proves(state_with(goal, ctx_ab()), "a ≤ max a b");
}

#[test]
#[serial]
fn test_omega_proves_b_le_max_a_b() {
    // a b : Nat ⊢ b ≤ max a b     (Nat.le_max_right)
    let a = nat_fvar(0);
    let b = nat_fvar(1);
    let goal = nat_le_tc(b.clone(), nat_max(a, b));
    assert_omega_proves(state_with(goal, ctx_ab()), "b ≤ max a b");
}

// ---- POSITIVE: equality shapes ----

#[test]
#[serial]
fn test_omega_proves_min_comm() {
    // a b : Nat ⊢ min a b = min b a     (Nat.min_comm)
    let a = nat_fvar(0);
    let b = nat_fvar(1);
    let goal = nat_eq(nat_min(a.clone(), b.clone()), nat_min(b, a));
    assert_omega_proves(state_with(goal, ctx_ab()), "min a b = min b a");
}

#[test]
#[serial]
fn test_omega_proves_max_comm() {
    // a b : Nat ⊢ max a b = max b a     (Nat.max_comm)
    let a = nat_fvar(0);
    let b = nat_fvar(1);
    let goal = nat_eq(nat_max(a.clone(), b.clone()), nat_max(b, a));
    assert_omega_proves(state_with(goal, ctx_ab()), "max a b = max b a");
}

#[test]
#[serial]
fn test_omega_proves_min_self() {
    // a : Nat ⊢ min a a = a     (Nat.min_self)
    let a = nat_fvar(0);
    let goal = nat_eq(nat_min(a.clone(), a.clone()), a);
    assert_omega_proves(state_with(goal, vec![nat_local(0, "a")]), "min a a = a");
}

#[test]
#[serial]
fn test_omega_proves_max_self() {
    // a : Nat ⊢ max a a = a     (Nat.max_self)
    let a = nat_fvar(0);
    let goal = nat_eq(nat_max(a.clone(), a.clone()), a);
    assert_omega_proves(state_with(goal, vec![nat_local(0, "a")]), "max a a = a");
}

// ---- KERNEL-CHECK + axiom-closure teeth ----

#[test]
#[serial]
fn test_omega_min_le_left_term_kernel_checks_and_axiom_closure_clean() {
    let goal = nat_le_tc(nat_min(const_a(), const_b()), const_a());
    assert_term_kernel_checks(&goal, "Nat.min_le_left", "min a b ≤ a");
}

#[test]
#[serial]
fn test_omega_le_max_right_term_kernel_checks() {
    let goal = nat_le_tc(const_b(), nat_max(const_a(), const_b()));
    assert_term_kernel_checks(&goal, "Nat.le_max_right", "b ≤ max a b");
}

#[test]
#[serial]
fn test_omega_min_comm_term_kernel_checks() {
    let goal = nat_eq(nat_min(const_a(), const_b()), nat_min(const_b(), const_a()));
    assert_term_kernel_checks(&goal, "Nat.min_comm", "min a b = min b a");
}

#[test]
#[serial]
fn test_omega_min_self_term_kernel_checks() {
    let goal = nat_eq(nat_min(const_a(), const_a()), const_a());
    assert_term_kernel_checks(&goal, "Nat.min_self", "min a a = a");
}

#[test]
#[serial]
fn test_omega_max_self_term_kernel_checks() {
    let goal = nat_eq(nat_max(const_a(), const_a()), const_a());
    assert_term_kernel_checks(&goal, "Nat.max_self", "max a a = a");
}

// ---- NEGATIVE: false min/max goals must be rejected (fail closed) ----

#[test]
#[serial]
fn test_omega_rejects_a_le_min_a_b() {
    // a b : Nat ⊢ a ≤ min a b      (FALSE for b < a)
    let a = nat_fvar(0);
    let b = nat_fvar(1);
    let goal = nat_le_tc(a.clone(), nat_min(a, b));
    assert_omega_rejects(state_with(goal, ctx_ab()), "a ≤ min a b");
}

#[test]
#[serial]
fn test_omega_rejects_max_a_b_le_a() {
    // a b : Nat ⊢ max a b ≤ a      (FALSE for b > a)
    let a = nat_fvar(0);
    let b = nat_fvar(1);
    let goal = nat_le_tc(nat_max(a.clone(), b), a);
    assert_omega_rejects(state_with(goal, ctx_ab()), "max a b ≤ a");
}

#[test]
#[serial]
fn test_omega_rejects_min_a_b_eq_a() {
    // a b : Nat ⊢ min a b = a      (FALSE for b < a, symbolic)
    let a = nat_fvar(0);
    let b = nat_fvar(1);
    let goal = nat_eq(nat_min(a.clone(), b), a);
    assert_omega_rejects(state_with(goal, ctx_ab()), "min a b = a");
}

#[test]
#[serial]
fn test_omega_rejects_min_a_b_eq_min_b_c() {
    // a b c : Nat ⊢ min a b = min b c   (FALSE; not a comm shape, a ≠ c)
    let a = nat_fvar(0);
    let b = nat_fvar(1);
    let cc = nat_fvar(2);
    let goal = nat_eq(nat_min(a, b.clone()), nat_min(b, cc));
    assert_omega_rejects(
        state_with(
            goal,
            vec![nat_local(0, "a"), nat_local(1, "b"), nat_local(2, "c")],
        ),
        "min a b = min b c",
    );
}

// ---- Direct-prover unit teeth: false shapes must yield None ----

#[test]
fn test_direct_minmax_prover_returns_none_on_false_shapes() {
    let a = nat_fvar(0);
    let b = nat_fvar(1);
    let cc = nat_fvar(2);

    // a ≤ min a b  (false for b < a)
    let f1 = nat_le_tc(a.clone(), nat_min(a.clone(), b.clone()));
    assert!(
        try_prove_nat_inequality_direct_with_hyps(&f1, &[]).is_none(),
        "direct prover must reject `a ≤ min a b`"
    );

    // max a b ≤ a  (false for b > a)
    let f2 = nat_le_tc(nat_max(a.clone(), b.clone()), a.clone());
    assert!(
        try_prove_nat_inequality_direct_with_hyps(&f2, &[]).is_none(),
        "direct prover must reject `max a b ≤ a`"
    );

    // min a b = a  (false for b < a)
    let f3 = nat_eq(nat_min(a.clone(), b.clone()), a.clone());
    assert!(
        try_prove_nat_inequality_direct_with_hyps(&f3, &[]).is_none(),
        "direct prover must reject `min a b = a`"
    );

    // min a b = min b c  (not a comm shape; a ≠ c)
    let f4 = nat_eq(
        nat_min(a.clone(), b.clone()),
        nat_min(b.clone(), cc.clone()),
    );
    assert!(
        try_prove_nat_inequality_direct_with_hyps(&f4, &[]).is_none(),
        "direct prover must reject `min a b = min b c`"
    );

    // min a b ≤ c  (c unrelated; not min_le_left/right)
    let f5 = nat_le_tc(nat_min(a.clone(), b.clone()), cc.clone());
    assert!(
        try_prove_nat_inequality_direct_with_hyps(&f5, &[]).is_none(),
        "direct prover must reject `min a b ≤ c`"
    );

    // c ≤ max a b  (c unrelated; not le_max_left/right)
    let f6 = nat_le_tc(cc.clone(), nat_max(a.clone(), b.clone()));
    assert!(
        try_prove_nat_inequality_direct_with_hyps(&f6, &[]).is_none(),
        "direct prover must reject `c ≤ max a b`"
    );

    // max a a = b  (max_self must only fire when RHS matches the operand)
    let f7 = nat_eq(nat_max(a.clone(), a.clone()), b.clone());
    assert!(
        try_prove_nat_inequality_direct_with_hyps(&f7, &[]).is_none(),
        "direct prover must reject `max a a = b`"
    );
}

// ---- SURFACE typeclass-projection heads (`@Min.min Nat instMinNat a b`) ----
//
// After the `Min`/`Max` class + `instMinNat`/`instMaxNat` instances are wired
// into `with_prelude`, surface `min a b` elaborates to `@Min.min Nat instMinNat
// a b` (projection head), NOT the bare `Nat.min a b`. These tests pin that the
// omega recognizer peels the projection head back to the bare op and discharges
// the same true shapes — and still rejects the false ones (fail-closed).

#[test]
#[serial]
fn test_omega_proves_min_proj_le_left() {
    // a b : Nat ⊢ @Min.min Nat instMinNat a b ≤ a   (surface `min a b ≤ a`)
    let a = nat_fvar(0);
    let b = nat_fvar(1);
    let goal = nat_le_tc(min_proj(a.clone(), b), a);
    assert_omega_proves(state_with(goal, ctx_ab()), "Min.min a b ≤ a");
}

#[test]
#[serial]
fn test_omega_proves_a_le_max_proj() {
    // a b : Nat ⊢ a ≤ @Max.max Nat instMaxNat a b   (surface `a ≤ max a b`)
    let a = nat_fvar(0);
    let b = nat_fvar(1);
    let goal = nat_le_tc(a.clone(), max_proj(a, b));
    assert_omega_proves(state_with(goal, ctx_ab()), "a ≤ Max.max a b");
}

#[test]
#[serial]
fn test_omega_proves_min_proj_comm() {
    // a b : Nat ⊢ Min.min a b = Min.min b a   (surface `min a b = min b a`)
    let a = nat_fvar(0);
    let b = nat_fvar(1);
    let goal = nat_eq(min_proj(a.clone(), b.clone()), min_proj(b, a));
    assert_omega_proves(state_with(goal, ctx_ab()), "Min.min a b = Min.min b a");
}

#[test]
#[serial]
fn test_omega_rejects_a_le_min_proj() {
    // a b : Nat ⊢ a ≤ @Min.min Nat instMinNat a b   (FALSE; surface `a ≤ min a b`)
    let a = nat_fvar(0);
    let b = nat_fvar(1);
    let goal = nat_le_tc(a.clone(), min_proj(a, b));
    assert_omega_rejects(state_with(goal, ctx_ab()), "a ≤ Min.min a b");
}

#[test]
#[serial]
fn test_omega_rejects_max_proj_le_a() {
    // a b : Nat ⊢ @Max.max Nat instMaxNat a b ≤ a   (FALSE; surface `max a b ≤ a`)
    let a = nat_fvar(0);
    let b = nat_fvar(1);
    let goal = nat_le_tc(max_proj(a.clone(), b), a);
    assert_omega_rejects(state_with(goal, ctx_ab()), "Max.max a b ≤ a");
}

#[test]
#[serial]
fn test_omega_rejects_min_proj_eq_a() {
    // a b : Nat ⊢ @Min.min Nat instMinNat a b = a   (FALSE; surface `min a b = a`)
    let a = nat_fvar(0);
    let b = nat_fvar(1);
    let goal = nat_eq(min_proj(a.clone(), b), a);
    assert_omega_rejects(state_with(goal, ctx_ab()), "Min.min a b = a");
}

#[test]
fn test_direct_minmax_prover_peels_projection_heads() {
    // Unit teeth: the direct prover extracts the trailing operands from a
    // projection-headed term exactly as from the bare op.
    let a = nat_fvar(0);
    let b = nat_fvar(1);

    // TRUE projection-headed shapes synthesize a term.
    let t1 = nat_le_tc(min_proj(a.clone(), b.clone()), a.clone());
    assert!(
        try_prove_nat_inequality_direct_with_hyps(&t1, &[]).is_some(),
        "direct prover should peel `Min.min a b ≤ a`"
    );
    let t2 = nat_le_tc(b.clone(), max_proj(a.clone(), b.clone()));
    assert!(
        try_prove_nat_inequality_direct_with_hyps(&t2, &[]).is_some(),
        "direct prover should peel `b ≤ Max.max a b`"
    );

    // FALSE projection-headed shapes still yield None (fail-closed).
    let f1 = nat_le_tc(a.clone(), min_proj(a.clone(), b.clone()));
    assert!(
        try_prove_nat_inequality_direct_with_hyps(&f1, &[]).is_none(),
        "direct prover must reject `a ≤ Min.min a b`"
    );
    let f2 = nat_le_tc(max_proj(a.clone(), b.clone()), a);
    assert!(
        try_prove_nat_inequality_direct_with_hyps(&f2, &[]).is_none(),
        "direct prover must reject `Max.max a b ≤ a`"
    );
}
