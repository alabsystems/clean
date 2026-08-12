// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! ADVERSARIAL review tests for the omega Nat-equality-from-hyps path.
//! Reviewer-authored. Hammers non-following goals + kernel teeth.

use super::*;
use crate::tactic::arith_linarith_nat_eq::try_prove_nat_equality_from_hyps;
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
fn nat_add(l: Expr, r: Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("Nat.add"), vec![]), l),
        r,
    )
}
fn nat_eq(l: Expr, r: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [nat_type(), l, r],
    )
}
fn eq_hyp(id: u64, name: &str, l: Expr, r: Expr) -> LocalDecl {
    LocalDecl {
        fvar: FVarId::new(id),
        name: name.to_string(),
        ty: nat_eq(l, r),
        value: None,
    }
}

fn collect_consts(e: &Expr, out: &mut HashSet<String>) {
    use clean_kernel::expr::ExprKind;
    match e.kind() {
        ExprKind::Const(name, _) => {
            out.insert(name.to_string());
        }
        ExprKind::App(f, a) => {
            collect_consts(f, out);
            collect_consts(a, out);
        }
        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
            collect_consts(ty, out);
            collect_consts(body, out);
        }
        ExprKind::Let(_, ty, val, body, _) => {
            collect_consts(ty, out);
            collect_consts(val, out);
            collect_consts(body, out);
        }
        _ => {}
    }
}

fn rejects(state: ProofState, label: &str) {
    let mut state = state;
    let result = omega(&mut state);
    assert!(
        result.is_err() && !state.is_complete(),
        "UNSOUND: omega closed non-following goal `{label}`: {result:?}"
    );
}

// ============ NON-FOLLOWING TEETH (synthesizer must be None) =============

#[test]
fn adv_synth_none_a_eq_b_plus_1() {
    // (h : a = b) ⊢ a = b + 1   D = -1 (constant), no constant-only relation -> None
    let (a, b) = (nat_fvar(0), nat_fvar(1));
    let goal = nat_eq(a.clone(), nat_add(b.clone(), Expr::nat_lit(1)));
    assert!(
        try_prove_nat_equality_from_hyps(&goal, &[(nat_fvar(2), nat_eq(a, b))]).is_none(),
        "a = b+1 must NOT follow from a = b"
    );
}

#[test]
fn adv_synth_none_coeff_mismatch_2a_eq_2b_wrong_target() {
    // (h : a = b) ⊢ a + a = b + b + 1   D has constant -1 -> None
    let (a, b) = (nat_fvar(0), nat_fvar(1));
    let goal = nat_eq(
        nat_add(a.clone(), a.clone()),
        nat_add(nat_add(b.clone(), b.clone()), Expr::nat_lit(1)),
    );
    assert!(
        try_prove_nat_equality_from_hyps(&goal, &[(nat_fvar(2), nat_eq(a, b))]).is_none(),
        "a+a = b+b+1 must NOT follow from a = b"
    );
}

#[test]
fn adv_synth_none_swapped_atoms() {
    // (h : a = b) ⊢ a + c = b + d   (c,d distinct free) D = c - d -> None
    let (a, b, c, d) = (nat_fvar(0), nat_fvar(1), nat_fvar(2), nat_fvar(3));
    let goal = nat_eq(nat_add(a.clone(), c), nat_add(b.clone(), d));
    assert!(
        try_prove_nat_equality_from_hyps(&goal, &[(nat_fvar(4), nat_eq(a, b))]).is_none(),
        "a+c = b+d must NOT follow from a = b alone"
    );
}

#[test]
fn adv_synth_none_partial_chain_gap() {
    // (h1 : a = b) ⊢ a = c   (no h2 : b = c) -> None
    let (a, b, c) = (nat_fvar(0), nat_fvar(1), nat_fvar(2));
    let goal = nat_eq(a.clone(), c);
    assert!(
        try_prove_nat_equality_from_hyps(&goal, &[(nat_fvar(3), nat_eq(a, b))]).is_none(),
        "a = c must NOT follow from a = b alone"
    );
}

#[test]
fn adv_synth_none_reverse_only_hyp() {
    // (h : a = b) ⊢ c = a   D = c - a -> None
    let (a, b, c) = (nat_fvar(0), nat_fvar(1), nat_fvar(2));
    let goal = nat_eq(c, a.clone());
    assert!(
        try_prove_nat_equality_from_hyps(&goal, &[(nat_fvar(3), nat_eq(a, b))]).is_none(),
        "c = a must NOT follow from a = b"
    );
}

#[test]
fn adv_synth_none_double_count_wrong() {
    // (h : a = b) ⊢ a + a = b   D = a (after b cancels) -> None (needs coeff 1 on a-b twice? no: a+a - b = a, not multiple of a-b)
    let (a, b) = (nat_fvar(0), nat_fvar(1));
    let goal = nat_eq(nat_add(a.clone(), a.clone()), b.clone());
    assert!(
        try_prove_nat_equality_from_hyps(&goal, &[(nat_fvar(2), nat_eq(a, b))]).is_none(),
        "a+a = b must NOT follow from a = b"
    );
}

#[test]
fn adv_synth_none_chain_constant_drift() {
    // (h1:a=b)(h2:b=c) ⊢ a + 1 = c + 2  D = -1 constant -> None
    let (a, b, c) = (nat_fvar(0), nat_fvar(1), nat_fvar(2));
    let goal = nat_eq(
        nat_add(a.clone(), Expr::nat_lit(1)),
        nat_add(c.clone(), Expr::nat_lit(2)),
    );
    assert!(
        try_prove_nat_equality_from_hyps(
            &goal,
            &[
                (nat_fvar(3), nat_eq(a, b.clone())),
                (nat_fvar(4), nat_eq(b, c))
            ]
        )
        .is_none(),
        "a+1 = c+2 must NOT follow from a=b, b=c"
    );
}

// ============ END-TO-END omega rejection (full close_goal gate) ==========

#[test]
#[serial]
fn adv_omega_rejects_a_eq_b_plus_1() {
    let (a, b) = (nat_fvar(0), nat_fvar(1));
    let goal = nat_eq(a.clone(), nat_add(b.clone(), Expr::nat_lit(1)));
    let state = ProofState::with_context(
        Environment::with_prelude(),
        goal,
        vec![nat_local(0, "a"), nat_local(1, "b"), eq_hyp(2, "h", a, b)],
    );
    rejects(state, "(h:a=b) ⊢ a = b+1");
}

#[test]
#[serial]
fn adv_omega_rejects_swapped_free_atoms() {
    let (a, b, c, d) = (nat_fvar(0), nat_fvar(1), nat_fvar(2), nat_fvar(3));
    let goal = nat_eq(nat_add(a.clone(), c.clone()), nat_add(b.clone(), d.clone()));
    let state = ProofState::with_context(
        Environment::with_prelude(),
        goal,
        vec![
            nat_local(0, "a"),
            nat_local(1, "b"),
            nat_local(2, "c"),
            nat_local(3, "d"),
            eq_hyp(4, "h", a, b),
        ],
    );
    rejects(state, "(h:a=b) ⊢ a+c = b+d");
}

#[test]
#[serial]
fn adv_omega_rejects_chain_constant_drift() {
    let (a, b, c) = (nat_fvar(0), nat_fvar(1), nat_fvar(2));
    let goal = nat_eq(
        nat_add(a.clone(), Expr::nat_lit(1)),
        nat_add(c.clone(), Expr::nat_lit(2)),
    );
    let state = ProofState::with_context(
        Environment::with_prelude(),
        goal,
        vec![
            nat_local(0, "a"),
            nat_local(1, "b"),
            nat_local(2, "c"),
            eq_hyp(3, "h1", a, b.clone()),
            eq_hyp(4, "h2", b, c),
        ],
    );
    rejects(state, "(h1:a=b)(h2:b=c) ⊢ a+1 = c+2");
}

#[test]
#[serial]
fn adv_omega_rejects_wrong_hyp_unrelated() {
    // hyp about totally unrelated atoms; goal cannot follow
    let (a, b, x, y) = (nat_fvar(0), nat_fvar(1), nat_fvar(2), nat_fvar(3));
    let goal = nat_eq(
        nat_add(a.clone(), Expr::nat_lit(1)),
        nat_add(b.clone(), Expr::nat_lit(1)),
    );
    let state = ProofState::with_context(
        Environment::with_prelude(),
        goal,
        vec![
            nat_local(0, "a"),
            nat_local(1, "b"),
            nat_local(2, "x"),
            nat_local(3, "y"),
            eq_hyp(4, "h", x, y),
        ],
    );
    rejects(state, "(h:x=y) ⊢ a+1 = b+1");
}

// ============ KERNEL TEETH: every PROVED term checks at goal ==============

/// Build a global-const env, synth a term for a TRUE goal, and confirm the
/// kernel TypeChecker accepts it AT THE GOAL (not just that it infers *some*
/// type). This is the real anti-unsoundness gate.
fn kernel_check_true_goal(
    setup: impl Fn() -> (
        Expr,              /*goal*/
        Vec<(Expr, Expr)>, /*hyps*/
        Environment,
    ),
    label: &str,
) {
    let (goal, hyps, env) = setup();
    let term = try_prove_nat_equality_from_hyps(&goal, &hyps)
        .unwrap_or_else(|| panic!("should synth for true goal `{label}`"));
    let tc = TypeChecker::with_mode(&env, env.mode());
    let _ = tc
        .infer_type(&term)
        .unwrap_or_else(|e| panic!("`{label}`: infer failed {e:?}"));
    tc.check_type(&term, &goal)
        .unwrap_or_else(|e| panic!("`{label}`: term does NOT check at goal {e:?}"));
    let mut consts = HashSet::new();
    collect_consts(&term, &mut consts);
    for forbidden in ["trustedAy", "trustedArith", "sorry", "sorryAx"] {
        assert!(!consts.contains(forbidden), "`{label}` uses {forbidden}");
    }
}

fn global_env_abc() -> Environment {
    let mut env = Environment::with_prelude();
    for nm in ["a", "b", "c"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(nm),
            level_params: vec![],
            type_: nat_type(),
        })
        .expect("axiom add");
    }
    env
}

#[test]
#[serial]
fn adv_kernel_checks_a_plus_c_eq_b_plus_c() {
    kernel_check_true_goal(
        || {
            let mut env = global_env_abc();
            let (a, b, c) = (
                Expr::const_(Name::from_string("a"), vec![]),
                Expr::const_(Name::from_string("b"), vec![]),
                Expr::const_(Name::from_string("c"), vec![]),
            );
            env.add_decl(Declaration::Axiom {
                name: Name::from_string("h"),
                level_params: vec![],
                type_: nat_eq(a.clone(), b.clone()),
            })
            .expect("h add");
            let h = Expr::const_(Name::from_string("h"), vec![]);
            let goal = nat_eq(nat_add(a.clone(), c.clone()), nat_add(b.clone(), c));
            (goal, vec![(h, nat_eq(a, b))], env)
        },
        "(h:a=b) ⊢ a+c = b+c",
    );
}

#[test]
#[serial]
fn adv_kernel_checks_symm_b_eq_a() {
    kernel_check_true_goal(
        || {
            let mut env = global_env_abc();
            let (a, b) = (
                Expr::const_(Name::from_string("a"), vec![]),
                Expr::const_(Name::from_string("b"), vec![]),
            );
            env.add_decl(Declaration::Axiom {
                name: Name::from_string("h"),
                level_params: vec![],
                type_: nat_eq(a.clone(), b.clone()),
            })
            .expect("h");
            let h = Expr::const_(Name::from_string("h"), vec![]);
            let goal = nat_eq(b.clone(), a.clone());
            (goal, vec![(h, nat_eq(a, b))], env)
        },
        "(h:a=b) ⊢ b = a",
    );
}

// ============ KERNEL BACKSTOP: a deliberately mistyped term is rejected ====
// Validates the claim that close_goal/add_decl is a real backstop independent
// of the synthesizer: feed a term of type (a+1 = a+1) at goal (a = b+1) and
// confirm close_goal rejects it. If THIS ever succeeded the whole trust model
// would be broken.
#[test]
#[serial]
fn adv_kernel_backstop_rejects_mistyped_proof() {
    let (a, b) = (nat_fvar(0), nat_fvar(1));
    // Non-following goal a = b + 1.
    let goal_ty = nat_eq(a.clone(), nat_add(b.clone(), Expr::nat_lit(1)));
    let mut state = ProofState::with_context(
        Environment::with_prelude(),
        goal_ty,
        vec![nat_local(0, "a"), nat_local(1, "b")],
    );
    let goal = state.goals.front().cloned().expect("goal");
    // Bogus proof: Eq.refl (a+1) : a+1 = a+1, which is NOT def-eq to a = b+1.
    let bogus = Expr::apps(
        Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        ),
        [nat_type(), nat_add(a.clone(), Expr::nat_lit(1))],
    );
    let res = state.close_goal(&goal, bogus);
    assert!(
        res.is_err(),
        "UNSOUND: close_goal accepted a mistyped proof: {res:?}"
    );
}

#[test]
fn adv_synth_none_no_hyps_nonzero_d() {
    // No hyps, goal a+1 = b+1 (a != b). D = a-b nonzero, no relations -> None.
    // Critical: must NOT hit the `coeffs all zero -> try_direct` branch and
    // wrongly succeed.
    let (a, b) = (nat_fvar(0), nat_fvar(1));
    let goal = nat_eq(nat_add(a, Expr::nat_lit(1)), nat_add(b, Expr::nat_lit(1)));
    assert!(
        try_prove_nat_equality_from_hyps(&goal, &[]).is_none(),
        "a+1 = b+1 with no hyps must be None"
    );
}

#[test]
fn adv_synth_some_no_hyps_true_permutation_defers() {
    // No hyps, true permutation a+b = b+a. D = 0, coeffs empty/all-zero ->
    // defers to goal-only direct, which SHOULD prove it.
    let (a, b) = (nat_fvar(0), nat_fvar(1));
    let goal = nat_eq(nat_add(a.clone(), b.clone()), nat_add(b, a));
    assert!(
        try_prove_nat_equality_from_hyps(&goal, &[]).is_some(),
        "a+b = b+a defers to goal-only and proves"
    );
}
