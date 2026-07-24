// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end tests for the omega Nat-inequality direct reconstruction path.
//!
//! Closes the `ineq_gap`: omega now proves linear Nat inequality goals such as
//! `n + 1 > n` by synthesizing a kernel-checked proof term from the negated
//! goal (no hypotheses required), instead of failing closed.
//!
//! Soundness teeth:
//! - PROVE: `n + 1 > n`, `n < n + 1`, `n ≤ n + 1`, `n + 2 > n`, and a
//!   hypothesis-carrying `(h : a ≤ b) ⊢ a ≤ b + 1` all close.
//! - KERNEL CHECK + AXIOM CLOSURE: the synthesized term for `n + 1 > n`
//!   type-checks against the goal via a real `clean_kernel::TypeChecker`, and
//!   its constant closure ⊆ {Nat.le.refl, Nat.le.step, Nat, Nat.add, ...} with
//!   ZERO `trustedAy` / `trustedArith` / `sorryAx`.
//! - NEGATIVE: `n > n + 1` and `n + 1 ≤ n` are FALSE and must STILL be rejected
//!   (omega must not prove false inequalities).

use super::*;
use crate::tactic::arith_linarith_nat_direct::try_prove_nat_inequality_direct;
use crate::tactic::tc_app::{mk_tc_rel, nat_le_tc, nat_lt_tc};
use clean_kernel::level::Level;
use clean_kernel::tc::TypeChecker;
use clean_kernel::Expr;
use serial_test::serial;
use std::collections::HashSet;

fn nat_type() -> Expr {
    Expr::const_(Name::from_string("Nat"), vec![])
}

/// A Nat variable bound as a **local** fvar `id`.
///
/// The mathverse/linarith linear parser only treats `ExprKind::FVar` as a
/// variable (global `Const` axioms are not parsed as variables), so the goal's
/// arithmetic variables must live in the local context as fvars.
fn nat_fvar(id: u64) -> Expr {
    Expr::fvar(FVarId::new(id))
}

/// `name : Nat` local declaration for fvar `id`.
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

/// `@GT.gt.{0} Nat instLTNat a b`.
fn nat_gt_tc(a: Expr, b: Expr) -> Expr {
    mk_tc_rel(
        Expr::const_(Name::from_string("GT.gt"), vec![Level::zero()]),
        nat_type(),
        Expr::const_(Name::from_string("instLTNat"), vec![]),
        a,
        b,
    )
}

/// Collect every `Const` name appearing in a proof term.
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

/// Build a state whose goal is `goal_target` with `n : Nat` (fvar 0) in context.
fn state_with_n(goal_target: Expr) -> ProofState {
    ProofState::with_context(
        Environment::with_prelude(),
        goal_target,
        vec![nat_local(0, "n")],
    )
}

/// Run omega on `state` and assert it closes the goal with no trusted axioms.
fn assert_omega_proves(mut state: ProofState, label: &str) -> ProofState {
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
    state
}

/// Run omega on `state` and assert it does NOT close (false inequality).
fn assert_omega_rejects(mut state: ProofState, label: &str) {
    reset_all_counters();
    let result = crate::tactic::omega_tactic::omega(&mut state);
    assert!(
        result.is_err() && !state.is_complete(),
        "omega must REJECT the false inequality `{label}`, but it closed: {result:?}"
    );
}

#[test]
#[serial]
fn test_omega_proves_n_plus_1_gt_n() {
    // n + 1 > n
    let n = nat_fvar(0);
    let goal = nat_gt_tc(nat_add(n.clone(), Expr::nat_lit(1)), n);
    assert_omega_proves(state_with_n(goal), "n + 1 > n");
}

#[test]
#[serial]
fn test_omega_proves_n_lt_n_plus_1() {
    // n < n + 1
    let n = nat_fvar(0);
    let goal = nat_lt_tc(n.clone(), nat_add(n, Expr::nat_lit(1)));
    assert_omega_proves(state_with_n(goal), "n < n + 1");
}

#[test]
#[serial]
fn test_omega_proves_n_le_n_plus_1() {
    // n ≤ n + 1
    let n = nat_fvar(0);
    let goal = nat_le_tc(n.clone(), nat_add(n, Expr::nat_lit(1)));
    assert_omega_proves(state_with_n(goal), "n ≤ n + 1");
}

#[test]
#[serial]
fn test_omega_proves_n_plus_2_gt_n() {
    // n + 2 > n
    let n = nat_fvar(0);
    let goal = nat_gt_tc(nat_add(n.clone(), Expr::nat_lit(2)), n);
    assert_omega_proves(state_with_n(goal), "n + 2 > n");
}

#[test]
#[serial]
fn test_omega_proves_with_hypothesis_a_le_b_plus_1() {
    // a : Nat (fvar 0), b : Nat (fvar 1), h : a ≤ b (fvar 2) ⊢ a ≤ b + 1
    let a = nat_fvar(0);
    let b = nat_fvar(1);
    let goal_target = nat_le_tc(a.clone(), nat_add(b.clone(), Expr::nat_lit(1)));

    reset_all_counters();
    let mut state = ProofState::with_context(
        Environment::with_prelude(),
        goal_target,
        vec![
            nat_local(0, "a"),
            nat_local(1, "b"),
            LocalDecl {
                fvar: FVarId::new(2),
                name: "h".to_string(),
                ty: nat_le_tc(a, b),
                value: None,
            },
        ],
    );
    let axiom_before = axiom_snapshot();
    let result = crate::tactic::omega_tactic::omega(&mut state);
    assert!(
        result.is_ok(),
        "omega should prove `(h : a ≤ b) ⊢ a ≤ b + 1`, got: {result:?}"
    );
    assert!(state.is_complete(), "goal should be closed");
    assert_no_trusted_axiom_usage("omega", "(h : a ≤ b) ⊢ a ≤ b + 1", axiom_before);
    let ledger = state.trust_ledger();
    assert_eq!(ledger.trusted_arith_count, 0);
    assert_eq!(ledger.trusted_ay_count, 0);
    assert_eq!(ledger.sorry_count, 0);
}

#[test]
#[serial]
fn test_omega_proves_false_from_n_plus_2_le_n_hyp() {
    // (h : n + 2 ≤ n) ⊢ False  — symbolic Nat cancellation (ineq_gap sub-fix 2).
    let n = nat_fvar(0);
    let false_ty = Expr::const_(Name::from_string("False"), vec![]);
    reset_all_counters();
    let mut state = ProofState::with_context(
        Environment::with_prelude(),
        false_ty,
        vec![
            nat_local(0, "n"),
            LocalDecl {
                fvar: FVarId::new(1),
                name: "h".to_string(),
                ty: nat_le_tc(nat_add(n.clone(), Expr::nat_lit(2)), n),
                value: None,
            },
        ],
    );
    let axiom_before = axiom_snapshot();
    let result = crate::tactic::omega_tactic::omega(&mut state);
    assert!(
        result.is_ok(),
        "omega should derive False from `n + 2 ≤ n`, got: {result:?}"
    );
    assert!(state.is_complete(), "False goal should be closed");
    assert_no_trusted_axiom_usage("omega", "(h : n + 2 ≤ n) ⊢ False", axiom_before);
    let ledger = state.trust_ledger();
    assert_eq!(ledger.trusted_arith_count, 0);
    assert_eq!(ledger.trusted_ay_count, 0);
    assert_eq!(ledger.sorry_count, 0);
}

/// The teeth: the synthesized term for `n + 1 > n` type-checks against the goal
/// via a real kernel `TypeChecker`, and its constant closure contains ZERO
/// trust axioms.
#[test]
#[serial]
fn test_omega_n_plus_1_gt_n_term_kernel_checks_and_axiom_closure_clean() {
    // `n` here is a global Nat constant so the term type-checks in a bare env
    // (the kernel TypeChecker has no local context). The direct prover matches
    // on the goal syntax, not on fvar-ness, so this exercises the same path.
    let mut env = Environment::with_prelude();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("n"),
        level_params: vec![],
        type_: nat_type(),
    })
    .expect("n : Nat axiom should add");
    let n = Expr::const_(Name::from_string("n"), vec![]);
    let goal = nat_gt_tc(nat_add(n.clone(), Expr::nat_lit(1)), n);

    // Synthesize the candidate proof term directly.
    let term = try_prove_nat_inequality_direct(&goal)
        .expect("direct prover should synthesize a term for `n + 1 > n`");

    // (1) Kernel re-check: confirm the term type-checks AT the goal type via a
    // real `clean_kernel::TypeChecker` (infer + whnf + def-eq against expected).
    let tc = TypeChecker::with_mode(&env, env.mode());
    let inferred = tc
        .infer_type(&term)
        .expect("synthesized term for `n + 1 > n` must type-check in the kernel");
    tc.check_type(&term, &goal).unwrap_or_else(|err| {
        panic!(
            "synthesized term must check at the goal type `n + 1 > n`: {err:?}\n  inferred = {inferred:?}\n  goal     = {goal:?}"
        )
    });

    // (2) Axiom closure ⊆ FOUNDATIONAL: no trustedAy, no trustedArith, no sorry.
    let mut consts = HashSet::new();
    collect_const_names(&term, &mut consts);
    for forbidden in ["trustedAy", "trustedArith", "sorry", "sorryAx"] {
        assert!(
            !consts.contains(forbidden),
            "synthesized term must not reference `{forbidden}`; closure = {consts:?}"
        );
    }
    // Positive: the term is built only from the Nat.le inductive constructors.
    assert!(
        consts.contains("Nat.le.refl"),
        "term should be built from Nat.le.refl; closure = {consts:?}"
    );
}

// ---- NEGATIVE TEETH: false inequalities must STILL be rejected ----

#[test]
#[serial]
fn test_omega_rejects_n_gt_n_plus_1() {
    // n > n + 1  (FALSE)
    let n = nat_fvar(0);
    let goal = nat_gt_tc(n.clone(), nat_add(n, Expr::nat_lit(1)));
    assert_omega_rejects(state_with_n(goal), "n > n + 1");
}

#[test]
#[serial]
fn test_omega_rejects_n_plus_1_le_n() {
    // n + 1 ≤ n  (FALSE)
    let n = nat_fvar(0);
    let goal = nat_le_tc(nat_add(n.clone(), Expr::nat_lit(1)), n);
    assert_omega_rejects(state_with_n(goal), "n + 1 ≤ n");
}

/// Direct-prover unit teeth: it must return `None` for false goals so omega
/// can fail closed (never fabricate a term for a false inequality).
#[test]
fn test_direct_prover_returns_none_on_false_goals() {
    let n = nat_fvar(0);
    // n + 1 ≤ n
    let false_le = nat_le_tc(nat_add(n.clone(), Expr::nat_lit(1)), n.clone());
    assert!(
        try_prove_nat_inequality_direct(&false_le).is_none(),
        "direct prover must reject `n + 1 ≤ n`"
    );
    // n > n + 1
    let false_gt = nat_gt_tc(n.clone(), nat_add(n, Expr::nat_lit(1)));
    assert!(
        try_prove_nat_inequality_direct(&false_gt).is_none(),
        "direct prover must reject `n > n + 1`"
    );
}

// ======================================================================
// REPRO: bounded omega slices (T1 a≤a+b ; T2 n<5 ⊢ n+1<7)
// ======================================================================

/// Build a state with given local decls and goal.
fn state_with(goal_target: Expr, ctx: Vec<LocalDecl>) -> ProofState {
    ProofState::with_context(Environment::with_prelude(), goal_target, ctx)
}

#[test]
#[serial]
fn repro_omega_proves_a_le_a_plus_b() {
    // a b : Nat ⊢ a ≤ a + b   (true: 0 ≤ b)
    let a = nat_fvar(0);
    let b = nat_fvar(1);
    let goal = nat_le_tc(a.clone(), nat_add(a, b));
    assert_omega_proves(
        state_with(goal, vec![nat_local(0, "a"), nat_local(1, "b")]),
        "a ≤ a + b",
    );
}

#[test]
#[serial]
fn repro_omega_proves_n_lt_5_implies_n_plus_1_lt_7() {
    // n : Nat, h : n < 5 ⊢ n + 1 < 7
    let n = nat_fvar(0);
    let goal = nat_lt_tc(nat_add(n.clone(), Expr::nat_lit(1)), Expr::nat_lit(7));
    let h = LocalDecl {
        fvar: FVarId::new(1),
        name: "h".to_string(),
        ty: nat_lt_tc(n, Expr::nat_lit(5)),
        value: None,
    };
    assert_omega_proves(
        state_with(goal, vec![nat_local(0, "n"), h]),
        "n < 5 ⊢ n + 1 < 7",
    );
}

#[test]
#[serial]
fn repro_omega_rejects_a_le_b() {
    // a b : Nat ⊢ a ≤ b   (FALSE: a=1,b=0)
    let a = nat_fvar(0);
    let b = nat_fvar(1);
    let goal = nat_le_tc(a, b);
    assert_omega_rejects(
        state_with(goal, vec![nat_local(0, "a"), nat_local(1, "b")]),
        "a ≤ b",
    );
}

#[test]
#[serial]
fn repro_omega_rejects_a_plus_b_le_a() {
    // a b : Nat ⊢ a + b ≤ a   (FALSE: a=0,b=1)
    let a = nat_fvar(0);
    let b = nat_fvar(1);
    let goal = nat_le_tc(nat_add(a.clone(), b), a);
    assert_omega_rejects(
        state_with(goal, vec![nat_local(0, "a"), nat_local(1, "b")]),
        "a + b ≤ a",
    );
}

#[test]
#[serial]
fn repro_omega_rejects_a_plus_1_le_a() {
    // a : Nat ⊢ a + 1 ≤ a   (FALSE)
    let a = nat_fvar(0);
    let goal = nat_le_tc(nat_add(a.clone(), Expr::nat_lit(1)), a);
    assert_omega_rejects(state_with(goal, vec![nat_local(0, "a")]), "a + 1 ≤ a");
}

// ======================================================================
// SHIFTED-OFFSET HYP FAMILY (omega hyp-inequality with offsets)
//   goal `core_l + k_l <op> core_r + k_r` from a hyp `core_l + h_l ≤ core_r +
//   h_r` (or the lt-hyp form a < b ≡ a + 1 ≤ b). PATH 2.5 in
//   try_prove_nat_inequality_direct_with_hyps.
// ======================================================================

/// `(h : a ≤ b) ⊢ a + 1 ≤ b + 1` — both sides shifted by the same k=1.
#[test]
#[serial]
fn shift_omega_proves_a_le_b_implies_a_plus_1_le_b_plus_1() {
    let a = nat_fvar(0);
    let b = nat_fvar(1);
    let goal = nat_le_tc(
        nat_add(a.clone(), Expr::nat_lit(1)),
        nat_add(b.clone(), Expr::nat_lit(1)),
    );
    let h = LocalDecl {
        fvar: FVarId::new(2),
        name: "h".to_string(),
        ty: nat_le_tc(a, b),
        value: None,
    };
    assert_omega_proves(
        state_with(goal, vec![nat_local(0, "a"), nat_local(1, "b"), h]),
        "(h : a ≤ b) ⊢ a + 1 ≤ b + 1",
    );
}

/// `(h : a < b) ⊢ a + 1 ≤ b` — lt-hyp normalizes to `a + 1 ≤ b`, matching the
/// goal exactly (offsets identical on both sides).
#[test]
#[serial]
fn shift_omega_proves_a_lt_b_implies_a_plus_1_le_b() {
    let a = nat_fvar(0);
    let b = nat_fvar(1);
    let goal = nat_le_tc(nat_add(a.clone(), Expr::nat_lit(1)), b.clone());
    let h = LocalDecl {
        fvar: FVarId::new(2),
        name: "h".to_string(),
        ty: nat_lt_tc(a, b),
        value: None,
    };
    assert_omega_proves(
        state_with(goal, vec![nat_local(0, "a"), nat_local(1, "b"), h]),
        "(h : a < b) ⊢ a + 1 ≤ b",
    );
}

/// `(h : a ≤ b) ⊢ a + 3 ≤ b + 3` — same shift k=3 on both sides (padding c=3).
#[test]
#[serial]
fn shift_omega_proves_a_le_b_implies_a_plus_3_le_b_plus_3() {
    let a = nat_fvar(0);
    let b = nat_fvar(1);
    let goal = nat_le_tc(
        nat_add(a.clone(), Expr::nat_lit(3)),
        nat_add(b.clone(), Expr::nat_lit(3)),
    );
    let h = LocalDecl {
        fvar: FVarId::new(2),
        name: "h".to_string(),
        ty: nat_le_tc(a, b),
        value: None,
    };
    assert_omega_proves(
        state_with(goal, vec![nat_local(0, "a"), nat_local(1, "b"), h]),
        "(h : a ≤ b) ⊢ a + 3 ≤ b + 3",
    );
}

// ---- SHIFTED-OFFSET NEGATIVE TEETH: false goals must STILL be rejected ----

/// FALSE: `(h : a ≤ b) ⊢ b + 1 ≤ a` — mismatched cores (goal LHS core `b`,
/// hyp LHS core `a`). Must be rejected.
#[test]
#[serial]
fn shift_omega_rejects_a_le_b_implies_b_plus_1_le_a() {
    let a = nat_fvar(0);
    let b = nat_fvar(1);
    let goal = nat_le_tc(nat_add(b.clone(), Expr::nat_lit(1)), a.clone());
    let h = LocalDecl {
        fvar: FVarId::new(2),
        name: "h".to_string(),
        ty: nat_le_tc(a, b),
        value: None,
    };
    assert_omega_rejects(
        state_with(goal, vec![nat_local(0, "a"), nat_local(1, "b"), h]),
        "(h : a ≤ b) ⊢ b + 1 ≤ a",
    );
}

/// FALSE: `(h : a ≤ b) ⊢ a + 2 ≤ b` — only the LHS is shifted (k_l=2, k_r=0),
/// so the goal slack is smaller than the hyp slack. Must be rejected.
#[test]
#[serial]
fn shift_omega_rejects_a_le_b_implies_a_plus_2_le_b() {
    let a = nat_fvar(0);
    let b = nat_fvar(1);
    let goal = nat_le_tc(nat_add(a.clone(), Expr::nat_lit(2)), b.clone());
    let h = LocalDecl {
        fvar: FVarId::new(2),
        name: "h".to_string(),
        ty: nat_le_tc(a, b),
        value: None,
    };
    assert_omega_rejects(
        state_with(goal, vec![nat_local(0, "a"), nat_local(1, "b"), h]),
        "(h : a ≤ b) ⊢ a + 2 ≤ b",
    );
}

/// FALSE without a hypothesis: `⊢ a + 1 ≤ b + 1` (distinct cores `a`, `b`, no
/// relating hypothesis). Must be rejected.
#[test]
#[serial]
fn shift_omega_rejects_no_hyp_a_plus_1_le_b_plus_1() {
    let a = nat_fvar(0);
    let b = nat_fvar(1);
    let goal = nat_le_tc(
        nat_add(a.clone(), Expr::nat_lit(1)),
        nat_add(b.clone(), Expr::nat_lit(1)),
    );
    assert_omega_rejects(
        state_with(goal, vec![nat_local(0, "a"), nat_local(1, "b")]),
        "⊢ a + 1 ≤ b + 1 (no hyp)",
    );
}

// ======================================================================
// ADVERSARIAL REVIEW TESTS (added by reviewer, not the implementer)
// ======================================================================

/// Orchestrator's decisive false goals: all MUST be rejected by omega.
#[test]
#[serial]
fn rev_omega_rejects_3_lt_2_concrete() {
    // (3:Nat) < 2  — FALSE concrete
    let goal = nat_lt_tc(Expr::nat_lit(3), Expr::nat_lit(2));
    assert_omega_rejects(state_with_n(goal), "(3:Nat) < 2");
}

#[test]
#[serial]
fn rev_omega_rejects_n_plus_5_le_n_plus_3() {
    // n + 5 ≤ n + 3  — FALSE on shared core (lhs_off=5 > rhs_off=3)
    let n = nat_fvar(0);
    let goal = nat_le_tc(
        nat_add(n.clone(), Expr::nat_lit(5)),
        nat_add(n, Expr::nat_lit(3)),
    );
    assert_omega_rejects(state_with_n(goal), "n + 5 ≤ n + 3");
}

#[test]
#[serial]
fn rev_omega_rejects_n_ge_n_plus_1() {
    // n ≥ n + 1  -> Nat.le (n+1) n  -> FALSE
    let n = nat_fvar(0);
    let goal = mk_tc_rel(
        Expr::const_(Name::from_string("GE.ge"), vec![Level::zero()]),
        nat_type(),
        Expr::const_(Name::from_string("instLENat"), vec![]),
        n.clone(),
        nat_add(n, Expr::nat_lit(1)),
    );
    assert_omega_rejects(state_with_n(goal), "n ≥ n + 1");
}

/// Distinct cores must NOT be conflated. `m + 1 > n` is NOT universally true
/// (e.g. m=0,n=5). The direct prover must return None (different fvars).
#[test]
fn rev_direct_prover_rejects_distinct_cores() {
    let m = nat_fvar(0);
    let n = nat_fvar(1);
    // m + 1 > n  : not valid for all m,n
    let g1 = nat_gt_tc(nat_add(m.clone(), Expr::nat_lit(1)), n.clone());
    assert!(
        try_prove_nat_inequality_direct(&g1).is_none(),
        "m + 1 > n has distinct cores and is not universally true; must be None"
    );
    // m ≤ n : not valid for all
    let g2 = nat_le_tc(m.clone(), n.clone());
    assert!(
        try_prove_nat_inequality_direct(&g2).is_none(),
        "m ≤ n has distinct cores; must be None"
    );
    // m + 3 ≤ n + 5 : distinct cores, not universally true
    let g3 = nat_le_tc(nat_add(m, Expr::nat_lit(3)), nat_add(n, Expr::nat_lit(5)));
    assert!(
        try_prove_nat_inequality_direct(&g3).is_none(),
        "m + 3 ≤ n + 5 has distinct cores; must be None"
    );
}

/// The DECISIVE soundness test: even if the direct prover produced a term for a
/// false goal, the FULL kernel check (`infer_only=false`, the path
/// `Environment::add_decl`/`check_type` use) must reject it. Here we manually
/// fabricate a bogus step term claiming to prove the FALSE goal `n ≥ n + 1`
/// (i.e. `Nat.le (n+1) n`) and confirm the real kernel rejects it.
#[test]
#[serial]
fn rev_full_kernel_rejects_fabricated_false_le_term() {
    let mut env = Environment::with_prelude();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("n"),
        level_params: vec![],
        type_: nat_type(),
    })
    .expect("n : Nat axiom should add");
    let n = Expr::const_(Name::from_string("n"), vec![]);

    // Fabricate `Nat.le.refl (n+1)` : Nat.le (n+1) (n+1). Claim it proves
    // the FALSE goal Nat.le (n+1) n. A sound kernel must reject the def-eq.
    let n_plus_1 = nat_add(n.clone(), Expr::nat_lit(1));
    let bogus = Expr::app(
        Expr::const_(Name::from_string("Nat.le.refl"), vec![]),
        n_plus_1.clone(),
    );
    let false_goal = nat_le_tc(n_plus_1, n);

    let tc = clean_kernel::tc::TypeChecker::with_mode(&env, env.mode());
    let res = tc.check_type(&bogus, &false_goal);
    assert!(
        res.is_err(),
        "FULL kernel check must REJECT a refl term claimed at a false ≤ goal; got Ok"
    );
}

/// Confirm the FULL kernel check (infer_only=false) ACCEPTS the genuine
/// synthesized term — i.e. the acceptance in the implementer's test is not an
/// artifact of the infer-only fast path skipping App argument checks.
#[test]
#[serial]
fn rev_full_kernel_accepts_genuine_term_n_plus_1_gt_n() {
    let mut env = Environment::with_prelude();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("n"),
        level_params: vec![],
        type_: nat_type(),
    })
    .expect("n : Nat axiom should add");
    let n = Expr::const_(Name::from_string("n"), vec![]);
    let goal = nat_gt_tc(nat_add(n.clone(), Expr::nat_lit(1)), n);

    let term = try_prove_nat_inequality_direct(&goal)
        .expect("direct prover should synthesize a term for `n + 1 > n`");

    let tc = clean_kernel::tc::TypeChecker::with_mode(&env, env.mode());
    // infer_only=false full check — the same mode add_decl uses.
    tc.check_type(&term, &goal)
        .expect("FULL kernel check (infer_only=false) must accept the genuine term");
}

/// A fabricated MALFORMED step term (wrong implicit endpoint) must be rejected
/// by the full kernel check. This probes whether a wrong `@Nat.le.step` arg
/// threading could ever check at a false goal.
#[test]
#[serial]
fn rev_full_kernel_rejects_malformed_step_term() {
    let mut env = Environment::with_prelude();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("n"),
        level_params: vec![],
        type_: nat_type(),
    })
    .expect("n : Nat axiom should add");
    let n = Expr::const_(Name::from_string("n"), vec![]);

    // @Nat.le.step n n (Nat.le.refl n) : Nat.le n (succ n).
    // Claim it proves the FALSE goal Nat.le (succ n) n (i.e. n+1 ≤ n).
    let le_refl = Expr::app(
        Expr::const_(Name::from_string("Nat.le.refl"), vec![]),
        n.clone(),
    );
    let step = Expr::apps(
        Expr::const_(Name::from_string("Nat.le.step"), vec![]),
        [n.clone(), n.clone(), le_refl],
    );
    let succ_n = Expr::app(
        Expr::const_(Name::from_string("Nat.succ"), vec![]),
        n.clone(),
    );
    let false_goal = nat_le_tc(succ_n, n);

    let tc = clean_kernel::tc::TypeChecker::with_mode(&env, env.mode());
    assert!(
        tc.check_type(&step, &false_goal).is_err(),
        "kernel must reject step term (Nat.le n (succ n)) claimed at false goal Nat.le (succ n) n"
    );
}

// ---- REVIEWER HAMMER: the prompt's decisive false teeth (full omega path) ----

/// FALSE: `(h : a ≤ b) ⊢ a + 1 ≤ b`. a ≤ b does NOT give a + 1 ≤ b
/// (counterexample a = b). Must be rejected through the entire omega path.
#[test]
#[serial]
fn rev_shift_omega_rejects_a_le_b_implies_a_plus_1_le_b() {
    let a = nat_fvar(0);
    let b = nat_fvar(1);
    let goal = nat_le_tc(nat_add(a.clone(), Expr::nat_lit(1)), b.clone());
    let h = LocalDecl {
        fvar: FVarId::new(2),
        name: "h".to_string(),
        ty: nat_le_tc(a, b),
        value: None,
    };
    assert_omega_rejects(
        state_with(goal, vec![nat_local(0, "a"), nat_local(1, "b"), h]),
        "(h : a ≤ b) ⊢ a + 1 ≤ b",
    );
}

/// FALSE: `(h : a < b) ⊢ b ≤ a`. a < b never gives b ≤ a. Must be rejected.
#[test]
#[serial]
fn rev_shift_omega_rejects_a_lt_b_implies_b_le_a() {
    let a = nat_fvar(0);
    let b = nat_fvar(1);
    let goal = nat_le_tc(b.clone(), a.clone());
    let h = LocalDecl {
        fvar: FVarId::new(2),
        name: "h".to_string(),
        ty: nat_lt_tc(a, b),
        value: None,
    };
    assert_omega_rejects(
        state_with(goal, vec![nat_local(0, "a"), nat_local(1, "b"), h]),
        "(h : a < b) ⊢ b ≤ a",
    );
}

/// FALSE: `(h : a ≤ b) ⊢ a + 2 ≤ b + 1`. Goal slack (-1) is SMALLER than hyp
/// slack (0); k_l=2,k_r=1,c=2,padded_rhs_off=2, k_r(1)<2 → reject.
#[test]
#[serial]
fn rev_shift_omega_rejects_a_le_b_implies_a_plus_2_le_b_plus_1() {
    let a = nat_fvar(0);
    let b = nat_fvar(1);
    let goal = nat_le_tc(
        nat_add(a.clone(), Expr::nat_lit(2)),
        nat_add(b.clone(), Expr::nat_lit(1)),
    );
    let h = LocalDecl {
        fvar: FVarId::new(2),
        name: "h".to_string(),
        ty: nat_le_tc(a, b),
        value: None,
    };
    assert_omega_rejects(
        state_with(goal, vec![nat_local(0, "a"), nat_local(1, "b"), h]),
        "(h : a ≤ b) ⊢ a + 2 ≤ b + 1",
    );
}

/// TRUE: `(h : a ≤ b) ⊢ a + 1 ≤ b + 2` (goal slack +1 > hyp slack 0). Should
/// PROVE through the full omega/kernel path — exercises rhs_steps > 0.
#[test]
#[serial]
fn rev_shift_omega_proves_a_le_b_implies_a_plus_1_le_b_plus_2() {
    let a = nat_fvar(0);
    let b = nat_fvar(1);
    let goal = nat_le_tc(
        nat_add(a.clone(), Expr::nat_lit(1)),
        nat_add(b.clone(), Expr::nat_lit(2)),
    );
    let h = LocalDecl {
        fvar: FVarId::new(2),
        name: "h".to_string(),
        ty: nat_le_tc(a, b),
        value: None,
    };
    assert_omega_proves(
        state_with(goal, vec![nat_local(0, "a"), nat_local(1, "b"), h]),
        "(h : a ≤ b) ⊢ a + 1 ≤ b + 2",
    );
}

/// TRUE-but-LHS-padded-asymmetrically: `(h : a ≤ b) ⊢ a + 2 ≤ b + 3`
/// (c=2, padded_rhs_off=2, k_r=3 → rhs_steps=1). Should PROVE.
#[test]
#[serial]
fn rev_shift_omega_proves_a_le_b_implies_a_plus_2_le_b_plus_3() {
    let a = nat_fvar(0);
    let b = nat_fvar(1);
    let goal = nat_le_tc(
        nat_add(a.clone(), Expr::nat_lit(2)),
        nat_add(b.clone(), Expr::nat_lit(3)),
    );
    let h = LocalDecl {
        fvar: FVarId::new(2),
        name: "h".to_string(),
        ty: nat_le_tc(a, b),
        value: None,
    };
    assert_omega_proves(
        state_with(goal, vec![nat_local(0, "a"), nat_local(1, "b"), h]),
        "(h : a ≤ b) ⊢ a + 2 ≤ b + 3",
    );
}
