// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Compound handler (`conv => body`) and hypothesis (`conv at h`) proof-carry tests.
//!
//! Split from `conv_proof_carry.rs` as part of #2547.
//! Part of #2519, #2540.

use super::*;
use crate::infer::ElabCtx;
use crate::tactic::registry::TacticEval;
use clean_parser::{SurfaceTactic, SurfaceTacticLocation};

// =========================================================================
// #2511: conv at hypothesis proof-carry
// =========================================================================

/// Build `h_eq : x = y, h_target : P(x) = P(x), hy : P(y) ⊢ P(y)`.
fn setup_conv_at_hyp_state() -> (ProofState, Environment) {
    let env = setup_env_with_full_eq();
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);
    let hyp_ty = make_eq(Expr::prop(), make_p(x.clone()), make_p(x.clone()));
    let goal = Expr::pi(
        BinderInfo::Default,
        make_eq_n(x, y.clone()),
        Expr::pi(
            BinderInfo::Default,
            hyp_ty,
            Expr::pi(BinderInfo::Default, make_p(y.clone()), make_p(y)),
        ),
    );
    let mut state = ProofState::new(env.clone(), goal);
    intro(&mut state, "h_eq").expect("intro h_eq");
    intro(&mut state, "h_target").expect("intro h_target");
    intro(&mut state, "hy").expect("intro hy");
    (state, env)
}

#[test]
#[serial]
fn test_conv_at_hypothesis_uses_local_proof_carry_without_trust() {
    reset_all_counters();
    let (mut state, env) = setup_conv_at_hyp_state();
    let h_target_fvar = local_fvar_by_name(&state, "h_target");
    let hy_fvar = local_fvar_by_name(&state, "hy");
    let mut ctx = ElabCtx::new(&env);
    let axiom_before = axiom_snapshot();
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);

    ctx.eval(
        &mut state,
        &SurfaceTactic::Conv(
            Span::dummy(),
            SurfaceTacticLocation::Hyps(vec!["h_target".into()]),
            vec![
                SurfaceTactic::ConvArg(Span::dummy(), -2),
                SurfaceTactic::Rw(
                    Span::dummy(),
                    vec![rw_rule("h_eq")],
                    SurfaceTacticLocation::Goal,
                ),
            ],
        ),
    )
    .expect("conv at h should rewrite through the local proof-carry API");

    let h_target = state
        .current_goal()
        .unwrap()
        .local_ctx
        .iter()
        .find(|d| d.name == "h_target")
        .expect("rewritten hypothesis should remain");
    assert_ne!(
        h_target.fvar, h_target_fvar,
        "replacement must allocate a fresh fvar"
    );
    assert_eq!(h_target.ty, make_eq(Expr::prop(), make_p(y), make_p(x)));
    assert_eq!(
        state.trusted_axiom_count(),
        0,
        "conv at h must not use trusted axioms"
    );
    assert_no_trusted_axiom_usage("conv at h", "hypothesis rewrite", axiom_before);

    exact(&mut state, Expr::fvar(hy_fvar)).expect("unchanged goal should close");
    assert!(
        state.proof_term().is_some(),
        "conv at h must preserve proof_term()"
    );
    assert!(
        state.closed_proof().is_some(),
        "conv at h must preserve closed_proof()"
    );
}

// =========================================================================
// #2519: Compound handler (eval_conv_goal) proof-carry regressions
//
// These tests exercise the real `conv => body` surface path through
// `ElabCtx::eval` → compound `Conv` handler → `eval_conv_goal`, which
// is distinct from the direct `conv_rw`/`conv_lhs`/`conv_rhs` API tested
// in the parent module.
//
// The compound handler now consumes an explicit focused equality witness from
// the nested conv body and lifts it through `conv_proof.rs` instead of trying
// to recover a single local hypothesis after the fact.
// =========================================================================

/// Test: compound `conv => lhs; rw [hxy]` on goal produces zero trusted axioms.
///
/// Exercises the full `eval_conv_goal` path in `builtins_phase3d_conv.rs`
/// through the compound handler dispatch. This is the primary acceptance
/// criterion for #2519: block-form `conv => body` on the goal target
/// must not use `replace_target_with_trusted_fallback`.
///
/// Part of #2519.
#[test]
#[serial]
fn test_conv_goal_compound_lhs_rewrite_zero_trusted_axioms() {
    reset_all_counters();
    let env = setup_env_with_full_eq();
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);
    // Goal: (x = y) → P(x) = P(y)
    let goal = Expr::pi(
        BinderInfo::Default,
        make_eq_n(x.clone(), y.clone()),
        make_eq(Expr::prop(), make_p(x.clone()), make_p(y.clone())),
    );
    let mut state = ProofState::new(env.clone(), goal);
    intro(&mut state, "hxy").expect("intro");
    let axiom_before = axiom_snapshot();

    let mut ctx = ElabCtx::new(&env);
    ctx.eval(
        &mut state,
        &SurfaceTactic::Conv(
            Span::dummy(),
            SurfaceTacticLocation::Goal,
            vec![
                SurfaceTactic::ConvArg(Span::dummy(), -2), // navigate to LHS
                SurfaceTactic::Rw(
                    Span::dummy(),
                    vec![rw_rule("hxy")],
                    SurfaceTacticLocation::Goal,
                ),
            ],
        ),
    )
    .expect("conv => lhs; rw [hxy] should succeed through the compound handler");

    // After conv: P(y) = P(y)
    assert_eq!(
        state.current_goal().unwrap().target,
        make_eq(Expr::prop(), make_p(y.clone()), make_p(y)),
        "compound conv goal should rewrite P(x) → P(y) in LHS"
    );

    rfl(&mut state).expect("P(y) = P(y) should close by rfl");
    assert_no_trusted_fallback(&state, "compound conv goal lhs", axiom_before);
    assert!(
        state.proof_term().is_some(),
        "compound conv goal must preserve proof_term()"
    );
    assert!(
        state.closed_proof().is_some(),
        "compound conv goal must preserve closed_proof()"
    );
}

/// Test: compound `conv => rhs; rw [hyx]` on goal produces zero trusted axioms.
///
/// Symmetric to the LHS test: rewrites the RHS of an equality goal through
/// the compound handler, verifying the proof-carrying path works for both
/// navigation directions.
///
/// Part of #2519.
#[test]
#[serial]
fn test_conv_goal_compound_rhs_rewrite_zero_trusted_axioms() {
    reset_all_counters();
    let env = setup_env_with_full_eq();
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);
    // Goal: (y = x) → P(x) = P(y)
    let goal = Expr::pi(
        BinderInfo::Default,
        make_eq_n(y.clone(), x.clone()),
        make_eq(Expr::prop(), make_p(x.clone()), make_p(y.clone())),
    );
    let mut state = ProofState::new(env.clone(), goal);
    intro(&mut state, "hyx").expect("intro");
    let axiom_before = axiom_snapshot();

    let mut ctx = ElabCtx::new(&env);
    ctx.eval(
        &mut state,
        &SurfaceTactic::Conv(
            Span::dummy(),
            SurfaceTacticLocation::Goal,
            vec![
                SurfaceTactic::ConvArg(Span::dummy(), -1), // navigate to RHS
                SurfaceTactic::Rw(
                    Span::dummy(),
                    vec![rw_rule("hyx")],
                    SurfaceTacticLocation::Goal,
                ),
            ],
        ),
    )
    .expect("conv => rhs; rw [hyx] should succeed through the compound handler");

    // After conv: P(x) = P(x)
    assert_eq!(
        state.current_goal().unwrap().target,
        make_eq(Expr::prop(), make_p(x.clone()), make_p(x)),
        "compound conv goal should rewrite P(y) → P(x) in RHS"
    );

    rfl(&mut state).expect("P(x) = P(x) should close by rfl");
    assert_no_trusted_fallback(&state, "compound conv goal rhs", axiom_before);
    assert!(
        state.proof_term().is_some(),
        "compound conv goal rhs must preserve proof_term()"
    );
    assert!(
        state.closed_proof().is_some(),
        "compound conv goal rhs must preserve closed_proof()"
    );
}

// NOTE: Whole-target (no-navigation) compound handler tests are NOT included
// because Rw's built-in rfl closeout solves the conv sub-goal, causing
// eval_conv_goal to return early without reaching replace_target_eq.
// Part of #2519.

// =========================================================================
// conv-congr soundness: `conv => congr; rw` must produce a kernel-checked
// proof of the ORIGINAL equality with no new (non-foundational) axioms.
//
// This is the strong soundness test for the conv-congr hardening. Unlike the
// previous `conv_ext::conv_congr` unit tests (which only asserted goal counts
// after a disconnected meta-split), this test:
//   1. drives the REAL surface routing (`SurfaceTactic::Named{name:"congr"}`
//      inside a `conv` body, dispatched via `run_conv_body` → `conv_congr`),
//   2. actually SOLVES the resulting goal (rewrites a focused sub-argument and
//      closes by rfl), and
//   3. extracts the closed proof term, KERNEL-TYPE-CHECKS it against the
//      original goal type, and verifies its transitive axiom closure introduces
//      no axiom beyond the statement's own vocabulary (and never `sorry` /
//      `trustedArith` / `trustedAy`).
// =========================================================================

/// Collect the transitive axiom closure of `expr` in `env`.
///
/// Walks every `Const` reachable from `expr` and, transitively, from the value
/// of every reachable definition/theorem, accumulating the names whose
/// `ConstantInfo` is an actual `Axiom` (no value). This is the closure the
/// soundness rules constrain.
fn transitive_axioms(env: &Environment, expr: &Expr) -> std::collections::BTreeSet<Name> {
    let mut axioms = std::collections::BTreeSet::new();
    let mut seen: std::collections::HashSet<Name> = std::collections::HashSet::new();
    let mut frontier: Vec<Name> = expr.collect_constants().into_iter().collect();
    while let Some(name) = frontier.pop() {
        if !seen.insert(name.clone()) {
            continue;
        }
        let Some(info) = env.get_const(&name) else {
            continue;
        };
        if info.value.is_none() && info.kind == clean_kernel::env::ConstantKind::Axiom {
            axioms.insert(name.clone());
        }
        if let Some(value) = &info.value {
            frontier.extend(value.collect_constants());
        }
    }
    axioms
}

/// Strong soundness: `conv => congr; congr; rw [hyx]` on goal `P x = P y`.
///
/// Goal: `(y = x) → (P x = P y)`.
/// Body: descend RHS-arg via `congr` (focus `P y`), descend `P`'s arg via a
/// second `congr` (focus `y`), then `rw [hyx]` (`hyx : y = x`) rewrites the
/// focused `y → x`. The conv reconstruction lifts the focus witness `y = x`
/// through the `[AppArg, AppArg]` navigation path via nested `congrArg`,
/// producing a kernel-checked proof of `(P x = P y) = (P x = P x)`, which
/// `replace_target_eq` uses (via `Eq.mpr`) to turn the goal into `P x = P x`,
/// closed by `rfl`.
///
/// This is the acceptance criterion for the conv-congr hardening: the multi-step
/// `congr` navigation produces a GENUINE, kernel-accepted congruence proof of
/// the original goal — not a goal-count illusion.
#[test]
#[serial]
fn test_conv_congr_surface_rewrite_kernel_checked_no_new_axioms() {
    reset_all_counters();
    let env = setup_env_with_full_eq();
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);
    // Goal: (y = x) → (P x = P y)
    let goal_ty = Expr::pi(
        BinderInfo::Default,
        make_eq_n(y.clone(), x.clone()),
        make_eq(Expr::prop(), make_p(x.clone()), make_p(y.clone())),
    );
    let mut state = ProofState::new(env.clone(), goal_ty.clone());
    intro(&mut state, "hyx").expect("intro hyx : y = x");
    let axiom_before = axiom_snapshot();

    let mut ctx = ElabCtx::new(&env);
    ctx.eval(
        &mut state,
        &SurfaceTactic::Conv(
            Span::dummy(),
            SurfaceTacticLocation::Goal,
            vec![
                // Surface `congr` inside conv: routed to conv_congr via run_conv_body.
                SurfaceTactic::Named {
                    span: Span::dummy(),
                    name: "congr".into(),
                    args: vec![],
                },
                SurfaceTactic::Named {
                    span: Span::dummy(),
                    name: "congr".into(),
                    args: vec![],
                },
                SurfaceTactic::Rw(
                    Span::dummy(),
                    vec![rw_rule("hyx")],
                    SurfaceTacticLocation::Goal,
                ),
            ],
        ),
    )
    .expect("conv => congr; congr; rw [hyx] should rewrite the focused argument");

    // After conv: P x = P x.
    assert_eq!(
        state.current_goal().unwrap().target,
        make_eq(Expr::prop(), make_p(x.clone()), make_p(x.clone())),
        "conv-congr should rewrite the RHS argument y → x via congruence"
    );

    rfl(&mut state).expect("P x = P x should close by rfl");
    assert_no_trusted_fallback(&state, "conv congr surface rewrite", axiom_before);

    // (1) The whole proof must be extractable (goal genuinely closed).
    let proof = state
        .closed_proof()
        .expect("conv-congr proof must be a closed term");

    // (2) The closed proof must KERNEL-TYPE-CHECK against the ORIGINAL goal type.
    //     This is the soundness boundary: the kernel — not the tactic — certifies
    //     that the assembled congruence proof actually proves `(y = x) → P x = P y`.
    let tc = clean_kernel::TypeChecker::new(&env);
    let inferred = tc
        .infer_type(&proof)
        .expect("conv-congr proof term must kernel-type-check");
    assert!(
        tc.is_def_eq(&inferred, &goal_ty),
        "conv-congr proof must have the ORIGINAL goal type; inferred {inferred:?}, expected {goal_ty:?}"
    );
    // NEGATIVE SANITY (teeth check): the kernel must REJECT a deliberately wrong
    // claimed type, so the positive assertion above is not vacuous.
    let wrong_ty = Expr::pi(
        BinderInfo::Default,
        make_eq_n(y.clone(), x.clone()),
        make_eq(Expr::prop(), make_p(y.clone()), make_p(x.clone())),
    );
    assert!(
        !tc.is_def_eq(&inferred, &wrong_ty),
        "kernel must reject a wrong claimed type for the conv-congr proof"
    );

    // (3) No `sorry` / trusted-arith escape hatches anywhere in the term.
    for forbidden in ["sorry", "trustedArith", "trustedAy"] {
        assert!(
            !expr_contains_const(&proof, forbidden),
            "conv-congr proof must not contain `{forbidden}`"
        );
    }

    // (4) Axiom closure: the proof must introduce no axiom beyond the
    //     statement's own vocabulary. The conv-congr machinery is built from
    //     Eq builtins (Eq, Eq.refl, Eq.mpr, congrArg, ...) — the foundational
    //     equality core — plus the signature constants already named in the
    //     goal (N, x, y, P). It must NOT pull in any further axiom.
    let stmt_axioms = transitive_axioms(&env, &goal_ty);
    let proof_axioms = transitive_axioms(&env, &proof);
    let introduced: Vec<Name> = proof_axioms.difference(&stmt_axioms).cloned().collect();
    assert!(
        introduced.is_empty(),
        "conv-congr proof introduced axioms beyond the statement vocabulary: {introduced:?}"
    );

    assert!(
        state.proof_term().is_some(),
        "conv-congr must preserve proof_term()"
    );
}

// =========================================================================
// #2540: Non-Prop focus conv rewrite regressions
//
// When conv navigates to a term-valued focus (e.g., lhs of `x = y` is `x : Nat`),
// the generic Eq.subst rewrite path builds an ill-typed motive (Nat→Nat instead
// of Nat→Prop). The fix dispatches through conv_focus_rewrite in
// builtins_phase3d_rewrite.rs for structural replacement, letting eval_conv_goal
// lift the proof via congruence.
// =========================================================================

/// Test: compound `conv => lhs; rw [hxy]` on a Nat-valued equality goal.
///
/// Goal: (x = y) → x = y
/// Body: conv => lhs; rw [hxy]
/// After conv: y = y
///
/// This is the primary acceptance criterion for #2540: navigating to a non-Prop
/// focus (`x : Nat`) and rewriting must succeed with zero trusted axioms.
///
/// Part of #2540.
#[test]
#[serial]
fn test_conv_goal_compound_nonprop_lhs_rewrite_zero_trusted_axioms() {
    reset_all_counters();
    let env = setup_env_with_full_eq();
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);
    // Goal: (x = y) → x = y
    let goal = Expr::pi(
        BinderInfo::Default,
        make_eq_n(x.clone(), y.clone()),
        make_eq_n(x.clone(), y.clone()),
    );
    let mut state = ProofState::new(env.clone(), goal);
    intro(&mut state, "hxy").expect("intro");
    let axiom_before = axiom_snapshot();

    let mut ctx = ElabCtx::new(&env);
    ctx.eval(
        &mut state,
        &SurfaceTactic::Conv(
            Span::dummy(),
            SurfaceTacticLocation::Goal,
            vec![
                SurfaceTactic::ConvArg(Span::dummy(), -2), // navigate to LHS
                SurfaceTactic::Rw(
                    Span::dummy(),
                    vec![rw_rule("hxy")],
                    SurfaceTacticLocation::Goal,
                ),
            ],
        ),
    )
    .expect("conv => lhs; rw [hxy] on non-Prop focus should succeed through conv_focus_rewrite");

    // After conv: y = y
    assert_eq!(
        state.current_goal().unwrap().target,
        make_eq_n(y.clone(), y.clone()),
        "compound conv should rewrite x → y in non-Prop LHS focus"
    );

    rfl(&mut state).expect("y = y should close by rfl");
    assert_no_trusted_fallback(&state, "compound conv non-Prop lhs", axiom_before);
    assert!(
        state.proof_term().is_some(),
        "compound conv non-Prop lhs must preserve proof_term()"
    );
    assert!(
        state.closed_proof().is_some(),
        "compound conv non-Prop lhs must preserve closed_proof()"
    );
}

// =========================================================================
// ADVERSARIAL (reviewer-added): try to BREAK conv-congr soundness.
// =========================================================================

/// ATTACK 1: a FALSE goal `P x = P y` (x != y, no equality witness in scope)
/// must NOT become closeable just because `conv => congr; congr` narrowed the
/// focus. conv_congr only navigates; with no rewrite there is no focus witness,
/// so the goal must remain `P x = P y` and rfl must fail.
#[test]
#[serial]
fn adversarial_conv_congr_cannot_close_false_goal_without_witness() {
    reset_all_counters();
    let env = setup_env_with_full_eq();
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);
    // FALSE: P x = P y with x, y distinct opaque constants, no eq hyp.
    let goal_ty = make_eq(Expr::prop(), make_p(x.clone()), make_p(y.clone()));
    let mut state = ProofState::new(env.clone(), goal_ty.clone());

    let mut ctx = ElabCtx::new(&env);
    let _ = ctx.eval(
        &mut state,
        &SurfaceTactic::Conv(
            Span::dummy(),
            SurfaceTacticLocation::Goal,
            vec![
                SurfaceTactic::Named {
                    span: Span::dummy(),
                    name: "congr".into(),
                    args: vec![],
                },
                SurfaceTactic::Named {
                    span: Span::dummy(),
                    name: "congr".into(),
                    args: vec![],
                },
            ],
        ),
    );

    // Goal must still be the ORIGINAL false equality (conv with no rewrite is
    // a no-op on the target via def-eq path).
    assert_eq!(
        state.current_goal().expect("goal present").target,
        goal_ty,
        "conv-congr with no rewrite must leave the false goal unchanged"
    );
    // rfl must FAIL: P x and P y are not def-eq.
    assert!(
        rfl(&mut state).is_err(),
        "SOUNDNESS HOLE: rfl closed P x = P y with x != y"
    );
    // No closed proof exists.
    assert!(
        state.closed_proof().is_none() || !state.goals.is_empty(),
        "SOUNDNESS HOLE: a false goal produced a closed proof"
    );
}

/// ATTACK 2: a wrong-direction / non-matching rewrite must not let the original
/// false goal `P x = P y` be discharged. We give `hzy : z = y` and try to
/// `rw [hzy]` at the focus `y` (whose lhs `z` does not match the focus). Either
/// the rw makes no progress (goal stays false) or it rewrites y->z making the
/// goal `P x = P z` — still false, still not closeable by rfl. In NEITHER case
/// may a closed proof of the ORIGINAL goal appear.
#[test]
#[serial]
fn adversarial_conv_congr_wrong_witness_cannot_discharge_original() {
    reset_all_counters();
    let env = setup_env_with_full_eq();
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);
    let z = Expr::const_(Name::from_string("z"), vec![]);
    // Goal: (z = y) -> (P x = P y).  The antecedent z=y does NOT prove P x = P y.
    let goal_ty = Expr::pi(
        BinderInfo::Default,
        make_eq_n(z.clone(), y.clone()),
        make_eq(Expr::prop(), make_p(x.clone()), make_p(y.clone())),
    );
    let mut state = ProofState::new(env.clone(), goal_ty.clone());
    intro(&mut state, "hzy").expect("intro hzy : z = y");

    let mut ctx = ElabCtx::new(&env);
    let _ = ctx.eval(
        &mut state,
        &SurfaceTactic::Conv(
            Span::dummy(),
            SurfaceTacticLocation::Goal,
            vec![
                SurfaceTactic::Named {
                    span: Span::dummy(),
                    name: "congr".into(),
                    args: vec![],
                },
                SurfaceTactic::Named {
                    span: Span::dummy(),
                    name: "congr".into(),
                    args: vec![],
                },
                SurfaceTactic::Rw(
                    Span::dummy(),
                    vec![rw_rule("hzy")],
                    SurfaceTacticLocation::Goal,
                ),
            ],
        ),
    );

    let cur = state.current_goal().expect("goal present").target.clone();
    let original_rhs = make_eq(Expr::prop(), make_p(x.clone()), make_p(y.clone()));
    let rewritten_rhs = make_eq(Expr::prop(), make_p(x.clone()), make_p(z.clone()));
    // The goal is either unchanged (P x = P y) or y->z rewritten (P x = P z).
    assert!(
        cur == original_rhs || cur == rewritten_rhs,
        "unexpected goal after wrong-witness conv-congr: {cur:?}"
    );
    // rfl must FAIL either way.
    assert!(
        rfl(&mut state).is_err(),
        "SOUNDNESS HOLE: a false goal closed by rfl after wrong-witness conv-congr"
    );
    // If a closed proof is somehow produced, it must NOT kernel-check at the
    // original false type.
    if state.goals.is_empty() {
        if let Some(proof) = state.closed_proof() {
            let tc = clean_kernel::TypeChecker::new(&env);
            if let Ok(inferred) = tc.infer_type(&proof) {
                assert!(
                    !tc.is_def_eq(&inferred, &goal_ty),
                    "SOUNDNESS HOLE: kernel accepted a proof of the false goal"
                );
            }
        }
    }
}

/// ATTACK 3: directly drive conv_congr then a focus rewrite to an UNEQUAL value
/// (rw with a real eq `y = x`) and confirm the reconstructed whole-target proof
/// kernel-checks ONLY for the genuine resulting type and the new goal is the
/// honest `P x = P x` (true) — i.e. the lifted congrArg proof never claims more
/// than the witness justifies. This is the positive control that the lift is
/// faithful (not over-strong).
#[test]
#[serial]
fn adversarial_conv_congr_lift_is_faithful_not_overstrong() {
    reset_all_counters();
    let env = setup_env_with_full_eq();
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);
    let goal_ty = Expr::pi(
        BinderInfo::Default,
        make_eq_n(y.clone(), x.clone()),
        make_eq(Expr::prop(), make_p(x.clone()), make_p(y.clone())),
    );
    let mut state = ProofState::new(env.clone(), goal_ty.clone());
    intro(&mut state, "hyx").expect("intro hyx : y = x");
    let mut ctx = ElabCtx::new(&env);
    ctx.eval(
        &mut state,
        &SurfaceTactic::Conv(
            Span::dummy(),
            SurfaceTacticLocation::Goal,
            vec![
                SurfaceTactic::Named {
                    span: Span::dummy(),
                    name: "congr".into(),
                    args: vec![],
                },
                SurfaceTactic::Named {
                    span: Span::dummy(),
                    name: "congr".into(),
                    args: vec![],
                },
                SurfaceTactic::Rw(
                    Span::dummy(),
                    vec![rw_rule("hyx")],
                    SurfaceTacticLocation::Goal,
                ),
            ],
        ),
    )
    .expect("legit conv-congr-rw");
    // The new goal must be exactly P x = P x (the witness y=x justifies exactly
    // this), never something stronger.
    assert_eq!(
        state.current_goal().unwrap().target,
        make_eq(Expr::prop(), make_p(x.clone()), make_p(x.clone())),
        "lift must produce exactly the witness-justified goal"
    );
    rfl(&mut state).expect("P x = P x closes by rfl");
    let proof = state.closed_proof().expect("closed");
    let tc = clean_kernel::TypeChecker::new(&env);
    let inferred = tc.infer_type(&proof).expect("kernel checks");
    assert!(
        tc.is_def_eq(&inferred, &goal_ty),
        "must prove the real goal"
    );
    // Teeth: must NOT prove the swapped (false-flavored) variant.
    let swapped = Expr::pi(
        BinderInfo::Default,
        make_eq_n(y.clone(), x.clone()),
        make_eq(Expr::prop(), make_p(y.clone()), make_p(x.clone())),
    );
    assert!(
        !tc.is_def_eq(&inferred, &swapped),
        "SOUNDNESS HOLE: proof also type-checks at a non-justified type"
    );
}
