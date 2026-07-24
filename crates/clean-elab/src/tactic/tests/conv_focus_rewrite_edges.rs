// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Edge-case regressions for conv-focus rewrite dispatch.
//!
//! Part of #2540.

use super::*;
use crate::infer::ElabCtx;
use crate::tactic::registry::TacticEval;
use clean_parser::{Span, SurfaceExpr, SurfaceRwRule, SurfaceTactic, SurfaceTacticLocation};
use serial_test::serial;

fn assert_no_trusted_fallback(state: &ProofState, tactic_name: &str, before: (u64, u64)) {
    assert_eq!(
        state.trusted_axiom_count(),
        0,
        "{tactic_name} must not record trusted axiom usage"
    );
    assert_no_trusted_axiom_usage(tactic_name, "focused conv rewrite", before);
}

fn rw_rule_reverse(name: &str) -> SurfaceRwRule {
    SurfaceRwRule {
        span: Span::dummy(),
        reverse: true,
        term: SurfaceExpr::Ident(Span::dummy(), name.to_string()),
    }
}

fn rw_rule_forward(name: &str) -> SurfaceRwRule {
    SurfaceRwRule {
        span: Span::dummy(),
        reverse: false,
        term: SurfaceExpr::Ident(Span::dummy(), name.to_string()),
    }
}

/// `conv => lhs; rw [envLemma]` where the rewrite rule is an ENVIRONMENT
/// constant — a ∀-quantified equation `g_id : ∀ (a : N), g a = a` — not a local
/// hypothesis. Before the env-const fallback, `conv_focus_rewrite` resolved the
/// rule only in `local_ctx` and failed `HypothesisNotFound`. Now it falls back
/// to the environment, peels the ∀ binder to a metavariable, unifies `g ?a`
/// against the focus `g x` (solving `?a := x`), and rewrites `g x -> x` — the
/// identical resolution `rw [g_id]` uses, lifted through conv's congruence
/// proof. SOUNDNESS: the emitted `@g_id x` proof and the lifted congruence
/// witness are kernel-re-checked; no trusted fallback is recorded.
#[test]
#[serial]
fn test_conv_focus_rewrite_env_lemma_quantified() {
    reset_all_counters();
    let mut env = setup_env_with_full_eq();
    let n_ty = Expr::const_(Name::from_string("N"), vec![]);
    // g : N → N
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("g"),
        level_params: vec![],
        type_: Expr::pi(BinderInfo::Default, n_ty.clone(), n_ty.clone()),
    })
    .unwrap();
    // g_id : ∀ (a : N), @Eq N (g a) a   — a genuinely quantified env equation.
    let g = Expr::const_(Name::from_string("g"), vec![]);
    let g_bvar = Expr::app(g.clone(), Expr::bvar(0));
    let g_id_ty = Expr::pi(
        BinderInfo::Default,
        n_ty.clone(),
        make_eq_n(g_bvar, Expr::bvar(0)),
    );
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("g_id"),
        level_params: vec![],
        type_: g_id_ty,
    })
    .unwrap();

    let x = Expr::const_(Name::from_string("x"), vec![]);
    let g_x = Expr::app(g.clone(), x.clone());
    // Goal: g x = x
    let goal = make_eq_n(g_x, x.clone());
    let mut state = ProofState::new(env.clone(), goal);
    let axiom_before = axiom_snapshot();

    let mut ctx = ElabCtx::new(&env);
    ctx.eval(
        &mut state,
        &SurfaceTactic::Conv(
            Span::dummy(),
            SurfaceTacticLocation::Goal,
            vec![
                SurfaceTactic::ConvArg(Span::dummy(), -2), // focus lhs = `g x`
                SurfaceTactic::Rw(
                    Span::dummy(),
                    vec![rw_rule_forward("g_id")],
                    SurfaceTacticLocation::Goal,
                ),
            ],
        ),
    )
    .expect("conv => lhs; rw [g_id] should resolve the env lemma and rewrite g x -> x");

    assert_eq!(
        state.current_goal().unwrap().target,
        make_eq_n(x.clone(), x.clone()),
        "conv should rewrite `g x` -> `x` in the lhs focus via the env lemma"
    );
    rfl(&mut state).expect("x = x should close by rfl");
    assert_no_trusted_fallback(&state, "conv env-lemma quantified rewrite", axiom_before);
    assert!(
        state.proof_term().is_some(),
        "conv env-lemma rewrite must preserve proof_term()"
    );
}

/// NEGATIVE: an env-constant rewrite rule whose `from` side does not occur in
/// the conv focus must fail LOUD (`RewriteNoMatch`) — the env-const fallback
/// must never silently succeed or misfire. Focus is `g x`; the lemma `yz : y = z`
/// looks for `y`, absent from `g x`.
#[test]
#[serial]
fn test_conv_focus_rewrite_env_lemma_no_match_fails_loud() {
    reset_all_counters();
    let mut env = setup_env_with_full_eq();
    let n_ty = Expr::const_(Name::from_string("N"), vec![]);
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("g"),
        level_params: vec![],
        type_: Expr::pi(BinderInfo::Default, n_ty.clone(), n_ty.clone()),
    })
    .unwrap();
    let y = Expr::const_(Name::from_string("y"), vec![]);
    let z = Expr::const_(Name::from_string("z"), vec![]);
    // yz : @Eq N y z  — an env equation whose LHS `y` is absent from the focus.
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("yz"),
        level_params: vec![],
        type_: make_eq_n(y, z),
    })
    .unwrap();

    let g = Expr::const_(Name::from_string("g"), vec![]);
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let g_x = Expr::app(g, x.clone());
    let goal = make_eq_n(g_x, x);
    let mut state = ProofState::new(env.clone(), goal);

    let mut ctx = ElabCtx::new(&env);
    let err = ctx
        .eval(
            &mut state,
            &SurfaceTactic::Conv(
                Span::dummy(),
                SurfaceTacticLocation::Goal,
                vec![
                    SurfaceTactic::ConvArg(Span::dummy(), -2), // focus lhs = `g x`
                    SurfaceTactic::Rw(
                        Span::dummy(),
                        vec![rw_rule_forward("yz")],
                        SurfaceTacticLocation::Goal,
                    ),
                ],
            ),
        )
        .expect_err("rw [yz] on a focus without `y` must fail, not silently succeed");
    assert!(
        matches!(err, TacticError::RewriteNoMatch { .. }),
        "expected RewriteNoMatch for a non-occurring env-lemma LHS, got {err:?}"
    );
}

/// Test: compound `conv => lhs; rw [<-hxy]` on a Nat-valued equality goal.
///
/// Goal: (x = y) -> y = x
/// Body: conv => lhs; rw [<-hxy]
/// After conv: x = x
///
/// This exercises the reverse orientation path through `conv_focus_rewrite`.
#[test]
#[serial]
fn test_conv_goal_compound_nonprop_lhs_reverse_rewrite_zero_trusted_axioms() {
    reset_all_counters();
    let env = setup_env_with_full_eq();
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);
    let goal = Expr::pi(
        BinderInfo::Default,
        make_eq_n(x.clone(), y.clone()),
        make_eq_n(y.clone(), x.clone()),
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
                SurfaceTactic::ConvArg(Span::dummy(), -2),
                SurfaceTactic::Rw(
                    Span::dummy(),
                    vec![rw_rule_reverse("hxy")],
                    SurfaceTacticLocation::Goal,
                ),
            ],
        ),
    )
    .expect("conv => lhs; rw [<-hxy] on non-Prop focus should succeed");

    assert_eq!(
        state.current_goal().unwrap().target,
        make_eq_n(x.clone(), x.clone()),
        "compound conv should rewrite y -> x in non-Prop lhs focus"
    );

    rfl(&mut state).expect("x = x should close by rfl");
    assert_no_trusted_fallback(&state, "compound conv non-Prop lhs reverse", axiom_before);
    assert!(
        state.proof_term().is_some(),
        "compound conv non-Prop lhs reverse must preserve proof_term()"
    );
    assert!(
        state.closed_proof().is_some(),
        "compound conv non-Prop lhs reverse must preserve closed_proof()"
    );
}

/// Test: reverse `rw` on a non-Prop focus reports `NoProgress` when the focused
/// term does not contain the oriented rewrite source.
///
/// Goal: (x = y) -> x = y
/// Body: conv => lhs; rw [<-hxy]
///
/// The lhs focus is `x`, but the reverse rewrite looks for `y`, so the body
/// should fail before any outer proof lifting occurs.
#[test]
#[serial]
fn test_conv_goal_compound_nonprop_lhs_reverse_rewrite_reports_no_progress() {
    reset_all_counters();
    let env = setup_env_with_full_eq();
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);
    let goal = Expr::pi(
        BinderInfo::Default,
        make_eq_n(x.clone(), y.clone()),
        make_eq_n(x.clone(), y.clone()),
    );
    let mut state = ProofState::new(env.clone(), goal);
    intro(&mut state, "hxy").expect("intro");
    let axiom_before = axiom_snapshot();

    let mut ctx = ElabCtx::new(&env);
    let err = ctx
        .eval(
            &mut state,
            &SurfaceTactic::Conv(
                Span::dummy(),
                SurfaceTacticLocation::Goal,
                vec![
                    SurfaceTactic::ConvArg(Span::dummy(), -2),
                    SurfaceTactic::Rw(
                        Span::dummy(),
                        vec![rw_rule_reverse("hxy")],
                        SurfaceTacticLocation::Goal,
                    ),
                ],
            ),
        )
        .expect_err("conv => lhs; rw [<-hxy] should fail with no progress");

    assert!(
        matches!(
            &err,
            TacticError::NoProgress { tactic } if tactic == "rw"
        ),
        "expected typed rw no-progress on reverse non-Prop focus miss, got: {err:?}"
    );
    assert_eq!(
        state.current_goal().unwrap().target,
        make_eq_n(x.clone(), y.clone()),
        "failed reverse rewrite should leave the outer goal unchanged"
    );
    assert_no_trusted_fallback(
        &state,
        "compound conv non-Prop lhs reverse no-progress",
        axiom_before,
    );
}
