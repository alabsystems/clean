// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Multi-step explicit witness regressions for compound `conv`.
//!
//! Part of #2555.

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

fn rw_rule(name: &str) -> SurfaceRwRule {
    SurfaceRwRule {
        span: Span::dummy(),
        reverse: false,
        term: SurfaceExpr::Ident(Span::dummy(), name.to_string()),
    }
}

fn local_fvar_by_name(state: &ProofState, name: &str) -> FVarId {
    state
        .current_goal()
        .expect("test state should have a current goal")
        .local_ctx
        .iter()
        .find(|decl| decl.name == name)
        .map(|decl| decl.fvar)
        .expect("named local should exist")
}

fn eval_conv_lhs_rw(
    ctx: &mut ElabCtx<'_>,
    state: &mut ProofState,
    rules: Vec<SurfaceRwRule>,
) -> Result<(), TacticError> {
    ctx.eval(
        state,
        &SurfaceTactic::Conv(
            Span::dummy(),
            SurfaceTacticLocation::Goal,
            vec![
                SurfaceTactic::ConvArg(Span::dummy(), -2),
                SurfaceTactic::Rw(Span::dummy(), rules, SurfaceTacticLocation::Goal),
            ],
        ),
    )
}

#[test]
#[serial]
fn test_conv_goal_compound_prop_multi_rule_rewrite_zero_trusted_axioms() {
    reset_all_counters();
    let env = setup_env_with_full_eq();
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);
    let z = Expr::const_(Name::from_string("z"), vec![]);
    let goal = Expr::pi(
        BinderInfo::Default,
        make_eq_n(x.clone(), y.clone()),
        Expr::pi(
            BinderInfo::Default,
            make_eq_n(y.clone(), z.clone()),
            make_eq(Expr::prop(), make_p(x.clone()), make_p(z.clone())),
        ),
    );
    let mut state = ProofState::new(env.clone(), goal);
    intro(&mut state, "hxy").expect("intro hxy");
    intro(&mut state, "hyz").expect("intro hyz");
    let axiom_before = axiom_snapshot();

    eval_conv_lhs_rw(
        &mut ElabCtx::new(&env),
        &mut state,
        vec![rw_rule("hxy"), rw_rule("hyz")],
    )
    .expect("multi-rule conv on a Prop-valued focus should succeed");

    assert_eq!(
        state.current_goal().unwrap().target,
        make_eq(Expr::prop(), make_p(z.clone()), make_p(z.clone())),
        "compound conv should rewrite P(x) -> P(z) across both rules"
    );
    rfl(&mut state).expect("rewritten Prop-valued equality should close by rfl");
    assert_no_trusted_fallback(&state, "compound conv prop multi-rule", axiom_before);
    assert!(state.proof_term().is_some());
    assert!(state.closed_proof().is_some());
}

#[test]
#[serial]
fn test_conv_goal_compound_nonprop_multi_rule_rewrite_zero_trusted_axioms() {
    reset_all_counters();
    let env = setup_env_with_full_eq();
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);
    let z = Expr::const_(Name::from_string("z"), vec![]);
    let goal = Expr::pi(
        BinderInfo::Default,
        make_eq_n(x.clone(), y.clone()),
        Expr::pi(
            BinderInfo::Default,
            make_eq_n(y.clone(), z.clone()),
            make_eq_n(x.clone(), z.clone()),
        ),
    );
    let mut state = ProofState::new(env.clone(), goal);
    intro(&mut state, "hxy").expect("intro hxy");
    intro(&mut state, "hyz").expect("intro hyz");
    let axiom_before = axiom_snapshot();

    eval_conv_lhs_rw(
        &mut ElabCtx::new(&env),
        &mut state,
        vec![rw_rule("hxy"), rw_rule("hyz")],
    )
    .expect("multi-rule conv on a Nat-valued focus should succeed");

    assert_eq!(
        state.current_goal().unwrap().target,
        make_eq_n(z.clone(), z.clone()),
        "compound conv should rewrite x -> z across both rules"
    );
    rfl(&mut state).expect("rewritten Nat-valued equality should close by rfl");
    assert_no_trusted_fallback(&state, "compound conv non-Prop multi-rule", axiom_before);
    assert!(state.proof_term().is_some());
    assert!(state.closed_proof().is_some());
}

#[test]
#[serial]
fn test_conv_at_hypothesis_multi_rule_rewrite_zero_trusted_axioms() {
    reset_all_counters();
    let env = setup_env_with_full_eq();
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);
    let z = Expr::const_(Name::from_string("z"), vec![]);
    let hyp_ty = make_eq(Expr::prop(), make_p(x.clone()), make_p(x.clone()));
    let goal = Expr::pi(
        BinderInfo::Default,
        make_eq_n(x.clone(), y.clone()),
        Expr::pi(
            BinderInfo::Default,
            make_eq_n(y.clone(), z.clone()),
            Expr::pi(
                BinderInfo::Default,
                hyp_ty,
                Expr::pi(BinderInfo::Default, make_p(z.clone()), make_p(z.clone())),
            ),
        ),
    );
    let mut state = ProofState::new(env.clone(), goal);
    intro(&mut state, "hxy").expect("intro hxy");
    intro(&mut state, "hyz").expect("intro hyz");
    intro(&mut state, "h_target").expect("intro h_target");
    intro(&mut state, "hz").expect("intro hz");
    let h_target_fvar = local_fvar_by_name(&state, "h_target");
    let hz_fvar = local_fvar_by_name(&state, "hz");
    let axiom_before = axiom_snapshot();

    let mut ctx = ElabCtx::new(&env);
    ctx.eval(
        &mut state,
        &SurfaceTactic::Conv(
            Span::dummy(),
            SurfaceTacticLocation::Hyps(vec!["h_target".into()]),
            vec![
                SurfaceTactic::ConvArg(Span::dummy(), -2),
                SurfaceTactic::Rw(
                    Span::dummy(),
                    vec![rw_rule("hxy"), rw_rule("hyz")],
                    SurfaceTacticLocation::Goal,
                ),
            ],
        ),
    )
    .expect("conv at h should compose multi-rule witnesses");

    let h_target = state
        .current_goal()
        .unwrap()
        .local_ctx
        .iter()
        .find(|decl| decl.name == "h_target")
        .expect("rewritten hypothesis should remain");
    assert_ne!(h_target.fvar, h_target_fvar);
    assert_eq!(
        h_target.ty,
        make_eq(Expr::prop(), make_p(z.clone()), make_p(x.clone())),
        "conv at h should rewrite the focused lhs across both rules"
    );
    assert_no_trusted_fallback(&state, "conv at h multi-rule", axiom_before);
    exact(&mut state, Expr::fvar(hz_fvar)).expect("unchanged goal should still close");
    assert!(state.proof_term().is_some());
    assert!(state.closed_proof().is_some());
}
