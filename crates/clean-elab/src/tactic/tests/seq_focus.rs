// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Regressions for the `<;>` (`SeqFocus`) tactic combinator.

use super::*;
use crate::infer::ElabCtx;
use crate::tactic::registry::TacticEval;
use clean_parser::{Span, SurfaceTactic};

fn named_tactic(name: &str) -> SurfaceTactic {
    SurfaceTactic::Named {
        span: Span::dummy(),
        name: name.to_string(),
        args: vec![],
    }
}

fn seq_focus_constructor_assumption() -> SurfaceTactic {
    SurfaceTactic::SeqFocus(
        Span::dummy(),
        Box::new(named_tactic("constructor")),
        Box::new(named_tactic("assumption")),
    )
}

fn focus_block_constructor_assumption() -> SurfaceTactic {
    SurfaceTactic::FocusBlock(
        Span::dummy(),
        vec![named_tactic("constructor"), named_tactic("assumption")],
    )
}

fn seq_focus_constructor_focus_block_assumption() -> SurfaceTactic {
    SurfaceTactic::SeqFocus(
        Span::dummy(),
        Box::new(named_tactic("constructor")),
        Box::new(focus_block_constructor_assumption()),
    )
}

fn and_expr(lhs: Expr, rhs: Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("And"), vec![]), lhs),
        rhs,
    )
}

#[test]
fn test_seq_focus_constructor_assumption_closes_each_goal_in_isolation() {
    let env = setup_env_with_and_or();
    let p = Expr::const_(Name::from_string("P"), vec![]);
    let q = Expr::const_(Name::from_string("Q"), vec![]);
    let target = Expr::pi(
        BinderInfo::Default,
        p.clone(),
        Expr::pi(
            BinderInfo::Default,
            q.clone(),
            and_expr(p.clone(), q.clone()),
        ),
    );

    let mut state = ProofState::new(env.clone(), target);
    intro(&mut state, "hp").expect("intro hp should expose the first hypothesis");
    intro(&mut state, "hq").expect("intro hq should expose the second hypothesis");

    let mut ctx = ElabCtx::new(&env);
    ctx.eval(&mut state, &seq_focus_constructor_assumption())
        .expect("constructor <;> assumption should solve both focused conjunction goals");

    assert!(
        state.is_complete(),
        "seq_focus should close both post-constructor goals"
    );
    assert!(
        state.closed_proof().is_some(),
        "successful seq_focus should leave a closed proof"
    );
}

#[test]
fn test_seq_focus_constructor_assumption_reports_unsolved_focused_goal() {
    let env = setup_env_with_and_or();
    let p = Expr::const_(Name::from_string("P"), vec![]);
    let q = Expr::const_(Name::from_string("Q"), vec![]);
    let target = Expr::pi(BinderInfo::Default, p.clone(), and_expr(p.clone(), q));

    let mut state = ProofState::new(env.clone(), target);
    intro(&mut state, "hp").expect("intro hp should expose the only matching hypothesis");

    let mut ctx = ElabCtx::new(&env);
    let err = ctx
        .eval(&mut state, &seq_focus_constructor_assumption())
        .expect_err("constructor <;> assumption should fail when a focused goal lacks a match");

    let err_text = format!("{err:?}");
    assert!(
        err_text.contains("no matching hypothesis found"),
        "expected assumption failure for the unmatched focused goal, got: {err_text}"
    );
    assert_eq!(
        state.goals().len(),
        1,
        "failed seq_focus should leave the unmatched focused goal outstanding"
    );
    assert!(
        state.goals()[0].target == Expr::const_(Name::from_string("Q"), vec![]),
        "failed seq_focus should leave the unmatched focused goal as the remaining work"
    );
}

#[test]
fn test_seq_focus_failure_preserves_active_focused_state() {
    let env = setup_env_with_and_or();
    let p = Expr::const_(Name::from_string("P"), vec![]);
    let q = Expr::const_(Name::from_string("Q"), vec![]);
    let target = Expr::pi(
        BinderInfo::Default,
        p.clone(),
        and_expr(and_expr(p.clone(), q.clone()), p.clone()),
    );

    let mut state = ProofState::new(env.clone(), target);
    intro(&mut state, "hp").expect("intro hp should expose the matching P hypothesis");

    let mut ctx = ElabCtx::new(&env);
    ctx.eval(&mut state, &seq_focus_constructor_focus_block_assumption())
        .expect_err(
            "constructor <;> { constructor; assumption } should fail on the first focused branch",
        );

    assert_eq!(
        state.goals().len(),
        1,
        "failed seq_focus should keep only the active focused branch state"
    );
    assert_eq!(
        state.goals()[0].target,
        q,
        "failed seq_focus should preserve the unsolved goal produced inside the failing focused branch"
    );
}
