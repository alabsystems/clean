// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::tactic::registry::{ElaboratedRefine, TacticEval};
use crate::tactic::ProofState;
use crate::unify::MetaState;
use clean_kernel::{Environment, Expr};
use clean_parser::{Span, SurfaceExpr};
use std::collections::VecDeque;

struct StubEval {
    calls: usize,
    results: VecDeque<Result<(), TacticError>>,
    metas: MetaState,
}

impl TacticEval for StubEval {
    fn eval(&mut self, _ps: &mut ProofState, _tac: &SurfaceTactic) -> Result<(), TacticError> {
        unreachable!("compound_first only uses eval_seq")
    }

    fn eval_seq(
        &mut self,
        ps: &mut ProofState,
        _tacs: &[SurfaceTactic],
    ) -> Result<(), TacticError> {
        self.calls += 1;
        match self.results.pop_front().expect("stub result for eval_seq") {
            Ok(()) => {
                ps.goals.clear();
                Ok(())
            }
            Err(err) => Err(err),
        }
    }

    fn elaborate(&mut self, _expr: &SurfaceExpr) -> Result<Expr, TacticError> {
        unreachable!("compound_first does not elaborate expressions")
    }

    fn infer_type(&mut self, _expr: &Expr) -> Result<Expr, TacticError> {
        unreachable!("compound_first does not infer types")
    }

    fn elaborate_refine(
        &mut self,
        _ps: &ProofState,
        _expr: &SurfaceExpr,
    ) -> Result<ElaboratedRefine, TacticError> {
        unreachable!("compound_first does not elaborate refine terms")
    }

    fn metas(&self) -> &MetaState {
        &self.metas
    }
}

fn first_tactic_surface() -> SurfaceTactic {
    SurfaceTactic::First(Span::dummy(), vec![vec![], vec![]])
}

fn test_state() -> ProofState {
    ProofState::new(Environment::new(), Expr::prop())
}

#[test]
fn test_compound_first_retries_recoverable_error() {
    let mut eval = StubEval {
        calls: 0,
        results: VecDeque::from([Err(TacticError::no_progress("assumption")), Ok(())]),
        metas: MetaState::new(),
    };
    let mut state = test_state();
    let handler = compound_first();

    (handler.handler)(&mut eval, &mut state, &first_tactic_surface())
        .expect("recoverable first-branch failure should try the next branch");

    assert_eq!(
        eval.calls, 2,
        "recoverable errors should advance to the next branch"
    );
    assert!(
        state.goals().is_empty(),
        "successful branch should commit its state"
    );
}

/// `first` must NOT swallow a fatal error.
///
/// "Fatal" here is a deliberate, narrow set — `NoGoals`, `UnknownTactic`,
/// `MissingArgument`, `UserThrowError`, `ParseFailed`. These signal a MALFORMED
/// SCRIPT or an explicit user abort, not "this branch did not apply", and
/// backtracking past them would hide the real problem behind a later branch
/// that happens to succeed.
///
/// This test previously used `TypeCheckFailed`, which has since been
/// RECLASSIFIED as recoverable on purpose (see
/// `TacticError::is_recoverable_first_failure`): Lean 4's `first` backtracks on
/// any tactic failure, and treating it as fatal made `first | rfl | exact h`
/// propagate `rfl`'s mismatch instead of falling through to `exact h`. The code
/// change was right and this test was left asserting the superseded semantics,
/// so it failed. Switched to `ParseFailed` — a malformed script, which must
/// never be silently retried past — which preserves what the test was actually
/// for.
#[test]
fn test_compound_first_stops_on_fatal_error() {
    let mut eval = StubEval {
        calls: 0,
        results: VecDeque::from([
            Err(TacticError::ParseFailed {
                tactic: "first branch".into(),
                detail: "fatal".into(),
            }),
            Ok(()),
        ]),
        metas: MetaState::new(),
    };
    let mut state = test_state();
    let handler = compound_first();

    let result = (handler.handler)(&mut eval, &mut state, &first_tactic_surface());

    assert!(
        matches!(result, Err(TacticError::ParseFailed { ref detail, .. }) if detail == "fatal"),
        "fatal branch failures should stop first immediately, got {result:?}"
    );
    assert_eq!(
        eval.calls, 1,
        "fatal errors should not evaluate later branches"
    );
    assert_eq!(
        state.goals().len(),
        1,
        "fatal branch should leave the original state intact"
    );
}

#[test]
fn test_compound_first_propagates_last_branch_error() {
    let mut eval = StubEval {
        calls: 0,
        results: VecDeque::from([
            Err(TacticError::no_progress("assumption")),
            Err(TacticError::TypeCheckFailed("last branch".into())),
        ]),
        metas: MetaState::new(),
    };
    let mut state = test_state();
    let handler = compound_first();

    let result = (handler.handler)(&mut eval, &mut state, &first_tactic_surface());

    assert!(
        matches!(result, Err(TacticError::TypeCheckFailed(ref msg)) if msg == "last branch"),
        "last branch should surface its concrete error instead of AllTacticsFailed, got {result:?}"
    );
    assert_eq!(eval.calls, 2, "the final branch should still run");
}

#[test]
fn case_rejects_relative_or_anonymous_selector_and_binder_before_dispatch() {
    let ordinary = clean_parser::parse_name("h").unwrap();
    for invalid in [
        ordinary.clone().with_relative_constructor(),
        SurfaceName::default(),
    ] {
        for (tag, binders) in [
            (invalid.clone(), vec![]),
            (ordinary.clone(), vec![invalid.clone()]),
        ] {
            let mut state = test_state();
            state.current_goal_mut().unwrap().tag = Some(ordinary.clone());
            let before = state.current_goal().unwrap().meta_id;
            let mut eval = StubEval {
                calls: 0,
                results: VecDeque::new(),
                metas: MetaState::new(),
            };
            let tactic = SurfaceTactic::Case(Span::dummy(), tag, binders, vec![]);
            assert!(matches!(
                (compound_case().handler)(&mut eval, &mut state, &tactic),
                Err(TacticError::InvalidTarget { .. })
            ));
            assert_eq!(eval.calls, 0);
            assert_eq!(state.goals.len(), 1);
            assert_eq!(state.current_goal().unwrap().meta_id, before);
            assert_eq!(state.current_goal().unwrap().tag, Some(ordinary.clone()));
        }
    }
}

#[test]
fn case_dispatch_accepts_quoted_literal_leading_dot_and_underscore() {
    for spelling in ["«.h»", "«_»"] {
        let tag = clean_parser::parse_name(spelling).unwrap();
        let mut state = test_state();
        state.current_goal_mut().unwrap().tag = Some(tag.clone());
        let mut eval = StubEval {
            calls: 0,
            results: VecDeque::from([Ok(())]),
            metas: MetaState::new(),
        };
        let tactic = SurfaceTactic::Case(Span::dummy(), tag, vec![], vec![]);
        (compound_case().handler)(&mut eval, &mut state, &tactic).unwrap();
        assert_eq!(eval.calls, 1);
        assert!(state.goals.is_empty());
    }
}

#[test]
fn failed_case_body_restores_unrelated_open_goals() {
    let selected = clean_parser::parse_name("selected").unwrap();
    let mut state = test_state();
    state.current_goal_mut().unwrap().tag = Some(selected.clone());
    let mut other = state.current_goal().unwrap().clone();
    other.meta_id = state.fresh_meta(Expr::prop());
    other.tag = Some(clean_parser::parse_name("other").unwrap());
    let other_id = other.meta_id;
    state.goals.push_back(other);
    let first_id = state.current_goal().unwrap().meta_id;
    let mut eval = StubEval {
        calls: 0,
        results: VecDeque::from([Err(TacticError::no_progress("assumption"))]),
        metas: MetaState::new(),
    };
    let tactic = SurfaceTactic::Case(Span::dummy(), selected, vec![], vec![]);
    assert!((compound_case().handler)(&mut eval, &mut state, &tactic).is_err());
    assert_eq!(eval.calls, 1);
    assert_eq!(state.goals.len(), 2);
    assert_eq!(state.goals[0].meta_id, first_id);
    assert_eq!(state.goals[1].meta_id, other_id);
    assert!(state.metas.get(other_id).unwrap().assignment.is_none());
}
