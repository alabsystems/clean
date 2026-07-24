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
        results: VecDeque::from([
            Err(TacticError::NoProgress {
                tactic: "assumption".into(),
            }),
            Ok(()),
        ]),
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

#[test]
fn test_compound_first_stops_on_fatal_error() {
    let mut eval = StubEval {
        calls: 0,
        results: VecDeque::from([Err(TacticError::TypeCheckFailed("fatal".into())), Ok(())]),
        metas: MetaState::new(),
    };
    let mut state = test_state();
    let handler = compound_first();

    let result = (handler.handler)(&mut eval, &mut state, &first_tactic_surface());

    assert!(
        matches!(result, Err(TacticError::TypeCheckFailed(ref msg)) if msg == "fatal"),
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
            Err(TacticError::NoProgress {
                tactic: "assumption".into(),
            }),
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
