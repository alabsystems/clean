// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::tactic::registry::{ElaboratedRefine, RefinePendingGoal, TacticEval};
use crate::tactic::ProofState;
use crate::unify::MetaState;

struct StubEval {
    elaborate_result: Expr,
    infer_type_result: Result<Expr, TacticError>,
    elaborate_refine_result: Result<ElaboratedRefine, TacticError>,
    injected_pending_goal_tys: Vec<Expr>,
    returned_pending_goal_count: usize,
    meta_state: MetaState,
    eval_case_tags: Vec<String>,
    eval_case_sizes: Vec<usize>,
}

impl TacticEval for StubEval {
    fn eval(&mut self, _ps: &mut ProofState, tac: &SurfaceTactic) -> Result<(), TacticError> {
        if let SurfaceTactic::Case(_, tag, _binders, tacs) = tac {
            self.eval_case_tags.push(tag.clone());
            self.eval_case_sizes.push(tacs.len());
        }
        Ok(())
    }

    fn eval_seq(
        &mut self,
        _ps: &mut ProofState,
        _tacs: &[SurfaceTactic],
    ) -> Result<(), TacticError> {
        unreachable!("tactic match lowering does not call eval_seq directly")
    }

    fn elaborate(&mut self, _expr: &SurfaceExpr) -> Result<Expr, TacticError> {
        Ok(self.elaborate_result.clone())
    }

    fn infer_type(&mut self, _expr: &Expr) -> Result<Expr, TacticError> {
        self.infer_type_result.clone()
    }

    fn elaborate_refine(
        &mut self,
        _ps: &ProofState,
        _expr: &SurfaceExpr,
    ) -> Result<ElaboratedRefine, TacticError> {
        let injected_meta_ids = self
            .injected_pending_goal_tys
            .iter()
            .map(|ty| self.meta_state.fresh(ty.clone()))
            .collect::<Vec<_>>();
        if !injected_meta_ids.is_empty() {
            let term = Expr::fvar(MetaState::to_fvar(injected_meta_ids[0]));
            let pending_goals = injected_meta_ids
                .iter()
                .take(self.returned_pending_goal_count)
                .map(|meta_id| RefinePendingGoal {
                    meta_id: *meta_id,
                    locals: vec![],
                    tag: None,
                })
                .collect();
            return Ok(ElaboratedRefine {
                term,
                pending_goals,
            });
        }
        self.elaborate_refine_result.clone()
    }

    fn metas(&self) -> &MetaState {
        &self.meta_state
    }
}

fn stub_eval() -> StubEval {
    StubEval {
        elaborate_result: Expr::prop(),
        infer_type_result: Ok(Expr::prop()),
        elaborate_refine_result: Err(TacticError::InvalidTarget {
            tactic: "match".into(),
            detail: "unexpected refine call".into(),
        }),
        injected_pending_goal_tys: Vec::new(),
        returned_pending_goal_count: 0,
        meta_state: MetaState::new(),
        eval_case_tags: Vec::new(),
        eval_case_sizes: Vec::new(),
    }
}

#[test]
fn test_planned_case_order_uses_ctor_first_occurrence_with_wildcard_fallback() {
    let mut env = Environment::new();
    env.init_nat().expect("Nat init should succeed");

    let order = planned_case_order(
        &env,
        &Expr::const_(Name::from_string("Nat"), vec![]),
        &[
            TacticMatchArm {
                span: Span::dummy(),
                pattern: SurfacePattern::Ctor("succ".into(), vec![SurfacePattern::Var("k".into())]),
                tactics: vec![],
            },
            TacticMatchArm {
                span: Span::dummy(),
                pattern: SurfacePattern::Wildcard,
                tactics: vec![],
            },
        ],
    );

    assert_eq!(
        order,
        vec![1, 0],
        "Nat constructor order is zero/succ, so wildcard fallback should run before the succ arm"
    );
}

#[test]
fn test_match_routes_case_tactics_in_ctor_order() {
    let mut env = Environment::new();
    env.init_nat().expect("Nat init should succeed");

    let mut meta_state = MetaState::new();
    let first_meta = meta_state.fresh(Expr::prop());
    let second_meta = meta_state.fresh(Expr::prop());
    let mut eval = StubEval {
        elaborate_result: Expr::app(
            Expr::const_(Name::from_string("Nat.succ"), vec![]),
            Expr::const_(Name::from_string("Nat.zero"), vec![]),
        ),
        infer_type_result: Ok(Expr::const_(Name::from_string("Nat"), vec![])),
        elaborate_refine_result: Ok(ElaboratedRefine {
            term: Expr::fvar(MetaState::to_fvar(first_meta)),
            pending_goals: vec![
                RefinePendingGoal {
                    meta_id: first_meta,
                    locals: vec![],
                    tag: None,
                },
                RefinePendingGoal {
                    meta_id: second_meta,
                    locals: vec![],
                    tag: None,
                },
            ],
        }),
        meta_state,
        ..stub_eval()
    };
    let mut state = ProofState::new(env, Expr::prop());
    let handler = compound_match();
    let tactic = SurfaceTactic::Match(
        Span::dummy(),
        vec![SurfaceExpr::Ident(Span::dummy(), "n".into())],
        vec![
            TacticMatchArm {
                span: Span::dummy(),
                pattern: SurfacePattern::Ctor("succ".into(), vec![SurfacePattern::Var("k".into())]),
                tactics: vec![
                    SurfaceTactic::Named {
                        span: Span::dummy(),
                        name: "succ_a".into(),
                        args: vec![],
                    },
                    SurfaceTactic::Named {
                        span: Span::dummy(),
                        name: "succ_b".into(),
                        args: vec![],
                    },
                ],
            },
            TacticMatchArm {
                span: Span::dummy(),
                pattern: SurfacePattern::Wildcard,
                tactics: vec![SurfaceTactic::Named {
                    span: Span::dummy(),
                    name: "wildcard".into(),
                    args: vec![],
                }],
            },
        ],
    );

    let result = (handler.handler)(&mut eval, &mut state, &tactic);

    assert!(result.is_ok(), "match lowering should succeed: {result:?}");
    assert_eq!(
        eval.eval_case_tags,
        vec!["match_1".to_string(), "match_2".to_string()],
        "compound_match should drive one synthetic case per pending goal"
    );
    assert_eq!(
        eval.eval_case_sizes,
        vec![1, 2],
        "wildcard fallback should be routed before the succ arm when constructor order rewrites the term match"
    );
}

#[test]
fn test_match_recovers_pending_goals_from_new_metas_when_refine_groups_arms() {
    let mut env = Environment::new();
    env.init_nat().expect("Nat init should succeed");

    let mut eval = StubEval {
        elaborate_result: Expr::const_(Name::from_string("Nat.zero"), vec![]),
        infer_type_result: Ok(Expr::const_(Name::from_string("Nat"), vec![])),
        injected_pending_goal_tys: vec![Expr::prop(), Expr::prop()],
        returned_pending_goal_count: 1,
        ..stub_eval()
    };
    let mut state = ProofState::new(env, Expr::prop());
    let handler = compound_match();
    let tactic = SurfaceTactic::Match(
        Span::dummy(),
        vec![SurfaceExpr::Ident(Span::dummy(), "n".into())],
        vec![
            TacticMatchArm {
                span: Span::dummy(),
                pattern: SurfacePattern::Ctor("succ".into(), vec![SurfacePattern::Var("k".into())]),
                tactics: vec![SurfaceTactic::Named {
                    span: Span::dummy(),
                    name: "succ".into(),
                    args: vec![],
                }],
            },
            TacticMatchArm {
                span: Span::dummy(),
                pattern: SurfacePattern::Wildcard,
                tactics: vec![SurfaceTactic::Named {
                    span: Span::dummy(),
                    name: "wildcard".into(),
                    args: vec![],
                }],
            },
        ],
    );

    let result = (handler.handler)(&mut eval, &mut state, &tactic);

    assert!(
        result.is_ok(),
        "match lowering should recover grouped refine holes from new metas: {result:?}"
    );
    assert_eq!(
        eval.eval_case_tags,
        vec!["match_1".to_string(), "match_2".to_string()],
        "recovered metas should still produce one synthetic case per source arm"
    );
    assert_eq!(
        eval.eval_case_sizes,
        vec![1, 1],
        "recovered pending goals should route tactics in constructor order"
    );
}

#[test]
fn test_match_no_arms_error() {
    let mut eval = stub_eval();
    let mut state = ProofState::new(Environment::new(), Expr::prop());
    let handler = compound_match();
    let tactic = SurfaceTactic::Match(
        Span::dummy(),
        vec![SurfaceExpr::Ident(Span::dummy(), "x".into())],
        vec![],
    );

    let result = (handler.handler)(&mut eval, &mut state, &tactic);
    assert!(
        result.is_err(),
        "match with no arms and open goals should fail"
    );
}
