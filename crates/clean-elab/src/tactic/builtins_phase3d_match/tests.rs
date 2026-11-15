// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::tactic::registry::{ElaboratedRefine, RefinePendingGoal, TacticEval};
use crate::tactic::ProofState;
use crate::unify::MetaState;
use clean_kernel::{Environment, Expr};
use clean_parser::SurfacePattern;

struct StubEval {
    elaborate_result: Expr,
    infer_type_result: Result<Expr, TacticError>,
    elaborate_refine_result: Result<ElaboratedRefine, TacticError>,
    injected_pending_goal_tys: Vec<Expr>,
    returned_pending_goal_count: usize,
    injected_arm_indices: Vec<usize>,
    injected_term_index: usize,
    meta_state: MetaState,
    eval_case_tags: Vec<SurfaceName>,
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
            let term = Expr::fvar(MetaState::to_fvar(
                injected_meta_ids[self.injected_term_index],
            ));
            let pending_goals = injected_meta_ids
                .iter()
                .take(self.returned_pending_goal_count)
                .enumerate()
                .map(|(index, meta_id)| RefinePendingGoal {
                    meta_id: *meta_id,
                    locals: vec![],
                    tag: Some(match_arm_tag(
                        self.injected_arm_indices
                            .get(index)
                            .copied()
                            .unwrap_or(index),
                    )),
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
        injected_arm_indices: vec![],
        injected_term_index: 0,
        meta_state: MetaState::new(),
        eval_case_tags: Vec::new(),
        eval_case_sizes: Vec::new(),
    }
}

#[test]
fn test_planned_case_order_uses_ctor_first_occurrence_with_wildcard_fallback() {
    let mut metas = MetaState::new();
    let pending = [1, 0].map(|arm| RefinePendingGoal {
        meta_id: metas.fresh(Expr::prop()),
        locals: vec![],
        tag: Some(match_arm_tag(arm)),
    });
    assert_eq!(
        pending_arm_order(&pending, 2).unwrap(),
        vec![1, 0],
        "actual wildcard/succ hole order controls dispatch, not source order or name guessing"
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
                    tag: Some(match_arm_tag(1)),
                },
                RefinePendingGoal {
                    meta_id: second_meta,
                    locals: vec![],
                    tag: Some(match_arm_tag(0)),
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
        None,
        vec![SurfaceExpr::Ident(
            Span::dummy(),
            SurfaceName::generated_path("n"),
        )],
        vec![
            TacticMatchArm {
                span: Span::dummy(),
                pattern: SurfacePattern::Ctor(
                    SurfaceName::generated_path("succ"),
                    vec![SurfacePattern::Var(SurfaceName::generated_path("k"))],
                ),
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
        vec![match_goal_tag(0), match_goal_tag(1)],
        "compound_match should drive one synthetic case per pending goal"
    );
    assert_eq!(
        eval.eval_case_sizes,
        vec![1, 2],
        "wildcard fallback should be routed before the succ arm when constructor order rewrites the term match"
    );
}

#[test]
fn test_match_routes_all_tagged_pending_goals_when_refine_groups_arms() {
    let mut env = Environment::new();
    env.init_nat().expect("Nat init should succeed");

    let mut eval = StubEval {
        elaborate_result: Expr::const_(Name::from_string("Nat.zero"), vec![]),
        infer_type_result: Ok(Expr::const_(Name::from_string("Nat"), vec![])),
        injected_pending_goal_tys: vec![Expr::prop(), Expr::prop()],
        returned_pending_goal_count: 2,
        injected_arm_indices: vec![1, 0],
        ..stub_eval()
    };
    let mut state = ProofState::new(env, Expr::prop());
    let handler = compound_match();
    let tactic = SurfaceTactic::Match(
        Span::dummy(),
        None,
        vec![SurfaceExpr::Ident(
            Span::dummy(),
            SurfaceName::generated_path("n"),
        )],
        vec![
            TacticMatchArm {
                span: Span::dummy(),
                pattern: SurfacePattern::Ctor(
                    SurfaceName::generated_path("succ"),
                    vec![SurfacePattern::Var(SurfaceName::generated_path("k"))],
                ),
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
        "match lowering should use the complete tagged refine census: {result:?}"
    );
    assert_eq!(
        eval.eval_case_tags,
        vec![match_goal_tag(0), match_goal_tag(1)],
        "each tagged pending meta must receive its own synthetic case"
    );
    assert_eq!(
        eval.eval_case_sizes,
        vec![1, 1],
        "actual pending tags should determine the source-arm dispatch"
    );
}

fn incomplete_refine_fixture(term_index: usize) -> (StubEval, ProofState, SurfaceTactic) {
    // This is a routing/bridge fixture, not source-match elaboration evidence.
    // Both fresh metas have type Prop, so either selected meta is a well-typed
    // term for the original Prop goal in the elaborator's own context.
    let eval = StubEval {
        injected_pending_goal_tys: vec![Expr::prop(), Expr::prop()],
        returned_pending_goal_count: 1,
        injected_arm_indices: vec![1],
        injected_term_index: term_index,
        ..stub_eval()
    };
    let state = ProofState::new(Environment::new(), Expr::prop());
    let arms = (0..2)
        .map(|index| TacticMatchArm {
            span: Span::dummy(),
            pattern: SurfacePattern::Wildcard,
            tactics: (0..=index)
                .map(|_| SurfaceTactic::Named {
                    span: Span::dummy(),
                    name: "routing_observation_only".into(),
                    args: vec![],
                })
                .collect(),
        })
        .collect();
    let tactic = SurfaceTactic::Match(
        Span::dummy(),
        None,
        vec![SurfaceExpr::ident("scrutinee")],
        arms,
    );
    (eval, state, tactic)
}

#[test]
fn match_incomplete_return_does_not_guess_an_unrelated_fresh_meta_as_an_arm() {
    // Retain the old two-injected/one-returned shape explicitly. Only meta0
    // occurs in the term; the unrelated meta1 must not become another case.
    let (mut eval, mut state, tactic) = incomplete_refine_fixture(0);
    let original = state.current_goal().unwrap().meta_id;
    (compound_match().handler)(&mut eval, &mut state, &tactic)
        .expect("route only the explicitly returned, reachable pending meta");
    assert_eq!(eval.eval_case_tags, vec![match_goal_tag(0)]);
    assert_eq!(eval.eval_case_sizes, vec![2]);
    assert_eq!(state.goals().len(), 1);
    assert_eq!(state.current_goal().unwrap().tag, Some(match_goal_tag(0)));
    assert_ne!(state.current_goal().unwrap().meta_id, original);
    assert!(state.metas().get(original).unwrap().assignment.is_some());
    assert!(
        !state.is_complete(),
        "the routing stub does not prove the pending goal"
    );
}

#[test]
fn match_incomplete_return_refuses_a_reachable_omitted_meta_before_case_dispatch() {
    // The same well-typed elaborator term now selects omitted meta1. The bridge
    // must refuse it instead of borrowing the same-numbered tactic-scope meta.
    let (mut eval, mut state, tactic) = incomplete_refine_fixture(1);
    let original = state.current_goal().unwrap().clone();
    let error = (compound_match().handler)(&mut eval, &mut state, &tactic)
        .expect_err("a reachable unsolved meta is absent from the returned census");
    assert!(
        matches!(error, TacticError::ElaborationFailed { ref detail }
        if detail.contains("retains unresolved elaborator metas"))
    );
    assert!(eval.eval_case_tags.is_empty());
    assert!(eval.eval_case_sizes.is_empty());
    assert_eq!(state.goals().len(), 1);
    let after = state.current_goal().unwrap();
    assert_eq!(after.meta_id, original.meta_id);
    assert_eq!(after.target, original.target);
    assert_eq!(after.tag, original.tag);
    assert_eq!(after.case_binders, original.case_binders);
    assert!(original.local_ctx.is_empty());
    assert!(after.local_ctx.is_empty());
    assert!(state
        .metas()
        .get(original.meta_id)
        .unwrap()
        .assignment
        .is_none());
    assert!(!state.is_complete());
}

#[test]
fn test_match_no_arms_error() {
    let mut eval = stub_eval();
    let mut state = ProofState::new(Environment::new(), Expr::prop());
    let handler = compound_match();
    let tactic = SurfaceTactic::Match(
        Span::dummy(),
        None,
        vec![SurfaceExpr::Ident(
            Span::dummy(),
            SurfaceName::generated_path("x"),
        )],
        vec![],
    );

    let result = (handler.handler)(&mut eval, &mut state, &tactic);
    assert!(
        result.is_err(),
        "match with no arms and open goals should fail"
    );
}

#[test]
fn pending_arm_mapping_allows_repeated_arms_but_not_duplicate_or_foreign_metas() {
    let mut metas = MetaState::new();
    let pending = [1, 1, 0].map(|arm| RefinePendingGoal {
        meta_id: metas.fresh(Expr::prop()),
        locals: vec![],
        tag: Some(match_arm_tag(arm)),
    });
    assert_eq!(pending_arm_order(&pending, 2).unwrap(), vec![1, 1, 0]);
    assert!(pending_arm_order(&[pending[0].clone(), pending[0].clone()], 2).is_err());
    for tag in [
        None,
        Some(match_arm_tag(2)),
        Some(SurfaceName::generated_path("match_1")),
        Some(match_goal_tag(0)),
    ] {
        let mut altered = pending[0].clone();
        altered.tag = tag;
        assert!(pending_arm_order(&[altered], 2).is_err());
    }
}

#[test]
fn source_arm_holes_have_exact_tags_independent_of_constructor_spelling() {
    let patterns = ["«A.B».«c.d»", "A.B.«c.d»"];
    let arms: Vec<_> = patterns
        .iter()
        .map(|name| TacticMatchArm {
            span: Span::dummy(),
            pattern: SurfacePattern::Ctor(clean_parser::parse_name(name).unwrap(), vec![]),
            tactics: vec![],
        })
        .collect();
    let term = build_tactic_match_expr(Span::dummy(), &[SurfaceExpr::ident("x")], &arms);
    let SurfaceExpr::Match(_, _, _, actual) = term else {
        panic!("expected match")
    };
    for (index, arm) in actual.iter().enumerate() {
        let SurfaceExpr::NamedHole(_, tag) = &arm.body else {
            panic!("anonymous hole loses arm identity")
        };
        assert!(tag.same_syntax(&match_arm_tag(index)));
    }
}

#[test]
fn match_with_no_discriminant_refuses_before_elaboration() {
    let mut eval = stub_eval();
    let mut state = ProofState::new(Environment::new(), Expr::prop());
    let tactic = SurfaceTactic::Match(
        Span::dummy(),
        None,
        vec![],
        vec![TacticMatchArm {
            span: Span::dummy(),
            pattern: SurfacePattern::Wildcard,
            tactics: vec![],
        }],
    );
    assert!((compound_match().handler)(&mut eval, &mut state, &tactic).is_err());
    assert_eq!(state.goals().len(), 1);
}

#[test]
fn test_match_term_of_the_wrong_type_is_refused_by_the_assembled_close() {
    // The tactic `match` closes its goal through `close_goal_assembled`,
    // which infers the eliminator term LENIENTLY (its open arm metas carry
    // tactic FVars) but must still compare that type with the goal. A term
    // of type `Prop` never closes a goal whose target is `Nat`: the close
    // refuses it before any arm is dispatched, and the goal stays open.
    let mut env = Environment::new();
    env.init_nat().expect("Nat init should succeed");
    let mut eval = StubEval {
        injected_pending_goal_tys: vec![Expr::prop()],
        returned_pending_goal_count: 1,
        injected_arm_indices: vec![0],
        ..stub_eval()
    };
    let mut state = ProofState::new(env, Expr::const_(Name::from_string("Nat"), vec![]));
    let original = state.current_goal().unwrap().meta_id;
    let tactic = SurfaceTactic::Match(
        Span::dummy(),
        None,
        vec![SurfaceExpr::ident("n")],
        vec![TacticMatchArm {
            span: Span::dummy(),
            pattern: SurfacePattern::Wildcard,
            tactics: vec![],
        }],
    );
    let error = (compound_match().handler)(&mut eval, &mut state, &tactic)
        .expect_err("a `Prop`-typed match term must not close a `Nat` goal");
    assert!(
        matches!(error, TacticError::TypeMismatch { .. }),
        "the refusal is the assembled close's type check: {error:?}"
    );
    assert!(eval.eval_case_tags.is_empty(), "no arm may be dispatched");
    assert!(state.metas().get(original).unwrap().assignment.is_none());
}
