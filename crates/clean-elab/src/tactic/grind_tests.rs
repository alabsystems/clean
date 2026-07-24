// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the `grind` tactic.
//!
//! Integration tests that call `grind_with_config` with a `ProofState` are
//! omitted because the clean-elab test binary (~52MB debug) has a systemic
//! stack overflow issue — even trivial `ProofState` operations overflow with
//! 128MB thread stacks due to the binary size. Other unrelated tests (e.g.
//! `test_ring_nf_fails_on_non_equality`) also exhibit this behavior.
//!
//! The tests below exercise grind's internal logic (config builders, ite
//! condition detection, equality hypothesis collection) without constructing
//! a `ProofState`. Full integration testing requires a properly bootstrapped
//! environment loaded from .olean files.

use super::*;
use clean_kernel::level::Level;
use clean_kernel::name::Name;

#[test]
fn test_grind_config_defaults() {
    let config = GrindConfig::default();
    assert_eq!(config.max_depth, 8);
    assert_eq!(config.max_splits, 32);
    assert!(config.use_simp);
    assert!(config.use_cc);
    assert!(config.split_disjunctions);
    assert!(config.split_ite);
    assert!(config.use_tauto);
    assert!(config.use_automation);
    assert!(config.use_arithmetic_closers);
    assert_eq!(config.automation_timeout_ms, 100);
    assert_eq!(config.solve_by_elim_depth, 3);
}

#[test]
fn test_grind_config_builder() {
    let config = GrindConfig::new()
        .with_max_depth(4)
        .with_max_splits(16)
        .with_use_simp(false)
        .with_use_cc(false)
        .with_use_tauto(false)
        .with_use_automation(false)
        .with_use_arithmetic_closers(false)
        .with_solve_by_elim_depth(1)
        .with_automation_timeout_ms(50);

    assert_eq!(config.max_depth, 4);
    assert_eq!(config.max_splits, 16);
    assert!(!config.use_simp);
    assert!(!config.use_cc);
    assert!(!config.use_tauto);
    assert!(!config.use_automation);
    assert!(!config.use_arithmetic_closers);
    assert_eq!(config.solve_by_elim_depth, 1);
    assert_eq!(config.automation_timeout_ms, 50);
}

#[test]
fn test_find_ite_condition_none_for_non_ite() {
    let a = Expr::const_(Name::from_string("A"), vec![]);
    assert!(find_ite_condition(&a).is_none());
}

#[test]
fn test_find_ite_condition_detects_ite() {
    // Build @ite P inst t e
    let p = Expr::const_(Name::from_string("P"), vec![]);
    let inst = Expr::const_(Name::from_string("inst"), vec![]);
    let t = Expr::const_(Name::from_string("t"), vec![]);
    let e = Expr::const_(Name::from_string("e"), vec![]);

    let ite_expr = Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("ite"), vec![Level::succ(Level::zero())]),
                    p.clone(),
                ),
                inst,
            ),
            t,
        ),
        e,
    );

    let result = find_ite_condition(&ite_expr);
    assert!(result.is_some(), "should detect ite condition");
}

#[test]
fn test_find_ite_condition_detects_dite() {
    // Build @dite P inst t e — same structure as ite
    let p = Expr::const_(Name::from_string("P"), vec![]);
    let inst = Expr::const_(Name::from_string("inst"), vec![]);
    let t = Expr::const_(Name::from_string("t"), vec![]);
    let e = Expr::const_(Name::from_string("e"), vec![]);

    let dite_expr = Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("dite"), vec![Level::succ(Level::zero())]),
                    p.clone(),
                ),
                inst,
            ),
            t,
        ),
        e,
    );

    let result = find_ite_condition(&dite_expr);
    assert!(result.is_some(), "should detect dite condition");
    // The extracted condition should be P (first arg to dite)
    if let Some(cond) = result {
        assert_eq!(format!("{cond:?}"), format!("{p:?}"));
    }
}

#[test]
fn test_find_ite_condition_insufficient_args() {
    // ite with only 3 args (needs 4) should not match
    let p = Expr::const_(Name::from_string("P"), vec![]);
    let inst = Expr::const_(Name::from_string("inst"), vec![]);
    let t = Expr::const_(Name::from_string("t"), vec![]);

    let partial_ite = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("ite"), vec![Level::succ(Level::zero())]),
                p,
            ),
            inst,
        ),
        t,
    );

    assert!(
        find_ite_condition(&partial_ite).is_none(),
        "ite with <4 args should not match"
    );
}

#[test]
fn test_collect_eq_hypotheses_empty() {
    use crate::unify::MetaState;

    let goal = Goal {
        meta_id: crate::unify::MetaId(0),
        target: Expr::const_(Name::from_string("A"), vec![]),
        local_ctx: vec![],
        tag: None,
    };
    let metas = MetaState::new();
    let eqs = collect_eq_hypotheses(&goal, &metas);
    assert!(eqs.is_empty());
}

#[test]
fn test_collect_or_hypothesis_names_preserves_context_order() {
    use crate::tactic::LocalDecl;
    use crate::unify::{MetaId, MetaState};
    use clean_kernel::FVarId;

    let prop_a = Expr::const_(Name::from_string("A"), vec![]);
    let prop_b = Expr::const_(Name::from_string("B"), vec![]);
    let prop_c = Expr::const_(Name::from_string("C"), vec![]);
    let or_ab = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Or"), vec![]),
            prop_a.clone(),
        ),
        prop_b.clone(),
    );
    let or_bc = Expr::app(
        Expr::app(Expr::const_(Name::from_string("Or"), vec![]), prop_b),
        prop_c,
    );

    let goal = Goal {
        meta_id: MetaId(0),
        target: prop_a.clone(),
        local_ctx: vec![
            LocalDecl {
                fvar: FVarId::new(0),
                name: "plain".to_string(),
                ty: prop_a,
                value: None,
            },
            LocalDecl {
                fvar: FVarId::new(1),
                name: "h_or_left".to_string(),
                ty: or_ab,
                value: None,
            },
            LocalDecl {
                fvar: FVarId::new(2),
                name: "h_or_right".to_string(),
                ty: or_bc,
                value: None,
            },
        ],
        tag: None,
    };

    assert_eq!(
        collect_or_hypothesis_names(&goal, &MetaState::new()),
        vec!["h_or_left".to_string(), "h_or_right".to_string()]
    );
}

#[test]
fn test_grind_resource_limit_diagnostics_are_stable() {
    let config = GrindConfig::new().with_max_depth(2);

    assert!(!grind_max_depth_exceeded(2, &config));
    assert!(grind_max_depth_exceeded(3, &config));

    assert!(matches!(
        grind_no_progress(GRIND_MAX_DEPTH_EXHAUSTED),
        TacticError::NoProgress { tactic } if tactic == "grind/max-depth"
    ));
    assert!(matches!(
        grind_no_progress(GRIND_SPLIT_LIMIT_EXHAUSTED),
        TacticError::NoProgress { tactic } if tactic == "grind/split-limit"
    ));
}

#[test]
fn test_grind_arithmetic_closer_closes_nat_contradiction() {
    use crate::tactic::LocalDecl;
    use clean_kernel::env::Environment;
    use clean_kernel::FVarId;

    let false_ty = Expr::const_(Name::from_string("False"), vec![]);
    let h_ty = super::super::tc_app::nat_le_tc(Expr::nat_lit(5), Expr::nat_lit(3));
    let mut state = ProofState::with_context(
        Environment::with_prelude(),
        false_ty,
        vec![LocalDecl {
            fvar: FVarId::new(0),
            name: "h".to_string(),
            ty: h_ty,
            value: None,
        }],
    );

    assert!(
        try_arithmetic_closers(&mut state),
        "grind arithmetic closers should close a contradictory Nat inequality"
    );
    assert!(
        state.is_complete(),
        "grind arithmetic closer success must close the goal"
    );
}

#[test]
fn test_grind_triggered_solve_by_elim_instantiates_matching_implication() {
    use crate::tactic::LocalDecl;
    use clean_kernel::env::Environment;
    use clean_kernel::FVarId;

    let p = Expr::const_(Name::from_string("P"), vec![]);
    let q = Expr::const_(Name::from_string("Q"), vec![]);
    let mut state = ProofState::with_context(
        Environment::new(),
        q.clone(),
        vec![
            LocalDecl {
                fvar: FVarId::new(0),
                name: "hp".to_string(),
                ty: p.clone(),
                value: None,
            },
            LocalDecl {
                fvar: FVarId::new(1),
                name: "h_trigger".to_string(),
                ty: Expr::arrow(p, q.clone()),
                value: None,
            },
        ],
    );

    let goal = state.current_goal().expect("goal").clone();
    assert_eq!(
        collect_ematch_trigger_candidates(&goal, state.metas()),
        vec!["h_trigger".to_string()]
    );
    assert!(
        try_triggered_solve_by_elim(&mut state, 2),
        "grind trigger-guided instantiation should apply h_trigger and solve hp"
    );
    assert!(
        state.is_complete(),
        "trigger-guided instantiation should close the goal"
    );
}

#[test]
fn test_grind_config_non_exhaustive() {
    // Verify #[non_exhaustive] prevents external construction but
    // builder pattern works.
    let config = GrindConfig::new().with_max_depth(0).with_max_splits(0);
    assert_eq!(config.max_depth, 0);
    assert_eq!(config.max_splits, 0);
    // Other fields retain defaults
    assert!(config.use_simp);
    assert!(config.use_cc);
}
