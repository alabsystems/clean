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

use super::super::grind_split::{
    collect_eq_hypotheses, collect_ite_conditions, collect_or_hypotheses,
    condition_already_decided, split_candidate_conditions,
};
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

/// The first condition `collect_ite_conditions` finds — the single answer
/// `find_ite_condition` used to give, kept here because these four cases pin
/// WHICH argument of the spine is the condition (argument 1, not the result
/// type) and that reading is what the collector must preserve.
fn first_ite_condition(expr: &Expr) -> Option<Expr> {
    collect_ite_conditions(expr).into_iter().next()
}

#[test]
fn test_collect_ite_conditions_non_ite_yields_none() {
    let a = Expr::const_(Name::from_string("A"), vec![]);
    assert!(first_ite_condition(&a).is_none());
}

/// `@ite α c inst t e` / `@dite α c inst t e` — the real five-argument spine
/// (the condition is argument 1; argument 0 is the result type).
fn ite_like(head: &str, n_args: usize) -> (Expr, Expr) {
    let alpha = Expr::const_(Name::from_string("Alpha"), vec![]);
    let p = Expr::const_(Name::from_string("P"), vec![]);
    let inst = Expr::const_(Name::from_string("inst"), vec![]);
    let t = Expr::const_(Name::from_string("t"), vec![]);
    let e = Expr::const_(Name::from_string("e"), vec![]);
    let args = [alpha, p.clone(), inst, t, e];
    let mut expr = Expr::const_(Name::from_string(head), vec![Level::succ(Level::zero())]);
    for arg in args.into_iter().take(n_args) {
        expr = Expr::app(expr, arg);
    }
    (expr, p)
}

#[test]
fn test_collect_ite_conditions_detects_ite_condition() {
    let (ite_expr, p) = ite_like("ite", 5);
    let cond = first_ite_condition(&ite_expr).expect("should detect the ite condition");
    assert_eq!(cond, p, "the condition is argument 1, not the result type");
}

#[test]
fn test_collect_ite_conditions_detects_dite_condition() {
    let (dite_expr, p) = ite_like("dite", 5);
    let cond = first_ite_condition(&dite_expr).expect("should detect the dite condition");
    assert_eq!(cond, p, "the condition is argument 1, not the result type");
}

#[test]
fn test_collect_ite_conditions_partial_spine_yields_none() {
    // Four arguments is a partial application (Lean's isIte needs five).
    let (partial_ite, _) = ite_like("ite", 4);
    assert!(
        first_ite_condition(&partial_ite).is_none(),
        "ite with fewer than 5 args should not match"
    );
}

/// The re-split guard's exact contract: a condition this branch has ALREADY
/// decided is skipped and the NEXT one is chosen.
///
/// Compared by condition EXPRESSION, never by the `h_grind` name prefix — a
/// name test would also block a legitimately nested split on a distinct
/// condition. Both spellings of a decided condition are recognised:
/// `by_cases` pushes `h : c` in the positive branch and `h : c → False` in the
/// negative one (it builds the negation as a `Pi`, not as a `Not`
/// application), and a hand-written `¬c` is the third.
#[test]
fn test_split_candidate_skips_a_decided_condition_and_takes_the_next() {
    use crate::tactic::LocalDecl;
    use crate::unify::{MetaId, MetaState};
    use clean_kernel::FVarId;

    let p = Expr::const_(Name::from_string("P"), vec![]);
    let q = Expr::const_(Name::from_string("Q"), vec![]);
    let false_c = Expr::const_(Name::from_string("False"), vec![]);
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let inst = Expr::const_(Name::from_string("inst"), vec![]);
    let ite = |c: &Expr, t: Expr, e: Expr| {
        Expr::apps(
            Expr::const_(Name::from_string("ite"), vec![Level::succ(Level::zero())]),
            [nat.clone(), c.clone(), inst.clone(), t, e],
        )
    };
    // `if P then (if Q then a else b) else b` — two DISTINCT conditions.
    let target = ite(&p, ite(&q, a.clone(), b.clone()), b);
    assert_eq!(
        collect_ite_conditions(&target),
        vec![p.clone(), q.clone()],
        "both conditions are found, outermost first"
    );

    let metas = MetaState::new();
    // The splitter's own case hypothesis, which is the ONLY scope the guard
    // reads: an ordinary context hypothesis that happens to decide a condition
    // must not block the split (pinned e2e by
    // `tests_grind_preprocess::test_grind_splits_on_a_condition_an_ordinary_hypothesis_decides`).
    let case_hyps = [clean_parser::SurfaceName::generated_path("h_grind.0")];
    let goal_with = |hyp_ty: Expr| Goal {
        meta_id: MetaId(0),
        target: target.clone(),
        local_ctx: vec![LocalDecl {
            binder_info: Default::default(),
            fvar: FVarId::new(0),
            name: clean_parser::SurfaceName::generated_path("h_grind.0"),
            ty: hyp_ty,
            value: None,
        }],
        case_binders: Vec::new(),
        tag: None,
    };

    for decided in [
        p.clone(),
        Expr::pi(clean_kernel::BinderInfo::Default, p.clone(), false_c),
        Expr::app(Expr::const_(Name::from_string("Not"), vec![]), p.clone()),
    ] {
        let goal = goal_with(decided.clone());
        assert!(
            condition_already_decided(&goal, &metas, &case_hyps, &p),
            "`{decided:?}` decides P"
        );
        assert!(
            !condition_already_decided(&goal, &metas, &case_hyps, &q),
            "`{decided:?}` says nothing about Q"
        );
        let chosen = collect_ite_conditions(&goal.target)
            .into_iter()
            .find(|c| !condition_already_decided(&goal, &metas, &case_hyps, c));
        assert_eq!(
            chosen,
            Some(q.clone()),
            "the split must move on to the undecided condition"
        );
    }

    // An ORDINARY hypothesis with the same type decides NOTHING: the guard
    // reads only the names the splitter itself minted. Reading the whole
    // context refused `(hP : P) ⊢ (if P then a else b) = a`, which pinned Lean
    // closes — and nothing would have collapsed the `ite` instead, because
    // only `case_hyps` are handed to the preprocessing simp.
    let user_hyp_goal = Goal {
        meta_id: MetaId(0),
        target: target.clone(),
        local_ctx: vec![LocalDecl {
            binder_info: Default::default(),
            fvar: FVarId::new(0),
            name: clean_parser::SurfaceName::component("hP", false),
            ty: p.clone(),
            value: None,
        }],
        case_binders: Vec::new(),
        tag: None,
    };
    assert!(
        !condition_already_decided(&user_hyp_goal, &metas, &case_hyps, &p),
        "an ordinary hypothesis is not one of grind's own case splits"
    );
    assert_eq!(
        collect_ite_conditions(&user_hyp_goal.target)
            .into_iter()
            .find(|c| !condition_already_decided(&user_hyp_goal, &metas, &case_hyps, c)),
        Some(p.clone()),
        "the split still happens when only a user hypothesis decides it"
    );

    // With NOTHING decided the outermost condition is still chosen first, so
    // the guard changes which condition is picked only when it has to.
    let empty_goal = Goal {
        meta_id: MetaId(0),
        target: target.clone(),
        local_ctx: Vec::new(),
        case_binders: Vec::new(),
        tag: None,
    };
    let chosen = collect_ite_conditions(&empty_goal.target)
        .into_iter()
        .find(|c| !condition_already_decided(&empty_goal, &metas, &case_hyps, c));
    assert_eq!(chosen, Some(p), "unchanged when nothing is decided");
}

#[test]
fn test_collect_eq_hypotheses_empty() {
    use crate::unify::MetaState;

    let goal = Goal {
        meta_id: crate::unify::MetaId(0),
        target: Expr::const_(Name::from_string("A"), vec![]),
        local_ctx: vec![],
        tag: None,
        case_binders: Vec::new(),
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
                binder_info: Default::default(),
                fvar: FVarId::new(0),
                name: clean_parser::SurfaceName::generated_path("plain"),
                ty: prop_a,
                value: None,
            },
            LocalDecl {
                binder_info: Default::default(),
                fvar: FVarId::new(1),
                name: clean_parser::SurfaceName::generated_path("h_or_left"),
                ty: or_ab,
                value: None,
            },
            LocalDecl {
                binder_info: Default::default(),
                fvar: FVarId::new(2),
                name: clean_parser::SurfaceName::generated_path("h_or_right"),
                ty: or_bc,
                value: None,
            },
        ],
        tag: None,
        case_binders: Vec::new(),
    };

    assert_eq!(
        collect_or_hypotheses(&goal, &MetaState::new()),
        vec![FVarId::new(1), FVarId::new(2)]
    );
}

#[test]
fn test_grind_resource_limit_diagnostics_are_stable() {
    let config = GrindConfig::new().with_max_depth(2);

    assert!(!grind_max_depth_exceeded(2, &config));
    assert!(grind_max_depth_exceeded(3, &config));

    assert!(matches!(
        grind_no_progress(GRIND_MAX_DEPTH_EXHAUSTED),
        TacticError::NoProgress { tactic, .. } if tactic == "grind/max-depth"
    ));
    assert!(matches!(
        grind_no_progress(GRIND_SPLIT_LIMIT_EXHAUSTED),
        TacticError::NoProgress { tactic, .. } if tactic == "grind/split-limit"
    ));
}

/// The goal-free helper stays goal-free, and renders exactly the string it
/// always did.
///
/// `grind_no_progress` is what the three SWALLOWED sites use —
/// `try_propext_bridge`, `try_funext_propext_bridge` (both called as
/// `let _ = …`) and the automation engine inside `try_tactic_preserving_state`.
/// Their errors never reach a human, so formatting a goal there would be pure
/// cost. The escaping four in `grind_core` use `grind_no_progress_at`, whose
/// rendering `tests::grind_no_progress_goal` pins end to end.
#[test]
fn test_grind_swallowed_sites_carry_no_goal() {
    for tactic in [
        GRIND_NO_PROGRESS,
        GRIND_MAX_DEPTH_EXHAUSTED,
        GRIND_SPLIT_LIMIT_EXHAUSTED,
        GRIND_FUNEXT_NO_PROGRESS,
    ] {
        let err = grind_no_progress(tactic);
        assert!(
            matches!(&err, TacticError::NoProgress { goal: None, .. }),
            "{tactic}: the goal-free helper must not attach a goal, got {err:?}"
        );
        assert_eq!(
            err.to_string(),
            format!("{tactic}: no progress made"),
            "{tactic}: the goal-free rendering must not gain a suffix"
        );
    }
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
            binder_info: Default::default(),
            fvar: FVarId::new(0),
            name: clean_parser::SurfaceName::generated_path("h"),
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
                binder_info: Default::default(),
                fvar: FVarId::new(0),
                name: clean_parser::SurfaceName::generated_path("hp"),
                ty: p.clone(),
                value: None,
            },
            LocalDecl {
                binder_info: Default::default(),
                fvar: FVarId::new(1),
                name: clean_parser::SurfaceName::generated_path("h_trigger"),
                ty: Expr::arrow(p, q.clone()),
                value: None,
            },
        ],
    );

    let goal = state.current_goal().expect("goal").clone();
    assert_eq!(
        collect_ematch_trigger_candidates(&goal, state.metas()),
        vec![FVarId::new(1)]
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
fn test_grind_trigger_uses_hidden_local_identity() {
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
                binder_info: Default::default(),
                fvar: FVarId::new(0),
                name: clean_parser::SurfaceName::generated_path("hp"),
                ty: p.clone(),
                value: None,
            },
            LocalDecl {
                binder_info: Default::default(),
                fvar: FVarId::new(1),
                name: clean_parser::SurfaceName::generated_path("h_trigger"),
                ty: Expr::arrow(p, q.clone()),
                value: None,
            },
            LocalDecl {
                binder_info: Default::default(),
                fvar: FVarId::new(2),
                name: clean_parser::SurfaceName::generated_path("h_trigger"),
                ty: Expr::const_(Name::from_string("R"), vec![]),
                value: None,
            },
        ],
    );

    let goal = state.current_goal().expect("goal").clone();
    assert_eq!(
        collect_ematch_trigger_candidates(&goal, state.metas()),
        vec![FVarId::new(1)]
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

/// A hypothesis's `ite` condition read out from UNDER its binder carries a
/// loose bound variable, and such a term is not a term of the goal's context
/// at all — handing it to `by_cases` would put it through `infer_type`.
///
/// This is why `try_split_ite` filters the candidate list on
/// `has_loose_bvars` rather than trusting `by_cases` to refuse it. The shape
/// is `Function.Injective.dite`'s: a `dite` inside a `∀`-quantified
/// hypothesis. Measured with `CLEAN_GRIND_TRACE` on the e2e version
/// (`raw candidates depth=0 n=1`, `App(FVar(0), BVar(0))`), so the collector
/// really does produce it — the filter is not guarding an empty case.
#[test]
fn test_split_candidates_include_a_binder_bound_condition_that_is_filtered_out() {
    use crate::tactic::LocalDecl;
    use crate::unify::{MetaId, MetaState};
    use clean_kernel::FVarId;

    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let inst = Expr::const_(Name::from_string("inst"), vec![]);
    let r = Expr::const_(Name::from_string("R"), vec![]);
    let g = Expr::const_(Name::from_string("g"), vec![]);
    let k = Expr::const_(Name::from_string("k"), vec![]);
    // `∀ n : Nat, (if R n then g n else k n) = g n`
    let cond_under_binder = Expr::app(r, Expr::bvar(0));
    let body = Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [
            nat.clone(),
            Expr::apps(
                Expr::const_(Name::from_string("ite"), vec![Level::succ(Level::zero())]),
                [
                    nat.clone(),
                    cond_under_binder.clone(),
                    inst,
                    Expr::app(g.clone(), Expr::bvar(0)),
                    Expr::app(k, Expr::bvar(0)),
                ],
            ),
            Expr::app(g, Expr::bvar(0)),
        ],
    );
    let hyp_ty = Expr::pi(clean_kernel::BinderInfo::Default, nat, body);

    let goal = Goal {
        meta_id: MetaId(0),
        // No `ite` in the target, so every candidate comes from the context.
        target: Expr::const_(Name::from_string("Qq"), vec![]),
        local_ctx: vec![LocalDecl {
            binder_info: Default::default(),
            fvar: FVarId::new(0),
            name: clean_parser::SurfaceName::component("hbind", false),
            ty: hyp_ty,
            value: None,
        }],
        case_binders: Vec::new(),
        tag: None,
    };
    let metas = MetaState::new();
    let raw = split_candidate_conditions(&goal, &metas, &goal.target);
    assert_eq!(
        raw,
        vec![cond_under_binder.clone()],
        "the hypothesis scan does yield the binder-bound condition"
    );
    assert!(
        cond_under_binder.has_loose_bvars(),
        "and it is not a term of this context"
    );
    assert!(
        !raw.iter().any(|c| !c.has_loose_bvars()),
        "so the split has no candidate it can pose, and must say so rather \
         than hand a loose bound variable to by_cases"
    );
}
