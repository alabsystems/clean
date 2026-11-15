// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Residual forall arguments must remain real obligations of a rewrite proof.

use crate::tactic::{assumption, rewrite_ltr, rewrite_with_proof, rfl, LocalDecl, ProofState};
use clean_kernel::{BinderInfo, Environment, Expr, FVarId, Level, Name, TypeChecker};
use clean_parser::SurfaceName;
use serde_json::json;

fn conditional_rule_state() -> (ProofState, Expr, Expr) {
    let env = Environment::with_prelude();
    let p = Expr::fvar(FVarId::new(1));
    let a = Expr::fvar(FVarId::new(2));
    let b = Expr::fvar(FVarId::new(3));
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let target = Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [nat.clone(), a, b],
    );
    let types = [
        Expr::prop(),
        nat.clone(),
        nat,
        Expr::pi(BinderInfo::Default, p.clone(), target.clone()),
        p.clone(),
    ];
    let context = ["P", "a", "b", "rule", "h"]
        .into_iter()
        .zip(types)
        .enumerate()
        .map(|(index, (name, ty))| LocalDecl {
            binder_info: Default::default(),
            fvar: FVarId::new(index as u64 + 1),
            name: SurfaceName::component(name, false),
            ty,
            value: None,
        })
        .collect();
    (
        ProofState::with_elab_context(env, target.clone(), context),
        p,
        target,
    )
}

fn check_conditional_rule(use_proof_term: bool) {
    let (mut state, p, target) = conditional_rule_state();
    let original_goal = state.current_goal().expect("initial goal").clone();
    if use_proof_term {
        rewrite_with_proof(&mut state, Expr::fvar(FVarId::new(4)), false)
            .expect("rewrite by the actual local rule term");
    } else {
        rewrite_ltr(&mut state, &SurfaceName::component("rule", false))
            .expect("rewrite by the actual named local rule");
    }
    let goals: Vec<_> = state
        .goals()
        .iter()
        .map(|goal| {
            json!({
                "meta": format!("{:?}", goal.meta_id), "target": goal.target,
                "locals": goal.local_ctx.iter().map(|local| json!({
                    "id": local.fvar.as_u64(), "name": local.name.to_string(), "type": local.ty,
                })).collect::<Vec<_>>(),
            })
        })
        .collect();
    let metas: Vec<_> = state
        .metas()
        .iter()
        .map(|(id, meta)| {
            json!({
                "id": format!("{id:?}"), "type": meta.ty, "assignment": meta.assignment,
            })
        })
        .collect();
    eprintln!(
        "conditional-rewrite-state {}",
        json!({"proof_term_path": use_proof_term,
        "goals": goals, "metas": metas, "proof": state.instantiated_proof()})
    );
    assert_eq!(
        state.goals().len(),
        2,
        "the rewritten equality and unsolved P argument must both remain visible"
    );
    assert_eq!(state.goals()[1].target, p);
    rfl(&mut state).expect("the rewritten main equality closes by reflexivity");
    assert_eq!(state.current_goal().expect("condition remains").target, p);
    assumption(&mut state).expect("the actual h:P discharges the condition");
    assert!(state.goals().is_empty());
    let proof = state
        .closed_proof()
        .expect("all actual proof obligations resolved");
    assert!(!proof.has_expr_mvar_quick());
    assert!(!proof.has_level_mvar_quick());
    assert!(!proof.has_loose_bvars());
    let checker = TypeChecker::with_context(state.env(), state.build_local_ctx(&original_goal));
    checker
        .check_type(&proof, &target)
        .expect("the whole assembled proof fully checks");
    assert!(!checker.heartbeat_spent());
    eprintln!(
        "conditional-rewrite-checked {}",
        json!({"proof":proof,"target":target,"public_full_check":"PASS"})
    );
}

#[test]
fn named_conditional_rewrite_preserves_its_premise_obligation() {
    check_conditional_rule(false);
}

#[test]
fn proof_term_conditional_rewrite_preserves_its_premise_obligation() {
    check_conditional_rule(true);
}

fn check_closed_state(state: &ProofState, original: &crate::tactic::Goal) {
    assert!(state.goals().is_empty());
    let proof = state
        .closed_proof()
        .expect("all proof obligations resolved");
    assert!(!proof.has_expr_mvar_quick());
    assert!(!proof.has_level_mvar_quick());
    assert!(!proof.has_loose_bvars());
    let checker = TypeChecker::with_context(state.env(), state.build_local_ctx(original));
    checker
        .check_type(&proof, &original.target)
        .expect("full assembled proof checks");
    assert!(!checker.heartbeat_spent());
}

fn check_conditional_hypothesis(use_proof_term: bool) {
    let (base, p, eq_ab) = conditional_rule_state();
    let mut context = base
        .current_goal()
        .expect("initial context")
        .local_ctx
        .clone();
    context.push(LocalDecl {
        binder_info: Default::default(),
        fvar: FVarId::new(6),
        name: SurfaceName::component("hx", false),
        ty: eq_ab,
        value: None,
    });
    let eq_bb = Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [
            Expr::const_(Name::from_string("Nat"), vec![]),
            Expr::fvar(FVarId::new(3)),
            Expr::fvar(FVarId::new(3)),
        ],
    );
    let mut state = ProofState::with_elab_context(base.env().clone(), eq_bb, context);
    let original = state.current_goal().expect("initial goal").clone();
    if use_proof_term {
        crate::tactic::rewrite_at_with_proof(
            &mut state,
            Expr::fvar(FVarId::new(4)),
            &SurfaceName::component("hx", false),
            false,
        )
        .expect("conditional proof-term cast");
    } else {
        crate::tactic::rewrite_at(
            &mut state,
            &SurfaceName::component("rule", false),
            &SurfaceName::component("hx", false),
            false,
        )
        .expect("conditional named cast");
    }
    assert_eq!(state.goals().len(), 2);
    assert_eq!(state.goals()[1].target, p);
    let premise_context: Vec<_> = state.goals()[1]
        .local_ctx
        .iter()
        .map(|d| (d.fvar, d.ty.clone()))
        .collect();
    let original_context: Vec<_> = original
        .local_ctx
        .iter()
        .map(|d| (d.fvar, d.ty.clone()))
        .collect();
    assert_eq!(
        premise_context, original_context,
        "the premise retains its creation scope, before replacing hx"
    );
    assumption(&mut state).expect("rewritten hx closes main goal");
    assumption(&mut state).expect("h closes the actual rule premise");
    check_closed_state(&state, &original);
}

#[test]
fn named_conditional_hypothesis_rewrite_preserves_original_scope() {
    check_conditional_hypothesis(false);
}

#[test]
fn proof_term_conditional_hypothesis_rewrite_preserves_original_scope() {
    check_conditional_hypothesis(true);
}

#[test]
fn conditional_rewrite_places_real_premise_before_existing_sibling() {
    let (base, p, eq_ab) = conditional_rule_state();
    let target = Expr::apps(
        Expr::const_(Name::from_string("And"), vec![]),
        [eq_ab, p.clone()],
    );
    let mut state = ProofState::with_elab_context(
        base.env().clone(),
        target,
        base.current_goal().expect("context").local_ctx.clone(),
    );
    let original = state.current_goal().expect("root").clone();
    crate::tactic::constructor(&mut state).expect("two genuine conjunction children");
    assert_eq!(state.goals().len(), 2);
    let sibling = state.goals()[1].meta_id;
    rewrite_ltr(&mut state, &SurfaceName::component("rule", false)).expect("conditional rewrite");
    assert_eq!(state.goals().len(), 3);
    assert_eq!(state.goals()[1].target, p);
    assert_ne!(state.goals()[1].meta_id, sibling);
    assert_eq!(state.goals()[2].meta_id, sibling);
    rfl(&mut state).expect("rewritten equality");
    assumption(&mut state).expect("rewrite premise");
    assert_eq!(
        state.current_goal().expect("sibling remains").meta_id,
        sibling
    );
    assumption(&mut state).expect("original sibling");
    check_closed_state(&state, &original);
}

#[test]
fn multiple_conditional_arguments_retain_distinct_goal_ids() {
    let (base, p, target) = conditional_rule_state();
    let mut context = base.current_goal().expect("context").local_ctx.clone();
    context[3].ty = Expr::pi(BinderInfo::Default, p.clone(), context[3].ty.clone());
    let mut state = ProofState::with_elab_context(base.env().clone(), target, context);
    let original = state.current_goal().expect("root").clone();
    rewrite_with_proof(&mut state, Expr::fvar(FVarId::new(4)), false).expect("two-condition rule");
    assert_eq!(state.goals().len(), 3);
    assert_eq!(state.goals()[1].target, p);
    assert_eq!(state.goals()[2].target, p);
    assert_ne!(state.goals()[1].meta_id, state.goals()[2].meta_id);
    rfl(&mut state).expect("rewritten equality");
    assumption(&mut state).expect("first premise");
    assumption(&mut state).expect("second premise");
    check_closed_state(&state, &original);
}

fn inferred_argument_state(bare_pattern: bool) -> ProofState {
    let (base, _, _) = conditional_rule_state();
    let mut context = base.current_goal().expect("context").local_ctx.clone();
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let side = |x| {
        if bare_pattern {
            x
        } else {
            Expr::app(Expr::const_(Name::from_string("Nat.succ"), vec![]), x)
        }
    };
    let equation = |lhs, rhs| {
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
            [nat.clone(), lhs, rhs],
        )
    };
    let conclusion = equation(side(Expr::bvar(0)), side(Expr::fvar(FVarId::new(3))));
    context[3].ty = Expr::pi(BinderInfo::Default, nat.clone(), conclusion);
    let target = equation(
        side(Expr::fvar(FVarId::new(2))),
        side(Expr::fvar(FVarId::new(3))),
    );
    ProofState::with_elab_context(base.env().clone(), target, context)
}

#[test]
fn inferred_telescope_argument_does_not_become_a_spurious_goal() {
    // A fixed Nat.succ head makes n inferable from the actual rewritten subterm.
    // The original new control used a bare n: Lean explicitly rejects a
    // metavariable-headed rewrite pattern (Meta/Tactic/Rewrite.lean).
    let mut state = inferred_argument_state(false);
    let original = state.current_goal().expect("root").clone();
    rewrite_ltr(&mut state, &SurfaceName::component("rule", false)).expect("infer n from succ n");
    assert_eq!(state.goals().len(), 1);
    rfl(&mut state).expect("rewritten equality");
    check_closed_state(&state, &original);
}

#[test]
fn bare_argument_pattern_does_not_produce_an_unchecked_closed_proof() {
    let mut state = inferred_argument_state(true);
    assert!(rewrite_ltr(&mut state, &SurfaceName::component("rule", false)).is_err());
    assert!(state.closed_proof().is_none());
    assert_eq!(state.goals().len(), 1);
}

#[test]
fn unresolved_condition_prevents_closed_proof() {
    let (base, p, target) = conditional_rule_state();
    let mut context = base.current_goal().expect("context").local_ctx.clone();
    context.pop().expect("remove h:P");
    let mut state = ProofState::with_elab_context(base.env().clone(), target, context);
    rewrite_ltr(&mut state, &SurfaceName::component("rule", false)).expect("conditional rewrite");
    rfl(&mut state).expect("rewritten equality");
    assert_eq!(state.current_goal().expect("unsolved premise").target, p);
    assert!(assumption(&mut state).is_err());
    assert!(state.closed_proof().is_none());
    assert_eq!(state.goals().len(), 1);
}
