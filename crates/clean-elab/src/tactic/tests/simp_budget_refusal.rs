// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `simp` refuses what it cannot finish — the in-traversal budget fixtures.
//!
//! `simp` has had a growth budget since the `import Init` blowup, but it was
//! consulted only BETWEEN top-level steps, so it could only ever see a runaway
//! that returned. The measured one does not: it lives inside a single
//! `simp_expr` traversal (`simp/budget.rs` carries the stack signature and the
//! `Mathlib/Logic/Basic.lean` `section ite` reproduction). These fixtures pin
//! the three properties the in-traversal budget has to have:
//!
//! 1. a traversal that would not terminate is REFUSED, not run;
//! 2. a refusal is an honest [`TacticError::BudgetExceeded`] with the goal left
//!    exactly as `simp` found it — never a partial rewrite, never a proof;
//! 3. the ordinary goals `simp` closes today are still closed, i.e. the budget
//!    is a guard against runaways and not a lower ceiling on real work.
//!
//! Reverting the budget alone flips fixture (1) from a fast refusal to a
//! non-terminating traversal, which is how it was verified.

use super::*;
use crate::tactic::simp::types::UnfoldDef;
use crate::tactic::{simp_with_budget, SimpBudget};

/// The runaway shape, reduced to its essentials: `f := g f f`.
///
/// `simp [f]` delta-unfolds every occurrence of `f` in the subterm it is at,
/// and THEN recurses into the children of what it just produced — children
/// that mention `f` again. Each level therefore re-unfolds, roughly doubling
/// the occurrence count, and the descent has no base case. Nothing here is
/// exotic: it is the mutually-referencing unfold interplay the original growth
/// budget was written for, expressed so it never returns to that budget's
/// between-steps check.
fn runaway_unfold_config() -> SimpConfig {
    let f = Name::from_string("ZZBudgetF");
    let g = Expr::const_(Name::from_string("ZZBudgetG"), vec![]);
    let f_const = Expr::const_(f.clone(), vec![]);
    // g f f
    let body = Expr::app(Expr::app(g, f_const.clone()), f_const);

    let mut config = SimpConfig::new();
    // Only simplify: this fixture is about the traversal, not about closing.
    config.only_simplify = true;
    config.unfold_defs.insert(
        f,
        UnfoldDef {
            level_params: vec![],
            value: body,
        },
    );
    config
}

fn runaway_state() -> ProofState {
    let mut env = setup_env();
    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    // g : A -> A -> A, f : A. Declaring both keeps the fixture on the ordinary
    // well-typed path (the matcher's projection peel and `whnf` see real
    // constants), so the refusal it measures is the traversal's, not an
    // unknown-constant accident.
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("ZZBudgetG"),
        level_params: vec![],
        type_: Expr::arrow(a_ty.clone(), Expr::arrow(a_ty.clone(), a_ty.clone())),
    })
    .expect("declaring ZZBudgetG must succeed");
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("ZZBudgetF"),
        level_params: vec![],
        type_: a_ty,
    })
    .expect("declaring ZZBudgetF must succeed");
    ProofState::new(env, Expr::const_(Name::from_string("ZZBudgetF"), vec![]))
}

#[test]
fn test_simp_refuses_a_nonterminating_unfold_traversal_instead_of_running_away() {
    let mut state = runaway_state();
    let target_before = state.goals()[0].target.clone();
    let goals_before = state.goals().len();

    let err = simp(&mut state, runaway_unfold_config())
        .expect_err("a traversal that cannot terminate must be refused, not answered");

    assert!(
        matches!(err, TacticError::BudgetExceeded { .. }),
        "refusal must be reported as BudgetExceeded, got: {err}"
    );
    assert_eq!(
        state.goals().len(),
        goals_before,
        "a refused simp must not add or drop goals"
    );
    assert_eq!(
        state.goals()[0].target,
        target_before,
        "a refused simp must leave the goal EXACTLY as it found it — a partial \
         rewrite is a term the tactic could not justify"
    );
}

#[test]
fn test_simp_budget_refusal_names_the_limit_it_hit() {
    let mut state = runaway_state();
    let err = simp(&mut state, runaway_unfold_config()).expect_err("must be refused");
    let msg = err.to_string();
    assert!(
        msg.contains("simp:"),
        "the refusal must say which tactic refused, got: {msg}"
    );
    assert!(
        msg.contains("the goal is left unchanged"),
        "the refusal must say the goal was left alone, got: {msg}"
    );
}

#[test]
fn test_simp_budget_size_trip_leaves_the_goal_untouched() {
    // A goal `(fun x : A => x) a = a` that simp normally rewrites (beta) and
    // closes. Under a budget whose size limit is 1 node, the very first
    // definitional rewrite is refused, so simp must decline the whole goal
    // rather than answer with a partial normal form.
    let mut env = setup_env();
    env.init_eq().expect("Eq must initialise");

    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let identity = Expr::lam(BinderInfo::Default, a_ty.clone(), Expr::bvar(0));
    let lhs = Expr::app(identity, a.clone());
    let eq = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                a_ty,
            ),
            lhs,
        ),
        a,
    );

    let mut state = ProofState::new(env, eq.clone());
    let goals_before = state.goals().len();

    let err = simp_with_budget(
        &mut state,
        SimpConfig::new(),
        SimpBudget::with_limits(u64::MAX, 1),
    )
    .expect_err("a size limit of 1 node refuses every rewrite");

    assert!(
        matches!(err, TacticError::BudgetExceeded { .. }),
        "expected BudgetExceeded, got: {err}"
    );
    assert!(
        err.to_string()
            .contains("while reducing a βζ redex, an expression reached the 1-node limit"),
        "the refusal must identify the operation and its materialized result: {err}"
    );
    assert_eq!(state.goals().len(), goals_before);
    assert_eq!(
        state.goals()[0].target,
        eq,
        "the target must be untouched after a refusal"
    );
}

#[test]
fn test_simp_estimates_zeta_growth_before_reducing_a_small_goal() {
    let mut env = Environment::with_prelude();
    let name = Name::from_string("NestedAnd");
    let and = Expr::const_(Name::from_string("And"), vec![]);
    let twice = Expr::app(Expr::app(and, Expr::bvar(0)), Expr::bvar(0));
    let mut value = Expr::const_(Name::from_string("True"), vec![]);
    // Thirteen shared lets occupy 92 expression nodes. Substituting their
    // values into both arguments of And yields 32765 nodes.
    for _ in 0..13 {
        value = Expr::let_named(
            Name::from_string("p"),
            Expr::prop(),
            value,
            twice.clone(),
            false,
        );
    }
    env.add_decl(Declaration::Definition {
        name: name.clone(),
        level_params: vec![],
        type_: Expr::prop(),
        value: value.clone(),
        is_reducible: false,
    })
    .expect("the shared proposition must kernel check");

    let target = Expr::const_(name.clone(), vec![]);
    let mut state = ProofState::new(env, target.clone());
    let mut config = SimpConfig::new();
    config.unfold_defs.insert(
        name,
        UnfoldDef {
            level_params: vec![],
            value,
        },
    );
    let err = simp_with_budget(&mut state, config, SimpBudget::with_limits(u64::MAX, 128))
        .expect_err("the unfolding fits but its estimated normal form reaches the guard");
    assert!(
        matches!(&err, TacticError::BudgetExceeded { detail, .. }
        if detail.contains("estimated βζ-normal form reached the 8192-node guard before reduction")),
        "the size estimate must have caused the refusal: {err}"
    );
    assert_eq!(state.goals().len(), 1);
    assert_eq!(state.goals()[0].target, target);
}

#[test]
fn test_simp_budget_fuel_trip_leaves_the_goal_untouched() {
    let mut env = setup_env();
    env.init_eq().expect("Eq must initialise");

    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let identity = Expr::lam(BinderInfo::Default, a_ty.clone(), Expr::bvar(0));
    let lhs = Expr::app(identity, a.clone());
    let eq = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                a_ty,
            ),
            lhs,
        ),
        a,
    );

    let mut state = ProofState::new(env, eq.clone());

    // Zero fuel: the traversal cannot even start.
    let err = simp_with_budget(
        &mut state,
        SimpConfig::new(),
        SimpBudget::with_limits(0, usize::MAX),
    )
    .expect_err("a traversal with no fuel must be refused");

    assert!(
        matches!(err, TacticError::BudgetExceeded { .. }),
        "expected BudgetExceeded, got: {err}"
    );
    assert_eq!(
        state.goals()[0].target,
        eq,
        "the target must be untouched after a refusal"
    );
}

#[test]
fn test_default_budget_still_closes_an_ordinary_simp_goal() {
    // The guard against "fixed the wedge by lowering the ceiling": the same
    // goal the size fixture above refuses under a 1-node limit must still be
    // rewritten and closed under the DEFAULT budget.
    let mut env = setup_env();
    env.init_eq().expect("Eq must initialise");

    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let identity = Expr::lam(BinderInfo::Default, a_ty.clone(), Expr::bvar(0));
    let lhs = Expr::app(identity, a.clone());
    let eq = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                a_ty,
            ),
            lhs,
        ),
        a,
    );

    let mut state = ProofState::new(env, eq);
    simp_default(&mut state).expect("the default budget must not refuse ordinary work");
    assert!(
        state.goals().is_empty(),
        "simp should still close this goal under the default budget"
    );
}
