// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for calc-mode tactic (#3082).

use clean_kernel::env::Declaration;
use clean_kernel::name::Name;
use clean_kernel::{Environment, Expr, Level};

use super::calc::{
    calc_block, calc_eq, calc_rel_from_name, CalcJustification, CalcRel, CalcState, CalcStep,
};
use super::calc_trans::lookup_trans_rule;
use super::core::{ProofState, TacticError};
use super::proof_term::exact;

/// Environment with Eq, type N, constants a/b/c/d : N, and equality proofs.
fn setup_calc_env() -> Environment {
    let mut env = Environment::new();
    env.init_eq().unwrap();

    let n = Expr::const_(Name::from_string("N"), vec![]);
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("N"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .unwrap();

    for name in ["a", "b", "c", "d"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: n.clone(),
        })
        .unwrap();
    }

    let a = c("a");
    let b = c("b");
    let cc = c("c");
    let d = c("d");

    for (hyp, lhs, rhs) in [
        ("h_ab", &a, &b),
        ("h_bc", &b, &cc),
        ("h_cd", &cc, &d),
        ("h_ac", &a, &cc),
    ] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(hyp),
            level_params: vec![],
            type_: make_eq_n(&n, lhs, rhs),
        })
        .unwrap();
    }

    env
}

fn make_eq_n(ty: &Expr, lhs: &Expr, rhs: &Expr) -> Expr {
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                ty.clone(),
            ),
            lhs.clone(),
        ),
        rhs.clone(),
    )
}

fn c(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

fn n_ty() -> Expr {
    c("N")
}

#[test]
fn test_calc_rel_from_name_all_relations() {
    // Eq variants
    assert_eq!(calc_rel_from_name("="), Some(CalcRel::Eq));
    assert_eq!(calc_rel_from_name("Eq"), Some(CalcRel::Eq));
    assert_eq!(calc_rel_from_name("eq"), Some(CalcRel::Eq));
    // Le variants
    assert_eq!(calc_rel_from_name("<="), Some(CalcRel::Le));
    assert_eq!(calc_rel_from_name("le"), Some(CalcRel::Le));
    assert_eq!(calc_rel_from_name("LE.le"), Some(CalcRel::Le));
    // Lt variants
    assert_eq!(calc_rel_from_name("<"), Some(CalcRel::Lt));
    assert_eq!(calc_rel_from_name("lt"), Some(CalcRel::Lt));
    assert_eq!(calc_rel_from_name("LT.lt"), Some(CalcRel::Lt));
    // Ge variants
    assert_eq!(calc_rel_from_name(">="), Some(CalcRel::Ge));
    assert_eq!(calc_rel_from_name("ge"), Some(CalcRel::Ge));
    assert_eq!(calc_rel_from_name("GE.ge"), Some(CalcRel::Ge));
    // Gt variants
    assert_eq!(calc_rel_from_name(">"), Some(CalcRel::Gt));
    assert_eq!(calc_rel_from_name("gt"), Some(CalcRel::Gt));
    assert_eq!(calc_rel_from_name("GT.gt"), Some(CalcRel::Gt));
    // Ne variants
    assert_eq!(calc_rel_from_name("!="), Some(CalcRel::Ne));
    assert_eq!(calc_rel_from_name("ne"), Some(CalcRel::Ne));
    assert_eq!(calc_rel_from_name("Ne"), Some(CalcRel::Ne));
    // Iff variants
    assert_eq!(calc_rel_from_name("iff"), Some(CalcRel::Iff));
    assert_eq!(calc_rel_from_name("Iff"), Some(CalcRel::Iff));
}

#[test]
fn test_calc_rel_from_name_unknown() {
    assert_eq!(calc_rel_from_name("mod"), None);
    assert_eq!(calc_rel_from_name(""), None);
    assert_eq!(calc_rel_from_name("divides"), None);
}

#[test]
fn test_trans_equality_chains() {
    // Eq + Eq = Eq
    assert_eq!(
        lookup_trans_rule(CalcRel::Eq, CalcRel::Eq)
            .unwrap()
            .result_rel,
        CalcRel::Eq
    );
    // Eq + Le = Le
    assert_eq!(
        lookup_trans_rule(CalcRel::Eq, CalcRel::Le)
            .unwrap()
            .result_rel,
        CalcRel::Le
    );
    // Le + Eq = Le
    assert_eq!(
        lookup_trans_rule(CalcRel::Le, CalcRel::Eq)
            .unwrap()
            .result_rel,
        CalcRel::Le
    );
    // Eq + Lt = Lt
    assert_eq!(
        lookup_trans_rule(CalcRel::Eq, CalcRel::Lt)
            .unwrap()
            .result_rel,
        CalcRel::Lt
    );
    // Lt + Eq = Lt
    assert_eq!(
        lookup_trans_rule(CalcRel::Lt, CalcRel::Eq)
            .unwrap()
            .result_rel,
        CalcRel::Lt
    );
    // Eq + Ge = Ge
    assert_eq!(
        lookup_trans_rule(CalcRel::Eq, CalcRel::Ge)
            .unwrap()
            .result_rel,
        CalcRel::Ge
    );
    // Ge + Eq = Ge
    assert_eq!(
        lookup_trans_rule(CalcRel::Ge, CalcRel::Eq)
            .unwrap()
            .result_rel,
        CalcRel::Ge
    );
    // Eq + Gt = Gt
    assert_eq!(
        lookup_trans_rule(CalcRel::Eq, CalcRel::Gt)
            .unwrap()
            .result_rel,
        CalcRel::Gt
    );
    // Gt + Eq = Gt
    assert_eq!(
        lookup_trans_rule(CalcRel::Gt, CalcRel::Eq)
            .unwrap()
            .result_rel,
        CalcRel::Gt
    );
    // Eq + Ne = Ne
    assert_eq!(
        lookup_trans_rule(CalcRel::Eq, CalcRel::Ne)
            .unwrap()
            .result_rel,
        CalcRel::Ne
    );
    // Ne + Eq = Ne
    assert_eq!(
        lookup_trans_rule(CalcRel::Ne, CalcRel::Eq)
            .unwrap()
            .result_rel,
        CalcRel::Ne
    );
}

#[test]
fn test_trans_order_chains() {
    // Le + Le = Le
    assert_eq!(
        lookup_trans_rule(CalcRel::Le, CalcRel::Le)
            .unwrap()
            .result_rel,
        CalcRel::Le
    );
    // Lt + Lt = Lt
    assert_eq!(
        lookup_trans_rule(CalcRel::Lt, CalcRel::Lt)
            .unwrap()
            .result_rel,
        CalcRel::Lt
    );
    // Lt + Le = Lt
    assert_eq!(
        lookup_trans_rule(CalcRel::Lt, CalcRel::Le)
            .unwrap()
            .result_rel,
        CalcRel::Lt
    );
    // Le + Lt = Lt
    assert_eq!(
        lookup_trans_rule(CalcRel::Le, CalcRel::Lt)
            .unwrap()
            .result_rel,
        CalcRel::Lt
    );
    // Ge + Ge = Ge
    assert_eq!(
        lookup_trans_rule(CalcRel::Ge, CalcRel::Ge)
            .unwrap()
            .result_rel,
        CalcRel::Ge
    );
    // Gt + Gt = Gt
    assert_eq!(
        lookup_trans_rule(CalcRel::Gt, CalcRel::Gt)
            .unwrap()
            .result_rel,
        CalcRel::Gt
    );
    // Ge + Gt = Gt
    assert_eq!(
        lookup_trans_rule(CalcRel::Ge, CalcRel::Gt)
            .unwrap()
            .result_rel,
        CalcRel::Gt
    );
    // Gt + Ge = Gt
    assert_eq!(
        lookup_trans_rule(CalcRel::Gt, CalcRel::Ge)
            .unwrap()
            .result_rel,
        CalcRel::Gt
    );
    // Iff + Iff = Iff
    assert_eq!(
        lookup_trans_rule(CalcRel::Iff, CalcRel::Iff)
            .unwrap()
            .result_rel,
        CalcRel::Iff
    );
}

#[test]
fn test_trans_incompatible_returns_none() {
    assert!(lookup_trans_rule(CalcRel::Lt, CalcRel::Gt).is_none());
    assert!(lookup_trans_rule(CalcRel::Iff, CalcRel::Le).is_none());
    assert!(lookup_trans_rule(CalcRel::Ne, CalcRel::Ne).is_none());
    assert!(lookup_trans_rule(CalcRel::Le, CalcRel::Ge).is_none());
}

#[test]
fn test_calc_state_new_empty() {
    let cs = CalcState::new(c("a"));
    assert!(cs.steps().is_empty());
    assert!(cs.current_rhs().is_none());
    assert!(cs.result_relation().is_none());
}

#[test]
fn test_calc_state_single_step() {
    let mut cs = CalcState::new(c("a"));
    cs.add_step(CalcStep {
        rel: CalcRel::Eq,
        rhs: c("b"),
        justification: CalcJustification::Refl,
    })
    .expect("first step should always succeed");

    assert_eq!(cs.steps().len(), 1);
    assert_eq!(cs.result_relation(), Some(CalcRel::Eq));
    assert!(cs.current_rhs().is_some());
}

#[test]
fn test_calc_state_mixed_relation_chains() {
    // Eq + Le = Le
    let mut cs = CalcState::new(c("a"));
    cs.add_step(CalcStep {
        rel: CalcRel::Eq,
        rhs: c("b"),
        justification: CalcJustification::Term(c("h1")),
    })
    .unwrap();
    cs.add_step(CalcStep {
        rel: CalcRel::Le,
        rhs: c("c"),
        justification: CalcJustification::Term(c("h2")),
    })
    .unwrap();
    assert_eq!(cs.result_relation(), Some(CalcRel::Le));

    // Le + Lt = Lt (fresh state)
    let mut cs2 = CalcState::new(c("a"));
    cs2.add_step(CalcStep {
        rel: CalcRel::Le,
        rhs: c("b"),
        justification: CalcJustification::Term(c("h1")),
    })
    .unwrap();
    cs2.add_step(CalcStep {
        rel: CalcRel::Lt,
        rhs: c("c"),
        justification: CalcJustification::Term(c("h2")),
    })
    .unwrap();
    assert_eq!(cs2.result_relation(), Some(CalcRel::Lt));
}

#[test]
fn test_calc_state_three_step_chain() {
    // a = b, b = c, c = d  =>  a = d
    let mut cs = CalcState::new(c("a"));
    for name in ["b", "c", "d"] {
        cs.add_step(CalcStep {
            rel: CalcRel::Eq,
            rhs: c(name),
            justification: CalcJustification::Term(c("proof")),
        })
        .unwrap();
    }
    assert_eq!(cs.steps().len(), 3);
    assert_eq!(cs.result_relation(), Some(CalcRel::Eq));

    // a = b, b <= c, c < d  =>  a < d
    let mut cs2 = CalcState::new(c("a"));
    cs2.add_step(CalcStep {
        rel: CalcRel::Eq,
        rhs: c("b"),
        justification: CalcJustification::Term(c("h1")),
    })
    .unwrap();
    cs2.add_step(CalcStep {
        rel: CalcRel::Le,
        rhs: c("c"),
        justification: CalcJustification::Term(c("h2")),
    })
    .unwrap();
    cs2.add_step(CalcStep {
        rel: CalcRel::Lt,
        rhs: c("d"),
        justification: CalcJustification::Term(c("h3")),
    })
    .unwrap();
    assert_eq!(cs2.steps().len(), 3);
    assert_eq!(cs2.result_relation(), Some(CalcRel::Lt));
}

#[test]
fn test_calc_state_incompatible_step_errors() {
    let mut cs = CalcState::new(c("a"));
    cs.add_step(CalcStep {
        rel: CalcRel::Iff,
        rhs: c("b"),
        justification: CalcJustification::Term(c("h1")),
    })
    .unwrap();

    // Iff + Le is not supported
    let result = cs.add_step(CalcStep {
        rel: CalcRel::Le,
        rhs: c("c"),
        justification: CalcJustification::Term(c("h2")),
    });
    assert!(result.is_err());
    // State unchanged after error
    assert_eq!(cs.steps().len(), 1);
    assert_eq!(cs.result_relation(), Some(CalcRel::Iff));
}

#[test]
fn test_calc_state_current_rhs_updates() {
    let mut cs = CalcState::new(c("a"));
    cs.add_step(CalcStep {
        rel: CalcRel::Eq,
        rhs: c("b"),
        justification: CalcJustification::Refl,
    })
    .unwrap();
    assert!(cs.current_rhs().is_some());

    cs.add_step(CalcStep {
        rel: CalcRel::Eq,
        rhs: c("c"),
        justification: CalcJustification::Refl,
    })
    .unwrap();
    assert!(cs.current_rhs().is_some());
    assert_eq!(cs.steps().len(), 2);
}

#[test]
fn test_calc_block_empty_steps_errors() {
    let env = setup_calc_env();
    let target = make_eq_n(&n_ty(), &c("a"), &c("b"));
    let mut state = ProofState::new(env, target);

    let result = calc_block(&mut state, c("a"), vec![]);
    assert!(matches!(result, Err(TacticError::MissingArgument { .. })));
}

#[test]
fn test_calc_block_single_step_closes_goal() {
    let env = setup_calc_env();
    let target = make_eq_n(&n_ty(), &c("a"), &c("b"));
    let mut state = ProofState::new(env, target);

    calc_block(
        &mut state,
        c("a"),
        vec![CalcStep {
            rel: CalcRel::Eq,
            rhs: c("b"),
            justification: CalcJustification::Term(c("h_ab")),
        }],
    )
    .expect("single step calc_block should succeed");
    assert!(state.is_complete());
}

#[test]
fn test_calc_block_no_goals_errors() {
    let env = setup_calc_env();
    let target = make_eq_n(&n_ty(), &c("a"), &c("b"));
    let mut state = ProofState::new(env, target);

    exact(&mut state, c("h_ab")).unwrap();
    let result = calc_block(
        &mut state,
        c("a"),
        vec![CalcStep {
            rel: CalcRel::Eq,
            rhs: c("b"),
            justification: CalcJustification::Term(c("h_ab")),
        }],
    );
    assert!(matches!(result, Err(TacticError::NoGoals)));
}

#[test]
fn test_calc_eq_creates_two_subgoals() {
    let env = setup_calc_env();
    let target = make_eq_n(&n_ty(), &c("a"), &c("c"));
    let mut state = ProofState::new(env, target);

    calc_eq(&mut state, c("b")).expect("calc_eq should succeed");
    assert_eq!(state.goals().len(), 2);
}

#[test]
fn test_calc_eq_subgoals_closeable() {
    let env = setup_calc_env();
    let target = make_eq_n(&n_ty(), &c("a"), &c("c"));
    let mut state = ProofState::new(env, target);

    calc_eq(&mut state, c("b")).unwrap();
    exact(&mut state, c("h_ab")).unwrap();
    exact(&mut state, c("h_bc")).unwrap();
    assert!(state.is_complete());
}

#[test]
fn test_calc_eq_no_goals_errors() {
    let env = setup_calc_env();
    let target = make_eq_n(&n_ty(), &c("a"), &c("c"));
    let mut state = ProofState::new(env, target);

    exact(&mut state, c("h_ac")).unwrap();
    let result = calc_eq(&mut state, c("b"));
    assert!(matches!(result, Err(TacticError::NoGoals)));
}

#[test]
fn test_calc_eq_non_equality_goal_errors() {
    let env = setup_calc_env();
    let mut state = ProofState::new(env, n_ty());

    let result = calc_eq(&mut state, c("b"));
    assert!(matches!(result, Err(TacticError::GoalMismatch(_))));
}

#[test]
fn test_calc_state_finish_single_step() {
    let env = setup_calc_env();
    let target = make_eq_n(&n_ty(), &c("a"), &c("b"));
    let mut state = ProofState::new(env, target);

    let mut cs = CalcState::new(c("a"));
    cs.add_step(CalcStep {
        rel: CalcRel::Eq,
        rhs: c("b"),
        justification: CalcJustification::Term(c("h_ab")),
    })
    .unwrap();

    cs.finish(&mut state).expect("finish should succeed");
    assert!(state.is_complete());
}

#[test]
fn test_calc_state_finish_empty_errors() {
    let env = setup_calc_env();
    let target = make_eq_n(&n_ty(), &c("a"), &c("b"));
    let mut state = ProofState::new(env, target);

    let cs = CalcState::new(c("a"));
    let result = cs.finish(&mut state);
    assert!(matches!(result, Err(TacticError::MissingArgument { .. })));
}

#[test]
fn test_justification_variants_success() {
    // Lemma justification
    let mut env = setup_calc_env();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("my_lemma"),
        level_params: vec![],
        type_: make_eq_n(&n_ty(), &c("a"), &c("b")),
    })
    .unwrap();
    let target = make_eq_n(&n_ty(), &c("a"), &c("b"));
    let mut state = ProofState::new(env.clone(), target);
    calc_block(
        &mut state,
        c("a"),
        vec![CalcStep {
            rel: CalcRel::Eq,
            rhs: c("b"),
            justification: CalcJustification::Lemma("my_lemma".into()),
        }],
    )
    .expect("lemma justification should work");
    assert!(state.is_complete());

    // Refl via explicit proof term (Eq.refl with correct universe)
    let refl_proof = Expr::app(
        Expr::app(
            Expr::const_(
                Name::from_string("Eq.refl"),
                vec![Level::succ(Level::zero())],
            ),
            n_ty(),
        ),
        c("a"),
    );
    let target2 = make_eq_n(&n_ty(), &c("a"), &c("a"));
    let mut state2 = ProofState::new(env, target2);
    calc_block(
        &mut state2,
        c("a"),
        vec![CalcStep {
            rel: CalcRel::Eq,
            rhs: c("a"),
            justification: CalcJustification::Term(refl_proof),
        }],
    )
    .expect("refl proof term should close a = a");
    assert!(state2.is_complete());
}

#[test]
fn test_justification_error_cases() {
    let env = setup_calc_env();

    // Hyp not found
    let target = make_eq_n(&n_ty(), &c("a"), &c("b"));
    let mut state = ProofState::new(env.clone(), target);
    let result = calc_block(
        &mut state,
        c("a"),
        vec![CalcStep {
            rel: CalcRel::Eq,
            rhs: c("b"),
            justification: CalcJustification::Hyp("nonexistent".into()),
        }],
    );
    assert!(matches!(result, Err(TacticError::HypothesisNotFound(_))));

    // Refl for strict inequality
    let target2 = make_eq_n(&n_ty(), &c("a"), &c("b"));
    let mut state2 = ProofState::new(env, target2);
    let result2 = calc_block(
        &mut state2,
        c("a"),
        vec![CalcStep {
            rel: CalcRel::Lt,
            rhs: c("b"),
            justification: CalcJustification::Refl,
        }],
    );
    assert!(matches!(result2, Err(TacticError::InvalidTarget { .. })));
}
