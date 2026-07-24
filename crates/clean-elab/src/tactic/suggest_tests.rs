// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for exact?/apply? suggestion tactics backed by library_search.
//!
//! Part of #3082.

use super::tests::*;
use super::*;

use clean_kernel::env::Declaration;
use clean_kernel::name::Name;

use super::suggest::{eval_apply_question, eval_exact_question, format_suggestions, Suggestion};

fn const_expr(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

fn add_axiom(env: &mut Environment, name: &str, type_: Expr) {
    env.add_decl(Declaration::Axiom {
        name: Name::from_string(name),
        level_params: vec![],
        type_,
    })
    .unwrap();
}

fn setup_suggest_env() -> Environment {
    let mut env = Environment::new();
    let prop = Expr::sort(Level::zero());
    add_axiom(&mut env, "A", prop.clone());
    add_axiom(&mut env, "B", prop.clone());
    add_axiom(&mut env, "C", prop);
    env
}

// =========================================================================
// exact? tests
// =========================================================================

#[test]
fn test_exact_question_finds_matching_lemma() {
    let mut env = setup_suggest_env();
    add_axiom(&mut env, "env_exact", const_expr("A"));

    let mut state = ProofState::new(env, const_expr("A"));
    let suggestions = eval_exact_question(&mut state).unwrap();

    assert!(!suggestions.is_empty(), "exact? should find env_exact");
    assert_eq!(suggestions[0].lemma_name.to_string(), "env_exact");
    assert_eq!(suggestions[0].tactic_text, "exact env_exact");
    assert!(suggestions[0].confidence > 0.9);
}

#[test]
fn test_exact_question_no_goals() {
    let env = setup_suggest_env();
    let mut state = ProofState::new(env, Expr::type_());
    state.goals.clear();

    let err = eval_exact_question(&mut state).unwrap_err();
    assert!(
        matches!(err, TacticError::NoGoals),
        "exact? with no goals should produce NoGoals"
    );
}

#[test]
fn test_exact_question_prefers_local_hypotheses() {
    let mut env = setup_suggest_env();
    add_axiom(&mut env, "env_exact", const_expr("A"));

    let mut state = ProofState::new(env, const_expr("A"));
    let local_fvar = state.fresh_fvar();
    state.current_goal_mut().unwrap().local_ctx.push(LocalDecl {
        fvar: local_fvar,
        name: "h_local".to_string(),
        ty: const_expr("A"),
        value: None,
    });

    let suggestions = eval_exact_question(&mut state).unwrap();
    assert!(
        suggestions.len() >= 2,
        "should find both local and env match"
    );
    // Local hypothesis should be first (higher confidence)
    assert_eq!(suggestions[0].lemma_name.to_string(), "h_local");
    assert!(suggestions[0].confidence > suggestions[1].confidence);
}

// =========================================================================
// apply? tests
// =========================================================================

#[test]
fn test_apply_question_finds_applicable_lemma() {
    let mut env = setup_suggest_env();
    // env_apply : B -> A
    add_axiom(
        &mut env,
        "env_apply",
        Expr::pi(BinderInfo::Default, const_expr("B"), const_expr("A")),
    );

    let mut state = ProofState::new(env, const_expr("A"));
    let suggestions = eval_apply_question(&mut state).unwrap();

    assert!(!suggestions.is_empty(), "apply? should find env_apply");
    assert_eq!(suggestions[0].lemma_name.to_string(), "env_apply");
    assert_eq!(suggestions[0].tactic_text, "apply env_apply");
}

#[test]
fn test_suggestions_ranked_by_specificity() {
    let mut env = setup_suggest_env();
    add_axiom(&mut env, "env_exact", const_expr("A"));
    add_axiom(
        &mut env,
        "env_apply",
        Expr::pi(BinderInfo::Default, const_expr("B"), const_expr("A")),
    );

    let mut state = ProofState::new(env, const_expr("A"));
    let suggestions = eval_apply_question(&mut state).unwrap();

    assert!(suggestions.len() >= 2, "should find both exact and apply");
    // Exact match should rank higher than apply match
    assert_eq!(suggestions[0].lemma_name.to_string(), "env_exact");
    assert_eq!(suggestions[1].lemma_name.to_string(), "env_apply");
    assert!(suggestions[0].confidence > suggestions[1].confidence);
}

#[test]
fn test_no_suggestions_for_unsolvable_goal() {
    let env = setup_suggest_env();
    // No lemma of type C exists in the environment
    let mut state = ProofState::new(env, const_expr("C"));
    let exact_sugg = eval_exact_question(&mut state).unwrap();
    let apply_sugg = eval_apply_question(&mut state).unwrap();

    assert!(exact_sugg.is_empty(), "no exact match for unsolvable goal");
    assert!(apply_sugg.is_empty(), "no apply match for unsolvable goal");
}

// =========================================================================
// format tests
// =========================================================================

#[test]
fn test_format_suggestions_empty() {
    assert_eq!(format_suggestions(&[]), "No suggestions found.");
}

#[test]
fn test_format_suggestions_output() {
    let suggestions = vec![
        Suggestion {
            tactic_text: "exact h".to_string(),
            lemma_name: Name::from_string("h"),
            confidence: 1.0,
        },
        Suggestion {
            tactic_text: "apply f".to_string(),
            lemma_name: Name::from_string("f"),
            confidence: 0.80,
        },
    ];

    let output = format_suggestions(&suggestions);
    assert!(output.contains("exact h"), "output should contain exact h");
    assert!(output.contains("apply f"), "output should contain apply f");
    assert!(
        output.contains("1.00"),
        "output should contain confidence 1.00"
    );
    assert!(
        output.contains("0.80"),
        "output should contain confidence 0.80"
    );
}
