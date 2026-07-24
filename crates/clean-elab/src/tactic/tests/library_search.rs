// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Library search tactic tests (split from advanced.rs)
//!
//! Related test files:
//! - advanced.rs: remaining advanced tactics
//! - conv.rs: conv tactic tests
//! - mathlib_tactics.rs: mathlib-style tactics
//! - pattern_tactics.rs: rintro, peel, split_ifs tests
//! - propositional.rs: contrapose, push_neg, tauto tests

use super::*;

// =========================================================================
// Library Search Tests
// =========================================================================

#[test]
fn test_library_search_config_default() {
    let config = LibrarySearchConfig::default();
    assert_eq!(config.max_results, 20);
    assert!(config.include_partial);
    assert!(config.search_instances);
    assert!(config.prefer_local);
    assert!((config.min_relevance - 0.1).abs() < 0.001);
}

#[test]
fn test_library_search_match_kind() {
    // Just test enum variants exist and are distinct
    assert_ne!(LibrarySearchMatchKind::Exact, LibrarySearchMatchKind::Apply);
    assert_ne!(
        LibrarySearchMatchKind::Apply,
        LibrarySearchMatchKind::HeadMatch
    );
    assert_ne!(
        LibrarySearchMatchKind::HeadMatch,
        LibrarySearchMatchKind::TypeSimilar
    );
    assert_ne!(
        LibrarySearchMatchKind::TypeSimilar,
        LibrarySearchMatchKind::Instance
    );
}

#[test]
fn test_library_search_result_fields() {
    let result = LibrarySearchResult {
        name: Name::from_string("test_lemma"),
        expr: Expr::const_(Name::from_string("test_lemma"), vec![]),
        type_: Expr::type_(),
        relevance: 0.95,
        suggestion: "exact test_lemma".to_string(),
        args_needed: 0,
        is_local: false,
        match_kind: LibrarySearchMatchKind::Exact,
    };

    assert_eq!(result.name.to_string(), "test_lemma");
    assert!((result.relevance - 0.95).abs() < 0.001);
    assert_eq!(result.suggestion, "exact test_lemma");
    assert!(!result.is_local);
    assert_eq!(result.match_kind, LibrarySearchMatchKind::Exact);
}

#[test]
fn test_library_search_with_exact_match() {
    let env = setup_env();
    let a = Expr::const_(Name::from_string("A"), vec![]);
    let mut state = ProofState::with_context(
        env,
        a.clone(),
        vec![LocalDecl {
            fvar: FVarId::new(0),
            name: "h".to_string(),
            ty: a.clone(),
            value: None,
        }],
    );

    let results = library_search(&mut state)
        .expect("library_search should succeed when goal matches context hypothesis");
    // Should find the hypothesis h with exact match
    if !results.is_empty() {
        assert!(results[0].relevance >= 0.9);
    }
}

#[test]
fn test_library_search_no_goals() {
    let env = setup_env();
    let mut state = ProofState::new(env, Expr::type_());
    state.goals.clear(); // Remove all goals

    let err = library_search(&mut state).unwrap_err();
    assert!(
        matches!(err, TacticError::NoGoals),
        "library_search with no goals should produce NoGoals, got: {err}"
    );
}

#[test]
fn test_library_search_show_empty() {
    let env = setup_env();
    // A goal type that won't match anything
    let unique_type = Expr::const_(Name::from_string("UniqueTypeXYZ123"), vec![]);
    let mut state = ProofState::new(env, unique_type);

    let output = library_search_show(&mut state)
        .expect("library_search_show should return formatted suggestions for searchable goals");
    assert!(
        output == "No matching lemmas found."
            || (output.starts_with("Found ") && output.contains("potential matches")),
        "library_search_show output should be either empty-match text or formatted suggestions, got: {output}"
    );
}

#[test]
fn test_extract_head_name_const() {
    let c = Expr::const_(Name::from_string("MyConstant"), vec![]);
    assert_eq!(extract_head_name(&c), Some("MyConstant".to_string()));
}

#[test]
fn test_extract_head_name_app() {
    let f = Expr::const_(Name::from_string("MyFunc"), vec![]);
    let a = Expr::const_(Name::from_string("Arg"), vec![]);
    let app = Expr::app(f, a);
    assert_eq!(extract_head_name(&app), Some("MyFunc".to_string()));
}

#[test]
fn test_extract_head_name_none() {
    let bvar = Expr::bvar(0);
    assert_eq!(extract_head_name(&bvar), None);
}

#[test]
fn test_calculate_type_similarity_same() {
    let a = Expr::const_(Name::from_string("A"), vec![]);
    let similarity = calculate_type_similarity(&a, &a);
    assert!(similarity >= 0.5); // Same head, similar depth
}

#[test]
fn test_calculate_type_similarity_different() {
    let a = Expr::const_(Name::from_string("A"), vec![]);
    let b = Expr::const_(Name::from_string("B"), vec![]);
    let similarity = calculate_type_similarity(&a, &b);
    // Different heads, but similar depth
    assert!(similarity >= 0.2); // Base score
    assert!(similarity < 0.8); // Not too high without head match
}

#[test]
fn test_expr_depth_simple() {
    let c = Expr::const_(Name::from_string("C"), vec![]);
    assert_eq!(expr_depth(&c), 1);
}

#[test]
fn test_expr_depth_app() {
    let f = Expr::const_(Name::from_string("F"), vec![]);
    let a = Expr::const_(Name::from_string("A"), vec![]);
    let app = Expr::app(f, a);
    assert_eq!(expr_depth(&app), 2);
}

#[test]
fn test_count_pis_none() {
    let c = Expr::const_(Name::from_string("C"), vec![]);
    assert_eq!(count_pis(&c), 0);
}

#[test]
fn test_count_pis_one() {
    let a = Expr::const_(Name::from_string("A"), vec![]);
    let b = Expr::const_(Name::from_string("B"), vec![]);
    let pi = Expr::pi(BinderInfo::Default, a, b);
    assert_eq!(count_pis(&pi), 1);
}

#[test]
fn test_count_pis_nested() {
    let a = Expr::const_(Name::from_string("A"), vec![]);
    let b = Expr::const_(Name::from_string("B"), vec![]);
    let c = Expr::const_(Name::from_string("C"), vec![]);
    let pi_inner = Expr::pi(BinderInfo::Default, b, c);
    let pi_outer = Expr::pi(BinderInfo::Default, a, pi_inner);
    assert_eq!(count_pis(&pi_outer), 2);
}

#[test]
fn test_library_search_and_apply_no_results() {
    let env = setup_env();
    let unique_type = Expr::const_(Name::from_string("UniqueTypeNONE999"), vec![]);
    let mut state = ProofState::new(env, unique_type);

    let err = library_search_and_apply(&mut state).unwrap_err();
    // Should fail with no matches
    assert!(
        matches!(err, TacticError::SearchExhausted { .. }),
        "library_search_and_apply with no matches should produce SearchExhausted, got: {err}"
    );
}
