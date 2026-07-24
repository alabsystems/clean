// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for pattern matching exhaustiveness and redundancy checking.
//!
//! Part of #3084 - Match expression compilation for native execution.

use super::*;

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn mk_ctor(name: &str, args: Vec<CheckPattern>) -> CheckPattern {
    CheckPattern::Constructor {
        name: name.to_string(),
        args,
    }
}

fn mk_wild() -> CheckPattern {
    CheckPattern::Wildcard
}

fn mk_lit_bool(b: bool) -> CheckPattern {
    CheckPattern::Literal(LitPattern::Bool(b))
}

fn mk_lit_nat(n: u64) -> CheckPattern {
    CheckPattern::Literal(LitPattern::Nat(n))
}

/// Build a checker with Bool type registered.
fn checker_with_bool() -> ExhaustivenessChecker {
    let mut checker = ExhaustivenessChecker::new();
    checker.register_type(TypeInfo {
        name: "Bool".to_string(),
        constructors: vec![
            ConstructorInfo {
                name: "true".to_string(),
                arity: 0,
                field_types: vec![],
            },
            ConstructorInfo {
                name: "false".to_string(),
                arity: 0,
                field_types: vec![],
            },
        ],
        is_recursive: false,
    });
    checker
}

/// Build a checker with Option type registered (wraps Bool).
fn checker_with_option_bool() -> ExhaustivenessChecker {
    let mut checker = checker_with_bool();
    checker.register_type(TypeInfo {
        name: "Option".to_string(),
        constructors: vec![
            ConstructorInfo {
                name: "None".to_string(),
                arity: 0,
                field_types: vec![],
            },
            ConstructorInfo {
                name: "Some".to_string(),
                arity: 1,
                field_types: vec!["Bool".to_string()],
            },
        ],
        is_recursive: false,
    });
    checker
}

/// Build a checker with List type (recursive: nil, cons(head, tail)).
fn checker_with_list() -> ExhaustivenessChecker {
    let mut checker = ExhaustivenessChecker::new();
    checker.register_type(TypeInfo {
        name: "List".to_string(),
        constructors: vec![
            ConstructorInfo {
                name: "nil".to_string(),
                arity: 0,
                field_types: vec![],
            },
            ConstructorInfo {
                name: "cons".to_string(),
                arity: 2,
                field_types: vec!["Elem".to_string(), "List".to_string()],
            },
        ],
        is_recursive: true,
    });
    checker
}

// ---------------------------------------------------------------------------
// Single wildcard — always exhaustive
// ---------------------------------------------------------------------------

#[test]
fn test_exhaustive_single_wildcard() {
    let checker = ExhaustivenessChecker::new();
    let patterns = vec![vec![mk_wild()]];
    let result = checker.check(&patterns, "AnyType");
    assert_eq!(result, ExhaustivenessResult::Exhaustive);
}

// ---------------------------------------------------------------------------
// Bool type: true + false
// ---------------------------------------------------------------------------

#[test]
fn test_exhaustive_bool_both_constructors() {
    let checker = checker_with_bool();
    let patterns = vec![
        vec![mk_ctor("true", vec![])],
        vec![mk_ctor("false", vec![])],
    ];
    let result = checker.check(&patterns, "Bool");
    assert_eq!(result, ExhaustivenessResult::Exhaustive);
}

// ---------------------------------------------------------------------------
// Missing constructor
// ---------------------------------------------------------------------------

#[test]
fn test_nonexhaustive_missing_constructor() {
    let checker = checker_with_bool();
    let patterns = vec![vec![mk_ctor("true", vec![])]];
    let result = checker.check(&patterns, "Bool");
    match result {
        ExhaustivenessResult::NonExhaustive { missing } => {
            assert_eq!(missing.len(), 1);
            assert_eq!(
                missing[0],
                CheckPattern::Constructor {
                    name: "false".to_string(),
                    args: vec![]
                }
            );
        }
        other => panic!("expected NonExhaustive, got {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// Redundant pattern
// ---------------------------------------------------------------------------

#[test]
fn test_redundant_pattern() {
    let checker = checker_with_bool();
    // wildcard covers everything, so the second row is redundant.
    let patterns = vec![vec![mk_wild()], vec![mk_ctor("true", vec![])]];
    let result = checker.check(&patterns, "Bool");
    match result {
        ExhaustivenessResult::Redundant { redundant_indices } => {
            assert_eq!(redundant_indices, vec![1]);
        }
        other => panic!("expected Redundant, got {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// Nested patterns: Option of Bool
// ---------------------------------------------------------------------------

#[test]
fn test_exhaustive_nested_option_bool() {
    let checker = checker_with_option_bool();
    // None, Some(true), Some(false)
    let patterns = vec![
        vec![mk_ctor("None", vec![])],
        vec![mk_ctor("Some", vec![mk_ctor("true", vec![])])],
        vec![mk_ctor("Some", vec![mk_ctor("false", vec![])])],
    ];
    let result = checker.check(&patterns, "Option");
    assert_eq!(result, ExhaustivenessResult::Exhaustive);
}

#[test]
fn test_nonexhaustive_nested_option_missing_some_false() {
    let checker = checker_with_option_bool();
    // None and Some(true), but missing Some(false)
    let patterns = vec![
        vec![mk_ctor("None", vec![])],
        vec![mk_ctor("Some", vec![mk_ctor("true", vec![])])],
    ];
    let result = checker.check(&patterns, "Option");
    match result {
        ExhaustivenessResult::NonExhaustive { missing } => {
            assert!(!missing.is_empty(), "should report missing pattern");
            // Should mention Some with false inside.
            let has_some_false = missing.iter().any(|p| {
                matches!(
                    p,
                    CheckPattern::Constructor { name, args }
                    if name == "Some" && args.iter().any(|a| matches!(
                        a,
                        CheckPattern::Constructor { name: inner, .. } if inner == "false"
                    ))
                )
            });
            assert!(
                has_some_false,
                "missing should include Some(false), got: {missing:?}"
            );
        }
        other => panic!("expected NonExhaustive, got {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// Literal patterns
// ---------------------------------------------------------------------------

#[test]
fn test_exhaustive_bool_literals() {
    let checker = ExhaustivenessChecker::new();
    let patterns = vec![vec![mk_lit_bool(true)], vec![mk_lit_bool(false)]];
    let result = checker.check(&patterns, "Bool");
    assert_eq!(result, ExhaustivenessResult::Exhaustive);
}

#[test]
fn test_nonexhaustive_nat_literal() {
    let checker = ExhaustivenessChecker::new();
    // Nat literals are never exhaustive without a wildcard (infinite domain).
    let patterns = vec![vec![mk_lit_nat(0)], vec![mk_lit_nat(1)]];
    let result = checker.check(&patterns, "Nat");
    match result {
        ExhaustivenessResult::NonExhaustive { .. } => {}
        other => panic!("expected NonExhaustive for nat literals, got {other:?}"),
    }
}

#[test]
fn test_exhaustive_nat_literal_with_wildcard() {
    let checker = ExhaustivenessChecker::new();
    let patterns = vec![vec![mk_lit_nat(0)], vec![mk_wild()]];
    let result = checker.check(&patterns, "Nat");
    assert_eq!(result, ExhaustivenessResult::Exhaustive);
}

// ---------------------------------------------------------------------------
// Or-patterns
// ---------------------------------------------------------------------------

#[test]
fn test_exhaustive_or_pattern() {
    let checker = checker_with_bool();
    // (true | false) covers everything.
    let patterns = vec![vec![CheckPattern::Or(vec![
        mk_ctor("true", vec![]),
        mk_ctor("false", vec![]),
    ])]];
    let result = checker.check(&patterns, "Bool");
    assert_eq!(result, ExhaustivenessResult::Exhaustive);
}

#[test]
fn test_nonexhaustive_or_pattern_incomplete() {
    let checker = checker_with_bool();
    // Only true in the or-pattern, missing false.
    let patterns = vec![vec![CheckPattern::Or(vec![mk_ctor("true", vec![])])]];
    let result = checker.check(&patterns, "Bool");
    match result {
        ExhaustivenessResult::NonExhaustive { .. } => {}
        other => panic!("expected NonExhaustive, got {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// Multiple missing constructors
// ---------------------------------------------------------------------------

#[test]
fn test_nonexhaustive_multiple_missing() {
    let mut checker = ExhaustivenessChecker::new();
    checker.register_type(TypeInfo {
        name: "Color".to_string(),
        constructors: vec![
            ConstructorInfo {
                name: "Red".to_string(),
                arity: 0,
                field_types: vec![],
            },
            ConstructorInfo {
                name: "Green".to_string(),
                arity: 0,
                field_types: vec![],
            },
            ConstructorInfo {
                name: "Blue".to_string(),
                arity: 0,
                field_types: vec![],
            },
        ],
        is_recursive: false,
    });
    let patterns = vec![vec![mk_ctor("Red", vec![])]];
    let result = checker.check(&patterns, "Color");
    match result {
        ExhaustivenessResult::NonExhaustive { missing } => {
            assert_eq!(missing.len(), 2);
            let names: Vec<&str> = missing
                .iter()
                .filter_map(|p| match p {
                    CheckPattern::Constructor { name, .. } => Some(name.as_str()),
                    _ => None,
                })
                .collect();
            assert!(names.contains(&"Green"), "missing should include Green");
            assert!(names.contains(&"Blue"), "missing should include Blue");
        }
        other => panic!("expected NonExhaustive, got {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// Empty pattern set
// ---------------------------------------------------------------------------

#[test]
fn test_nonexhaustive_empty_patterns() {
    let checker = checker_with_bool();
    let patterns: Vec<Vec<CheckPattern>> = vec![];
    let result = checker.check(&patterns, "Bool");
    match result {
        ExhaustivenessResult::NonExhaustive { missing } => {
            assert!(!missing.is_empty(), "empty patterns should report missing");
        }
        other => panic!("expected NonExhaustive, got {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// Recursive type: List
// ---------------------------------------------------------------------------

#[test]
fn test_exhaustive_list_nil_cons_wildcard() {
    let checker = checker_with_list();
    // nil + cons(_, _) is exhaustive.
    let patterns = vec![
        vec![mk_ctor("nil", vec![])],
        vec![mk_ctor("cons", vec![mk_wild(), mk_wild()])],
    ];
    let result = checker.check(&patterns, "List");
    assert_eq!(result, ExhaustivenessResult::Exhaustive);
}

#[test]
fn test_nonexhaustive_list_missing_nil() {
    let checker = checker_with_list();
    // Only cons — missing nil.
    let patterns = vec![vec![mk_ctor("cons", vec![mk_wild(), mk_wild()])]];
    let result = checker.check(&patterns, "List");
    match result {
        ExhaustivenessResult::NonExhaustive { missing } => {
            let has_nil = missing
                .iter()
                .any(|p| matches!(p, CheckPattern::Constructor { name, .. } if name == "nil"));
            assert!(has_nil, "missing should include nil, got: {missing:?}");
        }
        other => panic!("expected NonExhaustive, got {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// Mixed constructors and wildcards
// ---------------------------------------------------------------------------

#[test]
fn test_exhaustive_constructor_then_wildcard() {
    let checker = checker_with_option_bool();
    // None + wildcard covers everything.
    let patterns = vec![vec![mk_ctor("None", vec![])], vec![mk_wild()]];
    let result = checker.check(&patterns, "Option");
    assert_eq!(result, ExhaustivenessResult::Exhaustive);
}

#[test]
fn test_redundant_after_wildcard() {
    let checker = checker_with_option_bool();
    // Wildcard first, then None is redundant.
    let patterns = vec![vec![mk_wild()], vec![mk_ctor("None", vec![])]];
    let result = checker.check(&patterns, "Option");
    match result {
        ExhaustivenessResult::Redundant { redundant_indices } => {
            assert_eq!(redundant_indices, vec![1]);
        }
        other => panic!("expected Redundant, got {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// Usefulness predicate directly
// ---------------------------------------------------------------------------

#[test]
fn test_useful_empty_matrix_is_useful() {
    let checker = ExhaustivenessChecker::new();
    let matrix: Vec<Vec<CheckPattern>> = vec![];
    let vector = vec![mk_wild()];
    assert!(
        checker.useful(&matrix, &vector),
        "wildcard should be useful against empty matrix"
    );
}

#[test]
fn test_useful_wildcard_not_useful_after_wildcard() {
    let checker = ExhaustivenessChecker::new();
    let matrix = vec![vec![mk_wild()]];
    let vector = vec![mk_wild()];
    assert!(
        !checker.useful(&matrix, &vector),
        "wildcard should not be useful after existing wildcard"
    );
}

#[test]
fn test_useful_constructor_useful_against_different() {
    let checker = checker_with_bool();
    let matrix = vec![vec![mk_ctor("true", vec![])]];
    let vector = vec![mk_ctor("false", vec![])];
    assert!(
        checker.useful(&matrix, &vector),
        "false should be useful when only true is present"
    );
}

// ---------------------------------------------------------------------------
// Specialize and default_matrix unit tests
// ---------------------------------------------------------------------------

#[test]
fn test_specialize_basic() {
    let matrix = vec![
        vec![mk_ctor("Some", vec![mk_wild()]), mk_wild()],
        vec![mk_ctor("None", vec![]), mk_ctor("true", vec![])],
        vec![mk_wild(), mk_ctor("false", vec![])],
    ];
    let spec = ExhaustivenessChecker::specialize(&matrix, "Some", 1);
    // Row 0: Some(wild) -> [wild, wild]
    // Row 1: None -> skipped
    // Row 2: wild -> [wild, false]
    assert_eq!(spec.len(), 2);
    assert_eq!(spec[0], vec![mk_wild(), mk_wild()]);
    assert_eq!(spec[1], vec![mk_wild(), mk_ctor("false", vec![])]);
}

#[test]
fn test_default_matrix_basic() {
    let matrix = vec![
        vec![mk_ctor("Some", vec![mk_wild()]), mk_wild()],
        vec![mk_wild(), mk_ctor("true", vec![])],
    ];
    let def = ExhaustivenessChecker::default_matrix(&matrix);
    // Row 0: Some -> skipped
    // Row 1: wild -> [true]
    assert_eq!(def.len(), 1);
    assert_eq!(def[0], vec![mk_ctor("true", vec![])]);
}
