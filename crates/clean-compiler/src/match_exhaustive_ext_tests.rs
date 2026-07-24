// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for extended match exhaustiveness checking.
//!
//! Part of #3084 - Match expression compilation for native execution.

use clean_kernel::Name;

use crate::ir::{CtorInfo, IRAlt, IRArg, IRBody, IRLiteral, IRType};
use crate::match_exhaustive_ext::*;

// ---------------------------------------------------------------------------
// Test helpers
// ---------------------------------------------------------------------------

fn mk_ctor_info(name: &str, tag: u32, field_types: Vec<IRType>) -> CtorInfo {
    let num_objects = field_types.iter().filter(|t| t.is_object()).count() as u32;
    let num_scalars = field_types.iter().filter(|t| t.is_scalar()).count() as u32;
    CtorInfo {
        name: Name::from_string(name),
        tag,
        num_scalars,
        num_objects,
        field_types,
    }
}

fn mk_alt(ctor: CtorInfo) -> IRAlt {
    IRAlt {
        ctor,
        body: Box::new(IRBody::Ret(IRArg::Erased)),
    }
}

fn bool_ctors() -> Vec<CtorInfo> {
    vec![
        mk_ctor_info("false", 0, vec![]),
        mk_ctor_info("true", 1, vec![]),
    ]
}

fn option_ctors() -> Vec<CtorInfo> {
    vec![
        mk_ctor_info("none", 0, vec![]),
        mk_ctor_info("some", 1, vec![IRType::Object]),
    ]
}

fn color_ctors() -> Vec<CtorInfo> {
    vec![
        mk_ctor_info("red", 0, vec![]),
        mk_ctor_info("green", 1, vec![]),
        mk_ctor_info("blue", 2, vec![]),
    ]
}

fn list_ctors() -> Vec<CtorInfo> {
    vec![
        mk_ctor_info("nil", 0, vec![]),
        mk_ctor_info("cons", 1, vec![IRType::Object, IRType::Object]),
    ]
}

fn pair_ctors() -> Vec<CtorInfo> {
    vec![mk_ctor_info("mk", 0, vec![IRType::Object, IRType::Object])]
}

// ---------------------------------------------------------------------------
// Exhaustiveness: complete matches
// ---------------------------------------------------------------------------

#[test]
fn test_exhaustive_bool_all_ctors() {
    let ctors = bool_ctors();
    let alts: Vec<IRAlt> = ctors.iter().map(|c| mk_alt(c.clone())).collect();
    let result = check_exhaustiveness_ext_default(&alts, &IRType::Object, &ctors);
    assert!(
        result.is_exhaustive,
        "Bool with both ctors should be exhaustive"
    );
    assert!(result.missing_patterns.is_empty());
}

#[test]
fn test_exhaustive_option_all_ctors() {
    let ctors = option_ctors();
    let alts: Vec<IRAlt> = ctors.iter().map(|c| mk_alt(c.clone())).collect();
    let result = check_exhaustiveness_ext_default(&alts, &IRType::Object, &ctors);
    assert!(
        result.is_exhaustive,
        "Option with both ctors should be exhaustive"
    );
    assert!(result.missing_patterns.is_empty());
}

#[test]
fn test_exhaustive_color_all_ctors() {
    let ctors = color_ctors();
    let alts: Vec<IRAlt> = ctors.iter().map(|c| mk_alt(c.clone())).collect();
    let result = check_exhaustiveness_ext_default(&alts, &IRType::Object, &ctors);
    assert!(
        result.is_exhaustive,
        "Color with all 3 ctors should be exhaustive"
    );
}

#[test]
fn test_exhaustive_list_all_ctors() {
    let ctors = list_ctors();
    let alts: Vec<IRAlt> = ctors.iter().map(|c| mk_alt(c.clone())).collect();
    let result = check_exhaustiveness_ext_default(&alts, &IRType::Object, &ctors);
    assert!(
        result.is_exhaustive,
        "List with nil+cons should be exhaustive"
    );
}

#[test]
fn test_exhaustive_single_ctor_type() {
    let ctors = pair_ctors();
    let alts = vec![mk_alt(ctors[0].clone())];
    let result = check_exhaustiveness_ext_default(&alts, &IRType::Object, &ctors);
    assert!(
        result.is_exhaustive,
        "Single-ctor type with its ctor should be exhaustive"
    );
}

// ---------------------------------------------------------------------------
// Exhaustiveness: missing constructors
// ---------------------------------------------------------------------------

#[test]
fn test_nonexhaustive_missing_false() {
    let ctors = bool_ctors();
    // Only true (tag 1).
    let alts = vec![mk_alt(ctors[1].clone())];
    let result = check_exhaustiveness_ext_default(&alts, &IRType::Object, &ctors);
    assert!(
        !result.is_exhaustive,
        "Missing false should be non-exhaustive"
    );
    assert_eq!(result.missing_patterns.len(), 1);
    match &result.missing_patterns[0] {
        PatternDesc::Ctor { name, .. } => {
            assert_eq!(name, &Name::from_string("false"));
        }
        other => panic!("expected Ctor pattern, got {other:?}"),
    }
}

#[test]
fn test_nonexhaustive_missing_true() {
    let ctors = bool_ctors();
    // Only false (tag 0).
    let alts = vec![mk_alt(ctors[0].clone())];
    let result = check_exhaustiveness_ext_default(&alts, &IRType::Object, &ctors);
    assert!(!result.is_exhaustive);
    assert_eq!(result.missing_patterns.len(), 1);
    match &result.missing_patterns[0] {
        PatternDesc::Ctor { name, .. } => {
            assert_eq!(name, &Name::from_string("true"));
        }
        other => panic!("expected Ctor pattern, got {other:?}"),
    }
}

#[test]
fn test_nonexhaustive_missing_multiple_colors() {
    let ctors = color_ctors();
    // Only red.
    let alts = vec![mk_alt(ctors[0].clone())];
    let result = check_exhaustiveness_ext_default(&alts, &IRType::Object, &ctors);
    assert!(!result.is_exhaustive);
    assert_eq!(result.missing_patterns.len(), 2);
    let names: Vec<&Name> = result
        .missing_patterns
        .iter()
        .filter_map(|p| match p {
            PatternDesc::Ctor { name, .. } => Some(name),
            _ => None,
        })
        .collect();
    assert!(names.contains(&&Name::from_string("green")));
    assert!(names.contains(&&Name::from_string("blue")));
}

#[test]
fn test_nonexhaustive_empty_alts() {
    let ctors = bool_ctors();
    let alts: Vec<IRAlt> = vec![];
    let result = check_exhaustiveness_ext_default(&alts, &IRType::Object, &ctors);
    assert!(!result.is_exhaustive, "Empty alts should be non-exhaustive");
    assert_eq!(result.missing_patterns.len(), 2);
}

#[test]
fn test_nonexhaustive_option_missing_some() {
    let ctors = option_ctors();
    // Only none.
    let alts = vec![mk_alt(ctors[0].clone())];
    let result = check_exhaustiveness_ext_default(&alts, &IRType::Object, &ctors);
    assert!(!result.is_exhaustive);
    assert_eq!(result.missing_patterns.len(), 1);
    match &result.missing_patterns[0] {
        PatternDesc::Ctor { name, fields } => {
            assert_eq!(name, &Name::from_string("some"));
            assert_eq!(fields.len(), 1);
            assert_eq!(fields[0], PatternDesc::Wildcard);
        }
        other => panic!("expected Ctor pattern, got {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// Redundant arms
// ---------------------------------------------------------------------------

#[test]
fn test_redundant_duplicate_ctor() {
    let ctors = bool_ctors();
    // false, true, false (duplicate).
    let alts = vec![
        mk_alt(ctors[0].clone()),
        mk_alt(ctors[1].clone()),
        mk_alt(ctors[0].clone()),
    ];
    let result = check_exhaustiveness_ext_default(&alts, &IRType::Object, &ctors);
    assert!(result.is_exhaustive);
    assert_eq!(result.redundant_arms, vec![2]);
}

#[test]
fn test_redundant_all_after_complete_set() {
    let ctors = bool_ctors();
    // false, true, true, false — last two are redundant.
    let alts = vec![
        mk_alt(ctors[0].clone()),
        mk_alt(ctors[1].clone()),
        mk_alt(ctors[1].clone()),
        mk_alt(ctors[0].clone()),
    ];
    let result = check_exhaustiveness_ext_default(&alts, &IRType::Object, &ctors);
    assert!(result.is_exhaustive);
    assert_eq!(result.redundant_arms, vec![2, 3]);
}

#[test]
fn test_no_redundancy_distinct_ctors() {
    let ctors = color_ctors();
    let alts: Vec<IRAlt> = ctors.iter().map(|c| mk_alt(c.clone())).collect();
    let result = check_exhaustiveness_ext_default(&alts, &IRType::Object, &ctors);
    assert!(result.redundant_arms.is_empty());
}

// ---------------------------------------------------------------------------
// find_missing_patterns direct
// ---------------------------------------------------------------------------

#[test]
fn test_find_missing_patterns_none_missing() {
    let ctors = bool_ctors();
    let alts: Vec<IRAlt> = ctors.iter().map(|c| mk_alt(c.clone())).collect();
    let missing = find_missing_patterns(&alts, &ctors);
    assert!(missing.is_empty());
}

#[test]
fn test_find_missing_patterns_some_missing() {
    let ctors = color_ctors();
    let alts = vec![mk_alt(ctors[0].clone()), mk_alt(ctors[2].clone())];
    let missing = find_missing_patterns(&alts, &ctors);
    assert_eq!(missing.len(), 1);
    match &missing[0] {
        PatternDesc::Ctor { name, .. } => assert_eq!(name, &Name::from_string("green")),
        other => panic!("expected Ctor pattern, got {other:?}"),
    }
}

#[test]
fn test_find_missing_patterns_empty_alts() {
    let ctors = bool_ctors();
    let missing = find_missing_patterns(&[], &ctors);
    assert_eq!(missing.len(), 2);
}

// ---------------------------------------------------------------------------
// find_redundant_arms direct
// ---------------------------------------------------------------------------

#[test]
fn test_find_redundant_arms_no_redundancy() {
    let ctors = bool_ctors();
    let alts: Vec<IRAlt> = ctors.iter().map(|c| mk_alt(c.clone())).collect();
    let redundant = find_redundant_arms(&alts);
    assert!(redundant.is_empty());
}

#[test]
fn test_find_redundant_arms_with_redundancy() {
    let ctors = bool_ctors();
    let alts = vec![mk_alt(ctors[0].clone()), mk_alt(ctors[0].clone())];
    let redundant = find_redundant_arms(&alts);
    assert_eq!(redundant, vec![1]);
}

// ---------------------------------------------------------------------------
// pattern_matrix_useful
// ---------------------------------------------------------------------------

#[test]
fn test_pattern_matrix_useful_empty_matrix() {
    let matrix: Vec<Vec<PatternDesc>> = vec![];
    let row = vec![PatternDesc::Wildcard];
    assert!(pattern_matrix_useful(&matrix, &row));
}

#[test]
fn test_pattern_matrix_useful_wildcard_after_wildcard() {
    let matrix = vec![vec![PatternDesc::Wildcard]];
    let row = vec![PatternDesc::Wildcard];
    assert!(!pattern_matrix_useful(&matrix, &row));
}

#[test]
fn test_pattern_matrix_useful_different_ctor() {
    let matrix = vec![vec![PatternDesc::Ctor {
        name: Name::from_string("A"),
        fields: vec![],
    }]];
    let row = vec![PatternDesc::Ctor {
        name: Name::from_string("B"),
        fields: vec![],
    }];
    assert!(pattern_matrix_useful(&matrix, &row));
}

#[test]
fn test_pattern_matrix_useful_same_ctor() {
    let matrix = vec![vec![PatternDesc::Ctor {
        name: Name::from_string("A"),
        fields: vec![],
    }]];
    let row = vec![PatternDesc::Ctor {
        name: Name::from_string("A"),
        fields: vec![],
    }];
    assert!(!pattern_matrix_useful(&matrix, &row));
}

// ---------------------------------------------------------------------------
// expand_or_patterns
// ---------------------------------------------------------------------------

#[test]
fn test_expand_or_patterns_wildcard() {
    let result = expand_or_patterns(&PatternDesc::Wildcard);
    assert_eq!(result, vec![PatternDesc::Wildcard]);
}

#[test]
fn test_expand_or_patterns_literal() {
    let lit = PatternDesc::Literal(IRLiteral::Bool(true));
    let result = expand_or_patterns(&lit);
    assert_eq!(result.len(), 1);
}

#[test]
fn test_expand_or_patterns_flat_or() {
    let pat = PatternDesc::Or(vec![
        PatternDesc::Ctor {
            name: Name::from_string("A"),
            fields: vec![],
        },
        PatternDesc::Ctor {
            name: Name::from_string("B"),
            fields: vec![],
        },
    ]);
    let result = expand_or_patterns(&pat);
    assert_eq!(result.len(), 2);
    match &result[0] {
        PatternDesc::Ctor { name, .. } => assert_eq!(name, &Name::from_string("A")),
        other => panic!("expected Ctor A, got {other:?}"),
    }
    match &result[1] {
        PatternDesc::Ctor { name, .. } => assert_eq!(name, &Name::from_string("B")),
        other => panic!("expected Ctor B, got {other:?}"),
    }
}

#[test]
fn test_expand_or_patterns_nested_or() {
    let pat = PatternDesc::Or(vec![
        PatternDesc::Or(vec![
            PatternDesc::Wildcard,
            PatternDesc::Literal(IRLiteral::Bool(false)),
        ]),
        PatternDesc::Ctor {
            name: Name::from_string("X"),
            fields: vec![],
        },
    ]);
    let result = expand_or_patterns(&pat);
    assert_eq!(result.len(), 3);
}

#[test]
fn test_expand_or_patterns_ctor_with_or_field() {
    let pat = PatternDesc::Ctor {
        name: Name::from_string("Pair"),
        fields: vec![
            PatternDesc::Or(vec![
                PatternDesc::Literal(IRLiteral::Bool(true)),
                PatternDesc::Literal(IRLiteral::Bool(false)),
            ]),
            PatternDesc::Wildcard,
        ],
    };
    let result = expand_or_patterns(&pat);
    // Cartesian product: 2 * 1 = 2.
    assert_eq!(result.len(), 2);
}

// ---------------------------------------------------------------------------
// Config options
// ---------------------------------------------------------------------------

#[test]
fn test_config_no_missing_report() {
    let ctors = bool_ctors();
    let alts = vec![mk_alt(ctors[0].clone())]; // Only false.
    let config = ExhaustivenessConfig {
        report_missing_patterns: false,
        ..ExhaustivenessConfig::default()
    };
    let result = check_exhaustiveness_ext(&alts, &IRType::Object, &ctors, &config);
    assert!(!result.is_exhaustive);
    // With report_missing_patterns=false, missing_patterns should still be
    // computed by the find_missing_patterns fallback but only if we request it.
    // Actually the flag controls whether we compute them:
    assert!(result.missing_patterns.is_empty());
}

#[test]
fn test_config_no_redundancy_check() {
    let ctors = bool_ctors();
    let alts = vec![
        mk_alt(ctors[0].clone()),
        mk_alt(ctors[1].clone()),
        mk_alt(ctors[0].clone()), // Redundant.
    ];
    let config = ExhaustivenessConfig {
        check_redundancy: false,
        ..ExhaustivenessConfig::default()
    };
    let result = check_exhaustiveness_ext(&alts, &IRType::Object, &ctors, &config);
    assert!(result.is_exhaustive);
    assert!(
        result.redundant_arms.is_empty(),
        "redundancy checking disabled"
    );
}

#[test]
fn test_config_depth_limit() {
    let ctors = bool_ctors();
    let alts: Vec<IRAlt> = ctors.iter().map(|c| mk_alt(c.clone())).collect();
    let config = ExhaustivenessConfig {
        max_pattern_depth: 1,
        ..ExhaustivenessConfig::default()
    };
    let result = check_exhaustiveness_ext(&alts, &IRType::Object, &ctors, &config);
    // Even with depth=1, a flat Bool match should work.
    assert!(result.is_exhaustive);
}

#[test]
fn test_default_config_values() {
    let config = ExhaustivenessConfig::default();
    assert_eq!(config.max_pattern_depth, 10);
    assert!(!config.check_guards);
    assert!(config.report_missing_patterns);
    assert!(config.check_redundancy);
}

// ---------------------------------------------------------------------------
// Edge cases
// ---------------------------------------------------------------------------

#[test]
fn test_single_alt_nonexhaustive_multi_ctor() {
    let ctors = color_ctors();
    let alts = vec![mk_alt(ctors[1].clone())]; // green only
    let result = check_exhaustiveness_ext_default(&alts, &IRType::Object, &ctors);
    assert!(!result.is_exhaustive);
    assert_eq!(result.missing_patterns.len(), 2);
}

#[test]
fn test_ctor_with_fields_missing_pattern_has_wildcards() {
    let ctors = list_ctors();
    let alts = vec![mk_alt(ctors[0].clone())]; // nil only
    let result = check_exhaustiveness_ext_default(&alts, &IRType::Object, &ctors);
    assert!(!result.is_exhaustive);
    assert_eq!(result.missing_patterns.len(), 1);
    match &result.missing_patterns[0] {
        PatternDesc::Ctor { name, fields } => {
            assert_eq!(name, &Name::from_string("cons"));
            assert_eq!(fields.len(), 2);
            assert!(fields.iter().all(|f| *f == PatternDesc::Wildcard));
        }
        other => panic!("expected Ctor pattern, got {other:?}"),
    }
}

#[test]
fn test_unreachable_equals_redundant_without_guards() {
    let ctors = bool_ctors();
    let alts = vec![
        mk_alt(ctors[0].clone()),
        mk_alt(ctors[1].clone()),
        mk_alt(ctors[0].clone()), // Redundant.
    ];
    let result = check_exhaustiveness_ext_default(&alts, &IRType::Object, &ctors);
    assert_eq!(result.redundant_arms, result.unreachable_arms);
}

#[test]
fn test_empty_ctor_info_nonexhaustive() {
    // No constructors registered means we cannot prove exhaustiveness.
    let alts = vec![mk_alt(mk_ctor_info("x", 0, vec![]))];
    let result = check_exhaustiveness_ext_default(&alts, &IRType::Object, &[]);
    // With empty ctor_info the algorithm has no complete sigma, so wildcard
    // falls through to default matrix which is empty => useful => non-exhaustive.
    assert!(!result.is_exhaustive);
}

#[test]
fn test_many_redundant_arms() {
    let ctors = bool_ctors();
    let alts = vec![
        mk_alt(ctors[0].clone()),
        mk_alt(ctors[1].clone()),
        mk_alt(ctors[0].clone()),
        mk_alt(ctors[1].clone()),
        mk_alt(ctors[0].clone()),
    ];
    let result = check_exhaustiveness_ext_default(&alts, &IRType::Object, &ctors);
    assert!(result.is_exhaustive);
    assert_eq!(result.redundant_arms, vec![2, 3, 4]);
}

#[test]
fn test_order_matters_for_redundancy() {
    let ctors = color_ctors();
    // red, green, red — red at index 2 is redundant.
    let alts = vec![
        mk_alt(ctors[0].clone()),
        mk_alt(ctors[1].clone()),
        mk_alt(ctors[0].clone()),
    ];
    let result = check_exhaustiveness_ext_default(&alts, &IRType::Object, &ctors);
    assert!(!result.is_exhaustive); // Missing blue.
    assert_eq!(result.redundant_arms, vec![2]);
}

#[test]
fn test_result_exhaustive_helper() {
    let result = ExhaustivenessResult {
        is_exhaustive: true,
        missing_patterns: Vec::new(),
        redundant_arms: Vec::new(),
        unreachable_arms: Vec::new(),
    };
    assert!(result.is_exhaustive);
    assert!(result.missing_patterns.is_empty());
    assert!(result.redundant_arms.is_empty());
    assert!(result.unreachable_arms.is_empty());
}

// ---------------------------------------------------------------------------
// PatternDesc equality
// ---------------------------------------------------------------------------

#[test]
fn test_pattern_desc_wildcard_eq() {
    assert_eq!(PatternDesc::Wildcard, PatternDesc::Wildcard);
}

#[test]
fn test_pattern_desc_ctor_eq() {
    let a = PatternDesc::Ctor {
        name: Name::from_string("X"),
        fields: vec![PatternDesc::Wildcard],
    };
    let b = PatternDesc::Ctor {
        name: Name::from_string("X"),
        fields: vec![PatternDesc::Wildcard],
    };
    assert_eq!(a, b);
}

#[test]
fn test_pattern_desc_ctor_neq_different_name() {
    let a = PatternDesc::Ctor {
        name: Name::from_string("X"),
        fields: vec![],
    };
    let b = PatternDesc::Ctor {
        name: Name::from_string("Y"),
        fields: vec![],
    };
    assert_ne!(a, b);
}
