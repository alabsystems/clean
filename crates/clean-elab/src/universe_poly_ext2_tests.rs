// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for extended universe polymorphism analysis (phase 2).

use clean_kernel::{Level, Name};

use crate::universe_poly::{UniverseConstraint, UniverseParams};
use crate::universe_poly_ext2::*;

fn name(s: &str) -> Name {
    Name::from_string(s)
}
fn param(s: &str) -> Level {
    Level::param(name(s))
}
fn zero() -> Level {
    Level::zero()
}
fn succ(l: Level) -> Level {
    Level::succ(l)
}
fn one() -> Level {
    succ(zero())
}
fn two() -> Level {
    succ(one())
}
fn three() -> Level {
    succ(two())
}

fn make_params(names: &[&str], constraints: Vec<UniverseConstraint>) -> UniverseParams {
    UniverseParams {
        names: names.iter().map(|s| name(s)).collect(),
        constraints,
    }
}

// ── detect_conflicts ────────────────────────────────────────────────────

#[test]
fn test_detect_conflicts_no_conflicts() {
    let constraints = vec![
        UniverseConstraint::Eq(param("u"), one()),
        UniverseConstraint::Eq(param("v"), two()),
    ];
    let conflicts = detect_conflicts(&constraints);
    assert!(conflicts.is_empty());
}

#[test]
fn test_detect_conflicts_eq_eq_conflict() {
    let constraints = vec![
        UniverseConstraint::Eq(param("u"), one()),
        UniverseConstraint::Eq(param("u"), two()),
    ];
    let conflicts = detect_conflicts(&constraints);
    assert_eq!(conflicts.len(), 1);
    assert!(conflicts[0].explanation.contains("u"));
}

#[test]
fn test_detect_conflicts_eq_le_conflict() {
    // u = 2 but u <= 1 is impossible
    let constraints = vec![
        UniverseConstraint::Eq(param("u"), two()),
        UniverseConstraint::Le(param("u"), one()),
    ];
    let conflicts = detect_conflicts(&constraints);
    assert!(!conflicts.is_empty());
}

#[test]
fn test_detect_conflicts_eq_le_compatible() {
    // u = 1 and u <= 2 is fine
    let constraints = vec![
        UniverseConstraint::Eq(param("u"), one()),
        UniverseConstraint::Le(param("u"), two()),
    ];
    let conflicts = detect_conflicts(&constraints);
    assert!(conflicts.is_empty());
}

#[test]
fn test_detect_conflicts_le_lower_bound_conflict() {
    // u = 0 but 2 <= u means 2 <= 0 which is impossible
    let constraints = vec![
        UniverseConstraint::Eq(param("u"), zero()),
        UniverseConstraint::Le(two(), param("u")),
    ];
    let conflicts = detect_conflicts(&constraints);
    assert!(!conflicts.is_empty());
}

#[test]
fn test_detect_conflicts_display() {
    let conflict = ConstraintConflict {
        lhs: UniverseConstraint::Eq(param("u"), one()),
        rhs: UniverseConstraint::Eq(param("u"), two()),
        explanation: "u bound to both 1 and 2".to_owned(),
    };
    let s = format!("{conflict}");
    assert!(s.contains("conflict"));
}

// ── estimate_levels ─────────────────────────────────────────────────────

#[test]
fn test_estimate_levels_direct_eq() {
    let constraints = vec![UniverseConstraint::Eq(param("u"), one())];
    let estimates = estimate_levels(&constraints);
    assert_eq!(estimates.len(), 1);
    assert_eq!(estimates[0].param, name("u"));
    assert_eq!(estimates[0].level, one());
    assert_eq!(estimates[0].source, EstimateSource::DirectEquality);
}

#[test]
fn test_estimate_levels_lower_bound() {
    let constraints = vec![
        UniverseConstraint::Le(one(), param("u")),
        UniverseConstraint::Le(two(), param("u")),
    ];
    let estimates = estimate_levels(&constraints);
    assert_eq!(estimates.len(), 1);
    assert_eq!(estimates[0].param, name("u"));
    assert_eq!(estimates[0].level, two());
    assert_eq!(estimates[0].source, EstimateSource::LowerBound);
}

#[test]
fn test_estimate_levels_default() {
    let constraints = vec![UniverseConstraint::Eq(param("u"), param("v"))];
    let estimates = estimate_levels(&constraints);
    // Both u and v are non-ground, so they get Default
    assert!(estimates
        .iter()
        .all(|e| e.source == EstimateSource::Default));
}

#[test]
fn test_estimate_levels_empty() {
    let estimates = estimate_levels(&[]);
    assert!(estimates.is_empty());
}

#[test]
fn test_estimate_levels_mixed() {
    let constraints = vec![
        UniverseConstraint::Eq(param("u"), one()),
        UniverseConstraint::Le(zero(), param("v")),
    ];
    let estimates = estimate_levels(&constraints);
    assert_eq!(estimates.len(), 2);
    let u_est = estimates.iter().find(|e| e.param == name("u")).unwrap();
    assert_eq!(u_est.source, EstimateSource::DirectEquality);
    let v_est = estimates.iter().find(|e| e.param == name("v")).unwrap();
    assert_eq!(v_est.source, EstimateSource::LowerBound);
}

// ── compute_stats ───────────────────────────────────────────────────────

#[test]
fn test_stats_empty() {
    let params = make_params(&[], vec![]);
    let stats = compute_stats(&params);
    assert_eq!(stats.param_count, 0);
    assert_eq!(stats.eq_count, 0);
    assert_eq!(stats.le_count, 0);
    assert_eq!(stats.max_ground_level, 0);
    assert_eq!(stats.polymorphism_degree, 0);
}

#[test]
fn test_stats_basic() {
    let params = make_params(
        &["u", "v"],
        vec![
            UniverseConstraint::Eq(param("u"), two()),
            UniverseConstraint::Le(param("v"), three()),
        ],
    );
    let stats = compute_stats(&params);
    assert_eq!(stats.param_count, 2);
    assert_eq!(stats.eq_count, 1);
    assert_eq!(stats.le_count, 1);
    assert_eq!(stats.max_ground_level, 3);
}

#[test]
fn test_stats_polymorphism_degree() {
    let params = make_params(
        &["u", "v"],
        vec![
            UniverseConstraint::Eq(param("u"), one()),
            // v is free (only in Le, not ground-bound by Eq)
            UniverseConstraint::Le(param("v"), param("u")),
        ],
    );
    let stats = compute_stats(&params);
    assert_eq!(stats.polymorphism_degree, 1); // v is still poly
}

#[test]
fn test_stats_fully_monomorphic() {
    let params = make_params(&["u"], vec![UniverseConstraint::Eq(param("u"), zero())]);
    let stats = compute_stats(&params);
    assert_eq!(stats.polymorphism_degree, 0);
}

#[test]
fn test_stats_display() {
    let params = make_params(&["u"], vec![UniverseConstraint::Eq(param("u"), one())]);
    let stats = compute_stats(&params);
    let s = format!("{stats}");
    assert!(s.contains("params=1"));
    assert!(s.contains("eq=1"));
}

// ── suggest_annotations ─────────────────────────────────────────────────

#[test]
fn test_suggest_annotations_no_suggestions_when_bound() {
    let params = make_params(&["u"], vec![UniverseConstraint::Eq(param("u"), one())]);
    let suggestions = suggest_annotations(&params);
    assert!(suggestions.is_empty());
}

#[test]
fn test_suggest_annotations_from_lower_bound() {
    let params = make_params(&["u"], vec![UniverseConstraint::Le(one(), param("u"))]);
    let suggestions = suggest_annotations(&params);
    assert_eq!(suggestions.len(), 1);
    assert_eq!(suggestions[0].param, name("u"));
    assert_eq!(suggestions[0].suggested_level, one());
    assert!(suggestions[0].reason.contains("lower bound"));
}

#[test]
fn test_suggest_annotations_default_zero() {
    let params = make_params(&["u"], vec![UniverseConstraint::Eq(param("u"), param("v"))]);
    let suggestions = suggest_annotations(&params);
    assert!(suggestions.iter().all(|s| s.suggested_level == zero()));
}

// ── analyze_monomorphization ────────────────────────────────────────────

#[test]
fn test_mono_fully_monomorphizable() {
    let params = make_params(
        &["u", "v"],
        vec![
            UniverseConstraint::Eq(param("u"), one()),
            UniverseConstraint::Eq(param("v"), two()),
        ],
    );
    let result = analyze_monomorphization(&params);
    assert!(result.can_monomorphize);
    assert!(result.remaining_poly.is_empty());
    assert_eq!(result.assignments.get("u"), Some(&one()));
    assert_eq!(result.assignments.get("v"), Some(&two()));
}

#[test]
fn test_mono_not_monomorphizable() {
    let params = make_params(&["u"], vec![UniverseConstraint::Le(zero(), param("u"))]);
    let result = analyze_monomorphization(&params);
    assert!(!result.can_monomorphize);
    assert_eq!(result.remaining_poly, vec![name("u")]);
}

#[test]
fn test_mono_partial() {
    let params = make_params(
        &["u", "v"],
        vec![
            UniverseConstraint::Eq(param("u"), one()),
            UniverseConstraint::Le(param("v"), param("u")),
        ],
    );
    let result = analyze_monomorphization(&params);
    assert!(!result.can_monomorphize);
    assert_eq!(result.assignments.get("u"), Some(&one()));
    assert_eq!(result.remaining_poly, vec![name("v")]);
}

#[test]
fn test_mono_empty_constraints() {
    let params = make_params(&[], vec![]);
    let result = analyze_monomorphization(&params);
    assert!(!result.can_monomorphize);
}

// ── format_constraints ──────────────────────────────────────────────────

#[test]
fn test_format_constraints_empty() {
    let result = format_constraints(&[]);
    assert_eq!(result, "(no constraints)");
}

#[test]
fn test_format_constraints_eq() {
    let constraints = vec![UniverseConstraint::Eq(param("u"), one())];
    let result = format_constraints(&constraints);
    assert!(result.contains("[1]"));
    assert!(result.contains("u = 1"));
}

#[test]
fn test_format_constraints_le() {
    let constraints = vec![UniverseConstraint::Le(param("u"), two())];
    let result = format_constraints(&constraints);
    assert!(result.contains("u <= 2"));
}

#[test]
fn test_format_constraints_multi() {
    let constraints = vec![
        UniverseConstraint::Eq(param("u"), one()),
        UniverseConstraint::Le(param("v"), two()),
    ];
    let result = format_constraints(&constraints);
    assert!(result.contains("[1]"));
    assert!(result.contains("[2]"));
}

#[test]
fn test_format_constraint_system_header() {
    let params = make_params(&["u"], vec![UniverseConstraint::Eq(param("u"), one())]);
    let result = format_constraint_system(&params);
    assert!(result.contains("Universe constraint system"));
    assert!(result.contains("1 params"));
    assert!(result.contains("1 constraints"));
}

// ── solve_with_explanations ─────────────────────────────────────────────

#[test]
fn test_solve_simple() {
    let constraints = vec![
        UniverseConstraint::Eq(param("u"), one()),
        UniverseConstraint::Eq(param("v"), two()),
    ];
    let result = solve_with_explanations(&constraints).unwrap();
    assert!(result.conflicts.is_empty());
    assert!(result.unsolved.is_empty());
    assert_eq!(result.solutions.get(&name("u")), Some(&one()));
    assert_eq!(result.solutions.get(&name("v")), Some(&two()));
}

#[test]
fn test_solve_chain() {
    let constraints = vec![
        UniverseConstraint::Eq(param("u"), param("v")),
        UniverseConstraint::Eq(param("v"), one()),
    ];
    let result = solve_with_explanations(&constraints).unwrap();
    assert!(result.conflicts.is_empty());
    assert_eq!(result.solutions.get(&name("v")), Some(&one()));
}

#[test]
fn test_solve_with_conflict() {
    let constraints = vec![
        UniverseConstraint::Eq(param("u"), one()),
        UniverseConstraint::Eq(param("u"), two()),
    ];
    let result = solve_with_explanations(&constraints).unwrap();
    assert!(!result.conflicts.is_empty());
    assert!(result.solutions.is_empty());
}

#[test]
fn test_solve_empty() {
    let result = solve_with_explanations(&[]).unwrap();
    assert!(result.solutions.is_empty());
    assert!(result.unsolved.is_empty());
    assert!(result.conflicts.is_empty());
}

#[test]
fn test_solve_unsolvable_params() {
    let constraints = vec![UniverseConstraint::Le(param("u"), param("v"))];
    let result = solve_with_explanations(&constraints).unwrap();
    // Le-only constraints leave params unsolved
    assert_eq!(result.unsolved.len(), 2);
}

// ── error Display ───────────────────────────────────────────────────────

#[test]
fn test_error_conflicting_constraints() {
    let e = UniverseExt2Error::ConflictingConstraints {
        explanation: "u is bound twice".to_owned(),
    };
    assert!(e.to_string().contains("conflicting"));
    assert!(e.to_string().contains("u is bound twice"));
}

#[test]
fn test_error_no_valid_assignment() {
    let e = UniverseExt2Error::NoValidAssignment {
        param: "u".to_owned(),
    };
    assert!(e.to_string().contains("no valid level"));
    assert!(e.to_string().contains("u"));
}

#[test]
fn test_error_too_many_constraints() {
    let e = UniverseExt2Error::TooManyConstraints {
        count: 20000,
        limit: 10000,
    };
    assert!(e.to_string().contains("20000"));
    assert!(e.to_string().contains("10000"));
}

// ── edge cases ──────────────────────────────────────────────────────────

#[test]
fn test_estimate_with_succ_level() {
    let constraints = vec![UniverseConstraint::Eq(param("u"), succ(succ(zero())))];
    let estimates = estimate_levels(&constraints);
    assert_eq!(estimates.len(), 1);
    assert_eq!(estimates[0].level, two());
}

#[test]
fn test_conflict_with_max_levels() {
    let constraints = vec![
        UniverseConstraint::Eq(param("u"), Level::max(one(), two())),
        UniverseConstraint::Eq(param("u"), one()),
    ];
    // max(1, 2) normalizes to 2, which conflicts with 1
    let conflicts = detect_conflicts(&constraints);
    assert!(!conflicts.is_empty());
}

#[test]
fn test_mono_with_reversed_eq() {
    // Test that Eq(level, Param) works same as Eq(Param, level)
    let params = make_params(&["u"], vec![UniverseConstraint::Eq(one(), param("u"))]);
    let result = analyze_monomorphization(&params);
    assert!(result.can_monomorphize);
    assert_eq!(result.assignments.get("u"), Some(&one()));
}
