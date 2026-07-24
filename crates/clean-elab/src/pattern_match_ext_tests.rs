// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for extended pattern match elaboration (`pattern_match_ext`).

use crate::pattern_match_ext::*;
use clean_kernel::{Expr, Name};

// ===========================================================================
// Helper constructors
// ===========================================================================

fn var(s: &str) -> Pattern {
    Pattern::Var(Name::from_string(s))
}

fn wildcard() -> Pattern {
    Pattern::Wildcard
}

fn ctor(name: &str, args: Vec<Pattern>) -> Pattern {
    Pattern::Ctor {
        name: Name::from_string(name),
        args,
    }
}

fn lit_nat(n: u64) -> Pattern {
    Pattern::Literal(LitPattern::Nat(n))
}

fn lit_int(n: i64) -> Pattern {
    Pattern::Literal(LitPattern::Int(n))
}

fn lit_str(s: &str) -> Pattern {
    Pattern::Literal(LitPattern::String(s.to_string()))
}

fn lit_char(c: char) -> Pattern {
    Pattern::Literal(LitPattern::Char(c))
}

fn or_pat(alts: Vec<Pattern>) -> Pattern {
    Pattern::Or(alts)
}

fn as_pat(name: &str, inner: Pattern) -> Pattern {
    Pattern::As {
        name: Name::from_string(name),
        pattern: Box::new(inner),
    }
}

fn inaccessible() -> Pattern {
    Pattern::Inaccessible(Expr::const_str("_"))
}

fn mk_arm(patterns: Vec<Pattern>, body: Expr) -> MatchArm {
    MatchArm {
        patterns,
        guard: None,
        body,
    }
}

fn mk_guarded_arm(patterns: Vec<Pattern>, guard: Expr, body: Expr) -> MatchArm {
    MatchArm {
        patterns,
        guard: Some(guard),
        body,
    }
}

fn default_config() -> MatchElabConfig {
    MatchElabConfig::default()
}

fn scrutinee() -> Expr {
    Expr::const_str("x")
}

// ===========================================================================
// Pattern depth tests
// ===========================================================================

#[test]
fn test_pattern_depth_wildcard_is_zero() {
    assert_eq!(pattern_depth(&wildcard()), 0);
}

#[test]
fn test_pattern_depth_var_is_zero() {
    assert_eq!(pattern_depth(&var("x")), 0);
}

#[test]
fn test_pattern_depth_literal_is_zero() {
    assert_eq!(pattern_depth(&lit_nat(42)), 0);
}

#[test]
fn test_pattern_depth_inaccessible_is_zero() {
    assert_eq!(pattern_depth(&inaccessible()), 0);
}

#[test]
fn test_pattern_depth_ctor_no_args() {
    assert_eq!(pattern_depth(&ctor("Nil", vec![])), 1);
}

#[test]
fn test_pattern_depth_ctor_with_args() {
    let p = ctor("Cons", vec![var("x"), ctor("Nil", vec![])]);
    assert_eq!(pattern_depth(&p), 2);
}

#[test]
fn test_pattern_depth_nested_ctor() {
    let p = ctor(
        "Cons",
        vec![var("x"), ctor("Cons", vec![var("y"), ctor("Nil", vec![])])],
    );
    assert_eq!(pattern_depth(&p), 3);
}

#[test]
fn test_pattern_depth_or_pattern() {
    let p = or_pat(vec![var("x"), ctor("Nil", vec![])]);
    assert_eq!(pattern_depth(&p), 2); // 1 + max(0, 1)
}

#[test]
fn test_pattern_depth_as_pattern_var() {
    let p = as_pat("x", var("y"));
    assert_eq!(pattern_depth(&p), 1); // 1 + depth(Var) = 1 + 0
}

#[test]
fn test_pattern_depth_as_wrapping_ctor() {
    // as { inner: Ctor("Some", [Var]) }
    // depth = 1 + depth(Ctor) = 1 + (1 + max(depth(Var))) = 1 + 1 = 2
    let p = as_pat("x", ctor("Some", vec![var("y")]));
    assert_eq!(pattern_depth(&p), 2);
}

// ===========================================================================
// Well-formedness tests
// ===========================================================================

#[test]
fn test_well_formed_wildcard() {
    check_pattern_well_formed(&wildcard()).expect("wildcard should be well-formed");
}

#[test]
fn test_well_formed_var() {
    check_pattern_well_formed(&var("x")).expect("var should be well-formed");
}

#[test]
fn test_well_formed_literal() {
    check_pattern_well_formed(&lit_nat(0)).expect("literal should be well-formed");
}

#[test]
fn test_well_formed_ctor() {
    let p = ctor("Cons", vec![var("x"), wildcard()]);
    check_pattern_well_formed(&p).expect("ctor should be well-formed");
}

#[test]
fn test_well_formed_nested_ctor() {
    let p = ctor("Cons", vec![var("x"), ctor("Nil", vec![])]);
    check_pattern_well_formed(&p).expect("nested ctor should be well-formed");
}

#[test]
fn test_well_formed_or_pattern() {
    let p = or_pat(vec![var("x"), lit_nat(0)]);
    check_pattern_well_formed(&p).expect("or with 2 alts should be well-formed");
}

#[test]
fn test_not_well_formed_or_single() {
    let p = or_pat(vec![var("x")]);
    let err = check_pattern_well_formed(&p).unwrap_err();
    assert!(
        format!("{err}").contains("at least 2"),
        "expected or-pattern error, got: {err}"
    );
}

#[test]
fn test_not_well_formed_or_empty() {
    let p = or_pat(vec![]);
    let err = check_pattern_well_formed(&p).unwrap_err();
    assert!(format!("{err}").contains("at least 2"));
}

#[test]
fn test_well_formed_as_pattern() {
    let p = as_pat("x", ctor("Some", vec![var("y")]));
    check_pattern_well_formed(&p).expect("as-pattern should be well-formed");
}

#[test]
fn test_well_formed_inaccessible() {
    check_pattern_well_formed(&inaccessible()).expect("inaccessible should be well-formed");
}

// ===========================================================================
// Or-pattern expansion tests
// ===========================================================================

#[test]
fn test_expand_or_no_or_patterns() {
    let arm = mk_arm(vec![var("x")], Expr::const_str("body"));
    let expanded = expand_or_patterns(&arm);
    assert_eq!(expanded.len(), 1);
}

#[test]
fn test_expand_or_simple() {
    let arm = mk_arm(
        vec![or_pat(vec![lit_nat(0), lit_nat(1)])],
        Expr::const_str("body"),
    );
    let expanded = expand_or_patterns(&arm);
    assert_eq!(expanded.len(), 2);
    assert_eq!(expanded[0].patterns[0], lit_nat(0));
    assert_eq!(expanded[1].patterns[0], lit_nat(1));
}

#[test]
fn test_expand_or_preserves_guard() {
    let arm = mk_guarded_arm(
        vec![or_pat(vec![var("x"), var("y")])],
        Expr::const_str("guard"),
        Expr::const_str("body"),
    );
    let expanded = expand_or_patterns(&arm);
    assert_eq!(expanded.len(), 2);
    assert!(expanded[0].guard.is_some());
    assert!(expanded[1].guard.is_some());
}

#[test]
fn test_expand_or_multi_position() {
    // [A | B, C | D] → 4 arms: [A,C], [A,D], [B,C], [B,D]
    let arm = mk_arm(
        vec![
            or_pat(vec![lit_nat(0), lit_nat(1)]),
            or_pat(vec![lit_nat(2), lit_nat(3)]),
        ],
        Expr::const_str("body"),
    );
    let expanded = expand_or_patterns(&arm);
    assert_eq!(expanded.len(), 4);
}

#[test]
fn test_expand_or_three_alternatives() {
    let arm = mk_arm(
        vec![or_pat(vec![lit_nat(0), lit_nat(1), lit_nat(2)])],
        Expr::const_str("body"),
    );
    let expanded = expand_or_patterns(&arm);
    assert_eq!(expanded.len(), 3);
}

// ===========================================================================
// As-pattern binding tests
// ===========================================================================

#[test]
fn test_bind_as_patterns_no_as() {
    let arm = mk_arm(vec![var("x")], Expr::const_str("body"));
    let (new_arm, bindings) = bind_as_patterns(&arm);
    assert!(bindings.is_empty());
    assert_eq!(new_arm.patterns[0], var("x"));
}

#[test]
fn test_bind_as_patterns_simple() {
    let arm = mk_arm(
        vec![as_pat("x", ctor("Some", vec![var("y")]))],
        Expr::const_str("body"),
    );
    let (new_arm, bindings) = bind_as_patterns(&arm);
    assert_eq!(bindings.len(), 1);
    assert_eq!(bindings[0].0, Name::from_string("x"));
    // The inner pattern should be the ctor without the as wrapper.
    assert!(
        matches!(&new_arm.patterns[0], Pattern::Ctor { name, .. } if name == &Name::from_string("Some"))
    );
}

#[test]
fn test_bind_as_patterns_nested() {
    // as x @ (Cons (as y @ z) Nil)
    let arm = mk_arm(
        vec![as_pat(
            "x",
            ctor("Cons", vec![as_pat("y", var("z")), ctor("Nil", vec![])]),
        )],
        Expr::const_str("body"),
    );
    let (new_arm, bindings) = bind_as_patterns(&arm);
    assert_eq!(bindings.len(), 2);
    assert_eq!(bindings[0].0, Name::from_string("x"));
    assert_eq!(bindings[1].0, Name::from_string("y"));
    // Inner should have no As nodes.
    fn has_as(p: &Pattern) -> bool {
        match p {
            Pattern::As { .. } => true,
            Pattern::Ctor { args, .. } => args.iter().any(has_as),
            Pattern::Or(alts) => alts.iter().any(has_as),
            _ => false,
        }
    }
    assert!(!has_as(&new_arm.patterns[0]));
}

// ===========================================================================
// Compile patterns tests
// ===========================================================================

#[test]
fn test_compile_patterns_empty() {
    let result = compile_patterns(&scrutinee(), &[]);
    // Should produce a sorryAx placeholder.
    assert!(format!("{:?}", result).contains("sorryAx"));
}

#[test]
fn test_compile_patterns_single_wildcard() {
    let arms = vec![mk_arm(vec![wildcard()], Expr::const_str("body"))];
    let result = compile_patterns(&scrutinee(), &arms);
    // Wildcard is a catch-all; compiled to just the body.
    assert!(format!("{:?}", result).contains("body"));
}

#[test]
fn test_compile_patterns_single_var() {
    let arms = vec![mk_arm(vec![var("x")], Expr::const_str("body"))];
    let result = compile_patterns(&scrutinee(), &arms);
    assert!(format!("{:?}", result).contains("body"));
}

#[test]
fn test_compile_patterns_ctor_arm() {
    let arms = vec![mk_arm(
        vec![ctor("Option.some", vec![var("x")])],
        Expr::const_str("body"),
    )];
    let result = compile_patterns(&scrutinee(), &arms);
    // Should contain casesOn reference.
    assert!(format!("{:?}", result).contains("casesOn"));
}

#[test]
fn test_compile_patterns_literal_arm() {
    let arms = vec![
        mk_arm(vec![lit_nat(0)], Expr::const_str("zero")),
        mk_arm(vec![wildcard()], Expr::const_str("other")),
    ];
    let result = compile_patterns(&scrutinee(), &arms);
    let dbg = format!("{:?}", result);
    // Should contain ite for the literal comparison.
    assert!(dbg.contains("ite") || dbg.contains("beq") || dbg.contains("BEq"));
}

#[test]
fn test_compile_patterns_with_guard() {
    let arms = vec![mk_guarded_arm(
        vec![var("x")],
        Expr::const_str("guard_cond"),
        Expr::const_str("body"),
    )];
    let result = compile_patterns(&scrutinee(), &arms);
    let dbg = format!("{:?}", result);
    assert!(dbg.contains("ite"), "guarded arm should produce ite: {dbg}");
}

#[test]
fn test_compile_patterns_or_expansion() {
    let arms = vec![mk_arm(
        vec![or_pat(vec![lit_nat(0), lit_nat(1)])],
        Expr::const_str("body"),
    )];
    let result = compile_patterns(&scrutinee(), &arms);
    // The or-pattern should be expanded; result should reference nat literals.
    let dbg = format!("{:?}", result);
    assert!(dbg.contains("ite") || dbg.contains("BEq"));
}

#[test]
fn test_compile_patterns_as_binding() {
    let arms = vec![mk_arm(
        vec![as_pat("x", wildcard())],
        Expr::const_str("body"),
    )];
    let result = compile_patterns(&scrutinee(), &arms);
    let dbg = format!("{:?}", result);
    // Should contain a Let binding for the as-pattern.
    assert!(dbg.contains("Let"), "as-pattern should produce Let: {dbg}");
}

// ===========================================================================
// elaborate_match tests
// ===========================================================================

#[test]
fn test_elaborate_match_empty_arms() {
    let result = elaborate_match(&scrutinee(), &[], &default_config());
    let res = result.expect("empty arms should succeed");
    assert_eq!(res.arms_count, 0);
}

#[test]
fn test_elaborate_match_single_var_arm() {
    let arms = vec![mk_arm(vec![var("x")], Expr::const_str("body"))];
    let res = elaborate_match(&scrutinee(), &arms, &default_config()).expect("should succeed");
    assert_eq!(res.arms_count, 1);
    assert!(res.warnings.is_empty());
}

#[test]
fn test_elaborate_match_exhaustiveness_warning() {
    // Only ctor arms, no catch-all → non-exhaustive warning.
    let arms = vec![mk_arm(
        vec![ctor("Option.some", vec![var("x")])],
        Expr::const_str("body"),
    )];
    let res = elaborate_match(&scrutinee(), &arms, &default_config()).expect("should succeed");
    assert!(
        res.warnings
            .iter()
            .any(|w| matches!(w, MatchWarning::NonExhaustive { .. })),
        "expected non-exhaustive warning"
    );
}

#[test]
fn test_elaborate_match_no_exhaustiveness_warning_with_wildcard() {
    let arms = vec![
        mk_arm(
            vec![ctor("Option.some", vec![var("x")])],
            Expr::const_str("a"),
        ),
        mk_arm(vec![wildcard()], Expr::const_str("b")),
    ];
    let res = elaborate_match(&scrutinee(), &arms, &default_config()).expect("should succeed");
    assert!(
        !res.warnings
            .iter()
            .any(|w| matches!(w, MatchWarning::NonExhaustive { .. })),
        "should not warn when wildcard is present"
    );
}

#[test]
fn test_elaborate_match_redundancy_warning() {
    let arms = vec![
        mk_arm(vec![wildcard()], Expr::const_str("a")),
        mk_arm(vec![var("x")], Expr::const_str("b")),
    ];
    let res = elaborate_match(&scrutinee(), &arms, &default_config()).expect("should succeed");
    assert!(
        res.warnings
            .iter()
            .any(|w| matches!(w, MatchWarning::Redundant { arm_index: 1 })),
        "second arm after catch-all should be redundant"
    );
}

#[test]
fn test_elaborate_match_overlapping_guards() {
    let arms = vec![
        mk_guarded_arm(vec![var("x")], Expr::const_str("g1"), Expr::const_str("a")),
        mk_guarded_arm(vec![var("y")], Expr::const_str("g2"), Expr::const_str("b")),
    ];
    let res = elaborate_match(&scrutinee(), &arms, &default_config()).expect("should succeed");
    assert!(
        res.warnings
            .iter()
            .any(|w| matches!(w, MatchWarning::OverlappingGuards)),
        "should warn about overlapping guards"
    );
}

#[test]
fn test_elaborate_match_depth_exceeded() {
    // Build a pattern deeper than max_depth=2.
    let deep = ctor("A", vec![ctor("B", vec![ctor("C", vec![])])]);
    let arms = vec![mk_arm(vec![deep], Expr::const_str("body"))];
    let config = MatchElabConfig {
        max_depth: 2,
        ..Default::default()
    };
    let err = elaborate_match(&scrutinee(), &arms, &config).unwrap_err();
    assert!(
        format!("{err}").contains("depth"),
        "expected depth error, got: {err}"
    );
}

#[test]
fn test_elaborate_match_or_expansion_count() {
    let arms = vec![mk_arm(
        vec![or_pat(vec![lit_nat(0), lit_nat(1), lit_nat(2)])],
        Expr::const_str("body"),
    )];
    let res = elaborate_match(&scrutinee(), &arms, &default_config()).expect("should succeed");
    assert_eq!(res.arms_count, 3, "or with 3 alts should expand to 3 arms");
}

#[test]
fn test_elaborate_match_config_disable_checks() {
    let arms = vec![mk_arm(vec![ctor("Foo", vec![])], Expr::const_str("body"))];
    let config = MatchElabConfig {
        check_exhaustive: false,
        check_redundant: false,
        max_depth: 20,
    };
    let res = elaborate_match(&scrutinee(), &arms, &config).expect("should succeed");
    assert!(res.warnings.is_empty(), "all checks disabled, no warnings");
}

// ===========================================================================
// LitPattern variant tests
// ===========================================================================

#[test]
fn test_lit_pattern_int_negative() {
    let arms = vec![
        mk_arm(vec![lit_int(-1)], Expr::const_str("neg")),
        mk_arm(vec![wildcard()], Expr::const_str("other")),
    ];
    let result = compile_patterns(&scrutinee(), &arms);
    let dbg = format!("{:?}", result);
    assert!(dbg.contains("negSucc") || dbg.contains("ite"));
}

#[test]
fn test_lit_pattern_int_positive() {
    let arms = vec![
        mk_arm(vec![lit_int(5)], Expr::const_str("pos")),
        mk_arm(vec![wildcard()], Expr::const_str("other")),
    ];
    let result = compile_patterns(&scrutinee(), &arms);
    let dbg = format!("{:?}", result);
    assert!(dbg.contains("ofNat") || dbg.contains("ite"));
}

#[test]
fn test_lit_pattern_string() {
    let p = lit_str("hello");
    assert_eq!(pattern_depth(&p), 0);
    check_pattern_well_formed(&p).expect("string literal well-formed");
}

#[test]
fn test_lit_pattern_char() {
    let p = lit_char('a');
    assert_eq!(pattern_depth(&p), 0);
    check_pattern_well_formed(&p).expect("char literal well-formed");
}

// ===========================================================================
// Edge case tests
// ===========================================================================

#[test]
fn test_pattern_equality() {
    assert_eq!(var("x"), var("x"));
    assert_ne!(var("x"), var("y"));
    assert_eq!(wildcard(), wildcard());
    assert_eq!(lit_nat(0), lit_nat(0));
    assert_ne!(lit_nat(0), lit_nat(1));
    assert_eq!(ctor("Nil", vec![]), ctor("Nil", vec![]));
}

#[test]
fn test_elaborate_match_well_formedness_error_propagates() {
    // Single-element or-pattern should fail well-formedness.
    let arms = vec![mk_arm(
        vec![or_pat(vec![var("x")])],
        Expr::const_str("body"),
    )];
    let err = elaborate_match(&scrutinee(), &arms, &default_config()).unwrap_err();
    assert!(format!("{err}").contains("at least 2"));
}

#[test]
fn test_match_elab_config_default() {
    let cfg = MatchElabConfig::default();
    assert!(cfg.check_exhaustive);
    assert!(cfg.check_redundant);
    assert_eq!(cfg.max_depth, 20);
}

#[test]
fn test_compile_inaccessible_pattern() {
    let arms = vec![mk_arm(vec![inaccessible()], Expr::const_str("body"))];
    let result = compile_patterns(&scrutinee(), &arms);
    assert!(format!("{:?}", result).contains("body"));
}

#[test]
fn test_elaborate_match_multiple_ctor_arms() {
    let arms = vec![
        mk_arm(
            vec![ctor("Option.some", vec![var("x")])],
            Expr::const_str("some"),
        ),
        mk_arm(vec![ctor("Option.none", vec![])], Expr::const_str("none")),
    ];
    let res = elaborate_match(&scrutinee(), &arms, &default_config()).expect("should succeed");
    assert_eq!(res.arms_count, 2);
    // No catch-all, so non-exhaustive warning expected.
    assert!(res
        .warnings
        .iter()
        .any(|w| matches!(w, MatchWarning::NonExhaustive { .. })));
}
