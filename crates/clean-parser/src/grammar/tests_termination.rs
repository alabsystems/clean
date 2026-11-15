// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for real expression parsing in termination hints (#1132).
//!
//! Verifies that `termination_by` measure expressions and `decreasing_by`
//! tactic blocks are parsed as real AST nodes (not Hole placeholders).

use super::*;

#[test]
fn local_recursive_equations_keep_the_following_explicit_application() {
    let source = include_str!(
        "../../../../reports/local-function-headers-2026-11-06/sources/let_rec_equation_class.lean"
    );
    let decls = Parser::parse_file(source).expect("recursive declaration parses");
    let [SurfaceDecl::Def { val, .. }] = decls.as_slice() else {
        panic!("expected exactly the original definition: {decls:?}");
    };
    let SurfaceExpr::LetRec(_, binder, _, body) = val.as_ref() else {
        panic!("expected recursive binding: {val:?}");
    };
    let SurfaceExpr::App(_, head, args) = body.as_ref() else {
        panic!("expected continuation application: {body:?}");
    };
    let SurfaceExpr::Explicit(_, head) = head.as_ref() else {
        panic!("explicit marker lost: {head:?}");
    };
    assert!(matches!(head.as_ref(), SurfaceExpr::Ident(_, name) if name == &binder.name));
    assert_eq!(args.len(), 2);
}

#[test]
fn test_termination_measure_is_real_ident() {
    // Simple measure: `termination_by n` should parse as Ident("n")
    let code = "def foo (n : Nat) : Nat := n
termination_by n";
    let decls = Parser::parse_file(code).unwrap();
    assert_eq!(decls.len(), 1);
    match &decls[0] {
        SurfaceDecl::Def { termination, .. } => {
            let tb = termination
                .termination_by
                .as_ref()
                .expect("termination_by should be present");
            let measure = tb.measure.as_ref().expect("measure should exist");
            assert!(
                matches!(measure.as_ref(), SurfaceExpr::Ident(_, name) if (name).name() == crate::SurfaceName::generated_path("n").name()),
                "measure should be Ident(n), got {measure:?}"
            );
        }
        other => panic!("Expected Def, got {other:?}"),
    }
}

#[test]
fn test_termination_measure_with_arrow_is_real() {
    // Old syntax: `termination_by n => n` — measure after => is Ident("n")
    let code = "def f (n : Nat) : Nat := n
termination_by n => n";
    let decls = Parser::parse_file(code).unwrap();
    assert_eq!(decls.len(), 1);
    match &decls[0] {
        SurfaceDecl::Def { termination, .. } => {
            let tb = termination
                .termination_by
                .as_ref()
                .expect("termination_by should be present");
            assert_eq!(tb.kind, TerminationKind::WellFounded);
            let measure = tb.measure.as_ref().expect("measure should exist");
            assert!(
                matches!(measure.as_ref(), SurfaceExpr::Ident(_, name) if (name).name() == crate::SurfaceName::generated_path("n").name()),
                "measure should be Ident(n), got {measure:?}"
            );
        }
        other => panic!("Expected Def, got {other:?}"),
    }
}

#[test]
fn test_termination_complex_measure_not_hole() {
    // Complex measure: field access + arithmetic
    let code = "def merge (xs ys : List Nat) : List Nat := merge xs ys
termination_by xs.length + ys.length";
    let decls = Parser::parse_file(code).unwrap();
    assert_eq!(decls.len(), 1);
    match &decls[0] {
        SurfaceDecl::Def { termination, .. } => {
            let tb = termination
                .termination_by
                .as_ref()
                .expect("termination_by should be present");
            let measure = tb.measure.as_ref().expect("measure should exist");
            assert!(
                !matches!(measure.as_ref(), SurfaceExpr::Hole(_)),
                "complex measure should be parsed as real expression, not Hole. Got {measure:?}"
            );
        }
        other => panic!("Expected Def, got {other:?}"),
    }
}

#[test]
fn test_termination_tuple_measure_not_hole() {
    // Tuple measure: (m, n) for Ackermann-like functions
    let code = "def ack (m n : Nat) : Nat := ack m n
termination_by (m, n)";
    let decls = Parser::parse_file(code).unwrap();
    assert_eq!(decls.len(), 1);
    match &decls[0] {
        SurfaceDecl::Def { termination, .. } => {
            let tb = termination
                .termination_by
                .as_ref()
                .expect("termination_by should be present");
            let measure = tb.measure.as_ref().expect("tuple measure should exist");
            assert!(
                !matches!(measure.as_ref(), SurfaceExpr::Hole(_)),
                "tuple measure should be real expression, got {measure:?}"
            );
        }
        other => panic!("Expected Def, got {other:?}"),
    }
}

#[test]
fn test_decreasing_by_tactic_is_real() {
    // decreasing_by should produce ByTactic with parsed simp_arith
    let code = "def foo (n : Nat) : Nat := n
decreasing_by simp_arith";
    let decls = Parser::parse_file(code).unwrap();
    assert_eq!(decls.len(), 1);
    match &decls[0] {
        SurfaceDecl::Def { termination, .. } => {
            let db = termination
                .decreasing_by
                .as_ref()
                .expect("decreasing_by should be parsed");
            assert!(
                matches!(db.tactic.as_ref(), SurfaceExpr::ByTactic(_, tactics) if !tactics.is_empty()),
                "tactic should be ByTactic with parsed tactics, got {:?}",
                db.tactic
            );
        }
        other => panic!("Expected Def, got {other:?}"),
    }
}

#[test]
fn test_decreasing_by_compound_tactic() {
    // Compound tactic: all_goals simp_arith
    let code = "def f (n : Nat) : Nat := f (n - 1)
decreasing_by all_goals simp_arith";
    let decls = Parser::parse_file(code).unwrap();
    assert_eq!(decls.len(), 1);
    match &decls[0] {
        SurfaceDecl::Def { termination, .. } => {
            let db = termination
                .decreasing_by
                .as_ref()
                .expect("decreasing_by should be present");
            match db.tactic.as_ref() {
                SurfaceExpr::ByTactic(_, tactics) => {
                    assert!(
                        !tactics.is_empty(),
                        "tactic sequence should have at least one tactic"
                    );
                }
                other => panic!("Expected ByTactic, got {other:?}"),
            }
        }
        other => panic!("Expected Def, got {other:?}"),
    }
}

#[test]
fn test_both_hints_real_expressions() {
    // Both termination_by and decreasing_by should have real expressions
    let code = "def ack (m n : Nat) : Nat := match m, n with
| 0, n => n + 1
| m + 1, 0 => ack m 1
| m + 1, n + 1 => ack m (ack (m + 1) n)
termination_by m n => (m, n)
decreasing_by all_goals simp_arith";
    let decls = Parser::parse_file(code).unwrap();
    assert_eq!(decls.len(), 1);
    match &decls[0] {
        SurfaceDecl::Def { termination, .. } => {
            let tb = termination
                .termination_by
                .as_ref()
                .expect("ack should have termination_by");
            let measure = tb.measure.as_ref().expect("measure should exist");
            assert!(
                !matches!(measure.as_ref(), SurfaceExpr::Hole(_)),
                "measure should not be Hole, got {measure:?}"
            );
            let db = termination
                .decreasing_by
                .as_ref()
                .expect("ack should have decreasing_by");
            assert!(
                matches!(db.tactic.as_ref(), SurfaceExpr::ByTactic(_, tactics) if !tactics.is_empty()),
                "tactic should be ByTactic, got {:?}",
                db.tactic
            );
        }
        other => panic!("Expected Def, got {other:?}"),
    }
}

#[test]
fn test_decreasing_by_followed_by_termination_by() {
    // Reversed order: decreasing_by then termination_by
    // Tactic parser must stop at termination_by boundary
    let code = "def ack (m n : Nat) : Nat := ack m n
decreasing_by simp_arith
termination_by m n => (m, n)";
    let decls = Parser::parse_file(code).unwrap();
    assert_eq!(decls.len(), 1);
    match &decls[0] {
        SurfaceDecl::Def { termination, .. } => {
            let db = termination
                .decreasing_by
                .as_ref()
                .expect("decreasing_by should be present");
            assert!(
                matches!(db.tactic.as_ref(), SurfaceExpr::ByTactic(_, tactics) if !tactics.is_empty()),
                "tactic should be ByTactic, got {:?}",
                db.tactic
            );
            let tb = termination
                .termination_by
                .as_ref()
                .expect("termination_by should be present after decreasing_by");
            let measure = tb.measure.as_ref().expect("measure should exist");
            assert!(
                !matches!(measure.as_ref(), SurfaceExpr::Hole(_)),
                "measure should not be Hole, got {measure:?}"
            );
        }
        other => panic!("Expected Def, got {other:?}"),
    }
}

/// A `termination_by` (or `decreasing_by`) on a `where` helper that is not
/// the last one ends at the next helper's header: the hint belongs to its
/// helper, the next helper parses whole, and nothing is recovered. Lean
/// 4.8.0 accepts both spellings.
#[test]
fn test_where_helper_hint_before_another_helper() {
    for code in [
        "def twoHelpers (limit : Nat) : Nat :=
  up 0 + other limit
where
  up (i : Nat) : Nat :=
    if i < limit then up (i + 1) else i
  termination_by limit - i
  other (n : Nat) : Nat := n",
        "def twoHelpers (limit : Nat) : Nat :=
  up 0 + other limit
where
  up (i : Nat) : Nat :=
    if h : i < limit then up (i + 1) else i
  termination_by limit - i
  decreasing_by simp_wf; omega
  other (n : Nat) : Nat := n",
    ] {
        let report = crate::parse_file_with_diagnostics(code).unwrap();
        assert!(
            report.diagnostics.is_empty(),
            "nothing may be recovered: {:?}",
            report.diagnostics
        );
        let [SurfaceDecl::Def { where_decls, .. }] = report.decls.as_slice() else {
            panic!("expected one def, got {:?}", report.decls);
        };
        let names: Vec<String> = where_decls.iter().map(|d| d.name.to_string()).collect();
        assert_eq!(names, ["up", "other"], "both helpers parse");
        let up = &where_decls[0].termination;
        assert!(
            up.termination_by
                .as_ref()
                .and_then(|tb| tb.well_founded_measure())
                .is_some(),
            "`up` keeps its measure"
        );
        let other = &where_decls[1].termination;
        assert!(
            other.termination_by.is_none() && other.decreasing_by.is_none(),
            "`other` has no hint of its own"
        );
        assert!(
            matches!(where_decls[1].body, SurfaceExpr::Ident(..)),
            "`other`'s body is `n`: {:?}",
            where_decls[1].body
        );
    }
}
