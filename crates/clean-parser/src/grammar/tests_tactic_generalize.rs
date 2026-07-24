// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Parser tests for the `generalize` tactic surface syntax.
//!
//! Covers both Lean 4 forms:
//!   - bare:        `generalize e = x`        → args = [e, Ident(x)]
//!   - hypothesis:  `generalize h : e = x`    → args = [e, Ident(x), Ident(h)]
//!
//! Regression for the gap where `parse_tactic_expr` greedily consumed the `=`
//! separator as an `Eq` application, so the trailing `expect(Eq)` failed and the
//! whole `by` block recovered to a synthetic sorry.

#![allow(clippy::unwrap_used)]

use super::*;

/// Extract the tactic sequence from `theorem t ... := by <tactics>`.
fn tactics_of(src: &str) -> Vec<SurfaceTactic> {
    let decls = Parser::parse_file(src).expect("source should parse");
    assert_eq!(decls.len(), 1, "expected exactly one declaration");
    match &decls[0] {
        SurfaceDecl::Theorem { proof, .. } => match proof.as_ref() {
            SurfaceExpr::ByTactic(_, tactics) => tactics.clone(),
            other => panic!("expected a ByTactic proof, got {other:?}"),
        },
        other => panic!("expected a Theorem, got {other:?}"),
    }
}

fn ident_name(e: &SurfaceExpr) -> &str {
    match e {
        SurfaceExpr::Ident(_, name) => name.as_str(),
        other => panic!("expected an Ident, got {other:?}"),
    }
}

#[test]
fn test_parse_generalize_bare_form_two_args() {
    // `generalize n + 1 = m` (no hypothesis): the term `n + 1` must NOT swallow
    // the `=` separator, and `m` is the fresh variable.
    let tactics = tactics_of("theorem t (n : Nat) : True := by\n  generalize n + 1 = m\n  trivial");
    let SurfaceTactic::Named { name, args, .. } = &tactics[0] else {
        panic!("expected a Named tactic, got {:?}", tactics[0]);
    };
    assert_eq!(name, "generalize");
    assert_eq!(args.len(), 2, "bare form has 2 args: [term, var]");
    // args[0] is the term `n + 1` (an application), not an `Eq`.
    assert!(
        matches!(&args[0], SurfaceExpr::App(..)),
        "term arg should be the `n + 1` application, got {:?}",
        args[0]
    );
    assert_eq!(
        ident_name(&args[1]),
        "m",
        "second arg is the fresh variable"
    );
}

#[test]
fn test_parse_generalize_hypothesis_form_three_args() {
    // `generalize h : n + 0 = m`: `h` is the hypothesis name (slot 2), `n + 0`
    // is the term (slot 0), `m` is the fresh variable (slot 1).
    let tactics =
        tactics_of("theorem t (n : Nat) : n + 0 = n := by\n  generalize h : n + 0 = m\n  sorry");
    let SurfaceTactic::Named { name, args, .. } = &tactics[0] else {
        panic!("expected a Named tactic, got {:?}", tactics[0]);
    };
    assert_eq!(name, "generalize");
    assert_eq!(
        args.len(),
        3,
        "hypothesis form has 3 args: [term, var, hyp]"
    );
    assert!(
        matches!(&args[0], SurfaceExpr::App(..)),
        "term arg should be the `n + 0` application, got {:?}",
        args[0]
    );
    assert_eq!(
        ident_name(&args[1]),
        "m",
        "second arg is the fresh variable"
    );
    assert_eq!(
        ident_name(&args[2]),
        "h",
        "third arg is the hypothesis name"
    );
}

#[test]
fn test_parse_generalize_simple_var_does_not_swallow_eq() {
    // `generalize n = m`: the LHS is a bare identifier; the `=` is still the
    // separator (not part of an `Eq` term), yielding 2 args [n, m].
    let tactics = tactics_of("theorem t (n : Nat) : n = n := by\n  generalize n = m\n  rfl");
    let SurfaceTactic::Named { name, args, .. } = &tactics[0] else {
        panic!("expected a Named tactic, got {:?}", tactics[0]);
    };
    assert_eq!(name, "generalize");
    assert_eq!(args.len(), 2);
    assert_eq!(ident_name(&args[0]), "n", "term is the bare identifier n");
    assert_eq!(ident_name(&args[1]), "m");
}

#[test]
fn test_parse_generalize_missing_target_var_recovers() {
    // Malformed: `generalize h : n` with no `= x`. Lean reports a parse error
    // ("unexpected identifier; expected '='"). Clean must not panic — the `by`
    // block recovers to a synthetic sorry rather than crashing.
    let decls = Parser::parse_file("theorem t (n : Nat) : n = n := by\n  generalize h : n\n  rfl")
        .expect("parser must not panic on a malformed generalize");
    assert_eq!(decls.len(), 1);
    match &decls[0] {
        SurfaceDecl::Theorem { proof, .. } => {
            // The malformed tactic block is recovered as a synthetic sorry;
            // the key property is graceful recovery (no panic, still a decl).
            assert!(
                matches!(proof.as_ref(), SurfaceExpr::SyntheticSorry(_)),
                "malformed generalize should recover to a synthetic sorry, got {:?}",
                proof
            );
        }
        other => panic!("expected a Theorem decl after recovery, got {other:?}"),
    }
}
