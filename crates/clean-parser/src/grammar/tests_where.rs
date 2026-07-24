// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for `where` local definition parsing.

use crate::grammar::Parser;
use crate::surface::{SurfaceDecl, SurfaceExpr};

#[test]
fn test_parse_where_local_def_multiple_binders() {
    // def foo : Nat := helper 1 2
    // where
    //   helper (a : Nat) (b : Nat) : Nat := a + b
    let code = "def foo : Nat := helper 1 2\nwhere\n  helper (a : Nat) (b : Nat) : Nat := a + b";
    let decls = Parser::parse_file(code).unwrap();
    assert_eq!(decls.len(), 1);
    match &decls[0] {
        SurfaceDecl::Def {
            name, where_decls, ..
        } => {
            assert_eq!(name, "foo");
            assert_eq!(where_decls.len(), 1);
            assert_eq!(where_decls[0].name, "helper");
            assert_eq!(
                where_decls[0].binders.len(),
                2,
                "helper should have 2 binders"
            );
            assert!(where_decls[0].ret_ty.is_some(), "helper has return type");
        }
        other => panic!("Expected Def, got {other:?}"),
    }
}

#[test]
fn test_parse_where_local_def_no_type_annotation() {
    // def foo := helper where helper := 42
    let code = "def foo := helper\nwhere\n  helper := 42";
    let decls = Parser::parse_file(code).unwrap();
    assert_eq!(decls.len(), 1);
    match &decls[0] {
        SurfaceDecl::Def {
            name, where_decls, ..
        } => {
            assert_eq!(name, "foo");
            assert_eq!(where_decls.len(), 1);
            assert_eq!(where_decls[0].name, "helper");
            assert!(where_decls[0].binders.is_empty(), "no binders");
            assert!(
                where_decls[0].ret_ty.is_none(),
                "no type annotation for helper"
            );
        }
        other => panic!("Expected Def, got {other:?}"),
    }
}

#[test]
fn test_parse_where_local_def_equation_form() {
    // A `where` helper defined by pattern-matching *equations* (`| pat => body`)
    // rather than `:= expr` — the same equation sugar a top-level `def` accepts.
    // Previously `parse_single_where_def` hard-required `:=` and dropped the
    // helper (leaving `go` an unknown identifier).
    let code =
        "def top (n : Nat) : Nat := go n\n  where go : Nat -> Nat\n    | 0 => 0\n    | _ => 1";
    let decls = Parser::parse_file(code).expect("where-equation def should parse");
    assert_eq!(decls.len(), 1);
    match &decls[0] {
        SurfaceDecl::Def {
            name, where_decls, ..
        } => {
            assert_eq!(name, "top");
            assert_eq!(where_decls.len(), 1, "the `go` helper must be captured");
            assert_eq!(where_decls[0].name, "go");
            assert!(where_decls[0].ret_ty.is_some(), "go has a return type");
            // The equation body desugars to a pattern-matching lambda, exactly as
            // a top-level equation `def` does.
            assert!(
                matches!(where_decls[0].body, SurfaceExpr::PatternMatchLambda(..)),
                "go's body should be a PatternMatchLambda, got {:?}",
                where_decls[0].body
            );
        }
        other => panic!("Expected Def, got {other:?}"),
    }
}

#[test]
fn test_parse_where_multiple_defs_with_dependencies() {
    // def foo : Nat := baz (bar 1)
    // where
    //   bar (n : Nat) : Nat := n + 1
    //   baz (n : Nat) : Nat := bar n + 1
    let code = "def foo : Nat := baz (bar 1)\nwhere\n  bar (n : Nat) : Nat := n + 1\n  baz (n : Nat) : Nat := bar n + 1";
    let decls = Parser::parse_file(code).unwrap();
    assert_eq!(decls.len(), 1);
    match &decls[0] {
        SurfaceDecl::Def {
            name, where_decls, ..
        } => {
            assert_eq!(name, "foo");
            assert_eq!(
                where_decls.len(),
                2,
                "should parse two where local definitions"
            );
            assert_eq!(where_decls[0].name, "bar");
            assert_eq!(where_decls[1].name, "baz");
        }
        other => panic!("Expected Def, got {other:?}"),
    }
}
