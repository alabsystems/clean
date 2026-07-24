// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for structural recursion detection.

use super::detect::find_decreasing_arg;
use super::*;
use clean_parser::{Projection, Span, SurfaceArg};

fn dummy_span() -> Span {
    Span::new(0, 0)
}

#[test]
fn test_detect_no_recursion() {
    // def f x := x
    let body = SurfaceExpr::Ident(dummy_span(), "x".to_string());
    let info = detect_recursion("f", &body);
    assert!(!info.is_recursive);
    assert!(info.calls.is_empty());
}

#[test]
fn test_detect_simple_recursion() {
    // def f x := f x
    let body = SurfaceExpr::App(
        dummy_span(),
        Box::new(SurfaceExpr::Ident(dummy_span(), "f".to_string())),
        vec![SurfaceArg::positional(SurfaceExpr::Ident(
            dummy_span(),
            "x".to_string(),
        ))],
    );
    let info = detect_recursion("f", &body);
    assert!(info.is_recursive);
    assert_eq!(info.calls.len(), 1);
    assert!(matches!(info.calls[0].args[0], RecursiveArg::Var(ref n) if n == "x"));
}

#[test]
fn test_detect_recursion_curried_application() {
    // def f x y := f a b  (#389)
    // Represented as App(App(f, [a]), [b])
    let body = SurfaceExpr::App(
        dummy_span(),
        Box::new(SurfaceExpr::App(
            dummy_span(),
            Box::new(SurfaceExpr::Ident(dummy_span(), "f".to_string())),
            vec![SurfaceArg::positional(SurfaceExpr::Ident(
                dummy_span(),
                "a".to_string(),
            ))],
        )),
        vec![SurfaceArg::positional(SurfaceExpr::Ident(
            dummy_span(),
            "b".to_string(),
        ))],
    );
    let info = detect_recursion("f", &body);
    assert!(info.is_recursive, "Should detect curried recursive call");
    assert_eq!(info.calls.len(), 1, "Should be exactly one call");
    // Both args a and b should be recorded
    assert_eq!(info.calls[0].args.len(), 2, "Should have 2 args");
    assert!(matches!(info.calls[0].args[0], RecursiveArg::Var(ref n) if n == "a"));
    assert!(matches!(info.calls[0].args[1], RecursiveArg::Var(ref n) if n == "b"));
}

#[test]
fn test_detect_recursion_with_qualified_projection() {
    // def foo.bar x := foo.bar x
    let body = SurfaceExpr::App(
        dummy_span(),
        Box::new(SurfaceExpr::Proj(
            dummy_span(),
            Box::new(SurfaceExpr::Ident(dummy_span(), "foo".to_string())),
            Projection::Named("bar".to_string()),
        )),
        vec![SurfaceArg::positional(SurfaceExpr::Ident(
            dummy_span(),
            "x".to_string(),
        ))],
    );
    let info = detect_recursion("foo.bar", &body);
    assert!(info.is_recursive);
    assert_eq!(info.calls.len(), 1);
}

#[test]
fn test_detect_recursion_with_paren_qualified_projection() {
    // def foo.bar x := (foo).bar x
    let body = SurfaceExpr::App(
        dummy_span(),
        Box::new(SurfaceExpr::Proj(
            dummy_span(),
            Box::new(SurfaceExpr::Paren(
                dummy_span(),
                Box::new(SurfaceExpr::Ident(dummy_span(), "foo".to_string())),
            )),
            Projection::Named("bar".to_string()),
        )),
        vec![SurfaceArg::positional(SurfaceExpr::Ident(
            dummy_span(),
            "x".to_string(),
        ))],
    );
    let info = detect_recursion("foo.bar", &body);
    assert!(info.is_recursive);
    assert_eq!(info.calls.len(), 1);
}

#[test]
fn test_detect_recursion_with_short_name_in_namespace() {
    // def foo.bar x := bar x
    let body = SurfaceExpr::App(
        dummy_span(),
        Box::new(SurfaceExpr::Ident(dummy_span(), "bar".to_string())),
        vec![SurfaceArg::positional(SurfaceExpr::Ident(
            dummy_span(),
            "x".to_string(),
        ))],
    );
    let info = detect_recursion("foo.bar", &body);
    assert!(info.is_recursive);
    assert_eq!(info.calls.len(), 1);
}

#[test]
fn test_detect_recursion_shadowed_short_name_in_namespace() {
    // def foo.bar x := fun bar => bar x
    let body = SurfaceExpr::Lambda(
        dummy_span(),
        vec![clean_parser::SurfaceBinder::new(
            "bar",
            None,
            clean_parser::SurfaceBinderInfo::Explicit,
        )],
        Box::new(SurfaceExpr::App(
            dummy_span(),
            Box::new(SurfaceExpr::Ident(dummy_span(), "bar".to_string())),
            vec![SurfaceArg::positional(SurfaceExpr::Ident(
                dummy_span(),
                "x".to_string(),
            ))],
        )),
    );
    let info = detect_recursion("foo.bar", &body);
    assert!(!info.is_recursive);
    assert!(info.calls.is_empty());
}

#[test]
fn test_detect_recursion_shadowed_namespace_base() {
    // def foo.bar x := let foo := foo in foo.bar x
    let body = SurfaceExpr::Let(
        dummy_span(),
        clean_parser::SurfaceBinder::new("foo", None, clean_parser::SurfaceBinderInfo::Explicit),
        Box::new(SurfaceExpr::Ident(dummy_span(), "foo".to_string())),
        Box::new(SurfaceExpr::App(
            dummy_span(),
            Box::new(SurfaceExpr::Proj(
                dummy_span(),
                Box::new(SurfaceExpr::Ident(dummy_span(), "foo".to_string())),
                Projection::Named("bar".to_string()),
            )),
            vec![SurfaceArg::positional(SurfaceExpr::Ident(
                dummy_span(),
                "x".to_string(),
            ))],
        )),
    );
    let info = detect_recursion("foo.bar", &body);
    assert!(!info.is_recursive);
    assert!(info.calls.is_empty());
}

#[test]
fn test_detect_recursion_with_root_qualified_name() {
    // def foo.bar x := _root_.foo.bar x
    let body = SurfaceExpr::App(
        dummy_span(),
        Box::new(SurfaceExpr::Proj(
            dummy_span(),
            Box::new(SurfaceExpr::Proj(
                dummy_span(),
                Box::new(SurfaceExpr::Ident(dummy_span(), "_root_".to_string())),
                Projection::Named("foo".to_string()),
            )),
            Projection::Named("bar".to_string()),
        )),
        vec![SurfaceArg::positional(SurfaceExpr::Ident(
            dummy_span(),
            "x".to_string(),
        ))],
    );
    let info = detect_recursion("foo.bar", &body);
    assert!(info.is_recursive);
    assert_eq!(info.calls.len(), 1);
}

#[test]
fn test_detect_recursion_with_universe_inst() {
    // def foo.bar x := (foo.bar).{u} x
    let body = SurfaceExpr::App(
        dummy_span(),
        Box::new(SurfaceExpr::UniverseInst(
            dummy_span(),
            Box::new(SurfaceExpr::Ident(dummy_span(), "foo.bar".to_string())),
            vec![clean_parser::LevelExpr::Param("u".to_string())],
        )),
        vec![SurfaceArg::positional(SurfaceExpr::Ident(
            dummy_span(),
            "x".to_string(),
        ))],
    );
    let info = detect_recursion("foo.bar", &body);
    assert!(info.is_recursive);
    assert_eq!(info.calls.len(), 1);
}

#[test]
fn test_detect_recursion_with_explicit_wrapper() {
    // def f x := (@f) x  (#387)
    let body = SurfaceExpr::App(
        dummy_span(),
        Box::new(SurfaceExpr::Explicit(
            dummy_span(),
            Box::new(SurfaceExpr::Ident(dummy_span(), "f".to_string())),
        )),
        vec![SurfaceArg::positional(SurfaceExpr::Ident(
            dummy_span(),
            "x".to_string(),
        ))],
    );
    let info = detect_recursion("f", &body);
    assert!(info.is_recursive, "Explicit wrapper should be unwrapped");
    assert_eq!(info.calls.len(), 1);
}

#[test]
fn test_detect_recursion_with_ascription_wrapper() {
    // def f x := (f : T) x  (#387)
    let body = SurfaceExpr::App(
        dummy_span(),
        Box::new(SurfaceExpr::Ascription(
            dummy_span(),
            Box::new(SurfaceExpr::Ident(dummy_span(), "f".to_string())),
            Box::new(SurfaceExpr::Ident(dummy_span(), "T".to_string())),
        )),
        vec![SurfaceArg::positional(SurfaceExpr::Ident(
            dummy_span(),
            "x".to_string(),
        ))],
    );
    let info = detect_recursion("f", &body);
    assert!(info.is_recursive, "Ascription wrapper should be unwrapped");
    assert_eq!(info.calls.len(), 1);
}

#[test]
fn test_qualified_name_from_proj_with_explicit_base() {
    // (@foo).bar  (#388)
    let expr = SurfaceExpr::Proj(
        dummy_span(),
        Box::new(SurfaceExpr::Explicit(
            dummy_span(),
            Box::new(SurfaceExpr::Ident(dummy_span(), "foo".to_string())),
        )),
        Projection::Named("bar".to_string()),
    );
    let name = qualified_name_from_proj(&expr);
    assert_eq!(name, Some("foo.bar".to_string()));
}

#[test]
fn test_qualified_name_from_proj_with_ascription_base() {
    // (foo : T).bar  (#388)
    let expr = SurfaceExpr::Proj(
        dummy_span(),
        Box::new(SurfaceExpr::Ascription(
            dummy_span(),
            Box::new(SurfaceExpr::Ident(dummy_span(), "foo".to_string())),
            Box::new(SurfaceExpr::Ident(dummy_span(), "T".to_string())),
        )),
        Projection::Named("bar".to_string()),
    );
    let name = qualified_name_from_proj(&expr);
    assert_eq!(name, Some("foo.bar".to_string()));
}

#[test]
fn test_detect_recursion_in_match() {
    // def f x := match x with | _ => f y
    let body = SurfaceExpr::Match(
        dummy_span(),
        None,
        Box::new(SurfaceExpr::Ident(dummy_span(), "x".to_string())),
        vec![clean_parser::SurfaceMatchArm {
            span: dummy_span(),
            pattern: SurfacePattern::Wildcard,
            body: SurfaceExpr::App(
                dummy_span(),
                Box::new(SurfaceExpr::Ident(dummy_span(), "f".to_string())),
                vec![SurfaceArg::positional(SurfaceExpr::Ident(
                    dummy_span(),
                    "y".to_string(),
                ))],
            ),
        }],
    );
    let info = detect_recursion("f", &body);
    assert!(info.is_recursive);
    assert_eq!(info.calls.len(), 1);
}

#[test]
fn test_detect_recursion_shadowed_by_lambda() {
    // def f x := fun f => f x
    let body = SurfaceExpr::Lambda(
        dummy_span(),
        vec![clean_parser::SurfaceBinder::new(
            "f",
            None,
            clean_parser::SurfaceBinderInfo::Explicit,
        )],
        Box::new(SurfaceExpr::App(
            dummy_span(),
            Box::new(SurfaceExpr::Ident(dummy_span(), "f".to_string())),
            vec![SurfaceArg::positional(SurfaceExpr::Ident(
                dummy_span(),
                "x".to_string(),
            ))],
        )),
    );
    let info = detect_recursion("f", &body);
    assert!(!info.is_recursive);
    assert!(info.calls.is_empty());
}

#[test]
fn test_find_decreasing_arg() {
    // All calls pass variable at position 1
    let calls = vec![
        RecursiveCall {
            args: vec![RecursiveArg::Other, RecursiveArg::Var("xs".to_string())],
        },
        RecursiveCall {
            args: vec![RecursiveArg::Other, RecursiveArg::Var("ys".to_string())],
        },
    ];
    assert_eq!(find_decreasing_arg(&calls, &[], None), Some(1));
}

#[test]
fn test_no_decreasing_arg() {
    // Position 0: not all vars, Position 1: not all vars
    let calls = vec![
        RecursiveCall {
            args: vec![RecursiveArg::Var("x".to_string()), RecursiveArg::Other],
        },
        RecursiveCall {
            args: vec![RecursiveArg::Other, RecursiveArg::Var("y".to_string())],
        },
    ];
    assert_eq!(find_decreasing_arg(&calls, &[], None), None);
}

#[test]
fn test_find_decreasing_arg_mismatched_arity() {
    let calls = vec![
        RecursiveCall {
            args: vec![RecursiveArg::Var("x".to_string())],
        },
        RecursiveCall {
            args: vec![RecursiveArg::Var("y".to_string()), RecursiveArg::Other],
        },
    ];
    assert_eq!(find_decreasing_arg(&calls, &[], None), None);
}

#[test]
fn test_find_decreasing_arg_prefers_changed_param() {
    // Two variable positions; only position 1 changes from the parameter name.
    let calls = vec![
        RecursiveCall {
            args: vec![
                RecursiveArg::Var("f".to_string()),
                RecursiveArg::Var("tail".to_string()),
            ],
        },
        RecursiveCall {
            args: vec![
                RecursiveArg::Var("f".to_string()),
                RecursiveArg::Var("rest".to_string()),
            ],
        },
    ];
    let param_names = vec!["f".to_string(), "xs".to_string()];
    assert_eq!(find_decreasing_arg(&calls, &param_names, None), Some(1));
}

#[test]
fn test_find_decreasing_arg_with_param_names() {
    // Test that param_names helps select the correct decreasing arg (#403)
    // Simulates: def myMap (f : A → B) (xs : List A) with call myMap f tail
    // Without param names, both positions are candidates (all vars)
    // With param names, position 1 is preferred (xs -> tail, different)
    let calls = vec![RecursiveCall {
        args: vec![
            RecursiveArg::Var("f".to_string()), // same as param, not decreasing
            RecursiveArg::Var("tail".to_string()), // different from param, decreasing!
        ],
    }];
    // Without param names: fallback to last position (1)
    assert_eq!(find_decreasing_arg(&calls, &[], None), Some(1));

    // With param names: correctly identifies position 1 (different from "xs")
    let param_names = vec!["f".to_string(), "xs".to_string()];
    assert_eq!(find_decreasing_arg(&calls, &param_names, None), Some(1));

    // Position 0 would be wrong: f -> f (same name, not decreasing)
    // The heuristic correctly skips it
}

#[test]
fn test_find_decreasing_arg_param_names_both_different() {
    // Test edge case: both positions differ from their parameters
    // Simulates: def fold (acc : A) (xs : List A) with call fold new_acc tail
    // When both differ, heuristic returns the FIRST differing position (0).
    // This may not always be correct - for fold, position 1 (xs) is typically
    // the structurally decreasing arg. However, additional type analysis during
    // elaboration handles this case - this heuristic is just a first guess.
    let calls = vec![RecursiveCall {
        args: vec![
            RecursiveArg::Var("new_acc".to_string()), // different from "acc"
            RecursiveArg::Var("tail".to_string()),    // different from "xs"
        ],
    }];
    let param_names = vec!["acc".to_string(), "xs".to_string()];
    // Returns first differing position - may need refinement for acc patterns
    assert_eq!(find_decreasing_arg(&calls, &param_names, None), Some(0));
}

#[test]
fn test_detect_recursion_through_lift_method() {
    // def f x := do let y <- f x; pure y
    // The recursive call `f x` is wrapped in LiftMethod(<- f x)
    let recursive_call = SurfaceExpr::App(
        dummy_span(),
        Box::new(SurfaceExpr::Ident(dummy_span(), "f".to_string())),
        vec![SurfaceArg::positional(SurfaceExpr::Ident(
            dummy_span(),
            "x".to_string(),
        ))],
    );
    let body = SurfaceExpr::LiftMethod(dummy_span(), Box::new(recursive_call));
    let info = detect_recursion("f", &body);
    assert!(
        info.is_recursive,
        "Should detect recursive call through LiftMethod wrapper"
    );
    assert_eq!(info.calls.len(), 1);
    assert!(matches!(info.calls[0].args[0], RecursiveArg::Var(ref n) if n == "x"));
}

#[test]
fn test_detect_recursion_lift_method_no_call() {
    // def f x := do let y <- g x; pure y
    // LiftMethod wraps a non-recursive call - should not detect recursion
    let non_recursive_call = SurfaceExpr::App(
        dummy_span(),
        Box::new(SurfaceExpr::Ident(dummy_span(), "g".to_string())),
        vec![SurfaceArg::positional(SurfaceExpr::Ident(
            dummy_span(),
            "x".to_string(),
        ))],
    );
    let body = SurfaceExpr::LiftMethod(dummy_span(), Box::new(non_recursive_call));
    let info = detect_recursion("f", &body);
    assert!(
        !info.is_recursive,
        "Should not detect recursion for non-recursive LiftMethod"
    );
    assert!(info.calls.is_empty());
}

#[test]
fn test_detect_recursion_nested_lift_method_in_app() {
    // def f x := h (<- f x)
    // App(h, [LiftMethod(App(f, [x]))])
    let recursive_call = SurfaceExpr::App(
        dummy_span(),
        Box::new(SurfaceExpr::Ident(dummy_span(), "f".to_string())),
        vec![SurfaceArg::positional(SurfaceExpr::Ident(
            dummy_span(),
            "x".to_string(),
        ))],
    );
    let body = SurfaceExpr::App(
        dummy_span(),
        Box::new(SurfaceExpr::Ident(dummy_span(), "h".to_string())),
        vec![SurfaceArg::positional(SurfaceExpr::LiftMethod(
            dummy_span(),
            Box::new(recursive_call),
        ))],
    );
    let info = detect_recursion("f", &body);
    assert!(
        info.is_recursive,
        "Should detect recursion through LiftMethod nested in App argument"
    );
    assert_eq!(info.calls.len(), 1);
}
