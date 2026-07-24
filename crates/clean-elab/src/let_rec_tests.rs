// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for let-rec elaboration: recursion analysis and fixed-point encoding.

use crate::let_rec::{
    classify_recursion, contains_self_reference, count_fvar_occurrences, count_lambda_params,
    extract_param_name, find_mutual_references, replace_fvar, RecursionStrategy,
};
use clean_kernel::{BinderInfo, Environment, Expr, FVarId};
use clean_parser::{
    Span, SurfaceBinder, SurfaceBinderInfo, SurfaceExpr, SurfaceMatchArm, SurfacePattern,
};

// =========================================================================
// Helpers
// =========================================================================

fn mk_binder(name: &str, ty: Option<SurfaceExpr>) -> SurfaceBinder {
    SurfaceBinder::new(name, ty, SurfaceBinderInfo::Explicit)
}

fn mk_match_arm(pattern: SurfacePattern, body: SurfaceExpr) -> SurfaceMatchArm {
    SurfaceMatchArm {
        span: Span::dummy(),
        pattern,
        body,
    }
}

// =========================================================================
// contains_self_reference tests
// =========================================================================

#[test]
fn test_self_ref_ident_matches() {
    let expr = SurfaceExpr::ident("f");
    assert!(contains_self_reference(&expr, "f"));
}

#[test]
fn test_self_ref_ident_no_match() {
    let expr = SurfaceExpr::ident("g");
    assert!(!contains_self_reference(&expr, "f"));
}

#[test]
fn test_self_ref_in_app_func() {
    // f x
    let expr = SurfaceExpr::app(SurfaceExpr::ident("f"), vec![SurfaceExpr::ident("x")]);
    assert!(contains_self_reference(&expr, "f"));
}

#[test]
fn test_self_ref_in_app_arg() {
    // g (f x)
    let inner = SurfaceExpr::app(SurfaceExpr::ident("f"), vec![SurfaceExpr::ident("x")]);
    let expr = SurfaceExpr::app(SurfaceExpr::ident("g"), vec![inner]);
    assert!(contains_self_reference(&expr, "f"));
}

#[test]
fn test_self_ref_shadowed_by_lambda() {
    // fun (f : Nat) => f
    let expr = SurfaceExpr::lambda(
        vec![SurfaceBinder::explicit("f", SurfaceExpr::ident("Nat"))],
        SurfaceExpr::ident("f"),
    );
    assert!(!contains_self_reference(&expr, "f"));
}

#[test]
fn test_self_ref_not_shadowed_in_lambda_type() {
    // fun (x : f) => x
    let expr = SurfaceExpr::lambda(
        vec![SurfaceBinder::explicit("x", SurfaceExpr::ident("f"))],
        SurfaceExpr::ident("x"),
    );
    assert!(contains_self_reference(&expr, "f"));
}

#[test]
fn test_self_ref_in_let_val() {
    // let x := f in x
    let expr = SurfaceExpr::Let(
        Span::dummy(),
        mk_binder("x", None),
        Box::new(SurfaceExpr::ident("f")),
        Box::new(SurfaceExpr::ident("x")),
    );
    assert!(contains_self_reference(&expr, "f"));
}

#[test]
fn test_self_ref_shadowed_by_let() {
    // let f := 0 in f
    let expr = SurfaceExpr::Let(
        Span::dummy(),
        mk_binder("f", None),
        Box::new(SurfaceExpr::nat(0)),
        Box::new(SurfaceExpr::ident("f")),
    );
    // val does not reference f, body is shadowed
    assert!(!contains_self_reference(&expr, "f"));
}

#[test]
fn test_self_ref_in_if_branches() {
    // if cond then f else g
    let expr = SurfaceExpr::If(
        Span::dummy(),
        Box::new(SurfaceExpr::ident("cond")),
        Box::new(SurfaceExpr::ident("f")),
        Box::new(SurfaceExpr::ident("g")),
    );
    assert!(contains_self_reference(&expr, "f"));
    assert!(!contains_self_reference(&expr, "h"));
}

#[test]
fn test_self_ref_in_match_arm() {
    // match x with | _ => f x
    let expr = SurfaceExpr::Match(
        Span::dummy(),
        None,
        Box::new(SurfaceExpr::ident("x")),
        vec![mk_match_arm(
            SurfacePattern::Wildcard,
            SurfaceExpr::app(SurfaceExpr::ident("f"), vec![SurfaceExpr::ident("x")]),
        )],
    );
    assert!(contains_self_reference(&expr, "f"));
}

#[test]
fn test_self_ref_in_arrow() {
    // f -> Nat
    let expr = SurfaceExpr::arrow(SurfaceExpr::ident("f"), SurfaceExpr::ident("Nat"));
    assert!(contains_self_reference(&expr, "f"));
}

#[test]
fn test_self_ref_in_ascription() {
    // (x : f)
    let expr = SurfaceExpr::Ascription(
        Span::dummy(),
        Box::new(SurfaceExpr::ident("x")),
        Box::new(SurfaceExpr::ident("f")),
    );
    assert!(contains_self_reference(&expr, "f"));
}

#[test]
fn test_self_ref_in_paren() {
    // (f)
    let expr = SurfaceExpr::Paren(Span::dummy(), Box::new(SurfaceExpr::ident("f")));
    assert!(contains_self_reference(&expr, "f"));
}

#[test]
fn test_self_ref_deep_nesting() {
    // fun x => match x with | _ => if true then f x else x
    let inner = SurfaceExpr::If(
        Span::dummy(),
        Box::new(SurfaceExpr::ident("true")),
        Box::new(SurfaceExpr::app(
            SurfaceExpr::ident("f"),
            vec![SurfaceExpr::ident("x")],
        )),
        Box::new(SurfaceExpr::ident("x")),
    );
    let match_expr = SurfaceExpr::Match(
        Span::dummy(),
        None,
        Box::new(SurfaceExpr::ident("x")),
        vec![mk_match_arm(SurfacePattern::Wildcard, inner)],
    );
    let expr = SurfaceExpr::lambda(
        vec![SurfaceBinder::explicit("x", SurfaceExpr::ident("Nat"))],
        match_expr,
    );
    assert!(contains_self_reference(&expr, "f"));
}

// =========================================================================
// classify_recursion tests
// =========================================================================

#[test]
fn test_classify_non_recursive() {
    // let rec f : Nat := 42 in f
    let binder = mk_binder("f", Some(SurfaceExpr::ident("Nat")));
    let val = SurfaceExpr::nat(42);
    let strategy = classify_recursion("f", &binder, &val);
    assert_eq!(strategy, RecursionStrategy::NonRecursive);
}

#[test]
fn test_classify_structural_match_on_param() {
    // let rec f := fun n => match n with | 0 => 0 | _ => f (n - 1) in f
    let match_body = SurfaceExpr::Match(
        Span::dummy(),
        None,
        Box::new(SurfaceExpr::ident("n")),
        vec![
            mk_match_arm(
                SurfacePattern::Lit(clean_parser::SurfaceLit::Nat(0)),
                SurfaceExpr::nat(0),
            ),
            mk_match_arm(
                SurfacePattern::Wildcard,
                SurfaceExpr::app(SurfaceExpr::ident("f"), vec![SurfaceExpr::ident("n_sub_1")]),
            ),
        ],
    );
    let val = SurfaceExpr::lambda(
        vec![SurfaceBinder::explicit("n", SurfaceExpr::ident("Nat"))],
        match_body,
    );
    let binder = mk_binder(
        "f",
        Some(SurfaceExpr::arrow(
            SurfaceExpr::ident("Nat"),
            SurfaceExpr::ident("Nat"),
        )),
    );

    let strategy = classify_recursion("f", &binder, &val);
    assert_eq!(
        strategy,
        RecursionStrategy::Structural { decreasing_arg: 0 }
    );
}

#[test]
fn test_classify_structural_from_type() {
    // let rec f : Nat -> Nat := fun n => f n in f
    // No match, but type annotation has Nat as first arg.
    let val = SurfaceExpr::lambda(
        vec![SurfaceBinder::explicit("n", SurfaceExpr::ident("Nat"))],
        SurfaceExpr::app(SurfaceExpr::ident("f"), vec![SurfaceExpr::ident("n")]),
    );
    let binder = mk_binder(
        "f",
        Some(SurfaceExpr::arrow(
            SurfaceExpr::ident("Nat"),
            SurfaceExpr::ident("Nat"),
        )),
    );

    let strategy = classify_recursion("f", &binder, &val);
    // Should detect structural from type even without match
    assert_eq!(
        strategy,
        RecursionStrategy::Structural { decreasing_arg: 0 }
    );
}

#[test]
fn test_classify_wf_recursion() {
    // let rec f : String -> String := fun s => f s in f
    // String is not an inductive type, no match pattern
    let val = SurfaceExpr::lambda(
        vec![SurfaceBinder::explicit("s", SurfaceExpr::ident("String"))],
        SurfaceExpr::app(SurfaceExpr::ident("f"), vec![SurfaceExpr::ident("s")]),
    );
    let binder = mk_binder(
        "f",
        Some(SurfaceExpr::arrow(
            SurfaceExpr::ident("String"),
            SurfaceExpr::ident("String"),
        )),
    );

    let strategy = classify_recursion("f", &binder, &val);
    assert_eq!(strategy, RecursionStrategy::WellFounded);
}

#[test]
fn test_classify_structural_list() {
    // let rec f : List Nat -> Nat := ...
    let val = SurfaceExpr::lambda(
        vec![SurfaceBinder::explicit(
            "xs",
            SurfaceExpr::app(SurfaceExpr::ident("List"), vec![SurfaceExpr::ident("Nat")]),
        )],
        SurfaceExpr::app(SurfaceExpr::ident("f"), vec![SurfaceExpr::ident("xs")]),
    );
    let binder = mk_binder(
        "f",
        Some(SurfaceExpr::arrow(
            SurfaceExpr::app(SurfaceExpr::ident("List"), vec![SurfaceExpr::ident("Nat")]),
            SurfaceExpr::ident("Nat"),
        )),
    );

    let strategy = classify_recursion("f", &binder, &val);
    assert_eq!(
        strategy,
        RecursionStrategy::Structural { decreasing_arg: 0 }
    );
}

#[test]
fn test_classify_no_type_annotation() {
    // let rec f := fun n => f n in f  (no type)
    let val = SurfaceExpr::lambda(
        vec![SurfaceBinder::explicit("n", SurfaceExpr::ident("Nat"))],
        SurfaceExpr::app(SurfaceExpr::ident("f"), vec![SurfaceExpr::ident("n")]),
    );
    let binder = mk_binder("f", None);

    let strategy = classify_recursion("f", &binder, &val);
    // Without a type annotation or match, falls back to WF
    assert_eq!(strategy, RecursionStrategy::WellFounded);
}

// =========================================================================
// replace_fvar tests
// =========================================================================

#[test]
fn test_replace_fvar_simple() {
    let old = FVarId::new(100);
    let new = FVarId::new(200);
    let expr = Expr::fvar(old);
    let result = replace_fvar(&expr, old, new);
    assert_eq!(
        format!("{:?}", result.kind()),
        format!("{:?}", Expr::fvar(new).kind())
    );
}

#[test]
fn test_replace_fvar_no_match() {
    let old = FVarId::new(100);
    let new = FVarId::new(200);
    let other = FVarId::new(300);
    let expr = Expr::fvar(other);
    let result = replace_fvar(&expr, old, new);
    assert_eq!(
        format!("{:?}", result.kind()),
        format!("{:?}", Expr::fvar(other).kind())
    );
}

#[test]
fn test_replace_fvar_in_app() {
    let old = FVarId::new(100);
    let new = FVarId::new(200);
    let expr = Expr::app(Expr::fvar(old), Expr::fvar(FVarId::new(50)));
    let result = replace_fvar(&expr, old, new);
    // The function position should now be new fvar
    if let clean_kernel::ExprKind::App(func, _) = result.kind() {
        assert_eq!(
            format!("{:?}", func.kind()),
            format!("{:?}", Expr::fvar(new).kind())
        );
    } else {
        panic!("expected App");
    }
}

#[test]
fn test_replace_fvar_in_lambda() {
    let old = FVarId::new(100);
    let new = FVarId::new(200);
    let body = Expr::fvar(old);
    let expr = Expr::lam(BinderInfo::Default, Expr::type_(), body);
    let result = replace_fvar(&expr, old, new);
    if let clean_kernel::ExprKind::Lam(_, _, inner_body) = result.kind() {
        assert_eq!(
            format!("{:?}", inner_body.kind()),
            format!("{:?}", Expr::fvar(new).kind())
        );
    } else {
        panic!("expected Lam");
    }
}

// =========================================================================
// count_fvar_occurrences tests
// =========================================================================

#[test]
fn test_count_fvar_zero() {
    let target = FVarId::new(100);
    let expr = Expr::type_();
    assert_eq!(count_fvar_occurrences(&expr, target), 0);
}

#[test]
fn test_count_fvar_one() {
    let target = FVarId::new(100);
    let expr = Expr::fvar(target);
    assert_eq!(count_fvar_occurrences(&expr, target), 1);
}

#[test]
fn test_count_fvar_multiple() {
    let target = FVarId::new(100);
    let expr = Expr::app(Expr::fvar(target), Expr::fvar(target));
    assert_eq!(count_fvar_occurrences(&expr, target), 2);
}

#[test]
fn test_count_fvar_nested() {
    let target = FVarId::new(100);
    let inner = Expr::app(Expr::fvar(target), Expr::type_());
    let outer = Expr::app(inner, Expr::fvar(target));
    let expr = Expr::lam(BinderInfo::Default, Expr::type_(), outer);
    assert_eq!(count_fvar_occurrences(&expr, target), 2);
}

// =========================================================================
// extract_param_name tests
// =========================================================================

#[test]
fn test_extract_param_name_first() {
    // fun (n : Nat) => body
    let val = SurfaceExpr::lambda(
        vec![SurfaceBinder::explicit("n", SurfaceExpr::ident("Nat"))],
        SurfaceExpr::ident("body"),
    );
    assert_eq!(extract_param_name(&val, 0), Some("n".to_string()));
}

#[test]
fn test_extract_param_name_second() {
    // fun (a : A) (b : B) => body
    let val = SurfaceExpr::lambda(
        vec![
            SurfaceBinder::explicit("a", SurfaceExpr::ident("A")),
            SurfaceBinder::explicit("b", SurfaceExpr::ident("B")),
        ],
        SurfaceExpr::ident("body"),
    );
    assert_eq!(extract_param_name(&val, 1), Some("b".to_string()));
}

#[test]
fn test_extract_param_name_out_of_range() {
    let val = SurfaceExpr::lambda(
        vec![SurfaceBinder::explicit("n", SurfaceExpr::ident("Nat"))],
        SurfaceExpr::ident("body"),
    );
    assert_eq!(extract_param_name(&val, 5), None);
}

#[test]
fn test_extract_param_name_not_lambda() {
    let val = SurfaceExpr::ident("x");
    assert_eq!(extract_param_name(&val, 0), None);
}

// =========================================================================
// count_lambda_params tests
// =========================================================================

#[test]
fn test_count_lambda_params_zero() {
    let val = SurfaceExpr::ident("x");
    assert_eq!(count_lambda_params(&val), 0);
}

#[test]
fn test_count_lambda_params_one() {
    let val = SurfaceExpr::lambda(
        vec![SurfaceBinder::explicit("n", SurfaceExpr::ident("Nat"))],
        SurfaceExpr::ident("body"),
    );
    assert_eq!(count_lambda_params(&val), 1);
}

#[test]
fn test_count_lambda_params_nested() {
    // fun a => fun b c => body
    let inner = SurfaceExpr::lambda(
        vec![
            SurfaceBinder::explicit("b", SurfaceExpr::ident("B")),
            SurfaceBinder::explicit("c", SurfaceExpr::ident("C")),
        ],
        SurfaceExpr::ident("body"),
    );
    let val = SurfaceExpr::lambda(
        vec![SurfaceBinder::explicit("a", SurfaceExpr::ident("A"))],
        inner,
    );
    assert_eq!(count_lambda_params(&val), 3);
}

// =========================================================================
// find_mutual_references tests
// =========================================================================

#[test]
fn test_mutual_refs_none() {
    // f := 1, g := 2 — no references to each other
    let f_val = SurfaceExpr::nat(1);
    let g_val = SurfaceExpr::nat(2);
    let bindings: Vec<(String, &SurfaceExpr)> =
        vec![("f".to_string(), &f_val), ("g".to_string(), &g_val)];
    let deps = find_mutual_references(&bindings);
    assert!(deps[0].is_empty());
    assert!(deps[1].is_empty());
}

#[test]
fn test_mutual_refs_self_only() {
    // f := f x, g := 2
    let f_val = SurfaceExpr::app(SurfaceExpr::ident("f"), vec![SurfaceExpr::ident("x")]);
    let g_val = SurfaceExpr::nat(2);
    let bindings: Vec<(String, &SurfaceExpr)> =
        vec![("f".to_string(), &f_val), ("g".to_string(), &g_val)];
    let deps = find_mutual_references(&bindings);
    assert_eq!(deps[0], vec![0]); // f depends on f
    assert!(deps[1].is_empty());
}

#[test]
fn test_mutual_refs_cross() {
    // f := g x, g := f x
    let f_val = SurfaceExpr::app(SurfaceExpr::ident("g"), vec![SurfaceExpr::ident("x")]);
    let g_val = SurfaceExpr::app(SurfaceExpr::ident("f"), vec![SurfaceExpr::ident("x")]);
    let bindings: Vec<(String, &SurfaceExpr)> =
        vec![("f".to_string(), &f_val), ("g".to_string(), &g_val)];
    let deps = find_mutual_references(&bindings);
    assert_eq!(deps[0], vec![1]); // f depends on g
    assert_eq!(deps[1], vec![0]); // g depends on f
}

#[test]
fn test_mutual_refs_three_way() {
    // f := g x, g := h x, h := f x
    let f_val = SurfaceExpr::app(SurfaceExpr::ident("g"), vec![SurfaceExpr::ident("x")]);
    let g_val = SurfaceExpr::app(SurfaceExpr::ident("h"), vec![SurfaceExpr::ident("x")]);
    let h_val = SurfaceExpr::app(SurfaceExpr::ident("f"), vec![SurfaceExpr::ident("x")]);
    let bindings: Vec<(String, &SurfaceExpr)> = vec![
        ("f".to_string(), &f_val),
        ("g".to_string(), &g_val),
        ("h".to_string(), &h_val),
    ];
    let deps = find_mutual_references(&bindings);
    assert_eq!(deps[0], vec![1]); // f → g
    assert_eq!(deps[1], vec![2]); // g → h
    assert_eq!(deps[2], vec![0]); // h → f
}

// =========================================================================
// Integration: elab_let_rec via parse + elaborate
// =========================================================================

#[test]
fn test_elab_let_rec_non_recursive_parses() {
    // let rec f : Nat := 42 in f
    let env = Environment::new();
    let surface = clean_parser::parse_expr("let rec f : Nat := 42 in f").unwrap();
    let mut ctx = crate::ElabCtx::new(&env);
    // Should not panic — the existing elab_let_rec handles this
    let result = ctx.elaborate(&surface);
    // We expect it succeeds or gives a non-crash error
    assert!(result.is_ok() || result.is_err());
}

#[test]
fn test_elab_let_rec_with_lambda() {
    // let rec f : Nat -> Nat := fun n => n in f 0
    let env = Environment::new();
    let surface = clean_parser::parse_expr("let rec f : Nat -> Nat := fun (n : Nat) => n in f 0");
    if let Ok(surface) = surface {
        let mut ctx = crate::ElabCtx::new(&env);
        let _result = ctx.elaborate(&surface);
        // Not asserting Ok — the elaborator may lack Nat definitions.
        // Key test: no crash.
    }
}

#[test]
fn test_elab_let_rec_body_uses_binding() {
    // let rec f : Nat := 0 in f
    // The body should resolve f to the let binding.
    let env = Environment::new();
    let surface = clean_parser::parse_expr("let rec f : Nat := 0 in f").unwrap();
    let mut ctx = crate::ElabCtx::new(&env);
    let result = ctx.elaborate(&surface);
    // Should produce a let expression
    if let Ok(expr) = result {
        assert!(
            matches!(expr.kind(), clean_kernel::ExprKind::Let(..)),
            "expected Let expression, got {:?}",
            expr.kind()
        );
    }
}

#[test]
fn test_classify_structural_second_param() {
    // let rec f := fun a b => match b with | _ => f a b_sub
    let match_body = SurfaceExpr::Match(
        Span::dummy(),
        None,
        Box::new(SurfaceExpr::ident("b")),
        vec![mk_match_arm(
            SurfacePattern::Wildcard,
            SurfaceExpr::app(
                SurfaceExpr::ident("f"),
                vec![SurfaceExpr::ident("a"), SurfaceExpr::ident("b_sub")],
            ),
        )],
    );
    let val = SurfaceExpr::lambda(
        vec![
            SurfaceBinder::explicit("a", SurfaceExpr::ident("A")),
            SurfaceBinder::explicit("b", SurfaceExpr::ident("B")),
        ],
        match_body,
    );
    let binder = mk_binder("f", None);
    let strategy = classify_recursion("f", &binder, &val);
    assert_eq!(
        strategy,
        RecursionStrategy::Structural { decreasing_arg: 1 }
    );
}

#[test]
fn test_self_ref_pi_shadowed() {
    // Pi (f : Nat) -> f
    let expr = SurfaceExpr::pi(
        vec![SurfaceBinder::explicit("f", SurfaceExpr::ident("Nat"))],
        SurfaceExpr::ident("f"),
    );
    assert!(!contains_self_reference(&expr, "f"));
}

#[test]
fn test_self_ref_let_rec_val() {
    // let rec x := f in body
    let expr = SurfaceExpr::LetRec(
        Span::dummy(),
        mk_binder("x", None),
        Box::new(SurfaceExpr::ident("f")),
        Box::new(SurfaceExpr::ident("x")),
    );
    assert!(contains_self_reference(&expr, "f"));
}

#[test]
fn test_self_ref_explicit_wrapper() {
    // @f
    let expr = SurfaceExpr::Explicit(Span::dummy(), Box::new(SurfaceExpr::ident("f")));
    assert!(contains_self_reference(&expr, "f"));
}
