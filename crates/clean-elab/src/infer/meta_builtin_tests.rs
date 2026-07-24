// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Unit tests for the metaprogram value-constructor rewrite.
//!
//! These pin the *syntactic* rewrite from `mkConst`/`mkApp`/`Expr.*` builtin
//! calls to the equivalent ordinary surface expression. End-to-end
//! elaboration + kernel-check of a constructor-style body is exercised in
//! `tests/user_tactic_exec.rs`.

use super::*;
use clean_parser::{Projection, Span, SurfaceArg, SurfaceExpr};

fn ident(name: &str) -> SurfaceExpr {
    SurfaceExpr::Ident(Span::dummy(), name.to_owned())
}

fn name_lit(name: &str) -> SurfaceExpr {
    SurfaceExpr::SyntaxQuote(Span::dummy(), name.to_owned())
}

fn app(head: SurfaceExpr, args: Vec<SurfaceExpr>) -> SurfaceExpr {
    SurfaceExpr::App(
        Span::dummy(),
        Box::new(head),
        args.into_iter().map(SurfaceArg::positional).collect(),
    )
}

fn proj(base: &str, field: &str) -> SurfaceExpr {
    SurfaceExpr::Proj(
        Span::dummy(),
        Box::new(ident(base)),
        Projection::Named(field.to_owned()),
    )
}

#[test]
fn test_mkconst_rewrites_to_ident() {
    // `mkConst `Nat.zero`  =>  `Nat.zero`
    let body = app(ident("mkConst"), vec![name_lit("Nat.zero")]);
    let out = rewrite_meta_builtins(&body).expect("mkConst is a recognized builtin");
    assert!(
        matches!(&out, SurfaceExpr::Ident(_, n) if n == "Nat.zero"),
        "mkConst `Nat.zero should rewrite to the identifier Nat.zero, got {out:?}"
    );
}

#[test]
fn test_mkconst_with_levels_drops_levels() {
    // `mkConst `Foo bar`  =>  `Foo` (the level-list argument is dropped)
    let body = app(ident("mkConst"), vec![name_lit("Foo"), ident("bar")]);
    let out = rewrite_meta_builtins(&body).expect("mkConst/2 is recognized");
    assert!(
        matches!(&out, SurfaceExpr::Ident(_, n) if n == "Foo"),
        "mkConst `Foo us should rewrite to Foo, got {out:?}"
    );
}

#[test]
fn test_mkapp_rewrites_to_application() {
    // `mkApp f x`  =>  `f x`
    let body = app(ident("mkApp"), vec![ident("f"), ident("x")]);
    let out = rewrite_meta_builtins(&body).expect("mkApp is recognized");
    let SurfaceExpr::App(_, func, args) = out else {
        panic!("expected an application, got something else");
    };
    assert!(matches!(func.as_ref(), SurfaceExpr::Ident(_, n) if n == "f"));
    assert_eq!(args.len(), 1);
    assert!(matches!(&args[0].expr, SurfaceExpr::Ident(_, n) if n == "x"));
}

#[test]
fn test_nested_mkapp_mkconst_collapses() {
    // `mkApp (mkConst `Nat.succ) (mkConst `Nat.zero)`  =>  `Nat.succ Nat.zero`
    let inner_succ = app(ident("mkConst"), vec![name_lit("Nat.succ")]);
    let inner_zero = app(ident("mkConst"), vec![name_lit("Nat.zero")]);
    let body = app(ident("mkApp"), vec![inner_succ, inner_zero]);
    let out = rewrite_meta_builtins(&body).expect("nested builtins are recognized");
    let SurfaceExpr::App(_, func, args) = out else {
        panic!("expected an application");
    };
    assert!(
        matches!(func.as_ref(), SurfaceExpr::Ident(_, n) if n == "Nat.succ"),
        "head should collapse to Nat.succ, got {func:?}"
    );
    assert_eq!(args.len(), 1);
    assert!(
        matches!(&args[0].expr, SurfaceExpr::Ident(_, n) if n == "Nat.zero"),
        "arg should collapse to Nat.zero"
    );
}

#[test]
fn test_mkapp3_rewrites_three_args() {
    // `mkApp3 f a b c`  =>  `f a b c`
    let body = app(
        ident("mkApp3"),
        vec![ident("f"), ident("a"), ident("b"), ident("c")],
    );
    let out = rewrite_meta_builtins(&body).expect("mkApp3 is recognized");
    let SurfaceExpr::App(_, func, args) = out else {
        panic!("expected an application");
    };
    assert!(matches!(func.as_ref(), SurfaceExpr::Ident(_, n) if n == "f"));
    assert_eq!(args.len(), 3, "mkApp3 should apply three arguments");
}

#[test]
fn test_expr_const_projection_rewrites_to_ident() {
    // `Expr.const `Foo bar`  =>  `Foo`
    let body = app(proj("Expr", "const"), vec![name_lit("Foo"), ident("bar")]);
    let out = rewrite_meta_builtins(&body).expect("Expr.const is recognized");
    assert!(
        matches!(&out, SurfaceExpr::Ident(_, n) if n == "Foo"),
        "Expr.const `Foo us should rewrite to Foo, got {out:?}"
    );
}

#[test]
fn test_expr_app_projection_rewrites_to_application() {
    // `Expr.app f x`  =>  `f x`
    let body = app(proj("Expr", "app"), vec![ident("f"), ident("x")]);
    let out = rewrite_meta_builtins(&body).expect("Expr.app is recognized");
    assert!(
        matches!(&out, SurfaceExpr::App(_, _, args) if args.len() == 1),
        "Expr.app f x should rewrite to the application f x, got {out:?}"
    );
}

#[test]
fn test_no_builtin_returns_none() {
    // An ordinary body with no builtins is left untouched (None) so the caller
    // keeps the original and avoids an allocation.
    let body = app(ident("Nat.succ"), vec![ident("Nat.zero")]);
    assert!(
        rewrite_meta_builtins(&body).is_none(),
        "a body with no builtin call must not be rewritten"
    );
}

#[test]
fn test_mkconst_wrong_arity_is_not_rewritten() {
    // `mkConst` with three args is not the recognized shape; defer (None) so the
    // normal pipeline reports the unknown identifier honestly.
    let body = app(
        ident("mkConst"),
        vec![name_lit("Foo"), ident("a"), ident("b")],
    );
    assert!(
        rewrite_meta_builtins(&body).is_none(),
        "mkConst with wrong arity must defer rather than guess"
    );
}

#[test]
fn test_mkconst_non_name_literal_defers() {
    // `mkConst x` where `x` is not a name literal is not the recognized shape.
    let body = app(ident("mkConst"), vec![ident("x")]);
    assert!(
        rewrite_meta_builtins(&body).is_none(),
        "mkConst applied to a non-literal must defer"
    );
}

#[test]
fn test_builtin_under_application_arg_is_rewritten() {
    // `f (mkConst `Nat.zero)`  =>  `f Nat.zero` — a builtin nested in an argument
    // position is rewritten while the surrounding application is preserved.
    let inner = app(ident("mkConst"), vec![name_lit("Nat.zero")]);
    let body = app(ident("f"), vec![inner]);
    let out = rewrite_meta_builtins(&body).expect("nested-arg builtin is recognized");
    let SurfaceExpr::App(_, func, args) = out else {
        panic!("expected an application");
    };
    assert!(matches!(func.as_ref(), SurfaceExpr::Ident(_, n) if n == "f"));
    assert!(
        matches!(&args[0].expr, SurfaceExpr::Ident(_, n) if n == "Nat.zero"),
        "the nested mkConst should collapse to Nat.zero"
    );
}

#[test]
fn test_mkapp_with_named_arg_defers() {
    // A named argument (`mkApp (f := g) x`) does not match the flat positional
    // builtin shape; defer so it falls through to normal handling.
    let named = SurfaceArg {
        span: Span::dummy(),
        expr: ident("g"),
        name: Some("f".to_owned()),
    };
    let body = SurfaceExpr::App(
        Span::dummy(),
        Box::new(ident("mkApp")),
        vec![named, SurfaceArg::positional(ident("x"))],
    );
    assert!(
        rewrite_meta_builtins(&body).is_none(),
        "a named-argument call must not be treated as the positional builtin"
    );
}

// ---------------------------------------------------------------------------
// Binder builtins: `mkLambda` / `mkForall` / `Expr.lam` / `Expr.forallE`.
// ---------------------------------------------------------------------------

#[test]
fn test_mklambda_rewrites_to_lambda() {
    // `mkLambda `x Nat (mkConst `Nat.zero)`  =>  `fun (x : Nat) => Nat.zero`
    let body = app(
        ident("mkLambda"),
        vec![
            name_lit("x"),
            ident("Nat"),
            app(ident("mkConst"), vec![name_lit("Nat.zero")]),
        ],
    );
    let out = rewrite_meta_builtins(&body).expect("mkLambda is a recognized builtin");
    let SurfaceExpr::Lambda(_, binders, lam_body) = out else {
        panic!("expected a lambda, got something else");
    };
    assert_eq!(binders.len(), 1, "single binder");
    assert_eq!(binders[0].name, "x", "binder name preserved");
    assert!(
        matches!(binders[0].ty.as_deref(), Some(SurfaceExpr::Ident(_, n)) if n == "Nat"),
        "binder type should be Nat"
    );
    assert!(
        matches!(lam_body.as_ref(), SurfaceExpr::Ident(_, n) if n == "Nat.zero"),
        "nested mkConst body should collapse to Nat.zero, got {lam_body:?}"
    );
}

#[test]
fn test_mkforall_rewrites_to_pi() {
    // `mkForall `x Nat (mkConst `Nat)`  =>  `(x : Nat) → Nat`
    let body = app(
        ident("mkForall"),
        vec![
            name_lit("x"),
            ident("Nat"),
            app(ident("mkConst"), vec![name_lit("Nat")]),
        ],
    );
    let out = rewrite_meta_builtins(&body).expect("mkForall is a recognized builtin");
    let SurfaceExpr::Pi(_, binders, pi_body) = out else {
        panic!("expected a Pi, got something else");
    };
    assert_eq!(binders.len(), 1);
    assert_eq!(binders[0].name, "x");
    assert!(
        matches!(pi_body.as_ref(), SurfaceExpr::Ident(_, n) if n == "Nat"),
        "Pi body should collapse to Nat, got {pi_body:?}"
    );
}

#[test]
fn test_expr_lam_with_trailing_binderinfo_drops_it() {
    // `Expr.lam `x Nat (mkConst `Nat.zero) BinderInfo.default`
    //   =>  `fun (x : Nat) => Nat.zero` (the trailing BinderInfo is dropped).
    let body = app(
        proj("Expr", "lam"),
        vec![
            name_lit("x"),
            ident("Nat"),
            app(ident("mkConst"), vec![name_lit("Nat.zero")]),
            proj("BinderInfo", "default"),
        ],
    );
    let out = rewrite_meta_builtins(&body).expect("Expr.lam/4 is recognized");
    let SurfaceExpr::Lambda(_, binders, lam_body) = out else {
        panic!("expected a lambda");
    };
    assert_eq!(binders[0].name, "x");
    assert!(matches!(lam_body.as_ref(), SurfaceExpr::Ident(_, n) if n == "Nat.zero"));
}

#[test]
fn test_mklambda_with_binderinfo_drops_second_arg() {
    // `mkLambda `x BinderInfo.default Nat (mkConst `Nat.zero)`
    //   =>  `fun (x : Nat) => Nat.zero` (the 2nd BinderInfo arg is dropped, per
    //   Lean's `mkLambda (n) (bi) (t) (b)` helper signature).
    let body = app(
        ident("mkLambda"),
        vec![
            name_lit("x"),
            proj("BinderInfo", "default"),
            ident("Nat"),
            app(ident("mkConst"), vec![name_lit("Nat.zero")]),
        ],
    );
    let out = rewrite_meta_builtins(&body).expect("mkLambda/4 is recognized");
    let SurfaceExpr::Lambda(_, binders, lam_body) = out else {
        panic!("expected a lambda");
    };
    assert_eq!(binders[0].name, "x");
    assert!(
        matches!(binders[0].ty.as_deref(), Some(SurfaceExpr::Ident(_, n)) if n == "Nat"),
        "type slot for mkLambda/4 should be the 3rd argument (Nat)"
    );
    assert!(matches!(lam_body.as_ref(), SurfaceExpr::Ident(_, n) if n == "Nat.zero"));
}

#[test]
fn test_expr_forall_projection_rewrites_to_pi() {
    // `Expr.forallE `x Nat (mkConst `Nat) BinderInfo.default`  =>  `(x : Nat) → Nat`
    let body = app(
        proj("Expr", "forallE"),
        vec![
            name_lit("x"),
            ident("Nat"),
            app(ident("mkConst"), vec![name_lit("Nat")]),
            proj("BinderInfo", "default"),
        ],
    );
    let out = rewrite_meta_builtins(&body).expect("Expr.forallE is recognized");
    assert!(
        matches!(&out, SurfaceExpr::Pi(_, binders, _) if binders.len() == 1 && binders[0].name == "x"),
        "Expr.forallE should rewrite to a Pi binding x, got {out:?}"
    );
}

#[test]
fn test_mklambda_non_name_literal_defers() {
    // `mkLambda x Nat Nat.zero` where the name slot is a bare ident (not a
    // `` `x `` literal) is not the recognized binder shape: the `mkLambda` head
    // is NOT lowered to a `Lambda` (it stays an application, so the normal
    // pipeline fails honestly with `UnknownIdent("mkLambda")`). The body here has
    // no nested builtin, so the whole rewrite is a no-op (`None`).
    let body = app(
        ident("mkLambda"),
        vec![ident("x"), ident("Nat"), ident("Nat.zero")],
    );
    assert!(
        rewrite_meta_builtins(&body).is_none(),
        "mkLambda with a non-literal name slot must not become a Lambda"
    );
}

#[test]
fn test_mklambda_non_name_literal_does_not_lower_to_lambda() {
    // Even when a nested builtin elsewhere triggers a rewrite, a `mkLambda` whose
    // name slot is not a literal must NOT be lowered to a `Lambda` — it stays an
    // application head so elaboration reports the unknown `mkLambda` honestly.
    let body = app(
        ident("mkLambda"),
        vec![
            ident("x"),
            ident("Nat"),
            app(ident("mkConst"), vec![name_lit("Nat.zero")]),
        ],
    );
    // The nested mkConst is rewritten, so the overall result IS Some(..), but the
    // outer node must remain an `App` headed by `mkLambda`, never a `Lambda`.
    let out = rewrite_meta_builtins(&body).expect("nested mkConst triggers a rewrite");
    assert!(
        !matches!(out, SurfaceExpr::Lambda(..)),
        "a non-literal-name mkLambda must not be lowered to a Lambda, got {out:?}"
    );
    assert!(
        matches!(&out, SurfaceExpr::App(_, head, _) if matches!(head.as_ref(), SurfaceExpr::Ident(_, n) if n == "mkLambda")),
        "the deferred mkLambda head must be preserved, got {out:?}"
    );
}

#[test]
fn test_mklambda_wrong_arity_defers() {
    // `mkLambda `x Nat` (arity 2) is neither the 3- nor 4-argument binder shape.
    let body = app(ident("mkLambda"), vec![name_lit("x"), ident("Nat")]);
    assert!(
        rewrite_meta_builtins(&body).is_none(),
        "mkLambda with arity 2 must defer"
    );
}

#[test]
fn test_mkappn_array_form_defers() {
    // Clean's parser drops the `#[…]` array literal in `mkAppN f #[a, b]`, so the
    // call arrives as `mkAppN f` (arity 1). `mkAppN` is intentionally NOT a
    // recognized builtin: it defers and fails honestly as `UnknownIdent`.
    let body = app(ident("mkAppN"), vec![ident("f")]);
    assert!(
        rewrite_meta_builtins(&body).is_none(),
        "mkAppN must defer — the general array form is not lowered"
    );
}

#[test]
fn test_lambda_under_application_arg_is_rewritten() {
    // A binder builtin nested in an argument position is rewritten while the
    // surrounding application is preserved.
    let inner = app(
        ident("mkLambda"),
        vec![
            name_lit("x"),
            ident("Nat"),
            app(ident("mkConst"), vec![name_lit("Nat.zero")]),
        ],
    );
    let body = app(ident("f"), vec![inner]);
    let out = rewrite_meta_builtins(&body).expect("nested binder builtin is recognized");
    let SurfaceExpr::App(_, func, args) = out else {
        panic!("expected an application");
    };
    assert!(matches!(func.as_ref(), SurfaceExpr::Ident(_, n) if n == "f"));
    assert!(
        matches!(&args[0].expr, SurfaceExpr::Lambda(_, _, _)),
        "the nested mkLambda should collapse to a lambda argument"
    );
}
