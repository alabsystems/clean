// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Unit tests for user term-elaborator recognition and substitution.

use super::*;
use clean_parser::{Span, SurfaceArg, SurfaceExpr};

fn ident(name: SurfaceName) -> SurfaceExpr {
    SurfaceExpr::Ident(Span::dummy(), name)
}

fn app(head: SurfaceName, args: Vec<SurfaceExpr>) -> SurfaceExpr {
    SurfaceExpr::App(
        Span::dummy(),
        Box::new(ident(head)),
        args.into_iter().map(SurfaceArg::positional).collect(),
    )
}

fn registry_with(
    kw: &str,
    bound_vars: &[SurfaceName],
    body: SurfaceExpr,
) -> HashMap<String, UserTermElab> {
    let mut m = HashMap::new();
    m.insert(
        kw.to_owned(),
        UserTermElab {
            bound_vars: bound_vars.to_vec(),
            body,
            optional_trailing: false,
        },
    );
    m
}

#[test]
fn test_match_user_term_call_app_head_matches() {
    let reg = registry_with(
        "mywrap",
        &[SurfaceName::generated_path("e")],
        ident(SurfaceName::generated_path("e")),
    );
    let call = app(
        SurfaceName::generated_path("mywrap"),
        vec![ident(SurfaceName::generated_path("x"))],
    );
    let (kw, args) =
        match_user_term_call(&call, &reg).expect("registered keyword head should match");
    assert_eq!(kw, "mywrap");
    assert_eq!(args.len(), 1);
}

#[test]
fn test_match_user_term_call_nullary_bare_ident() {
    let reg = registry_with(
        "myunit",
        &[],
        ident(SurfaceName::generated_path("Unit.unit")),
    );
    let call = ident(SurfaceName::generated_path("myunit"));
    let (kw, args) =
        match_user_term_call(&call, &reg).expect("nullary keyword should match bare ident");
    assert_eq!(kw, "myunit");
    assert!(args.is_empty());
}

#[test]
fn test_match_user_term_call_unknown_head_is_none() {
    let reg = registry_with(
        "mywrap",
        &[SurfaceName::generated_path("e")],
        ident(SurfaceName::generated_path("e")),
    );
    let call = app(
        SurfaceName::generated_path("notregistered"),
        vec![ident(SurfaceName::generated_path("x"))],
    );
    assert!(
        match_user_term_call(&call, &reg).is_none(),
        "an unregistered head must not be intercepted"
    );
}

#[test]
fn test_match_user_term_call_named_arg_is_deferred() {
    let reg = registry_with(
        "mywrap",
        &[SurfaceName::generated_path("e")],
        ident(SurfaceName::generated_path("e")),
    );
    let named = SurfaceArg {
        span: Span::dummy(),
        expr: ident(SurfaceName::generated_path("x")),
        name: Some(SurfaceName::generated_path("foo")),
    };
    let call = SurfaceExpr::App(
        Span::dummy(),
        Box::new(ident(SurfaceName::generated_path("mywrap"))),
        vec![named],
    );
    assert!(
        match_user_term_call(&call, &reg).is_none(),
        "named-argument calls do not map to the flat positional pattern"
    );
}

#[test]
fn test_build_substituted_body_replaces_bound_ident() {
    // elab "mywrap" e:term : term => e   applied to `x`  => `x`
    let entry = UserTermElab {
        bound_vars: vec![SurfaceName::generated_path("e")],
        body: ident(SurfaceName::generated_path("e")),
        optional_trailing: false,
    };
    let out = build_substituted_body(&entry, &[ident(SurfaceName::generated_path("x"))])
        .expect("matching arity should substitute");
    match out {
        SurfaceExpr::Ident(_, name) => {
            assert_eq!(name, SurfaceName::generated_path("x"))
        }
        other => panic!("expected the bound arg `x`, got {other:?}"),
    }
}

#[test]
fn test_build_substituted_body_into_application() {
    // elab "myid" e:term : term => f e   applied to `x`  => `f x`
    let entry = UserTermElab {
        bound_vars: vec![SurfaceName::generated_path("e")],
        body: app(
            SurfaceName::generated_path("f"),
            vec![ident(SurfaceName::generated_path("e"))],
        ),
        optional_trailing: false,
    };
    let out = build_substituted_body(&entry, &[ident(SurfaceName::generated_path("x"))])
        .expect("substitution into app");
    let SurfaceExpr::App(_, func, args) = out else {
        panic!("expected an application result");
    };
    assert!(
        matches!(func.as_ref(), SurfaceExpr::Ident(_, n) if n == &SurfaceName::generated_path("f"))
    );
    assert_eq!(args.len(), 1);
    assert!(
        matches!(&args[0].expr, SurfaceExpr::Ident(_, n) if n == &SurfaceName::generated_path("x"))
    );
}

#[test]
fn test_build_substituted_body_arity_mismatch_is_none() {
    let entry = UserTermElab {
        bound_vars: vec![SurfaceName::generated_path("e")],
        body: ident(SurfaceName::generated_path("e")),
        optional_trailing: false,
    };
    // Declared one bound var; called with two arguments.
    assert!(
        build_substituted_body(
            &entry,
            &[
                ident(SurfaceName::generated_path("x")),
                ident(SurfaceName::generated_path("y"))
            ]
        )
        .is_none(),
        "an arity mismatch defers to normal (error-reporting) elaboration"
    );
}

// ---------------------------------------------------------------------------
// Optional trailing binder (`x:term?`) — `build_substituted_body` arity rules.
// ---------------------------------------------------------------------------

#[test]
fn test_build_substituted_body_optional_trailing_present_binds_arg() {
    // elab "optw" x:term? : term => f x   applied to `y`  => `f y` (optional present).
    let entry = UserTermElab {
        bound_vars: vec![SurfaceName::generated_path("x")],
        body: app(
            SurfaceName::generated_path("f"),
            vec![ident(SurfaceName::generated_path("x"))],
        ),
        optional_trailing: true,
    };
    let out = build_substituted_body(&entry, &[ident(SurfaceName::generated_path("y"))])
        .expect("optional binder present (full arity) should substitute");
    let SurfaceExpr::App(_, _, args) = out else {
        panic!("expected an application result");
    };
    assert!(
        matches!(&args[0].expr, SurfaceExpr::Ident(_, n) if n == &SurfaceName::generated_path("y")),
        "the present optional argument should be bound into the body"
    );
}

#[test]
fn test_build_substituted_body_optional_trailing_absent_leaves_var_free() {
    // elab "optw" x:term? : term => f x   applied with NO args. The optional `x`
    // is absent, so it is left unsubstituted (stays the free ident `x`); a body
    // referencing it will fail honestly downstream, never fabricating a binding.
    let entry = UserTermElab {
        bound_vars: vec![SurfaceName::generated_path("x")],
        body: app(
            SurfaceName::generated_path("f"),
            vec![ident(SurfaceName::generated_path("x"))],
        ),
        optional_trailing: true,
    };
    let out = build_substituted_body(&entry, &[])
        .expect("optional binder absent (arity-1) should still substitute the prefix");
    let SurfaceExpr::App(_, _, args) = out else {
        panic!("expected an application result");
    };
    assert!(
        matches!(&args[0].expr, SurfaceExpr::Ident(_, n) if n == &SurfaceName::generated_path("x")),
        "the absent optional variable must be left as a free identifier, not fabricated"
    );
}

#[test]
fn test_build_substituted_body_optional_trailing_prefix_present_absent_optional() {
    // elab "kw" a:term b:term? : term => g a b   applied to `p` only. The mandatory
    // `a` binds to `p`; the optional `b` is absent and stays free.
    let entry = UserTermElab {
        bound_vars: vec![
            SurfaceName::generated_path("a"),
            SurfaceName::generated_path("b"),
        ],
        body: app(
            SurfaceName::generated_path("g"),
            vec![
                ident(SurfaceName::generated_path("a")),
                ident(SurfaceName::generated_path("b")),
            ],
        ),
        optional_trailing: true,
    };
    let out = build_substituted_body(&entry, &[ident(SurfaceName::generated_path("p"))])
        .expect("mandatory prefix present, optional absent should substitute the prefix");
    let SurfaceExpr::App(_, _, args) = out else {
        panic!("expected an application result");
    };
    assert!(
        matches!(&args[0].expr, SurfaceExpr::Ident(_, n) if n == &SurfaceName::generated_path("p")),
        "mandatory `a` should bind to `p`"
    );
    assert!(
        matches!(&args[1].expr, SurfaceExpr::Ident(_, n) if n == &SurfaceName::generated_path("b")),
        "absent optional `b` should remain the free ident `b`"
    );
}

#[test]
fn test_build_substituted_body_optional_trailing_too_few_args_is_none() {
    // With one mandatory + one optional binder, supplying ZERO args is two fewer
    // than declared — below even the optional-absent floor, so defer (None).
    let entry = UserTermElab {
        bound_vars: vec![
            SurfaceName::generated_path("a"),
            SurfaceName::generated_path("b"),
        ],
        body: app(
            SurfaceName::generated_path("g"),
            vec![
                ident(SurfaceName::generated_path("a")),
                ident(SurfaceName::generated_path("b")),
            ],
        ),
        optional_trailing: true,
    };
    assert!(
        build_substituted_body(&entry, &[]).is_none(),
        "fewer args than the mandatory prefix must defer, not bind partially"
    );
}
