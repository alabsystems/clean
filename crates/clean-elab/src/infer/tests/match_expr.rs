// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Match expression elaboration tests

use super::*;

fn count_const_occurrences(expr: &Expr, needle: &str) -> usize {
    match expr.kind() {
        ExprKind::Const(name, _) => usize::from(name.to_string() == needle),
        ExprKind::App(func, arg) => {
            count_const_occurrences(func, needle) + count_const_occurrences(arg, needle)
        }
        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
            count_const_occurrences(ty, needle) + count_const_occurrences(body, needle)
        }
        ExprKind::Let(_, ty, val, body, _) => {
            count_const_occurrences(ty, needle)
                + count_const_occurrences(val, needle)
                + count_const_occurrences(body, needle)
        }
        _ => 0,
    }
}

#[test]
fn test_match_single_arm_var_pattern() {
    // match e with | x => body
    // The macro system desugars this to (fun x => body) e
    // which is semantically equivalent to let x := e in body
    let expr = elab("match 42 with | x => x").unwrap();
    // Should produce either a let binding or an application of a lambda
    // (both are semantically equivalent)
    let is_let_like = matches!(expr.kind(), ExprKind::Let(_, _, _, _, _))
        || matches!(expr.kind(), ExprKind::App(func, _) if matches!(func.kind(), ExprKind::Lam(_, _, _)));
    assert!(is_let_like, "expected Let or App(Lam,...), got {expr:?}");
}

#[test]
fn test_match_single_arm_wildcard() {
    // match e with | _ => body
    // The macro system desugars this to (fun _ => body) e
    let expr = elab("match 42 with | _ => 0").unwrap();
    // Should produce either a let binding or an application of a lambda
    let is_let_like = matches!(expr.kind(), ExprKind::Let(_, _, _, _, _))
        || matches!(expr.kind(), ExprKind::App(func, _) if matches!(func.kind(), ExprKind::Lam(_, _, _)));
    assert!(is_let_like, "expected Let or App(Lam,...), got {expr:?}");
}

#[test]
fn test_match_single_arm_inaccessible_pattern_checks_scrutinee() {
    let accepted = elab("match 0 with | .(0) => 0");
    assert!(
        accepted.is_ok(),
        "matching inaccessible pattern should elaborate when it is defeq to the scrutinee, got {accepted:?}"
    );

    let rejected = elab("match 0 with | .(1) => 0");
    assert!(
        matches!(rejected, Err(ElabError::TypeMismatch { .. })),
        "wrong inaccessible pattern should be rejected instead of silently accepted, got {rejected:?}"
    );
}

#[test]
fn test_match_single_arm_inaccessible_pattern_uses_defeq_scrutinee() {
    let env = Environment::with_prelude();
    let accepted = elab_with_env(&env, "match (let x := 0; x) with | .(0) => 0");
    assert!(
        accepted.is_ok(),
        "inaccessible pattern should compare against the reduced scrutinee, got {accepted:?}"
    );

    let rejected = elab_with_env(&env, "match (let x := 0; x) with | .(1) => 0");
    assert!(
        matches!(rejected, Err(ElabError::TypeMismatch { .. })),
        "non-defeq inaccessible pattern should still be rejected for reduced scrutinees, got {rejected:?}"
    );
}

#[test]
fn test_match_multi_arm_top_level_inaccessible_fails_closed() {
    let env = Environment::with_prelude();
    let result = elab_with_env(&env, "match 0 with | .(0) => 0 | _ => 1");
    assert!(
        matches!(&result, Err(ElabError::NotImplemented(msg)) if msg.contains("top-level inaccessible patterns in multi-arm match")),
        "multi-arm top-level inaccessible patterns should not silently act as wildcard alternatives, got {result:?}"
    );
}

#[test]
fn test_match_ctor_nested_inaccessible_nat_literal_elaborates_as_field_pattern() {
    let mut env = Environment::with_prelude();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("n"),
        level_params: vec![],
        type_: Expr::const_(Name::from_string("Nat"), vec![]),
    })
    .unwrap();

    let expr = elab_with_env(&env, "match n with | Nat.succ .(0) => 1 | _ => 0")
        .expect("nested inaccessible Nat literal should elaborate as a checked field pattern");

    assert!(
        count_const_occurrences(&expr, "Nat.casesOn") >= 2,
        "expected nested inaccessible Nat literal to add a field-level Nat.casesOn, got {expr:?}"
    );
}

#[test]
fn test_match_ctor_nested_inaccessible_nullary_ctor_elaborates_as_field_pattern() {
    let mut env = Environment::with_prelude();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("n"),
        level_params: vec![],
        type_: Expr::const_(Name::from_string("Nat"), vec![]),
    })
    .unwrap();

    let expr = elab_with_env(&env, "match n with | Nat.succ .(Nat.zero) => 1 | _ => 0").expect(
        "nested inaccessible nullary constructor should elaborate as a checked field pattern",
    );

    assert!(
        count_const_occurrences(&expr, "Nat.casesOn") >= 2,
        "expected nested inaccessible nullary constructor to add a field-level Nat.casesOn, got {expr:?}"
    );
}

#[test]
fn test_match_ctor_nested_inaccessible_ctor_app_elaborates_as_field_pattern() {
    let mut env = Environment::with_prelude();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("n"),
        level_params: vec![],
        type_: Expr::const_(Name::from_string("Nat"), vec![]),
    })
    .unwrap();

    let expr = elab_with_env(
        &env,
        "match n with | Nat.succ .(Nat.succ Nat.zero) => 2 | _ => 0",
    )
    .expect(
        "nested inaccessible constructor application should elaborate as a checked field pattern",
    );

    assert!(
        count_const_occurrences(&expr, "Nat.casesOn") >= 3,
        "expected nested inaccessible constructor application to add nested field-level Nat.casesOn layers, got {expr:?}"
    );
}

#[test]
fn test_match_ctor_nested_inaccessible_ctor_app_uses_argument_field_type() {
    let mut env = Environment::with_prelude();
    let option_nat = Expr::app(
        Expr::const_(Name::from_string("Option"), vec![Level::zero()]),
        Expr::const_(Name::from_string("Nat"), vec![]),
    );
    let option_option_nat = Expr::app(
        Expr::const_(Name::from_string("Option"), vec![Level::zero()]),
        option_nat,
    );
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("o"),
        level_params: vec![],
        type_: option_option_nat,
    })
    .unwrap();

    let expr = elab_with_env(
        &env,
        "match o with | Option.some .(Option.some Nat.zero) => 1 | _ => 0",
    )
    .expect(
        "nested inaccessible constructor application arguments should use constructor field types",
    );

    assert!(
        count_const_occurrences(&expr, "Option.casesOn") >= 2
            && count_const_occurrences(&expr, "Nat.casesOn") >= 1,
        "expected inaccessible Option.some Nat.zero to lower through Option and Nat casesOn layers, got {expr:?}"
    );
}

#[test]
fn test_match_ctor_nested_inaccessible_unqualified_ctor_app() {
    let mut env = Environment::with_prelude();
    let option_nat = Expr::app(
        Expr::const_(Name::from_string("Option"), vec![Level::zero()]),
        Expr::const_(Name::from_string("Nat"), vec![]),
    );
    let option_option_nat = Expr::app(
        Expr::const_(Name::from_string("Option"), vec![Level::zero()]),
        option_nat,
    );
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("o"),
        level_params: vec![],
        type_: option_option_nat,
    })
    .unwrap();

    let expr = elab_with_env(
        &env,
        "match o with | Option.some .(some Nat.zero) => 1 | _ => 0",
    )
    .expect("nested inaccessible constructor applications should resolve unqualified field constructors");

    assert!(
        count_const_occurrences(&expr, "Option.casesOn") >= 2
            && count_const_occurrences(&expr, "Nat.casesOn") >= 1,
        "expected unqualified inaccessible constructor application to lower through Option and Nat casesOn layers, got {expr:?}"
    );
}

#[test]
fn test_match_ctor_nested_inaccessible_deep_ctor_app_uses_argument_field_types() {
    let mut env = Environment::with_prelude();
    let option_nat = Expr::app(
        Expr::const_(Name::from_string("Option"), vec![Level::zero()]),
        Expr::const_(Name::from_string("Nat"), vec![]),
    );
    let option_option_nat = Expr::app(
        Expr::const_(Name::from_string("Option"), vec![Level::zero()]),
        option_nat,
    );
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("o"),
        level_params: vec![],
        type_: option_option_nat,
    })
    .unwrap();

    let expr = elab_with_env(
        &env,
        "match o with | Option.some .(some (Nat.succ Nat.zero)) => 1 | _ => 0",
    )
    .expect(
        "deep inaccessible constructor applications should keep narrowing by constructor field type",
    );

    assert!(
        count_const_occurrences(&expr, "Option.casesOn") >= 2
            && count_const_occurrences(&expr, "Nat.casesOn") >= 2,
        "expected deep inaccessible constructor application to lower through Option and Nat casesOn layers, got {expr:?}"
    );
}

#[test]
fn test_match_ctor_nested_inaccessible_local_ident_fails_closed() {
    let mut env = Environment::with_prelude();
    for name in ["n", "m"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: Expr::const_(Name::from_string("Nat"), vec![]),
        })
        .unwrap();
    }

    let result = elab_with_env(&env, "match n with | Nat.succ .(m) => 1 | _ => 0");
    assert!(
        matches!(&result, Err(ElabError::NotImplemented(msg))
            if msg.contains("nested inaccessible pattern requires field-level definitional equality checking")),
        "nested inaccessible local identifiers should fail closed until field defeq refinement is implemented, got {result:?}"
    );
}

#[test]
fn test_match_ctor_nested_inaccessible_local_projection_fails_closed() {
    let mut env = Environment::with_prelude();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("n"),
        level_params: vec![],
        type_: Expr::const_(Name::from_string("Nat"), vec![]),
    })
    .unwrap();

    let result = elab_with_env(&env, "match n with | Nat.succ .(p.fst) => 1 | _ => 0");
    assert!(
        matches!(&result, Err(ElabError::NotImplemented(msg))
            if msg.contains("nested inaccessible pattern requires field-level definitional equality checking")),
        "nested inaccessible local projections should fail closed until field defeq refinement is implemented, got {result:?}"
    );
}

#[test]
fn test_match_ctor_nested_inaccessible_nonconstructor_app_fails_closed() {
    let mut env = Environment::with_prelude();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("n"),
        level_params: vec![],
        type_: Expr::const_(Name::from_string("Nat"), vec![]),
    })
    .unwrap();

    let result = elab_with_env(&env, "match n with | Nat.succ .(f m) => 1 | _ => 0");
    assert!(
        matches!(&result, Err(ElabError::NotImplemented(msg))
            if msg.contains("nested inaccessible pattern requires field-level definitional equality checking")),
        "nested inaccessible non-constructor applications should fail closed until field defeq refinement is implemented, got {result:?}"
    );
}

#[test]
fn test_match_multiple_arms() {
    // Multiple arms - the macro only handles single-arm match,
    // so this should reach the elaborator's Match handler
    // Note: Two-arm match requires the type to have constructors,
    // so we test that the elaboration doesn't panic on the attempt
    let result = elab("match 42 with | x => x | _ => 0");
    // This may succeed or fail depending on whether Nat.casesOn is defined
    // The important thing is that it doesn't panic
    match result {
        Ok(expr) => {
            // Should be an application structure
            assert!(
                matches!(expr.kind(), ExprKind::App(_, _)),
                "expected App for casesOn, got {expr:?}"
            );
        }
        Err(ElabError::NotImplemented(msg)) => {
            // This is also acceptable - the type might not have casesOn
            assert!(
                msg.contains("type name") || msg.contains("casesOn"),
                "unexpected error: {msg}"
            );
        }
        Err(e) => {
            // Other errors are acceptable too - elaboration attempted the right path
            // Just make sure it's not a parsing error
            assert!(
                !matches!(e, ElabError::ParseError(_)),
                "unexpected parse error: {e:?}"
            );
        }
    }
}

#[test]
fn test_match_multi_discriminant_duplicate_top_level_ctor_elaborates() {
    let mut env = Environment::with_prelude();
    for name in &["x", "y"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: Expr::const_(Name::from_string("Nat"), vec![]),
        })
        .unwrap();
    }

    let result = elab_with_env(
        &env,
        "match x, y with | Nat.zero, k => k | Nat.succ n, _ => n",
    );
    assert!(
        result.is_ok(),
        "multi-discriminant match should compile repeated top-level Prod.mk arms into one constructor alternative, got {result:?}"
    );
}

#[test]
fn test_issue796_pattern_lambda_constructor_match_keeps_hygiene() {
    let mut env = Environment::with_prelude();
    let decls = [
        r"inductive T
            | t : T",
        r"@[reducible] def T.eval : T → Type
            | T.t => Int",
        r"def T.default (τ : T) : τ.eval :=
            match τ, τ.eval with
            | T.t, .(Int) => (0 : Int)",
    ];

    for decl_src in decls {
        let decl = parse_decl_for_elab(decl_src).expect("compat declaration should parse");
        let result = crate::elaborate_decl_and_register(&mut env, &decl);
        assert!(
            result.is_ok(),
            "1057-style constructor pattern lambda should elaborate without hygienic name leaks, got {result:?} for {decl_src}"
        );
    }

    assert!(
        env.get_const(&Name::from_string("T.eval")).is_some(),
        "T.eval should be registered after elaboration"
    );
    assert!(
        env.get_const(&Name::from_string("T.default")).is_some(),
        "T.default should be registered after elaboration"
    );
}

#[test]
fn test_match_arm_type_mismatch_returns_error() {
    // #1726: match arms with different types should produce MatchArmTypeMismatch
    // Construct: axiom b : Bool; match b with | Bool.false => 42 | Bool.true => Prop
    // First arm returns a Nat literal (type Nat), second arm returns Prop (type Type).
    // These types differ, so MatchArmTypeMismatch should fire on arm 1.
    use clean_parser::{Span, SurfaceMatchArm, SurfacePattern, UniverseExpr};

    let mut env = Environment::with_prelude();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("b"),
        level_params: vec![],
        type_: Expr::const_(Name::from_string("Bool"), vec![]),
    })
    .unwrap();

    let scrutinee = SurfaceExpr::Ident(Span::dummy(), "b".to_string());
    let match_expr = SurfaceExpr::Match(
        Span::dummy(),
        None,
        Box::new(scrutinee),
        vec![
            SurfaceMatchArm {
                span: Span::dummy(),
                pattern: SurfacePattern::Ctor("Bool.false".to_string(), vec![]),
                body: SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(42)),
            },
            SurfaceMatchArm {
                span: Span::dummy(),
                pattern: SurfacePattern::Ctor("Bool.true".to_string(), vec![]),
                body: SurfaceExpr::Universe(Span::dummy(), UniverseExpr::Prop),
            },
        ],
    );

    let mut ctx = ElabCtx::new(&env);
    let result = ctx.elaborate(&match_expr);
    assert!(
        matches!(
            result,
            Err(ElabError::MatchArmTypeMismatch { arm_index: 1, .. })
        ),
        "expected MatchArmTypeMismatch for arm 1, got {result:?}"
    );
}

#[test]
fn test_issue1726_match_arms_same_type_succeeds() {
    // #1726: arms with consistent types should elaborate without error.
    // Construct: axiom b : Bool; match b with | Bool.false => 0 | Bool.true => 1
    // Both arms return Nat literals, so no MatchArmTypeMismatch should fire.
    use clean_parser::{Span, SurfaceMatchArm, SurfacePattern};

    let mut env = Environment::with_prelude();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("b"),
        level_params: vec![],
        type_: Expr::const_(Name::from_string("Bool"), vec![]),
    })
    .unwrap();

    let scrutinee = SurfaceExpr::Ident(Span::dummy(), "b".to_string());
    let match_expr = SurfaceExpr::Match(
        Span::dummy(),
        None,
        Box::new(scrutinee),
        vec![
            SurfaceMatchArm {
                span: Span::dummy(),
                pattern: SurfacePattern::Ctor("Bool.false".to_string(), vec![]),
                body: SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(0)),
            },
            SurfaceMatchArm {
                span: Span::dummy(),
                pattern: SurfacePattern::Ctor("Bool.true".to_string(), vec![]),
                body: SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(1)),
            },
        ],
    );

    let mut ctx = ElabCtx::new(&env);
    let result = ctx.elaborate(&match_expr);
    assert!(
        result.is_ok(),
        "match arms with same type should succeed, got {result:?}"
    );
}

#[test]
fn test_match_empty_arms_error() {
    // An empty match (`nomatch`) is only valid on an *uninhabited* scrutinee.
    // Here the scrutinee is `42 : Nat` — an inhabited type — so the arm-less
    // match must still be REJECTED: a zero-minor recursor cannot discharge a
    // type that has constructors. See `elab_empty_match`. (A `False`/`Empty`
    // scrutinee, by contrast, now succeeds — covered by the corpus test
    // `test_nomatch_uninhabited`.)
    let surface = SurfaceExpr::Match(
        clean_parser::Span::dummy(),
        None,
        Box::new(SurfaceExpr::Lit(
            clean_parser::Span::dummy(),
            SurfaceLit::Nat(42),
        )),
        vec![],
    );
    let env = Environment::new();
    let mut ctx = ElabCtx::new(&env);
    let result = ctx.elaborate(&surface);
    assert!(
        result.is_err(),
        "empty match on an inhabited/non-empty scrutinee must be rejected, got {result:?}"
    );
}

#[test]
fn test_infer_type_fails_on_unknown_fvar() {
    // #2206: Verifies the precondition for the check_arm_type fix.
    // An expression containing an unknown FVar must fail infer_type.
    // Before the fix, check_arm_type swallowed this error with
    // `Err(_) => return Ok(())`, creating a soundness hole because
    // register_elab_result now defaults to full kernel type checking
    // (#2454), but the elaborator must still catch this early (#2198).
    let env = Environment::new();
    let ctx = ElabCtx::new(&env);

    // FVarId::new(99999) is not in the local context — infer_type must fail
    let unknown_fvar = Expr::fvar(FVarId::new(99999));
    let result = ctx.infer_type(&unknown_fvar);
    assert!(
        result.is_err(),
        "infer_type on unknown FVar should fail, got: {result:?}"
    );
}

#[test]
fn test_match_lit_nat_zero_pattern() {
    // #796: Literal Nat(0) pattern should elaborate as the zero constructor case.
    // match n : Nat with | 0 => 1 | x => 0
    // Previously returned NotImplemented("match arm pattern: Lit(Nat(0))")
    use clean_parser::{Span, SurfaceMatchArm, SurfacePattern};

    let mut env = Environment::with_prelude();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("n"),
        level_params: vec![],
        type_: Expr::const_(Name::from_string("Nat"), vec![]),
    })
    .unwrap();

    let scrutinee = SurfaceExpr::Ident(Span::dummy(), "n".to_string());
    let match_expr = SurfaceExpr::Match(
        Span::dummy(),
        None,
        Box::new(scrutinee),
        vec![
            SurfaceMatchArm {
                span: Span::dummy(),
                pattern: SurfacePattern::Lit(SurfaceLit::Nat(0)),
                body: SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(1)),
            },
            SurfaceMatchArm {
                span: Span::dummy(),
                pattern: SurfacePattern::Var("x".to_string()),
                body: SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(0)),
            },
        ],
    );

    let mut ctx = ElabCtx::new(&env);
    let result = ctx.elaborate(&match_expr);
    assert!(
        result.is_ok(),
        "Nat.zero literal pattern should elaborate in match, got {result:?}"
    );
}

#[test]
fn test_match_numeral_add_pattern() {
    // #796: NumeralAdd(n, 1) pattern should elaborate as the succ constructor case.
    // match n : Nat with | 0 => 0 | k + 1 => k
    // Previously returned NotImplemented("match arm pattern: NumeralAdd(...)")
    use clean_parser::{Span, SurfaceMatchArm, SurfacePattern};

    let mut env = Environment::with_prelude();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("n"),
        level_params: vec![],
        type_: Expr::const_(Name::from_string("Nat"), vec![]),
    })
    .unwrap();

    let scrutinee = SurfaceExpr::Ident(Span::dummy(), "n".to_string());
    let match_expr = SurfaceExpr::Match(
        Span::dummy(),
        None,
        Box::new(scrutinee),
        vec![
            SurfaceMatchArm {
                span: Span::dummy(),
                pattern: SurfacePattern::Lit(SurfaceLit::Nat(0)),
                body: SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(0)),
            },
            SurfaceMatchArm {
                span: Span::dummy(),
                pattern: SurfacePattern::NumeralAdd(
                    Box::new(SurfacePattern::Var("k".to_string())),
                    1,
                ),
                body: SurfaceExpr::Ident(Span::dummy(), "k".to_string()),
            },
        ],
    );

    let mut ctx = ElabCtx::new(&env);
    let result = ctx.elaborate(&match_expr);
    assert!(
        result.is_ok(),
        "`n + 1` pattern should elaborate in match, got {result:?}"
    );
}

#[test]
fn test_match_nonzero_nat_literal_pattern_supported() {
    // #796: Non-zero Nat literal patterns desugar to nested Nat.succ casesOn.
    // match n : Nat with | 0 => 0 | 1 => 1 | _ => 0
    use clean_parser::{Span, SurfaceMatchArm, SurfacePattern};

    let mut env = Environment::with_prelude();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("n"),
        level_params: vec![],
        type_: Expr::const_(Name::from_string("Nat"), vec![]),
    })
    .unwrap();

    let scrutinee = SurfaceExpr::Ident(Span::dummy(), "n".to_string());
    let match_expr = SurfaceExpr::Match(
        Span::dummy(),
        None,
        Box::new(scrutinee),
        vec![
            SurfaceMatchArm {
                span: Span::dummy(),
                pattern: SurfacePattern::Lit(SurfaceLit::Nat(0)),
                body: SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(0)),
            },
            SurfaceMatchArm {
                span: Span::dummy(),
                pattern: SurfacePattern::Lit(SurfaceLit::Nat(1)),
                body: SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(1)),
            },
            SurfaceMatchArm {
                span: Span::dummy(),
                pattern: SurfacePattern::Wildcard,
                body: SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(0)),
            },
        ],
    );

    let mut ctx = ElabCtx::new(&env);
    let result = ctx.elaborate(&match_expr);
    assert!(
        result.is_ok(),
        "Nat literal 1 pattern should elaborate in match, got {result:?}"
    );
}

#[test]
fn test_match_nat_literal_2_pattern_supported() {
    // #796: Nat(2) desugars to two nested Nat.succ casesOn around Nat.zero.
    // match n : Nat with | 0 => 0 | 2 => 2 | _ => 0
    use clean_parser::{Span, SurfaceMatchArm, SurfacePattern};

    let mut env = Environment::with_prelude();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("n"),
        level_params: vec![],
        type_: Expr::const_(Name::from_string("Nat"), vec![]),
    })
    .unwrap();

    let scrutinee = SurfaceExpr::Ident(Span::dummy(), "n".to_string());
    let match_expr = SurfaceExpr::Match(
        Span::dummy(),
        None,
        Box::new(scrutinee),
        vec![
            SurfaceMatchArm {
                span: Span::dummy(),
                pattern: SurfacePattern::Lit(SurfaceLit::Nat(0)),
                body: SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(0)),
            },
            SurfaceMatchArm {
                span: Span::dummy(),
                pattern: SurfacePattern::Lit(SurfaceLit::Nat(2)),
                body: SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(2)),
            },
            SurfaceMatchArm {
                span: Span::dummy(),
                pattern: SurfacePattern::Wildcard,
                body: SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(0)),
            },
        ],
    );

    let mut ctx = ElabCtx::new(&env);
    let result = ctx.elaborate(&match_expr);
    assert!(
        result.is_ok(),
        "Nat literal 2 pattern should elaborate in match, got {result:?}"
    );
}

#[test]
fn test_match_numeral_add_offset_two_pattern_supported() {
    // #796: `n + 2` desugars to two nested Nat.succ casesOn layers.
    use clean_parser::{Span, SurfaceMatchArm, SurfacePattern};

    let mut env = Environment::with_prelude();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("n"),
        level_params: vec![],
        type_: Expr::const_(Name::from_string("Nat"), vec![]),
    })
    .unwrap();

    let scrutinee = SurfaceExpr::Ident(Span::dummy(), "n".to_string());
    let match_expr = SurfaceExpr::Match(
        Span::dummy(),
        None,
        Box::new(scrutinee),
        vec![
            SurfaceMatchArm {
                span: Span::dummy(),
                pattern: SurfacePattern::Lit(SurfaceLit::Nat(0)),
                body: SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(0)),
            },
            SurfaceMatchArm {
                span: Span::dummy(),
                pattern: SurfacePattern::NumeralAdd(
                    Box::new(SurfacePattern::Var("k".to_string())),
                    2,
                ),
                body: SurfaceExpr::Ident(Span::dummy(), "k".to_string()),
            },
            SurfaceMatchArm {
                span: Span::dummy(),
                pattern: SurfacePattern::Wildcard,
                body: SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(0)),
            },
        ],
    );

    let mut ctx = ElabCtx::new(&env);
    let result = ctx.elaborate(&match_expr);
    assert!(
        result.is_ok(),
        "`n + 2` pattern should elaborate in match, got {result:?}"
    );
}

#[test]
fn test_match_nat_literal_pattern_requires_nat_scrutinee() {
    use clean_parser::{Span, SurfaceMatchArm, SurfacePattern};

    let mut env = Environment::with_prelude();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("b"),
        level_params: vec![],
        type_: Expr::const_(Name::from_string("Bool"), vec![]),
    })
    .unwrap();

    let scrutinee = SurfaceExpr::Ident(Span::dummy(), "b".to_string());
    let match_expr = SurfaceExpr::Match(
        Span::dummy(),
        None,
        Box::new(scrutinee),
        vec![
            SurfaceMatchArm {
                span: Span::dummy(),
                pattern: SurfacePattern::Lit(SurfaceLit::Nat(0)),
                body: SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(1)),
            },
            SurfaceMatchArm {
                span: Span::dummy(),
                pattern: SurfacePattern::Wildcard,
                body: SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(0)),
            },
        ],
    );

    let mut ctx = ElabCtx::new(&env);
    let result = ctx.elaborate(&match_expr);
    // A Nat literal pattern on a `Bool` scrutinee is a type error. Since the
    // literal-cascade path now handles non-Nat literal types generally, this
    // lowers to `BEq.beq (b : Bool) (0 : Nat)`, which the kernel rejects with a
    // precise `TypeMismatch` (`Bool` vs `Nat`) — a still-loud, fail-closed
    // rejection (formerly a targeted `NotImplemented`).
    assert!(
        result.is_err(),
        "Nat literal on a Bool scrutinee must fail loud, got {result:?}"
    );
}

#[test]
fn test_match_numeral_add_pattern_requires_nat_scrutinee() {
    use clean_parser::{Span, SurfaceMatchArm, SurfacePattern};

    let mut env = Environment::with_prelude();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("b"),
        level_params: vec![],
        type_: Expr::const_(Name::from_string("Bool"), vec![]),
    })
    .unwrap();

    let scrutinee = SurfaceExpr::Ident(Span::dummy(), "b".to_string());
    let match_expr = SurfaceExpr::Match(
        Span::dummy(),
        None,
        Box::new(scrutinee),
        vec![
            SurfaceMatchArm {
                span: Span::dummy(),
                pattern: SurfacePattern::NumeralAdd(
                    Box::new(SurfacePattern::Var("k".to_string())),
                    1,
                ),
                body: SurfaceExpr::Ident(Span::dummy(), "k".to_string()),
            },
            SurfaceMatchArm {
                span: Span::dummy(),
                pattern: SurfacePattern::Wildcard,
                body: SurfaceExpr::Ident(Span::dummy(), "b".to_string()),
            },
        ],
    );

    let mut ctx = ElabCtx::new(&env);
    let result = ctx.elaborate(&match_expr);
    assert!(
        matches!(result, Err(ElabError::NotImplemented(ref msg)) if msg.contains("only supported for Nat scrutinees")),
        "expected fail-closed NotImplemented for numeral-add on Bool match, got {result:?}"
    );
}

/// Or-patterns in match should be expanded into separate arms.
#[test]
fn test_match_or_pattern_expands_to_separate_arms() {
    use clean_parser::{Span, SurfaceMatchArm, SurfacePattern};

    let mut env = Environment::with_prelude();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("b"),
        level_params: vec![],
        type_: Expr::const_(Name::from_string("Bool"), vec![]),
    })
    .unwrap();

    let scrutinee = SurfaceExpr::Ident(Span::dummy(), "b".to_string());

    // match b with | Bool.true | Bool.false => 0
    // Or-pattern should expand to: | Bool.true => 0 | Bool.false => 0
    let match_expr = SurfaceExpr::Match(
        Span::dummy(),
        None,
        Box::new(scrutinee),
        vec![SurfaceMatchArm {
            span: Span::dummy(),
            pattern: SurfacePattern::Or(
                Box::new(SurfacePattern::Ctor("Bool.true".to_string(), vec![])),
                Box::new(SurfacePattern::Ctor("Bool.false".to_string(), vec![])),
            ),
            body: SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(0)),
        }],
    );

    let mut ctx = ElabCtx::new(&env);
    let result = ctx.elaborate(&match_expr);
    assert!(
        result.is_ok(),
        "match Or-pattern should expand and elaborate, got {result:?}"
    );
}

/// A scrutinee whose type is an opaque local binder SHADOWING a known
/// inductive's name is rejected with a typed error.
///
/// `fun (Nat : Type) (x : Nat) => match x with | Nat.zero => ... ` is invalid:
/// the scrutinee's type is the opaque local `Nat`, not the global inductive,
/// and an eliminator application whose major premise has the opaque-fvar type
/// can never pass kernel re-check. Lean 4 rejects this shape; the former
/// name-based leniency (#796's FVar branch feeding eliminator construction)
/// fabricated exactly such a term and only "worked" because it was never
/// kernel-checked. The authenticated eliminator boundary now fails closed.
#[test]
fn test_match_shadowing_fvar_type_rejected() {
    use clean_parser::{Span, SurfaceMatchArm, SurfacePattern};

    let env = Environment::with_prelude();
    let mut ctx = ElabCtx::new(&env);

    // Push a local named "Nat" with type Type -- this FVar shadows the global Nat.
    let nat_fvar = ctx.push_local("Nat".to_string(), Expr::type_());

    // Push a local "x" whose type is FVar(nat_fvar) -- i.e., x : Nat where
    // "Nat" refers to the local FVar, not Const("Nat").
    let _x_fvar = ctx.push_local("x".to_string(), Expr::fvar(nat_fvar));

    // match x with | Nat.zero => 0 | Nat.succ k => k
    // infer_type(x) = FVar(nat_fvar); the scrutinee's type is the opaque
    // local binder, so the authenticated eliminator boundary rejects it.
    let match_expr = SurfaceExpr::Match(
        Span::dummy(),
        None,
        Box::new(SurfaceExpr::Ident(Span::dummy(), "x".to_string())),
        vec![
            SurfaceMatchArm {
                span: Span::dummy(),
                pattern: SurfacePattern::Ctor("Nat.zero".to_string(), vec![]),
                body: SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(0)),
            },
            SurfaceMatchArm {
                span: Span::dummy(),
                pattern: SurfacePattern::Ctor(
                    "Nat.succ".to_string(),
                    vec![SurfacePattern::Var("k".to_string())],
                ),
                body: SurfaceExpr::Ident(Span::dummy(), "k".to_string()),
            },
        ],
    );

    let result = ctx.elaborate(&match_expr);
    let err = result.expect_err("match on an opaque shadowing binder type must be rejected");
    let msg = format!("{err:?}");
    assert!(
        msg.contains("registered inductive scrutinee"),
        "expected the authenticated eliminator-boundary rejection, got {msg}"
    );
}

/// #796: get_type_name returns clear error for opaque FVar type.
///
/// When the scrutinee type is a genuinely opaque type variable (not
/// matching any known inductive), get_type_name should return a
/// NotImplemented error with a descriptive message.
#[test]
fn test_match_opaque_fvar_type_returns_error() {
    use clean_parser::{Span, SurfaceMatchArm, SurfacePattern};

    let env = Environment::new();
    let mut ctx = ElabCtx::new(&env);

    // Push a type parameter and a value of that type
    let alpha_fvar = ctx.push_local("alpha".to_string(), Expr::type_());
    let _x_fvar = ctx.push_local("x".to_string(), Expr::fvar(alpha_fvar));

    // match x with | y => y
    // Single-arm var pattern uses let-binding shortcut — doesn't call get_type_name.
    // Two arms would call get_type_name and fail on the opaque FVar.
    let match_expr = SurfaceExpr::Match(
        Span::dummy(),
        None,
        Box::new(SurfaceExpr::Ident(Span::dummy(), "x".to_string())),
        vec![
            SurfaceMatchArm {
                span: Span::dummy(),
                pattern: SurfacePattern::Ctor(
                    "Some".to_string(),
                    vec![SurfacePattern::Var("v".to_string())],
                ),
                body: SurfaceExpr::Ident(Span::dummy(), "v".to_string()),
            },
            SurfaceMatchArm {
                span: Span::dummy(),
                pattern: SurfacePattern::Wildcard,
                body: SurfaceExpr::Ident(Span::dummy(), "x".to_string()),
            },
        ],
    );

    let result = ctx.elaborate(&match_expr);
    assert!(
        result.is_err(),
        "match on opaque type variable should fail: {result:?}"
    );
    if let Err(ElabError::NotImplemented(msg)) = &result {
        assert!(
            msg.contains("FVar") || msg.contains("opaque"),
            "error should mention FVar or opaque, got: {msg}"
        );
    }
}

/// #2727: Match elaboration normalizes solved metavariables in the scrutinee type.
///
/// When infer_type returns a type containing a solved-but-uninstantiated metavar
/// (encoded as an FVar with the meta tag), the motive construction must see the
/// resolved type, not the raw metavar FVar. Without normalization at the top of
/// `elab_match_with_scrutinee`, the motive binder carries the raw metavar and
/// downstream arm elaboration may fail or produce kernel-invalid terms.
///
/// This test directly creates a solved metavar `?α := Nat`, pushes a local
/// whose type is the raw `FVar(?α)`, and elaborates a match — exercising the
/// exact path that #2727 Phase 1 fixes.
#[test]
fn test_match_scrutinee_type_solved_meta_normalization() {
    use crate::unify::MetaState;
    use clean_parser::{Span, SurfaceMatchArm, SurfacePattern};

    let env = Environment::with_prelude();
    let mut ctx = ElabCtx::new(&env);

    // Create a fresh metavar ?α : Type, then assign it to Nat.
    let meta_id = ctx.metas.fresh(Expr::type_());
    let meta_fvar_id = MetaState::to_fvar(meta_id);
    let meta_ty = Expr::fvar(meta_fvar_id);
    ctx.metas
        .assign(meta_id, Expr::const_(Name::from_string("Nat"), vec![]));

    // Push local `x : ?α` where ?α is solved to Nat but the type expression
    // still refers to the raw metavar FVar.
    let _x_fvar = ctx.push_local("x".to_string(), meta_ty);

    // match x with | Nat.zero => 0 | Nat.succ k => k
    // Without scrutinee-type normalization, the motive binder would carry
    // FVar(meta_tag | 0) instead of Const("Nat"), causing downstream failures.
    let match_expr = SurfaceExpr::Match(
        Span::dummy(),
        None,
        Box::new(SurfaceExpr::Ident(Span::dummy(), "x".to_string())),
        vec![
            SurfaceMatchArm {
                span: Span::dummy(),
                pattern: SurfacePattern::Ctor("Nat.zero".to_string(), vec![]),
                body: SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(0)),
            },
            SurfaceMatchArm {
                span: Span::dummy(),
                pattern: SurfacePattern::Ctor(
                    "Nat.succ".to_string(),
                    vec![SurfacePattern::Var("k".to_string())],
                ),
                body: SurfaceExpr::Ident(Span::dummy(), "k".to_string()),
            },
        ],
    );

    let result = ctx.elaborate(&match_expr);
    assert!(
        result.is_ok(),
        "match on solved-meta-typed scrutinee should succeed after normalization, got {result:?}"
    );
}

/// Track C — dependent elimination: `Eq.symm` via a GADT-style match whose
/// `Eq.casesOn` motive must be *index-refining*. The `Eq.refl` arm forces the
/// scrutinee index `b ≡ a`, so the motive is `fun (b) (h : Eq a b) => Eq b a`,
/// the minor premise has type `motive a rfl = Eq a a` (inhabited by `Eq.refl`),
/// and the whole application has type `motive b h = Eq b a`.
///
/// SOUNDNESS GATE: `elaborate_decl_and_register` runs the lowered term through
/// the kernel type-checker (strict enforce, default-on). A non-index-refining
/// (constant) motive produces `Eq b b`, which the kernel rejects. Registration
/// succeeding therefore *is* the proof that the synthesized motive is correct.
#[test]
fn test_trkc_depelim_eq_symm_index_refining_motive_kernel_checks() {
    let mut env = Environment::with_prelude();
    let decl = parse_decl_for_elab(
        "def symm {A : Type} {a b : A} (h : Eq a b) : Eq b a := match h with | Eq.refl => rfl",
    )
    .expect("symm should parse");
    let result = crate::elaborate_decl_and_register(&mut env, &decl);
    assert!(
        result.is_ok(),
        "Eq.symm GADT match must elaborate and kernel-check with an index-refining motive, got {result:?}"
    );
    assert!(
        env.get_const(&Name::from_string("symm")).is_some(),
        "symm should be registered after a successful kernel check"
    );
}

/// SOUNDNESS GATE (companion to the kernel check above): the registered `symm`
/// must rest on NO axioms — no `sorry`, no fabricated `Trusted` axiom leaked
/// into the proof term. Its axiom closure must be empty, witnessing a genuine
/// constructive dependent-elimination lowering.
#[test]
fn test_trkc_depelim_eq_symm_axiom_deps_empty() {
    let mut env = Environment::with_prelude();
    let decl = parse_decl_for_elab(
        "def symm {A : Type} {a b : A} (h : Eq a b) : Eq b a := match h with | Eq.refl => rfl",
    )
    .expect("symm should parse");
    crate::elaborate_decl_and_register(&mut env, &decl).expect("symm should register");
    let deps = env
        .axiom_deps(&Name::from_string("symm"))
        .expect("symm is registered, axiom_deps should return Some");
    let dep_names: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
    assert!(
        dep_names.is_empty(),
        "symm must have an empty axiom closure (genuine dependent-elimination proof), got {dep_names:?}"
    );
}
