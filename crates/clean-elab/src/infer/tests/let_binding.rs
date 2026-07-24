// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Let binding elaboration tests, including type inference

use super::*;

// =========================================================================
// Let with Inferred Type Tests
// Tests for let without explicit type annotation (let x := val in body)
// =========================================================================

#[test]
fn test_let_inferred_type_simple() {
    // Let without explicit type - type should be inferred from value
    let expr = elab("let x := Type in x").unwrap();
    // Result should be Let with inferred type Type and body that returns x
    assert!(matches!(expr.kind(), ExprKind::Let(_, _, _, _, _)));
}

#[test]
fn test_let_inferred_type_prop() {
    // Infer Prop type
    let expr = elab("let p := Prop in p").unwrap();
    assert!(matches!(expr.kind(), ExprKind::Let(_, _, _, _, _)));
}

#[test]
fn test_let_inferred_type_lambda() {
    // Infer type of lambda (identity function)
    let expr = elab("let id := fun (A : Type) (x : A) => x in id").unwrap();
    assert!(matches!(expr.kind(), ExprKind::Let(_, _, _, _, _)));
}

#[test]
fn test_let_inferred_vs_explicit_same_result() {
    // Both should elaborate to equivalent expressions
    let inferred = elab("let x := Type in x").unwrap();
    let explicit = elab("let x : Type := Type in x").unwrap();
    // Both should be Let expressions
    assert!(matches!(inferred.kind(), ExprKind::Let(_, _, _, _, _)));
    assert!(matches!(explicit.kind(), ExprKind::Let(_, _, _, _, _)));
}

#[test]
fn test_let_inferred_type_nested() {
    // Nested let with inferred types
    let expr = elab("let x := Type in let y := x in y").unwrap();
    assert!(matches!(expr.kind(), ExprKind::Let(_, _, _, _, _)));
}

#[test]
fn test_let_inferred_type_with_usage() {
    // Let where inferred type is used in body - simple case just returning the let-bound value
    let expr = elab("let x := Prop in x -> x").unwrap();
    // The body uses x in an arrow type, result could be Let or Pi
    assert!(
        matches!(expr.kind(), ExprKind::Let(_, _, _, _, _))
            || matches!(expr.kind(), ExprKind::Pi(_, _, _))
    );
}

#[test]
fn test_let_inferred_arrow_type() {
    // Let where value is a function type
    let expr = elab("let arrow := Type -> Type in arrow").unwrap();
    assert!(matches!(expr.kind(), ExprKind::Let(_, _, _, _, _)));
}

#[test]
fn test_let_inferred_type_forall() {
    // Forall type inferred using forall syntax
    let expr = elab("let dep := forall (A : Type), A -> A in dep").unwrap();
    assert!(matches!(expr.kind(), ExprKind::Let(_, _, _, _, _)));
}

/// Test Var pattern let-pattern elaboration via direct AST construction
/// Part of #751: Non-q-pattern let-pattern elaboration
#[test]
fn test_let_pattern_var_direct_ast() {
    use clean_parser::{Span, SurfaceExpr, SurfaceLit, SurfacePattern};

    let env = Environment::new();
    let mut ctx = ElabCtx::new(&env);

    // Build: let x := 42 | 0 in x
    // This AST cannot be produced by the parser (only q(...) can start let-patterns)
    // but tests the Var branch of elaborate_let_q_pattern
    let pattern = SurfacePattern::Var("x".to_string());
    let scrutinee = Box::new(SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(42)));
    let fallback = Box::new(SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(0)));
    let body = Box::new(SurfaceExpr::Ident(Span::dummy(), "x".to_string()));

    let surface = SurfaceExpr::LetPattern(Span::dummy(), pattern, scrutinee, fallback, body);

    let result = ctx.elaborate(&surface);
    assert!(
        result.is_ok(),
        "let x := 42 | 0 in x should elaborate: {:?}",
        result.err()
    );

    // Should produce a let expression
    let expr = result.unwrap();
    assert!(
        matches!(expr.kind(), ExprKind::Let(_, _, _, _, _)),
        "expected Let expression, got {:?}",
        expr
    );
}

/// Test Wildcard pattern let-pattern elaboration via direct AST construction
/// Part of #751: Non-q-pattern let-pattern elaboration
#[test]
fn test_let_pattern_wildcard_direct_ast() {
    use clean_parser::{Span, SurfaceExpr, SurfaceLit, SurfacePattern};

    let env = Environment::new();
    let mut ctx = ElabCtx::new(&env);

    // Build: let _ := 42 | 0 in 1
    // Tests the Wildcard branch - scrutinee evaluated for effects
    let pattern = SurfacePattern::Wildcard;
    let scrutinee = Box::new(SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(42)));
    let fallback = Box::new(SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(0)));
    let body = Box::new(SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(1)));

    let surface = SurfaceExpr::LetPattern(Span::dummy(), pattern, scrutinee, fallback, body);

    let result = ctx.elaborate(&surface);
    assert!(
        result.is_ok(),
        "let _ := 42 | 0 in 1 should elaborate: {:?}",
        result.err()
    );

    // Should produce a let expression
    let expr = result.unwrap();
    assert!(
        matches!(expr.kind(), ExprKind::Let(_, _, _, _, _)),
        "expected Let expression, got {:?}",
        expr
    );
}

/// Test that literal patterns in let-patterns desugar to match and fail in empty env
/// Part of #751: Non-q-pattern let-pattern elaboration
///
/// Literal patterns in let-patterns are desugared to match expressions.
/// Non-zero Nat literals desugar to Nat.succ chains, which in an empty
/// environment fails with UnknownIdent because Nat.succ is not declared.
#[test]
fn test_let_pattern_lit_desugar_not_implemented() {
    use clean_parser::{Span, SurfaceExpr, SurfaceLit, SurfacePattern};

    let env = Environment::new();
    let mut ctx = ElabCtx::new(&env);

    // Build: let 42 := scrutinee | fallback in body
    // Literal 42 desugars to a Nat.succ chain, which fails because
    // Nat.succ is not declared in the empty environment.
    let pattern = SurfacePattern::Lit(SurfaceLit::Nat(42));
    let scrutinee = Box::new(SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(42)));
    let fallback = Box::new(SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(0)));
    let body = Box::new(SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(1)));

    let surface = SurfaceExpr::LetPattern(Span::dummy(), pattern, scrutinee, fallback, body);

    let result = ctx.elaborate(&surface);
    assert!(
        result.is_err(),
        "literal pattern in empty env should return error"
    );
    assert!(
        result.is_err(),
        "literal pattern in empty env should return some error variant, got {:?}",
        result
    );
}

/// Test Ctor pattern let-pattern desugars to match expression
/// Part of #751: Non-q-pattern let-pattern elaboration
///
/// Constructor patterns in let-patterns are desugared to match expressions.
/// The match elaboration handles constructor patterns via casesOn.
#[test]
fn test_let_pattern_ctor_desugar() {
    use clean_parser::{Span, SurfaceExpr, SurfaceLit, SurfacePattern};

    let env = Environment::with_prelude();
    let mut ctx = ElabCtx::new(&env);

    // Build: let succ(x) := 42 | 0 in x
    // Desugars to: let __letpat_scrutinee := 42 in
    //              match __letpat_scrutinee with | succ(x) => x | _ => 0
    //
    // `succ` resolves to the genuine Nat.succ constructor of the scrutinee's
    // inductive; a constructor that does not belong to the scrutinee's type
    // (e.g. `Some` on a Nat) is a hard UnknownIdent error — the old fallback
    // typing lane for unrecognized constructors was a silent miscompile and
    // has been removed.
    let inner_pattern = SurfacePattern::Var("x".to_string());
    let pattern = SurfacePattern::Ctor("succ".to_string(), vec![inner_pattern]);
    let scrutinee = Box::new(SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(42)));
    let fallback = Box::new(SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(0)));
    let body = Box::new(SurfaceExpr::Ident(Span::dummy(), "x".to_string()));

    let surface = SurfaceExpr::LetPattern(Span::dummy(), pattern, scrutinee, fallback, body);

    let result = ctx.elaborate(&surface);
    // The outer structure should be a Let (binding __letpat_scrutinee).
    assert!(
        result.is_ok(),
        "constructor pattern let-pattern should elaborate via match desugaring: {:?}",
        result
    );

    // Verify outer structure is a Let expression
    let expr = result.unwrap();
    assert!(
        matches!(expr.kind(), ExprKind::Let(_, _, _, _, _)),
        "expected outer Let expression from desugaring, got {:?}",
        expr
    );
}

/// Test As pattern let-pattern desugars to match expression
/// Part of #751: Non-q-pattern let-pattern elaboration
///
/// As patterns (x @ pat) in let-patterns are desugared to match expressions.
#[test]
fn test_let_pattern_as_desugar() {
    use clean_parser::{Span, SurfaceExpr, SurfaceLit, SurfacePattern};

    let env = Environment::new();
    let mut ctx = ElabCtx::new(&env);

    // Build: let x @ _ := 42 | 0 in x
    // As pattern with wildcard inner pattern
    let inner_pattern = Box::new(SurfacePattern::Wildcard);
    let pattern = SurfacePattern::As("x".to_string(), inner_pattern);
    let scrutinee = Box::new(SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(42)));
    let fallback = Box::new(SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(0)));
    let body = Box::new(SurfaceExpr::Ident(Span::dummy(), "x".to_string()));

    let surface = SurfaceExpr::LetPattern(Span::dummy(), pattern, scrutinee, fallback, body);

    let result = ctx.elaborate(&surface);
    // As patterns desugar to match, which may succeed or fail depending
    // on how match elaboration handles As patterns in arms
    // The key is that it doesn't return NotImplemented for the let-pattern itself
    assert!(
        !matches!(result, Err(ElabError::NotImplemented(ref msg)) if msg.contains("let-pattern")),
        "As pattern should desugar (not direct NotImplemented for let-pattern): {:?}",
        result
    );

    // If elaboration succeeds, verify the result is a Let expression
    if let Ok(expr) = result {
        assert!(
            matches!(expr.kind(), ExprKind::Let(_, _, _, _, _)),
            "As pattern desugaring should produce Let expression, got {:?}",
            expr
        );
    }
}

/// Test Or pattern let-pattern desugars to match expression
/// Part of #751: Non-q-pattern let-pattern elaboration
///
/// Or patterns (pat1 | pat2) in let-patterns are desugared to match expressions.
#[test]
fn test_let_pattern_or_desugar() {
    use clean_parser::{Span, SurfaceExpr, SurfaceLit, SurfacePattern};

    let env = Environment::new();
    let mut ctx = ElabCtx::new(&env);

    // Build: let (x | y) := 42 | 0 in 1
    // Or pattern with two variable alternatives
    let left = Box::new(SurfacePattern::Var("x".to_string()));
    let right = Box::new(SurfacePattern::Var("y".to_string()));
    let pattern = SurfacePattern::Or(left, right);
    let scrutinee = Box::new(SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(42)));
    let fallback = Box::new(SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(0)));
    let body = Box::new(SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(1)));

    let surface = SurfaceExpr::LetPattern(Span::dummy(), pattern, scrutinee, fallback, body);

    let result = ctx.elaborate(&surface);
    // Or patterns desugar to match - verify desugaring happens (not direct NotImplemented)
    assert!(
        !matches!(result, Err(ElabError::NotImplemented(ref msg)) if msg.contains("let-pattern")),
        "Or pattern should desugar (not direct NotImplemented for let-pattern): {:?}",
        result
    );

    // If elaboration succeeds, verify the result is a Let expression
    if let Ok(expr) = result {
        assert!(
            matches!(expr.kind(), ExprKind::Let(_, _, _, _, _)),
            "Or pattern desugaring should produce Let expression, got {:?}",
            expr
        );
    }
}

/// Verify detailed kernel term structure after desugaring
/// Part of #751: Non-q-pattern let-pattern elaboration
///
/// This test verifies that the desugaring produces correct kernel terms by
/// examining the internal structure of the Let expression.
#[test]
fn test_let_pattern_ctor_desugar_kernel_structure() {
    use clean_kernel::Literal;
    use clean_parser::{Span, SurfaceExpr, SurfaceLit, SurfacePattern};

    let env = Environment::with_prelude();
    let mut ctx = ElabCtx::new(&env);

    // Build: let succ(x) := 42 | 0 in x
    // Desugars to: let __letpat_scrutinee := 42 in
    //              match __letpat_scrutinee with | succ(x) => x | _ => 0
    // (`succ` resolves to the genuine Nat.succ; a constructor foreign to the
    // scrutinee's inductive is a hard UnknownIdent error — the old fallback
    // typing lane was a silent miscompile and has been removed.)
    let inner_pattern = SurfacePattern::Var("x".to_string());
    let pattern = SurfacePattern::Ctor("succ".to_string(), vec![inner_pattern]);
    let scrutinee = Box::new(SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(42)));
    let fallback = Box::new(SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(0)));
    let body = Box::new(SurfaceExpr::Ident(Span::dummy(), "x".to_string()));

    let surface = SurfaceExpr::LetPattern(Span::dummy(), pattern, scrutinee, fallback, body);

    let result = ctx.elaborate(&surface);
    assert!(result.is_ok(), "should elaborate: {:?}", result);

    // Verify outer structure is Let(ty, val, body)
    let expr = result.unwrap();
    match expr.kind() {
        ExprKind::Let(_, ty, val, body, _) => {
            // val should be the elaborated scrutinee (Nat literal 42)
            assert!(
                matches!(val.kind(), ExprKind::Lit(Literal::Nat(_))),
                "let value should be Nat literal, got {:?}",
                val
            );

            // ty should be Nat type (elaborated from literal)
            // Check it's not empty/error
            assert!(
                !matches!(ty.kind(), ExprKind::BVar(_)),
                "let type should be resolved, not BVar: {:?}",
                ty
            );

            // body contains the elaborated match expression (abstracted over the synthetic var)
            // The body should reference BVar(0) somewhere if the let binding is used
            assert!(
                contains_bvar_zero(body),
                "let body should reference BVar(0) (the bound variable): {:?}",
                body
            );
        }
        _ => panic!("expected Let expression, got {:?}", expr),
    }
}

#[test]
fn test_let_pattern_var_body_reference_under_lambda() {
    use clean_parser::{Span, SurfaceBinder, SurfaceExpr, SurfaceLit, SurfacePattern};

    let env = Environment::new();
    let mut ctx = ElabCtx::new(&env);

    let pattern = SurfacePattern::Var("y".to_string());
    let scrutinee = Box::new(SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(42)));
    let fallback = Box::new(SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(0)));
    let body = Box::new(SurfaceExpr::lambda(
        vec![SurfaceBinder::explicit("_x", SurfaceExpr::prop())],
        SurfaceExpr::Ident(Span::dummy(), "y".to_string()),
    ));

    let surface = SurfaceExpr::LetPattern(Span::dummy(), pattern, scrutinee, fallback, body);
    let expr = ctx.elaborate(&surface).unwrap();

    match expr.kind() {
        ExprKind::Let(_, _, _, body, _) => {
            assert!(
                contains_bvar_zero(body),
                "let-pattern body should reference the bound variable under nested lambdas: {body:?}"
            );
        }
        _ => panic!("expected Let expression, got {:?}", expr),
    }
}

/// Helper to check if an expression references the surrounding binder.
///
/// `Expr::body` fields are inspected outside their enclosing binder node, so a
/// reference to the surrounding `let` binder appears as loose bvar 0 here.
/// Nested binders shift that index, so use `has_loose_bvar(0)` instead of
/// matching raw `BVar(0)` nodes directly.
fn contains_bvar_zero(expr: &Expr) -> bool {
    expr.has_loose_bvar(0)
}

fn let_rec_parts(expr: &Expr) -> (&Expr, &Expr) {
    match expr.kind() {
        ExprKind::Let(_, _, val, body, _) => (val, body),
        _ => panic!("expected Let expression, got {expr:?}"),
    }
}

/// A non-recursive `let rec` must lower exactly like a plain `let`: the real
/// (sorry-free) value bound, the body referencing the abstracted binder.
fn assert_let_rec_lowers_to_plain_let(expr: &Expr) {
    let (val, body) = let_rec_parts(expr);
    assert!(
        !val.has_sorry(),
        "non-recursive let rec must bind the REAL value, not a sorry placeholder (audit d04), got: {val:?}"
    );
    assert!(
        contains_bvar_zero(body),
        "let rec body should reference the abstracted binder, got: {body:?}"
    );
    assert!(
        !body.has_sorry(),
        "let rec body should contain the binder, not a sorry term: {body:?}"
    );
}

/// A recursive `let rec` that the structural lift cannot lower must FAIL
/// LOUD with the typed `WhereLetRecUnsupported` error — never a synthetic
/// `sorry` (the pre-2026-07 fallback, audit d04's "registers-anyway" trap).
fn assert_unliftable_let_rec_fails_loud(result: Result<Expr, ElabError>, what: &str) {
    match result {
        Err(ElabError::WhereLetRecUnsupported { name, .. }) => {
            assert_eq!(name, "f", "{what}: error should name the local definition");
        }
        Err(other) => panic!("{what}: expected WhereLetRecUnsupported, got {other:?}"),
        Ok(expr) => panic!("{what}: must fail loud, but elaborated to {expr:?}"),
    }
}

// =========================================================================
// Issue #796 / audit d04: let rec elaboration (sorry fallback ELIMINATED)
// =========================================================================

/// An unliftable recursive binding (`f : Prop := f` — zero parameters, pure
/// value-level fixpoint) fails loud. It previously bound a synthetic `sorry`.
#[test]
fn test_let_rec_unliftable_recursion_fails_loud() {
    // let rec f : Prop := f in f
    // Simplest recursive binding: f's value references itself.
    let result = elab("let rec f : Prop := f in f");
    assert_unliftable_let_rec_fails_loud(result, "zero-param recursive let rec");
}

/// let rec with simple non-recursive body elaborates to a plain let with the
/// real value (previously: sorry placeholder).
#[test]
fn test_let_rec_non_recursive_value_elaborates() {
    // Degenerate case: value doesn't actually reference f.
    let expr = elab("let rec f : Type := Type in f").unwrap();
    assert_let_rec_lowers_to_plain_let(&expr);
}

/// let rec without type annotation infers from value.
#[test]
fn test_let_rec_inferred_type() {
    // Without annotation, type is inferred from the value.
    let expr = elab("let rec f := Type in f").unwrap();
    assert_let_rec_lowers_to_plain_let(&expr);
}

/// The loud failure holds regardless of whether `sorryAx` is available in
/// the environment: availability of the axiom must not re-enable the
/// placeholder path.
#[test]
fn test_let_rec_unliftable_fails_loud_even_with_sorry_ax_available() {
    let env = Environment::with_prelude();
    let result = elab_with_env(&env, "let rec f : Prop := f in f");
    assert_unliftable_let_rec_fails_loud(result, "recursive let rec with prelude sorryAx");
}

#[test]
fn test_let_rec_unliftable_body_reference_under_lambda_fails_loud() {
    let result = elab("let rec f : Prop := f in fun (_x : Prop) => f");
    assert_unliftable_let_rec_fails_loud(result, "recursive let rec under lambda body");
}
