// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for parser-only do-notation compatibility forms.

use super::*;

fn elab_with_prelude_bare(input: &str) -> Result<Expr, ElabError> {
    let env = Environment::with_prelude();
    let mut ctx = ElabCtx::new(&env);
    // No current_expected_type — relies on level_eq callback to resolve universe params
    let surface = parse_expr(input).map_err(|e| ElabError::ParseError(e.to_string()))?;
    ctx.elaborate(&surface)
}

#[test]
fn test_bare_do_block_no_expected_type_resolves_universe_levels() {
    // Root cause regression test: bare do-block without current_expected_type.
    // Before the level_eq callback fix, this failed with:
    //   TypeMismatch { expected: Sort(Succ(Param("u_0"))), inferred: Sort(Succ(Zero)) }
    // because fresh_universe_param creates rigid Level::Param that couldn't unify
    // with concrete levels in the kernel's Level::is_def_eq.
    let result = elab_with_prelude_bare("do return Nat.zero");
    assert!(
        result.is_ok(),
        "bare do-block without expected type should elaborate via level_eq callback, got {result:?}"
    );
}

#[test]
fn test_elab_do_have_with_binders_uses_full_function_type() {
    let expr = elab("do have f (A : Type) : Type := A; f Prop")
        .expect("function-style do-have should elaborate");

    match expr.kind() {
        ExprKind::Let(_, ty, val, body, _) => {
            assert!(
                matches!(ty.kind(), ExprKind::Pi(_, _, _)),
                "do-have binder type should be a Pi, got {ty:?}"
            );
            assert!(
                matches!(val.kind(), ExprKind::Lam(_, _, _)),
                "do-have value should stay lambda-shaped, got {val:?}"
            );
            assert!(
                matches!(body.kind(), ExprKind::App(_, _)),
                "do-have body should apply the local function, got {body:?}"
            );
        }
        other => panic!("expected Let for function-style do-have, got {other:?}"),
    }
}

#[test]
fn test_elab_do_let_rec_with_binders_uses_full_function_type() {
    let expr = elab("do let rec f (A : Type) : Type := A; f Prop")
        .expect("function-style do-let-rec should elaborate");

    match expr.kind() {
        ExprKind::Let(_, ty, _, body, _) => {
            assert!(
                matches!(ty.kind(), ExprKind::Pi(_, _, _)),
                "do-let-rec binder type should be a Pi, got {ty:?}"
            );
            assert!(
                matches!(body.kind(), ExprKind::App(_, _)),
                "do-let-rec body should apply the recursive local, got {body:?}"
            );
        }
        other => panic!("expected Let for function-style do-let-rec, got {other:?}"),
    }
}

#[test]
fn test_elab_do_let_expr_pure_elaborates() {
    let expr = elab_with_prelude_bare("do let_expr x := Bool.true | return Bool.false; return x")
        .expect("pure let_expr should elaborate with prelude constructors");
    assert!(
        matches!(
            expr.kind(),
            ExprKind::App(_, _) | ExprKind::Let(_, _, _, _, _)
        ),
        "expected lowered let_expr expression, got {expr:?}"
    );
}

#[test]
fn test_elab_do_let_expr_bind_elaborates() {
    let expr = elab_with_prelude_bare(
        "do let_expr x <- Pure.pure Bool.true | return Bool.false; return x",
    )
    .expect("monadic let_expr should elaborate with prelude");
    assert!(
        matches!(
            expr.kind(),
            ExprKind::App(_, _) | ExprKind::Let(_, _, _, _, _)
        ),
        "expected lowered bind let_expr expression, got {expr:?}"
    );
}
