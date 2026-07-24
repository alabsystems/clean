// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Direct tests for elab_do_handlers.rs: break, continue, early return,
//! mutable reassignment, and pattern reassignment paths.
//!
//! These cover the ~490-line module that previously had ZERO direct test
//! coverage (#1795). Uses Environment::with_prelude() so monadic constants
//! are declared.

use super::*;
use clean_parser::{DoElem, Span, SurfaceExpr, SurfacePattern};

#[allow(dead_code)]
fn expr_contains_const(expr: &Expr, name: &str) -> bool {
    match expr.kind() {
        ExprKind::Const(n, _) => n.to_string() == name,
        ExprKind::App(f, a) => expr_contains_const(f, name) || expr_contains_const(a, name),
        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
            expr_contains_const(ty, name) || expr_contains_const(body, name)
        }
        ExprKind::Let(_, ty, val, body, _) => {
            expr_contains_const(ty, name)
                || expr_contains_const(val, name)
                || expr_contains_const(body, name)
        }
        _ => false,
    }
}

// === break outside loop ===

/// B08: `do break` OUTSIDE any loop is a typed descope, not a silent term.
/// Lean itself rejects `break` outside a `for`; Clean now surfaces a typed
/// `Unsupported` (the `for`/`break`/`continue` control-flow lane) rather than
/// the old ControlStack `OptionT.fail` lowering that produced unbound fvars.
#[test]
fn test_elab_do_break_outside_loop_is_loud_descope() {
    let env = Environment::with_prelude();
    let err = elab_with_env(&env, "do break")
        .expect_err("break outside a loop must be a typed descope, not a silent term");
    let msg = format!("{err:?}");
    assert!(
        matches!(err, ElabError::Unsupported { .. }),
        "break outside loop should be a typed Unsupported error, got {err:?}"
    );
    assert!(
        !msg.contains("free variable") && !msg.contains("9223372036854775808"),
        "descope must not leak unbound fvars, got {msg}"
    );
}

// === continue outside loop ===

/// B08: `do continue` outside a for-loop is a typed descope (see the `break`
/// test above), never an unbound-fvar term.
#[test]
fn test_elab_do_continue_outside_loop_is_loud_descope() {
    let env = Environment::with_prelude();
    let err = elab_with_env(&env, "do continue")
        .expect_err("continue outside a loop must be a typed descope, not a silent term");
    let msg = format!("{err:?}");
    assert!(
        matches!(err, ElabError::Unsupported { .. }),
        "continue outside loop should be a typed Unsupported error, got {err:?}"
    );
    assert!(
        !msg.contains("free variable") && !msg.contains("9223372036854775808"),
        "descope must not leak unbound fvars, got {msg}"
    );
}

// === break inside for loop ===

/// `do for x in xs do break` should elaborate without panicking,
/// exercising the ForInStep.done path in elab_do_break (Mode 1).
#[test]
fn test_elab_do_break_inside_for_loop() {
    let env = Environment::with_prelude();
    let result = elab_with_env(&env, "do for _ in [1] do break");
    // The elaboration may fail on missing ForIn instance or list syntax,
    // but should not panic. Any error should be type-related, not a
    // "break outside loop" error.
    match result {
        Ok(_) => {} // success is fine
        Err(e) => {
            let msg = format!("{e:?}");
            assert!(
                !msg.contains("outside of a loop"),
                "break inside for-loop should not report 'outside of a loop': {msg}"
            );
        }
    }
}

// === continue inside for loop ===

/// `do for _ in [1] do continue` exercises the ForInStep.yield path
/// in elab_do_continue (Mode 1).
#[test]
fn test_elab_do_continue_inside_for_loop() {
    let env = Environment::with_prelude();
    let result = elab_with_env(&env, "do for _ in [1] do continue");
    match result {
        Ok(_) => {}
        Err(e) => {
            let msg = format!("{e:?}");
            assert!(
                !msg.contains("outside of a loop"),
                "continue inside for-loop should not report 'outside of a loop': {msg}"
            );
        }
    }
}

// === mutable reassignment error path ===

/// `do x := 42` without a prior `let mut x` should produce an error about
/// missing mutable locals, exercising the guard at elab_do_handlers.rs:284-287.
#[test]
fn test_elab_do_reassign_without_let_mut_returns_error() {
    let env = Environment::with_prelude();
    let result = elab_with_env(&env, "do x := 42; return x");
    assert!(
        result.is_err(),
        "reassign without let mut should return Err"
    );
    let msg = format!("{:?}", result.unwrap_err());
    assert!(
        msg.contains("mutable")
            || msg.contains("reassign")
            || msg.contains("UnknownIdent")
            || msg.contains("NotImplemented"),
        "error should mention mutable/reassign context, got: {msg}"
    );
}

// === pattern reassignment desugaring ===

/// `desugar_pattern_reassign` should produce a let + individual reassign
/// elements for a Prod.mk pattern. This is a unit test on the desugaring
/// logic at elab_do_handlers.rs:434-449.
#[test]
fn test_desugar_pattern_reassign_prod() {
    let env = Environment::with_prelude();
    let ctx = ElabCtx::new(&env);
    let span = Span::new(0, 0);
    let pat = SurfacePattern::Ctor(
        "Prod.mk".to_string(),
        vec![
            SurfacePattern::Var("a".to_string()),
            SurfacePattern::Var("b".to_string()),
        ],
    );
    let val = SurfaceExpr::Ident(span, "expr".to_string());
    let rest = vec![];
    let elems = ctx.desugar_pattern_reassign(span, &pat, &val, &rest);
    // Should produce: let __reassign_tmp := expr; a := Prod.fst __reassign_tmp; b := Prod.snd __reassign_tmp
    assert!(
        elems.len() >= 3,
        "pattern reassign should produce at least 3 elements (let + 2 reassigns), got {}",
        elems.len()
    );
    // First element is always a Let binding for __reassign_tmp
    assert!(
        matches!(&elems[0], DoElem::Let(_, _, _)),
        "first element should be a Let, got {:?}",
        std::mem::discriminant(&elems[0])
    );
    // Remaining elements should be Reassign for each variable
    assert!(
        matches!(&elems[1], DoElem::Reassign(_, name, _) if name == "a"),
        "second element should be Reassign for 'a'"
    );
    assert!(
        matches!(&elems[2], DoElem::Reassign(_, name, _) if name == "b"),
        "third element should be Reassign for 'b'"
    );
}

/// `As(name, inner)` pattern emits a reassign for `name` AND recurses into `inner`.
/// Regression test for #2988: previously silently dropped via `_ => {}` catch-all.
#[test]
fn test_desugar_pattern_reassign_as_pattern() {
    let env = Environment::with_prelude();
    let ctx = ElabCtx::new(&env);
    let span = Span::new(0, 0);
    // As("n", Var("a")) — simulates `let n@a := expr`
    let pat = SurfacePattern::As(
        "n".to_string(),
        Box::new(SurfacePattern::Var("a".to_string())),
    );
    let val = SurfaceExpr::Ident(span, "expr".to_string());
    let elems = ctx.desugar_pattern_reassign(span, &pat, &val, &[]);
    // Should produce: let __reassign_tmp := expr; n := __reassign_tmp; a := __reassign_tmp
    assert!(
        elems.len() == 3,
        "As pattern should produce 3 elements (let + reassign for 'n' + reassign for 'a'), got {}",
        elems.len()
    );
    assert!(
        matches!(&elems[1], DoElem::Reassign(_, name, _) if name == "n"),
        "second element should be Reassign for 'n' (the As binding)"
    );
    assert!(
        matches!(&elems[2], DoElem::Reassign(_, name, _) if name == "a"),
        "third element should be Reassign for 'a' (the inner pattern)"
    );
}

/// `NumeralAdd(inner, k)` pattern recurses into the sub-pattern.
/// Regression test for #2988: previously silently dropped via `_ => {}` catch-all.
#[test]
fn test_desugar_pattern_reassign_numeral_add() {
    let env = Environment::with_prelude();
    let ctx = ElabCtx::new(&env);
    let span = Span::new(0, 0);
    // NumeralAdd(Var("m"), 1) — simulates `let (m + 1) := expr`
    let pat = SurfacePattern::NumeralAdd(Box::new(SurfacePattern::Var("m".to_string())), 1);
    let val = SurfaceExpr::Ident(span, "expr".to_string());
    let elems = ctx.desugar_pattern_reassign(span, &pat, &val, &[]);
    // Should produce: let __reassign_tmp := expr; m := __reassign_tmp
    assert!(
        elems.len() == 2,
        "NumeralAdd pattern should produce 2 elements (let + reassign for 'm'), got {}",
        elems.len()
    );
    assert!(
        matches!(&elems[1], DoElem::Reassign(_, name, _) if name == "m"),
        "second element should be Reassign for 'm' (the inner variable)"
    );
}

/// `As("n", NumeralAdd(Var("m"), 1))` — compound pattern exercises both paths.
/// Regression test for #2988.
#[test]
fn test_desugar_pattern_reassign_as_with_numeral_add() {
    let env = Environment::with_prelude();
    let ctx = ElabCtx::new(&env);
    let span = Span::new(0, 0);
    let pat = SurfacePattern::As(
        "n".to_string(),
        Box::new(SurfacePattern::NumeralAdd(
            Box::new(SurfacePattern::Var("m".to_string())),
            1,
        )),
    );
    let val = SurfaceExpr::Ident(span, "expr".to_string());
    let elems = ctx.desugar_pattern_reassign(span, &pat, &val, &[]);
    // Should produce: let __reassign_tmp := expr; n := __reassign_tmp; m := __reassign_tmp
    assert!(
        elems.len() == 3,
        "As+NumeralAdd pattern should produce 3 elements (let + 'n' + 'm'), got {}",
        elems.len()
    );
    assert!(
        matches!(&elems[1], DoElem::Reassign(_, name, _) if name == "n"),
        "second element should be Reassign for 'n'"
    );
    assert!(
        matches!(&elems[2], DoElem::Reassign(_, name, _) if name == "m"),
        "third element should be Reassign for 'm'"
    );
}

/// Wildcard in pattern reassignment should be skipped (no Reassign emitted).
#[test]
fn test_desugar_pattern_reassign_wildcard_skipped() {
    let env = Environment::with_prelude();
    let ctx = ElabCtx::new(&env);
    let span = Span::new(0, 0);
    let pat = SurfacePattern::Ctor(
        "Prod.mk".to_string(),
        vec![
            SurfacePattern::Var("a".to_string()),
            SurfacePattern::Wildcard,
        ],
    );
    let val = SurfaceExpr::Ident(span, "expr".to_string());
    let elems = ctx.desugar_pattern_reassign(span, &pat, &val, &[]);
    // Should produce: let __reassign_tmp := expr; a := Prod.fst __reassign_tmp
    // Wildcard produces no reassign
    assert!(
        elems.len() == 2,
        "wildcard should be skipped, expected 2 elements (let + 1 reassign), got {}",
        elems.len()
    );
    assert!(
        matches!(&elems[1], DoElem::Reassign(_, name, _) if name == "a"),
        "second element should be Reassign for 'a'"
    );
}
