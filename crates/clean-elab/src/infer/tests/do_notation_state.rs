// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! StateT integration tests for do-notation elaboration (#1818 Phase 4C).
//!
//! Tests for `let mut` reassignment, single-variable StateT wrapping,
//! multi-variable product projection, and control flow interaction with StateT.
//! Split from do_notation.rs for file size.

use super::*;

/// Helper: assert outermost expression is a named `Const`.
#[allow(dead_code)]
fn assert_head_is(expr: &Expr, expected: &str, context: &str) {
    let head = expr.get_app_fn();
    match head.kind() {
        ExprKind::Const(name, _) => {
            assert_eq!(name.to_string(), expected, "{context}: got {name}");
        }
        _ => panic!("{context}: expected Const({expected}, _), got {head:?}"),
    }
}

#[allow(dead_code)]
fn strip_lets(mut expr: &Expr) -> &Expr {
    while let ExprKind::Let(_, _, _, body, _) = expr.kind() {
        expr = body;
    }
    expr
}

/// Recursively search an `Expr` for a `Const` with the given name.
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

/// B08: the pure state-threading lane must never emit a `StateT` transformer.
fn expr_contains_state_t(expr: &Expr) -> bool {
    expr_contains_const(expr, "StateT.run")
        || expr_contains_const(expr, "StateT.set")
        || expr_contains_const(expr, "StateT.get")
}

fn nat_state_elab(input: &str) -> Result<Expr, ElabError> {
    let env = Environment::with_prelude();
    elab_with_env(&env, input)
}

/// Prelude environment with `xs : List Unit` — a collection that really has a
/// `ForIn` instance.
///
/// `nat_state_for_env` below declares `xs : Type`, which is deliberately NOT
/// iterable (its tests assert a descope). A test that wants the for-loop to
/// ELABORATE needs a real list, or `elab_ident("xs")` fails and the test
/// silently passes through its `Err` branch — the #1915 class.
fn list_unit_for_env() -> Environment {
    use clean_kernel::env::Declaration;
    use clean_kernel::name::Name;
    use clean_kernel::Level;

    let mut env = Environment::with_prelude();
    let list_unit = Expr::app(
        Expr::const_(Name::from_string("List"), vec![Level::zero()]),
        Expr::const_(Name::from_string("Unit"), vec![]),
    );
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("xs"),
        level_params: vec![],
        type_: list_unit,
    })
    .expect("adding xs axiom");
    env
}

fn nat_state_for_env() -> Environment {
    use clean_kernel::env::Declaration;
    use clean_kernel::name::Name;

    let mut env = Environment::with_prelude();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("xs"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .expect("adding xs axiom");
    env
}

fn opaque_do_condition_env() -> Environment {
    use clean_kernel::env::Declaration;

    let mut env = Environment::with_prelude();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("OpaqueDoP"),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .expect("register opaque do-condition proposition");
    env
}

#[test]
fn do_if_missing_decidable_fails_without_synthetic_sorry() {
    use clean_kernel::sorry::{reset_sorry_counter, synthetic_sorry_count};

    let env = opaque_do_condition_env();
    reset_sorry_counter();
    let before = synthetic_sorry_count();
    let err = elab_with_env(
        &env,
        "do { if OpaqueDoP then return (1 : Nat) else return (0 : Nat) }",
    )
    .expect_err("do-if must reject a missing Decidable instance");
    assert!(
        matches!(err, ElabError::FailedToSynthesize { ref class_name, .. } if class_name == &Name::from_string("Decidable")),
        "expected typed do-if Decidable synthesis failure, got {err:?}"
    );
    assert_eq!(synthetic_sorry_count(), before);
}

#[test]
fn pure_mutable_if_missing_decidable_fails_without_synthetic_sorry() {
    use clean_kernel::sorry::{reset_sorry_counter, synthetic_sorry_count};
    use clean_parser::{DoElem, Span, SurfaceExpr, SurfaceLit};

    let env = opaque_do_condition_env();
    let mut ctx = ElabCtx::new(&env);
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    ctx.push_local(SurfaceName::generated_path("x"), nat_ty);
    ctx.do_mut_vars.push(SurfaceName::generated_path("x"));
    let cond = SurfaceExpr::Ident(Span::dummy(), SurfaceName::generated_path("OpaqueDoP"));
    let then_branch = [DoElem::Reassign(
        Span::dummy(),
        SurfaceName::generated_path("x"),
        Box::new(SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(1))),
    )];
    let else_branch = [DoElem::Reassign(
        Span::dummy(),
        SurfaceName::generated_path("x"),
        Box::new(SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(2))),
    )];
    reset_sorry_counter();
    let before = synthetic_sorry_count();
    let err = ctx
        .elab_do_pure_if(&cond, &then_branch, Some(&else_branch), &[])
        .expect_err("pure mutable if must reject a missing Decidable instance");
    assert!(
        matches!(err, ElabError::FailedToSynthesize { ref class_name, .. } if class_name == &Name::from_string("Decidable")),
        "expected typed mutable-if Decidable synthesis failure, got {err:?}"
    );
    assert_eq!(synthetic_sorry_count(), before);
}

// === Single-variable StateT tests ===

/// B08: `do let mut x := 0; x := 1; x` — reassignment desugars to
/// `let`-shadowing, so the term is a plain nested `Let`, NOT a `StateT` stack.
#[test]
fn test_let_mut_reassign_desugars_to_let_shadowing() {
    let result = nat_state_elab("do { let mut x := 0; x := 1; x }");
    match result {
        Ok(expr) => {
            assert!(
                matches!(expr.kind(), ExprKind::Let(_, _, _, _, _)),
                "reassignment should be plain nested Let, got {expr:?}"
            );
            assert!(
                !expr_contains_state_t(&expr),
                "pure reassignment must not use the StateT transformer, got {expr:?}"
            );
        }
        // FAIL-CLOSED since 2026-09-16: MEASURED, `nat_state_elab` succeeds on
        // this input (outermost `Let`, no `StateT` const). The sibling
        // `test_let_mut_reassign_full_structure` already panics on `Err` for
        // the same input, so this arm could only ever hide a regression.
        Err(e) => panic!("`do {{ let mut x := 0; x := 1; x }}` must elaborate: {e:?}"),
    }
}

/// Terminal return optimization: `do { if <guard> then return Prop else return Prop }`
/// All returns are inside terminal branches — no ExceptT needed.
///
/// BROKEN FIXTURE, repaired 2026-09-16. `elab(...)` is a bare
/// `Environment::new()` and `Prop` is not a conditional guard, so this
/// elaboration has never succeeded: MEASURED, bare env gives
/// `TypeMismatch { expected: "valid type", actual: "Unknown constant: Pure.pure" }`
/// and the prelude gives `expected: "conditional guard of type Bool or Prop"`.
/// The `if let Ok(...)` wrapper turned that permanent failure into a pass, so
/// the `assert_ne!` inside it never ran. With the prelude and a `Bool` guard
/// the term elaborates (MEASURED: head `ite`, no `ExceptT`).
#[test]
fn test_terminal_return_in_branches_no_wrapping() {
    let env = Environment::with_prelude();
    let expr = elab_with_env(
        &env,
        "do { if Bool.true then return Prop else return Prop }",
    )
    .expect("terminal returns in both branches of a Bool guard must elaborate");
    let head = expr.get_app_fn();
    match head.kind() {
        ExprKind::Const(name, _) => assert_ne!(
            name.to_string(),
            "ExceptT.run",
            "terminal returns in all branches should NOT produce ExceptT.run"
        ),
        other => panic!("expected a Const head for the guarded do-block, got {other:?}"),
    }
    assert!(
        !expr_contains_const(&expr, "ExceptT.run"),
        "terminal returns in all branches must not reach the ExceptT transformer"
    );
}

// === End-to-end StateT integration tests (#1818 Phase 4C) ===

/// B08: `do { let mut x := 0; x := 1; x }` structure — the body is a nested
/// `let x := 0; let x := 1; x` (shadowing), with the `let mut` value staying a
/// `Nat` term and no `StateT` transformer anywhere.
#[test]
fn test_let_mut_reassign_full_structure() {
    let result = nat_state_elab("do { let mut x := 0; x := 1; x }");
    match result {
        Ok(expr) => {
            assert!(
                !expr_contains_state_t(&expr),
                "pure reassignment must not use StateT, got {expr:?}"
            );
            // Outer Let is `let x := 0`; its value stays a Nat term.
            if let ExprKind::Let(_, _, let_val, let_body, _) = expr.kind() {
                assert!(
                    !matches!(let_val.kind(), ExprKind::Sort(_)),
                    "let mut value should stay a Nat term, got {let_val:?}"
                );
                // Inner: `let x := 1` (the reassignment shadow), not a Bind.bind.
                assert!(
                    matches!(let_body.kind(), ExprKind::Let(_, _, _, _, _)),
                    "reassignment should be an inner shadowing Let, got {let_body:?}"
                );
            } else {
                panic!("outermost should be Let, got {expr:?}");
            }
        }
        Err(e) => panic!("failed to elaborate let mut + reassign: {e:?}"),
    }
}

/// B08: `do { let mut x := 0; x := 1; pure x }` — reassign then pure return.
/// Nested lets ending in `Pure.pure`, no `StateT`.
#[test]
fn test_let_mut_reassign_then_pure() {
    let result = nat_state_elab("do { let mut x := 0; x := 1; pure x }");
    match result {
        Ok(expr) => {
            assert!(
                matches!(expr.kind(), ExprKind::Let(_, _, _, _, _)),
                "reassign then pure should be nested Let, got {expr:?}"
            );
            assert!(
                !expr_contains_state_t(&expr),
                "reassign then pure must not use StateT, got {expr:?}"
            );
            assert!(
                expr_contains_const(&expr, "Pure.pure"),
                "the terminal `pure x` should be Pure.pure, got {expr:?}"
            );
        }
        // FAIL-CLOSED since 2026-09-16: MEASURED, this input elaborates
        // (`Environment::with_prelude()`, outermost `Let`, `Pure.pure` present,
        // no `StateT`). The disjunctive arm only protected the three assertions
        // above from ever running.
        Err(e) => panic!("`do {{ let mut x := 0; x := 1; pure x }}` must elaborate: {e:?}"),
    }
}

/// `do { let mut x := 0; x := true; x }` — reassignment must reject values that
/// do not match the mutable local's tracked type (B08 enforces the type before
/// building the shadowing `let`).
#[test]
fn test_let_mut_reassign_rejects_mismatched_type() {
    let err = nat_state_elab("do { let mut x := 0; x := true; x }")
        .expect_err("mismatched let mut reassignment should be rejected");
    assert!(
        matches!(err, ElabError::TypeMismatch { .. }),
        "expected TypeMismatch for mismatched let mut reassignment, got {err:?}"
    );
}

/// `do { let mut x := 0; x }` — let mut WITHOUT reassignment = no StateT.
#[test]
fn test_let_mut_without_reassign_no_state_t() {
    let result = nat_state_elab("do { let mut x := 0; x }");
    match result {
        Ok(expr) => {
            if let ExprKind::Const(name, _) = expr.get_app_fn().kind() {
                assert_ne!(
                    name.to_string(),
                    "StateT.run",
                    "let mut without reassignment should NOT produce StateT.run"
                );
            }
            assert!(
                matches!(expr.kind(), ExprKind::Let(_, _, _, _, _)),
                "let mut without reassign should be plain Let, got {expr:?}"
            );
        }
        Err(e) => panic!("failed to elaborate let mut without reassign: {e:?}"),
    }
}

/// B08: `do { let mut x := 0; x := 1; x := 2; x }` — a double reassign chains
/// as three nested shadowing `let`s (`0 → 1 → 2`), no `StateT`.
#[test]
fn test_let_mut_double_reassign() {
    let result = nat_state_elab("do { let mut x := 0; x := 1; x := 2; x }");
    match result {
        Ok(expr) => {
            assert!(
                !expr_contains_state_t(&expr),
                "double reassign must not use StateT, got {expr:?}"
            );
            // Three nested lets: let x:=0; let x:=1; let x:=2; x
            let mut depth = 0;
            let mut cur = &expr;
            while let ExprKind::Let(_, _, _, body, _) = cur.kind() {
                depth += 1;
                cur = body;
            }
            assert!(
                depth >= 3,
                "double reassign should nest at least 3 lets, got {depth}"
            );
        }
        Err(e) => panic!("failed to elaborate double reassign: {e:?}"),
    }
}

// === Multi-variable StateT tests (#1818 Phase 4C — product projection) ===

/// B08: two mutable variables with only `x` reassigned — straight-line
/// reassignment threads each mut var independently via `let`-shadowing (no
/// product-`StateT` tuple).
#[test]
fn test_multi_var_two_mutable_vars_reassign_first() {
    let result = nat_state_elab("do { let mut x := 0; let mut y := 1; x := 2; y }");
    match result {
        Ok(expr) => {
            assert!(
                matches!(expr.kind(), ExprKind::Let(_, _, _, _, _)),
                "multi-var reassign should be nested Let, got {expr:?}"
            );
            assert!(
                !expr_contains_state_t(&expr),
                "multi-var straight-line reassign must not use StateT, got {expr:?}"
            );
        }
        Err(e) => panic!("failed to elaborate multi-var: {e:?}"),
    }
}

/// B08: two mutable variables with only `y` reassigned — still pure
/// `let`-shadowing, no `StateT.get` rebind.
#[test]
fn test_multi_var_reassign_second() {
    let result = nat_state_elab("do { let mut x := 0; let mut y := 1; y := 2; x }");
    match result {
        Ok(expr) => {
            assert!(
                matches!(expr.kind(), ExprKind::Let(_, _, _, _, _)),
                "multi-var reassign second should be nested Let, got {expr:?}"
            );
            assert!(
                !expr_contains_state_t(&expr),
                "multi-var reassign second must not use StateT, got {expr:?}"
            );
        }
        Err(e) => panic!("failed to elaborate multi-var reassign second: {e:?}"),
    }
}

/// B08: multi-var with both variables reassigned sequentially — four nested
/// shadowing lets, no `StateT`/`Prod.mk` tuple.
#[test]
fn test_multi_var_both_reassigned() {
    let result = nat_state_elab("do { let mut x := 0; let mut y := 1; x := 2; y := 3; x }");
    match result {
        Ok(expr) => {
            assert!(
                !expr_contains_state_t(&expr),
                "multi-var double reassign must not use StateT, got {expr:?}"
            );
            let mut depth = 0;
            let mut cur = &expr;
            while let ExprKind::Let(_, _, _, body, _) = cur.kind() {
                depth += 1;
                cur = body;
            }
            assert!(
                depth >= 4,
                "two decls + two reassigns should nest 4 lets, got {depth}"
            );
        }
        Err(e) => panic!("failed to elaborate multi-var both reassigned: {e:?}"),
    }
}

// === For-loop + mutation is descoped LOUD (B08) ===
//
// A `for` loop that mutates a `let mut` variable needs the `ForIn`/`ForInStep`
// join-point machinery, which is outside the pure state-threading lane. The
// old StateT path emitted unbound-fvar terms (GAP_SWEEP do_notation p12); B08
// rejects these LOUD with a typed `Unsupported` instead.

/// Assert a for-loop-with-mutation block is descoped LOUD, never a term.
fn assert_for_loop_descope(env: &Environment, input: &str) {
    let err = elab_with_env(env, input)
        .expect_err("for-loop with mutation must be a typed descope, not a silent term");
    let msg = format!("{err:?}");
    assert!(
        matches!(err, ElabError::Unsupported { .. }),
        "for-loop + mutation should be a typed Unsupported error, got {err:?}"
    );
    assert!(
        !msg.contains("free variable") && !msg.contains("9223372036854775808"),
        "descope must not leak unbound fvars, got {msg}"
    );
}

/// `do { let mut x := 0; for y in xs do x := 1; x }` — descoped LOUD.
#[test]
fn test_for_loop_with_mut_var_reassign() {
    assert_for_loop_descope(
        &nat_state_for_env(),
        "do { let mut x := 0; for y in xs do x := 1; x }",
    );
}

/// `do { let mut x := 0; for y in xs do x := true; x }` — the type mismatch is
/// now masked by the earlier for-loop descope; still LOUD, never a term.
#[test]
fn test_for_loop_mut_reassign_rejects_mismatched_type() {
    assert_for_loop_descope(
        &nat_state_for_env(),
        "do { let mut x := 0; for y in xs do x := true; x }",
    );
}

/// `do { let mut x := 0; for y in xs do x := 1 }` — descoped LOUD.
#[test]
fn test_for_loop_mut_reassign_only() {
    assert_for_loop_descope(
        &nat_state_for_env(),
        "do { let mut x := 0; for y in xs do x := 1 }",
    );
}

/// `do { let mut x := 0; let mut y := 1; for z in xs do x := 2; y }` — descoped LOUD.
#[test]
fn test_for_loop_multi_var_projection() {
    assert_for_loop_descope(
        &nat_state_for_env(),
        "do { let mut x := 0; let mut y := 1; for z in xs do x := 2; y }",
    );
}

/// `do { let mut x := 0; for y in xs do return 1; x }`: the `for` body is the
/// sequence `return 1; x`, which pinned Lean 4.8.0 refuses ("must be last
/// element in a `do` sequence", measured 2026-10-16); so does Clean since
/// round-5 lane D (G54).
#[test]
fn test_for_loop_mut_and_early_return() {
    let err = nat_state_elab("do { let mut x := 0; for y in xs do return 1; x }")
        .expect_err("Lean refuses an element after `return` in the loop body");
    assert!(
        format!("{err:?}").contains("must be last element in a `do` sequence"),
        "the refusal is Lean's: {err:?}"
    );
}

#[test]
fn test_for_loop_mut_structural_bind_get() {
    assert_for_loop_descope(
        &nat_state_for_env(),
        "do { let mut x := 0; for y in xs do x := 1; pure x }",
    );
}

/// For-loop WITHOUT mutable variables should NOT inject a StateT projection.
/// `do { for x in xs do return x }` — no `let mut` in scope.
///
/// BROKEN FIXTURE, repaired 2026-09-16 — the #1915 class named in
/// `do_control_flow.rs::for_loop_env`. This test called `elab(...)`, a bare
/// `Environment::new()` in which `xs` is unbound, so the elaboration was always
/// `UnknownIdent("xs")` and the `Err` arm's `msg.contains("xs")` accepted it:
/// the `assert_ne!` in the `Ok` arm never ran once. With `xs : List Unit`
/// declared the term elaborates (MEASURED: head `Bind.bind`, containing
/// `List.rec`, `ForInStep.done` and `Option.some`, and no `StateT` const).
#[test]
fn test_for_loop_no_mut_no_projection() {
    let env = list_unit_for_env();
    let expr = elab_with_env(&env, "do { for x in xs do return x }")
        .expect("a for-loop over a real List must elaborate with no mut in scope");
    let head = expr.get_app_fn();
    match head.kind() {
        ExprKind::Const(name, _) => assert_ne!(
            name.to_string(),
            "StateT.run",
            "for-loop without mut should NOT produce StateT.run"
        ),
        other => panic!("expected a Const head for the for-loop, got {other:?}"),
    }
    assert!(
        !expr_contains_state_t(&expr),
        "a for-loop with no mut in scope must not reach the StateT transformer"
    );
}

#[test]
fn do_conditionals_reject_type_valued_guards_before_instance_synthesis() {
    use clean_parser::{DoElem, Span, SurfaceExpr, SurfaceLit};

    let env = Environment::with_prelude();
    let source = "do { if Type then return 1 else return 0 }";
    let err = elab_with_env(&env, source)
        .expect_err("a type-valued do guard is neither Bool nor a proposition");
    assert!(
        matches!(err, ElabError::TypeMismatch { ref expected, .. } if expected.contains("conditional guard")),
        "{source} must fail at do-condition classification, got {err:?}"
    );

    // Exercise the separate pure-mutable `mk_do_ite` lane directly; the surface
    // dispatcher deliberately descopes this branch shape before reaching it.
    let mut ctx = ElabCtx::new(&env);
    ctx.push_local(
        SurfaceName::generated_path("x"),
        Expr::const_(Name::from_string("Nat"), vec![]),
    );
    ctx.do_mut_vars.push(SurfaceName::generated_path("x"));
    let branch = |value| {
        [DoElem::Reassign(
            Span::dummy(),
            SurfaceName::generated_path("x"),
            Box::new(SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(value))),
        )]
    };
    let then_branch = branch(1);
    let else_branch = branch(2);
    let err = ctx
        .elab_do_pure_if(
            &SurfaceExpr::Ident(Span::dummy(), SurfaceName::generated_path("Type")),
            &then_branch,
            Some(&else_branch),
            &[],
        )
        .expect_err("the pure-mutable lane must reject a type-valued guard");
    assert!(
        matches!(err, ElabError::TypeMismatch { ref expected, .. } if expected.contains("conditional guard")),
        "pure-mutable do-if must fail at condition classification, got {err:?}"
    );
}
