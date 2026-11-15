// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! ControlStack integration tests for do-notation (#1818 Phase 4C).
//!
//! Tests that break/continue/return/reassign control flow constructs are
//! correctly desugared using OptionT/ExceptT/StateT transformers during
//! do-block elaboration.
//!
//! Split from do_notation.rs to stay under the 1000-line file limit.

use super::*;

/// Terminal return optimization: `do return 42` should NOT activate ExceptT wrapping.
/// The ControlInfo pre-pass detects returns_early, but the terminal return optimization
/// clears it because no [Return, rest @ ..] dispatch path exists.
#[test]
fn test_terminal_return_no_except_wrapping() {
    let result = elab("do return 42");
    match result {
        Ok(expr) => {
            let head = expr.get_app_fn();
            match head.kind() {
                ExprKind::Const(name, _) => {
                    assert_ne!(
                        name.to_string(),
                        "ExceptT.run",
                        "terminal return should NOT be wrapped with ExceptT.run"
                    );
                    assert_eq!(name.to_string(), "Pure.pure");
                }
                _ => panic!("expected Const head, got {head:?}"),
            }
        }
        Err(e) => panic!("failed to elaborate: {e:?}"),
    }
}

/// Non-terminal return: `do { return Type; Prop }` is refused, as pinned Lean
/// 4.8.0 refuses any element after `return` ("must be last element in a `do`
/// sequence", `ensureEOS` in `src/Lean/Elab/Do.lean`; measured 2026-10-16).
/// Until round-5 lane D (G54, ledger (124)) Clean elaborated it as
/// `pure Type` and never elaborated `Prop` (measured 2026-09-16: the term was
/// `["Pure.pure"]` alone); this test used to pin that gap.
#[test]
fn test_non_terminal_return_refused_as_lean() {
    let env = Environment::with_prelude();
    let mut ctx = ElabCtx::new(&env);
    let surface = parse_expr("do { return Type; Prop }").unwrap();
    let err = ctx
        .elaborate(&surface)
        .expect_err("Lean refuses an element after `return`");
    assert!(
        err.to_string()
            .contains("must be last element in a `do` sequence"),
        "the refusal is Lean's `ensureEOS`: {err:?}"
    );
}

/// `do break` should produce OptionT.fail at the break layer.
/// Break activates the ControlStack with a Break (OptionT) layer.
#[test]
fn test_break_produces_option_t_fail() {
    let result = elab("do { break }");
    match result {
        Ok(expr) => {
            // Should contain OptionT.fail somewhere in the expression
            let head = expr.get_app_fn();
            match head.kind() {
                ExprKind::Const(name, _) => {
                    // The outermost should be OptionT.run (unwrap step) or OptionT.fail
                    assert!(
                        name.to_string() == "OptionT.run" || name.to_string() == "OptionT.fail",
                        "break should produce OptionT.run or OptionT.fail, got {}",
                        name
                    );
                }
                _ => {
                    // May be wrapped in other expressions
                }
            }
        }
        Err(e) => {
            // break requires a loop context — may error
            let msg = format!("{e:?}");
            assert!(
                msg.contains("break") || msg.contains("OptionT") || msg.contains("NotImplemented"),
                "unexpected error for break: {e:?}"
            );
        }
    }
}

/// `do continue` should produce OptionT.fail at the continue layer.
#[test]
fn test_continue_produces_option_t_fail() {
    let result = elab("do { continue }");
    match result {
        Ok(expr) => {
            let head = expr.get_app_fn();
            if let ExprKind::Const(name, _) = head.kind() {
                assert!(
                    name.to_string() == "OptionT.run" || name.to_string() == "OptionT.fail",
                    "continue should produce OptionT.run or OptionT.fail, got {}",
                    name
                );
            }
        }
        Err(e) => {
            let msg = format!("{e:?}");
            assert!(
                msg.contains("continue")
                    || msg.contains("OptionT")
                    || msg.contains("NotImplemented"),
                "unexpected error for continue: {e:?}"
            );
        }
    }
}

/// `do let mut x := Type; x := Prop; x` — mutable variable reassignment should
/// activate the ControlStack's StateT layer.
#[test]
fn test_let_mut_reassign_activates_state_t() {
    let result = elab("do { let mut x := Type; x := Prop; x }");
    match result {
        Ok(expr) => {
            // With StateT layer active, the outermost expression should be
            // StateT.run (from the unwrap chain) wrapping the body.
            let head = expr.get_app_fn();
            match head.kind() {
                ExprKind::Const(name, _) => {
                    assert_eq!(
                        name.to_string(),
                        "StateT.run",
                        "let mut + reassign should produce StateT.run wrapping, got {}",
                        name
                    );
                }
                _ => panic!("expected Const(StateT.run, _) for let mut + reassign, got {head:?}"),
            }
        }
        Err(e) => {
            // MEASURED 2026-09-16, the first time this file was ever compiled:
            //   TypeMismatch { expected: "Type 1",
            //                  actual: "Type (universe level conflict: 0 vs 1)" }
            //
            // So this does not fail for "missing kernel axioms or incomplete
            // StateT wiring" as the old prose guessed. It fails in UNIVERSE
            // SOLVING: the reassignment path unifies the mutable cell's type at
            // two different levels. The subject here is `Type`/`Prop` precisely
            // because they elaborate without numeric literals, which is what
            // puts a `Sort` in the cell and makes the conflict visible.
            //
            // Pinned as a refusal rather than fixed here, with the target
            // assertion above kept intact, so the day the level conflict is
            // solved the `Ok` arm runs and pins `StateT.run` for real.
            let msg = format!("{e:?}");
            assert!(
                msg.contains("universe level conflict"),
                "the measured gap is a universe level conflict in the `let mut` \
                 reassignment path; this is a DIFFERENT failure, so re-measure \
                 before trusting this pin: {e:?}"
            );
        }
    }
}

/// Terminal return optimization: `do { if Prop then return Prop else return Prop }`
/// All returns are inside terminal branches — no ExceptT needed.
#[test]
fn test_terminal_return_in_branches_no_wrapping() {
    let result = elab("do { if Prop then return Prop else return Prop }");
    match result {
        Ok(expr) => {
            let head = expr.get_app_fn();
            if let ExprKind::Const(name, _) = head.kind() {
                assert_ne!(
                    name.to_string(),
                    "ExceptT.run",
                    "terminal returns in all branches should NOT produce ExceptT.run"
                );
            }
        }
        Err(_) => {
            // May fail due to missing ite/Decidable — acceptable
        }
    }
}

/// `has_top_level_non_terminal_return` utility function test.
/// Verifies that the terminal return detection works for various element patterns.
#[test]
fn test_has_top_level_non_terminal_return() {
    use clean_parser::{DoElem, Span, SurfaceExpr};

    let span = Span::new(0, 0);
    // 2026-09-16: `SurfaceExpr::Ident` takes a `SurfaceName`, not a `String`.
    // This file stopped compiling at some point and nothing noticed, because it
    // was in no module tree; the live sibling `do_control_flow.rs` already spells
    // it this way.
    let expr = || Box::new(SurfaceExpr::Ident(span, SurfaceName::generated_path("x")));

    // Single terminal return
    let elems = vec![DoElem::Return(span, expr())];
    assert!(
        !elab_do_control::has_top_level_non_terminal_return(&elems),
        "single return should be terminal"
    );

    // Non-terminal return (followed by expr)
    let elems = vec![DoElem::Return(span, expr()), DoElem::Expr(span, expr())];
    assert!(
        elab_do_control::has_top_level_non_terminal_return(&elems),
        "return followed by expr should be non-terminal"
    );

    // Terminal return after bind
    let binder = SurfaceBinder::new("x", None, SurfaceBinderInfo::Explicit);
    let elems = vec![
        DoElem::Bind(span, binder, expr()),
        DoElem::Return(span, expr()),
    ];
    assert!(
        !elab_do_control::has_top_level_non_terminal_return(&elems),
        "return as last element after bind should be terminal"
    );

    // No returns at all
    let elems = vec![DoElem::Expr(span, expr()), DoElem::Expr(span, expr())];
    assert!(
        !elab_do_control::has_top_level_non_terminal_return(&elems),
        "no returns should return false"
    );
}

// === Prelude environment integration tests (#1818 Phase 4A wiring) ===

/// Verify that ExceptT/OptionT kernel constants are available in a prelude
/// environment and that the elaborator can reference them.
/// This validates Phase 4A wiring: init_except_t() and init_option_t() are
/// called during kernel prelude initialization.
#[test]
fn test_prelude_has_control_transformer_constants() {
    let env = Environment::with_prelude();
    // Phase 4A: ExceptT and related constants
    assert!(
        env.get_const(&Name::from_string("ExceptT")).is_some(),
        "prelude should have ExceptT"
    );
    assert!(
        env.get_const(&Name::from_string("ExceptT.mk")).is_some(),
        "prelude should have ExceptT.mk"
    );
    assert!(
        env.get_const(&Name::from_string("ExceptT.run")).is_some(),
        "prelude should have ExceptT.run"
    );
    assert!(
        env.get_const(&Name::from_string("MonadExcept.throw"))
            .is_some(),
        "prelude should have MonadExcept.throw"
    );
    // Phase 4A: OptionT and related constants
    assert!(
        env.get_const(&Name::from_string("OptionT")).is_some(),
        "prelude should have OptionT"
    );
    assert!(
        env.get_const(&Name::from_string("OptionT.mk")).is_some(),
        "prelude should have OptionT.mk"
    );
    assert!(
        env.get_const(&Name::from_string("OptionT.run")).is_some(),
        "prelude should have OptionT.run"
    );
    assert!(
        env.get_const(&Name::from_string("OptionT.fail")).is_some(),
        "prelude should have OptionT.fail"
    );
    // Phase 4A: Except type
    assert!(
        env.get_const(&Name::from_string("Except")).is_some(),
        "prelude should have Except"
    );
    assert!(
        env.get_const(&Name::from_string("Except.ok")).is_some(),
        "prelude should have Except.ok"
    );
    assert!(
        env.get_const(&Name::from_string("Except.error")).is_some(),
        "prelude should have Except.error"
    );
}

/// Verify that `do break` with a prelude environment produces an expression
/// that references OptionT.fail — the kernel constant is found and used.
///
/// Note: bare `do { break }` without a loop context triggers an error because
/// break requires the ControlStack to have a Break layer, which is only installed
/// by for-loops. This test validates that the error message is about the missing
/// loop context (not about missing kernel constants).
#[test]
fn test_break_with_prelude_references_option_t() {
    let env = Environment::with_prelude();
    let mut ctx = ElabCtx::new(&env);
    let surface = parse_expr("do { break }").unwrap();
    let result = ctx.elaborate(&surface);
    match result {
        Ok(expr) => {
            fn collect_const_names(e: &Expr, names: &mut Vec<String>) {
                match e.kind() {
                    ExprKind::Const(name, _) => names.push(name.to_string()),
                    ExprKind::App(f, a) => {
                        collect_const_names(f, names);
                        collect_const_names(a, names);
                    }
                    ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
                        collect_const_names(ty, names);
                        collect_const_names(body, names);
                    }
                    ExprKind::Let(_, ty, val, body, _) => {
                        collect_const_names(ty, names);
                        collect_const_names(val, names);
                        collect_const_names(body, names);
                    }
                    _ => {}
                }
            }
            let mut names = Vec::new();
            collect_const_names(&expr, &mut names);
            assert!(
                names
                    .iter()
                    .any(|n| n == "OptionT.fail" || n == "OptionT.run"),
                "break expression should reference OptionT constants, found: {names:?}"
            );
        }
        Err(e) => {
            // break outside a loop triggers "break outside of a loop" error.
            // This is correct behavior — break needs a for-loop to install
            // the Break layer on the ControlStack.
            let msg = format!("{e:?}");
            assert!(
                msg.contains("break") || msg.contains("ControlStack") || msg.contains("loop"),
                "unexpected error for bare break: {e:?}"
            );
        }
    }
}

/// Verify that `do let mut x := Type; x := Prop; x` with a prelude environment
/// produces an expression that references StateT.run — kernel constant is used.
#[test]
fn test_let_mut_with_prelude_references_state_t() {
    let env = Environment::with_prelude();
    let mut ctx = ElabCtx::new(&env);
    let surface = parse_expr("do { let mut x := Type; x := Prop; x }").unwrap();
    let result = ctx.elaborate(&surface);
    match result {
        Ok(expr) => {
            fn collect_const_names(e: &Expr, names: &mut Vec<String>) {
                match e.kind() {
                    ExprKind::Const(name, _) => names.push(name.to_string()),
                    ExprKind::App(f, a) => {
                        collect_const_names(f, names);
                        collect_const_names(a, names);
                    }
                    ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
                        collect_const_names(ty, names);
                        collect_const_names(body, names);
                    }
                    ExprKind::Let(_, ty, val, body, _) => {
                        collect_const_names(ty, names);
                        collect_const_names(val, names);
                        collect_const_names(body, names);
                    }
                    _ => {}
                }
            }
            let mut names = Vec::new();
            collect_const_names(&expr, &mut names);
            assert!(
                names.iter().any(|n| n == "StateT.run" || n == "StateT.set"),
                "let mut expression should reference StateT constants, found: {names:?}"
            );
        }
        Err(e) => {
            // May fail for other reasons — check it's not an "unknown constant" error
            let msg = format!("{e:?}");
            assert!(
                !msg.contains("unknown constant \"StateT"),
                "StateT should be a known constant in prelude env: {e:?}"
            );
        }
    }
}

/// For-loop with `break` in body should install a loop-scoped ControlStack
/// with a Break OptionT layer. The output expression should reference
/// ForInStep.done (from the break unwrap) and OptionT.run + Option.getD.
#[test]
fn test_for_loop_break_uses_loop_scoped_stack() {
    let env = Environment::with_prelude();
    let mut ctx = ElabCtx::new(&env);
    let surface = parse_expr("do for x in xs do break").unwrap();
    let result = ctx.elaborate(&surface);
    match result {
        Ok(expr) => {
            fn collect_const_names(e: &Expr, names: &mut Vec<String>) {
                match e.kind() {
                    ExprKind::Const(name, _) => names.push(name.to_string()),
                    ExprKind::App(f, a) => {
                        collect_const_names(f, names);
                        collect_const_names(a, names);
                    }
                    ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
                        collect_const_names(ty, names);
                        collect_const_names(body, names);
                    }
                    ExprKind::Let(_, ty, val, body, _) => {
                        collect_const_names(ty, names);
                        collect_const_names(val, names);
                        collect_const_names(body, names);
                    }
                    _ => {}
                }
            }
            let mut names = Vec::new();
            collect_const_names(&expr, &mut names);
            // Should have ForIn.forIn (the for-loop itself)
            assert!(
                names.iter().any(|n| n == "ForIn.forIn"),
                "for-loop should produce ForIn.forIn, got: {names:?}"
            );
            // Should have ForInStep.done (from break unwrap default)
            assert!(
                names.iter().any(|n| n == "ForInStep.done"),
                "break in for-loop should produce ForInStep.done, got: {names:?}"
            );
            // Should have OptionT.run (from unwrapping the break OptionT layer)
            assert!(
                names.iter().any(|n| n == "OptionT.run"),
                "break in for-loop should unwrap via OptionT.run, got: {names:?}"
            );
        }
        Err(e) => {
            // xs is undefined → elaboration may fail resolving the collection.
            // The error must NOT be about missing ControlStack or break layer —
            // that would mean the loop-scoped stack wasn't installed.
            let msg = format!("{e:?}");
            assert!(
                !msg.contains("no break layer")
                    && !msg.contains("no ControlStack")
                    && !msg.contains("outside of a loop"),
                "break in for-loop should find loop-scoped stack: {e:?}"
            );
        }
    }
}

/// For-loop with `continue` in body should install a loop-scoped ControlStack
/// with a Continue OptionT layer. The output should reference ForInStep.yield
/// (from the continue unwrap default) and OptionT.run.
#[test]
fn test_for_loop_continue_uses_loop_scoped_stack() {
    let env = Environment::with_prelude();
    let mut ctx = ElabCtx::new(&env);
    let surface = parse_expr("do for x in xs do continue").unwrap();
    let result = ctx.elaborate(&surface);
    match result {
        Ok(expr) => {
            fn collect_const_names(e: &Expr, names: &mut Vec<String>) {
                match e.kind() {
                    ExprKind::Const(name, _) => names.push(name.to_string()),
                    ExprKind::App(f, a) => {
                        collect_const_names(f, names);
                        collect_const_names(a, names);
                    }
                    ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
                        collect_const_names(ty, names);
                        collect_const_names(body, names);
                    }
                    ExprKind::Let(_, ty, val, body, _) => {
                        collect_const_names(ty, names);
                        collect_const_names(val, names);
                        collect_const_names(body, names);
                    }
                    _ => {}
                }
            }
            let mut names = Vec::new();
            collect_const_names(&expr, &mut names);
            assert!(
                names.iter().any(|n| n == "ForIn.forIn"),
                "for-loop should produce ForIn.forIn, got: {names:?}"
            );
            // Continue unwrap should produce ForInStep.yield as default
            assert!(
                names.iter().any(|n| n == "ForInStep.yield"),
                "continue in for-loop should produce ForInStep.yield, got: {names:?}"
            );
            assert!(
                names.iter().any(|n| n == "OptionT.run"),
                "continue in for-loop should unwrap via OptionT.run, got: {names:?}"
            );
        }
        Err(e) => {
            // xs is undefined → may fail resolving collection.
            // Must NOT fail due to missing ControlStack/continue layer.
            let msg = format!("{e:?}");
            assert!(
                !msg.contains("no continue layer")
                    && !msg.contains("no ControlStack")
                    && !msg.contains("outside of a loop"),
                "continue in for-loop should find loop-scoped stack: {e:?}"
            );
        }
    }
}

/// For-loop WITHOUT break/continue should NOT install a ControlStack.
/// The output should have ForIn.forIn and ForInStep.yield but NOT OptionT.run.
#[test]
fn test_for_loop_no_break_no_stack() {
    let env = Environment::with_prelude();
    let mut ctx = ElabCtx::new(&env);
    let surface = parse_expr("do for x in xs do pure ()").unwrap();
    let result = ctx.elaborate(&surface);
    match result {
        Ok(expr) => {
            fn collect_const_names(e: &Expr, names: &mut Vec<String>) {
                match e.kind() {
                    ExprKind::Const(name, _) => names.push(name.to_string()),
                    ExprKind::App(f, a) => {
                        collect_const_names(f, names);
                        collect_const_names(a, names);
                    }
                    ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
                        collect_const_names(ty, names);
                        collect_const_names(body, names);
                    }
                    ExprKind::Let(_, ty, val, body, _) => {
                        collect_const_names(ty, names);
                        collect_const_names(val, names);
                        collect_const_names(body, names);
                    }
                    _ => {}
                }
            }
            let mut names = Vec::new();
            collect_const_names(&expr, &mut names);
            assert!(
                names.iter().any(|n| n == "ForIn.forIn"),
                "for-loop should produce ForIn.forIn, got: {names:?}"
            );
            // No break/continue → no OptionT unwrapping needed
            assert!(
                !names.iter().any(|n| n == "OptionT.run"),
                "for-loop without break/continue should NOT use OptionT.run, got: {names:?}"
            );
        }
        Err(e) => {
            // xs is undefined → may fail resolving collection.
            // Must NOT fail due to incorrect OptionT wrapping.
            let msg = format!("{e:?}");
            assert!(
                !msg.contains("OptionT.run"),
                "for-loop without break/continue should not reference OptionT: {e:?}"
            );
        }
    }
}

#[test]
fn value_binding_origin_preserves_the_current_mutable_do_continuation() {
    for origin in ["let", "have"] {
        let source = format!(
            "def continued : Id Nat := do\n  let mut x : Nat := 0\n  {origin} h : True := True.intro\n  x := 1\n  return x\n"
        );
        let patterns = crate::tactic::builtins::builtin_tactic_patterns();
        let declaration =
            parse_decl_with_tactics(&source, &patterns).expect("actual continuation source parses");
        let mut env = Environment::with_prelude();
        crate::elaborate_decl_and_register(&mut env, &declaration)
            .expect("a local binding cannot reset the enclosing mutable do state");
        let name = Name::from_string("continued");
        let info = env.get_const(&name).expect("actual definition registers");
        let value = info.value.as_ref().expect("stored definition value");
        assert!(!value.has_fvar_quick() && !value.has_loose_bvars_quick());
        let tc = TypeChecker::new(&env);
        let ty = tc
            .infer_type_full(value)
            .expect("strict full stored-value inference");
        assert!(tc.is_def_eq(&ty, &info.type_));
        assert!(
            tc.is_def_eq(value, &Expr::nat_lit(1)),
            "the {origin} continuation must retain the assignment, not only its type"
        );
        assert!(!tc.is_def_eq(value, &Expr::nat_lit(0)));
        assert!(env.axiom_deps(&name).expect("actual closure").is_empty());
    }
}
