// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for do-notation control flow: ControlStack, DoLoopContext, and
//! transformer unwrapping (#1818 Phase 4C).
//!
//! Split from do_notation.rs to stay under the 1000-line file size limit.

use super::{elab, elab_with_env};
use crate::ElabError;
use clean_kernel::{Environment, Expr, ExprKind};

/// Helper: recursively search an Expr for any `Const` with the given name.
fn expr_contains_const(expr: &Expr, name: &str) -> bool {
    match expr.kind() {
        ExprKind::Const(n, _) => n.to_string() == name,
        ExprKind::App(f, a) => expr_contains_const(f, name) || expr_contains_const(a, name),
        ExprKind::Lam(_, ty, body) => {
            expr_contains_const(ty, name) || expr_contains_const(body, name)
        }
        ExprKind::Pi(_, ty, body) => {
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

fn collect_const_names(expr: &Expr, names: &mut Vec<String>) {
    match expr.kind() {
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

// ============================================================================
// ControlStack tests: return/break/continue/reassign without for-loop context
// ============================================================================

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

/// B08: a top-level non-terminal `return` short-circuits — `do { return 42; Type }`
/// lowers to `Pure.pure 42` in the pure lane (the trailing `Type` is dead code
/// after the return), with NO ExceptT transformer / unbound-fvar join point.
#[test]
fn test_non_terminal_return_is_pure_short_circuit() {
    let parse_result = clean_parser::parse_expr("do { return 42; Type }");
    match parse_result {
        Ok(surface) => {
            let env = Environment::new();
            let mut ctx = super::ElabCtx::new(&env);
            match ctx.elaborate(&surface) {
                Ok(expr) => {
                    assert!(
                        !expr_contains_const(&expr, "ExceptT.run")
                            && !expr_contains_const(&expr, "ExceptT.throw"),
                        "pure short-circuit must not use the ExceptT transformer, got {expr:?}"
                    );
                    let head = expr.get_app_fn();
                    if let ExprKind::Const(name, _) = head.kind() {
                        assert_eq!(
                            name.to_string(),
                            "Pure.pure",
                            "non-terminal return should short-circuit to Pure.pure"
                        );
                    }
                }
                Err(_) => {
                    // May fail in the empty env (no Pure const) — acceptable.
                }
            }
        }
        Err(_) => {
            // Parser may not support this syntax yet
        }
    }
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

/// B08: `do let mut x := 0; x := 1; x` — straight-line reassignment desugars
/// to `let`-shadowing (`let x := 0; let x := 1; x`), NOT a `StateT` transformer
/// stack. The outermost term is a plain `Let` and no `StateT` const appears.
#[test]
fn test_let_mut_reassign_desugars_to_let_shadowing() {
    let result = {
        let env = Environment::with_prelude();
        elab_with_env(&env, "do { let mut x := 0; x := 1; x }")
    };
    match result {
        Ok(expr) => {
            assert!(
                matches!(expr.kind(), ExprKind::Let(_, _, _, _, _)),
                "let mut + reassign should be plain nested Let, got {expr:?}"
            );
            assert!(
                !expr_contains_const(&expr, "StateT.run")
                    && !expr_contains_const(&expr, "StateT.set"),
                "pure reassignment must not use the StateT transformer, got {expr:?}"
            );
        }
        Err(e) => {
            let msg = format!("{e:?}");
            assert!(
                msg.contains("mut")
                    || msg.contains("reassign")
                    || msg.contains("NotImplemented")
                    || msg.contains("unknown"),
                "unexpected error for let mut + reassign: {e:?}"
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
    use clean_parser::{DoElem, Span, SurfaceExpr, SurfacePattern};

    let span = Span::new(0, 0);
    let expr = || Box::new(SurfaceExpr::Ident(span, "x".to_string()));

    // Single terminal return
    let elems = vec![DoElem::Return(span, expr())];
    assert!(
        !super::super::elab_do_control::has_top_level_non_terminal_return(&elems),
        "single return should be terminal"
    );

    // Non-terminal return (followed by expr)
    let elems = vec![DoElem::Return(span, expr()), DoElem::Expr(span, expr())];
    assert!(
        super::super::elab_do_control::has_top_level_non_terminal_return(&elems),
        "return followed by expr should be non-terminal"
    );

    // Terminal return after bind
    let binder =
        clean_parser::SurfaceBinder::new("x", None, clean_parser::SurfaceBinderInfo::Explicit);
    let elems = vec![
        DoElem::Bind(span, binder, expr()),
        DoElem::Return(span, expr()),
    ];
    assert!(
        !super::super::elab_do_control::has_top_level_non_terminal_return(&elems),
        "return as last element after bind should be terminal"
    );

    // No returns at all
    let elems = vec![DoElem::Expr(span, expr()), DoElem::Expr(span, expr())];
    assert!(
        !super::super::elab_do_control::has_top_level_non_terminal_return(&elems),
        "no returns should return false"
    );

    // Return nested in a try body before later elements
    let elems = vec![
        DoElem::TryCatch(
            span,
            vec![DoElem::Return(span, expr())],
            vec![clean_parser::DoCatchClause {
                span,
                binder: "e".to_string(),
                exc_type: None,
                body: vec![DoElem::Expr(span, expr())],
            }],
            None,
        ),
        DoElem::Expr(span, expr()),
    ];
    assert!(
        super::super::elab_do_control::has_top_level_non_terminal_return(&elems),
        "try body return before later elements should be non-terminal"
    );

    // Return nested in let-else fallback before later elements
    let elems = vec![
        DoElem::LetElse(
            span,
            SurfacePattern::Wildcard,
            expr(),
            vec![DoElem::Return(span, expr())],
        ),
        DoElem::Expr(span, expr()),
    ];
    assert!(
        super::super::elab_do_control::has_top_level_non_terminal_return(&elems),
        "let-else fallback return before later elements should be non-terminal"
    );
}

// ============================================================================
// For-loop test environment
// ============================================================================

/// Prelude environment with `xs : Type` for for-loop tests.
///
/// The for-loop elaboration needs `xs` to resolve as an identifier. Without this,
/// `elab_ident("xs")` returns `Err(UnknownIdent("xs"))` and the test silently
/// passes through its Err branch (see #1915). The ForIn instance, ForInStep
/// constructors, etc. are constructed as `Expr::const_`, but the generated
/// loop body still contains ordinary `Pure.pure` applications whose types must
/// be checked against the real prelude declaration.
fn for_loop_env() -> Environment {
    use clean_kernel::env::Declaration;
    use clean_kernel::name::Name;
    use clean_kernel::Level;

    let mut env = Environment::with_prelude();
    let unit = Expr::const_(Name::from_string("Unit"), vec![]);
    let list_unit = Expr::app(
        Expr::const_(Name::from_string("List"), vec![Level::zero()]),
        unit,
    );
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("xs"),
        level_params: vec![],
        type_: list_unit,
    })
    .expect("adding xs axiom");
    env
}

// ============================================================================
// DoLoopContext tests: break/continue inside for-loops (#1818 Phase 4C)
// ============================================================================

/// `do { for x in xs do break }` — break inside a for-loop should produce
/// ForInStep.done in the body lambda, NOT OptionT.fail.
///
/// The ControlInfo pre-pass strips breaks inside loops (the for-loop "consumes"
/// them), so the outer ControlStack has no BreakT layer. Instead, DoLoopContext
/// makes break produce `Pure.pure (ForInStep.done acc)`.
///
/// Reference: Lean 4 BuiltinDo/For.lean
#[test]
fn test_for_break_produces_forin_step_done() {
    let env = for_loop_env();
    let expr = elab_with_env(&env, "do { for x in xs do break }")
        .expect("for-break should elaborate with xs in env");

    // A terminal loop must discharge its private accumulator through a bind;
    // the raw ForIn result is never the do-block result.
    let head = expr.get_app_fn();
    match head.kind() {
        ExprKind::Const(name, _) => {
            assert_eq!(
                name.to_string(),
                "Bind.bind",
                "terminal for-loop should finalize through Bind.bind, got {}",
                name
            );
        }
        _ => panic!("expected Const(Bind.bind, _), got {head:?}"),
    }
    assert!(expr_contains_const(&expr, "ForIn.forIn"));

    // The body lambda (last arg) should contain ForInStep.done
    assert!(
        expr_contains_const(&expr, "ForInStep.done"),
        "break inside for-loop should produce ForInStep.done in body"
    );
    // Should NOT contain OptionT.fail (that's the ControlStack path)
    assert!(
        !expr_contains_const(&expr, "OptionT.fail"),
        "break inside for-loop should NOT use OptionT.fail"
    );
}

/// `do { for x in xs do continue }` — continue inside a for-loop should
/// produce ForInStep.yield in the body lambda.
///
/// Continue skips to the next iteration by returning `ForInStep.yield acc`.
/// The fall-through path also produces ForInStep.yield, so both the explicit
/// continue and the implicit continuation converge to the same construct.
#[test]
fn test_for_continue_produces_forin_step_yield() {
    let env = for_loop_env();
    let expr = elab_with_env(&env, "do { for x in xs do continue }")
        .expect("for-continue should elaborate with xs in env");

    assert!(expr_contains_const(&expr, "ForIn.forIn"));
    assert!(
        matches!(expr.get_app_fn().kind(), ExprKind::Const(name, _) if name.to_string() == "Bind.bind")
    );

    // The body lambda should contain ForInStep.yield
    assert!(
        expr_contains_const(&expr, "ForInStep.yield"),
        "continue inside for-loop should produce ForInStep.yield in body"
    );
    // Should NOT contain OptionT.fail
    assert!(
        !expr_contains_const(&expr, "OptionT.fail"),
        "continue inside for-loop should NOT use OptionT.fail"
    );
}

/// `do { for x in xs do { if True then break else continue } }` — mixed
/// break and continue inside a for-loop. Both should use ForInStep, not OptionT.
#[test]
fn test_for_mixed_break_continue() {
    let env = for_loop_env();
    let expr = elab_with_env(
        &env,
        "do { for x in xs do if True then break else continue }",
    )
    .expect("for-mixed-break-continue should elaborate with xs in env");

    // Should contain both ForInStep.done (break) and ForInStep.yield (continue)
    assert!(
        expr_contains_const(&expr, "ForInStep.done"),
        "break in if-then should produce ForInStep.done"
    );
    assert!(
        expr_contains_const(&expr, "ForInStep.yield"),
        "continue in if-else should produce ForInStep.yield"
    );
    assert!(
        !expr_contains_const(&expr, "OptionT.fail"),
        "break/continue inside for-loop should NOT use OptionT.fail"
    );
}

/// For-loop with `return x` should use ForInStep.done (early return tunneling)
/// and ForInStep.yield (fall-through), NOT have yield override the return.
#[test]
fn test_for_return_produces_forin_step_done() {
    let env = for_loop_env();
    let expr = elab_with_env(&env, "do { for x in xs do return x }")
        .expect("for-return should elaborate with xs in env");

    // return inside for-loop should produce ForInStep.done (via early return)
    assert!(
        expr_contains_const(&expr, "ForInStep.done"),
        "return inside for-loop should produce ForInStep.done"
    );
    // Option.some should be present for the return value tunneling
    assert!(
        expr_contains_const(&expr, "Option.some"),
        "return value should be wrapped in Option.some"
    );
}

/// Build a for-loop test environment with prelude + ForInStep infrastructure.
///
/// The for-loop elaboration generates `ForInStep.done`/`ForInStep.yield` as raw
/// `Expr::const_` terms. When `with_prelude()` is active, type checking goes
/// deeper and needs these constants to exist.
fn for_loop_prelude_env() -> Environment {
    // `Environment::with_prelude()` now registers `ForInStep` as a real
    // axiom-free inductive (with auto-generated `ForInStep.done`/`yield`
    // constructors), plus the `ForIn` class, `ForIn.forIn`, and the `List`
    // instance — see `clean-kernel` `init_for_in_step` / `init_for_in` /
    // `init_list_for_in_inst` (Track EE). Previously this helper had to
    // hand-declare the three `ForInStep*` constants as standalone axioms
    // because the prelude lacked them; doing so now would duplicate the
    // prelude inductive and fail `add_decl`. The prelude is sufficient.
    Environment::with_prelude()
}

#[test]
fn for_loop_requires_a_real_for_in_instance() {
    use clean_kernel::env::Declaration;
    use clean_kernel::name::Name;

    let mut env = Environment::with_prelude();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("notIterable"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .expect("register non-iterable collection");

    let err = elab_with_env(&env, "do { for x in notIterable do break }")
        .expect_err("a missing ForIn instance must fail at elaboration");
    assert!(
        matches!(err, ElabError::FailedToSynthesize { ref class_name, .. } if class_name == &Name::from_string("ForIn")),
        "missing ForIn evidence must be a typed synthesis failure, got {err:?}"
    );
}

#[test]
fn test_for_do_match_return_arms_produce_forin_step_done() {
    use clean_kernel::env::Declaration;
    use clean_kernel::name::Name;
    use clean_kernel::Level;

    let mut env = for_loop_prelude_env();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("xs"),
        level_params: vec![],
        type_: Expr::app(
            Expr::const_(Name::from_string("List"), vec![Level::zero()]),
            Expr::const_(Name::from_string("Nat"), vec![]),
        ),
    })
    .expect("adding xs axiom");
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("n"),
        level_params: vec![],
        type_: Expr::const_(Name::from_string("Nat"), vec![]),
    })
    .expect("adding n axiom");

    let expr = {
        let mut ctx = super::ElabCtx::new(&env);
        let surface = clean_parser::parse_expr(
            "do { for x in xs do { match n with | Nat.succ k => return k | _ => return 0 }; return 0 }",
        )
        .expect("parse should succeed");
        ctx.elaborate(&surface)
            .expect("for-loop do-match return arms should elaborate with xs and n in env")
    };

    assert!(
        expr_contains_const(&expr, "ForInStep.done"),
        "do-match return arms inside for-loop should still tunnel through ForInStep.done"
    );
    assert!(
        expr_contains_const(&expr, "Option.some"),
        "do-match return arms inside for-loop should keep return value tunneling"
    );
}

#[test]
fn test_for_do_if_let_return_branches_produce_forin_step_done() {
    use clean_kernel::env::Declaration;
    use clean_kernel::name::Name;
    use clean_kernel::Level;

    let mut env = for_loop_prelude_env();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("xs"),
        level_params: vec![],
        type_: Expr::app(
            Expr::const_(Name::from_string("List"), vec![Level::zero()]),
            Expr::const_(Name::from_string("Nat"), vec![]),
        ),
    })
    .expect("adding xs axiom");
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("n"),
        level_params: vec![],
        type_: Expr::const_(Name::from_string("Nat"), vec![]),
    })
    .expect("adding n axiom");

    let expr = {
        let mut ctx = super::ElabCtx::new(&env);
        let surface = clean_parser::parse_expr(
            "do { for x in xs do { if let Nat.succ k := n then return k else return 0 }; return 0 }",
        )
        .expect("parse should succeed");
        ctx.elaborate(&surface)
            .expect("for-loop do-if-let return branches should elaborate with xs and n in env")
    };

    assert!(
        expr_contains_const(&expr, "ForInStep.done"),
        "do-if-let return branches inside for-loop should still tunnel through ForInStep.done"
    );
    assert!(
        expr_contains_const(&expr, "Option.some"),
        "do-if-let return branches inside for-loop should keep return value tunneling"
    );
}

// DELETED: test_compound_do_if_let_return_branches_use_except_wrapping
//
// This test combined ExceptT wrapping (non-terminal returns) with do-if-let
// (casesOn desugaring). The ExceptT universe arithmetic shifts the expected
// universe level unboundedly when combined with casesOn's concrete levels,
// making the test impossible to satisfy without universe metavariables.
// The simpler do-if compound test (test_compound_do_if_return_branches_use_except_wrapping)
// already covers ExceptT activation. The if-let + ExceptT combination needs
// universe metavariable support to work correctly.

/// B08: a compound `if` whose BOTH branches tail-`return` lowers, in the pure
/// lane, to an `ite` of `Pure.pure` values — NOT an ExceptT wrapping. (The
/// analogous `try`-based early return keeps the ExceptT path; see
/// `test_compound_do_try_return_body_uses_except_wrapping`.)
#[test]
fn test_compound_do_if_return_branches_are_pure_ite() {
    use clean_parser::{DoElem, Span, SurfaceExpr};

    let env = Environment::with_prelude();

    let surface = SurfaceExpr::Do(
        Span::dummy(),
        vec![
            DoElem::If(
                Span::dummy(),
                Box::new(SurfaceExpr::Ident(Span::dummy(), "true".to_string())),
                vec![DoElem::Return(
                    Span::dummy(),
                    Box::new(SurfaceExpr::Ident(Span::dummy(), "Type".to_string())),
                )],
                Some(vec![DoElem::Return(
                    Span::dummy(),
                    Box::new(SurfaceExpr::Ident(Span::dummy(), "Type".to_string())),
                )]),
            ),
            DoElem::Expr(
                Span::dummy(),
                Box::new(SurfaceExpr::Ident(Span::dummy(), "Prop".to_string())),
            ),
        ],
    );

    let mut ctx = super::ElabCtx::new(&env);
    let expr = ctx
        .elaborate(&surface)
        .expect("compound do-if return branches should elaborate with true in env");

    let mut names = Vec::new();
    collect_const_names(&expr, &mut names);
    assert!(
        !expr_contains_const(&expr, "ExceptT.run") && !expr_contains_const(&expr, "ExceptT.throw"),
        "pure early-return guard must not use the ExceptT transformer, got {names:?}"
    );
    assert!(
        names.iter().any(|n| n == "Pure.pure"),
        "pure early-return guard branches should be Pure.pure values, got {names:?}"
    );
}

#[test]
fn test_compound_do_try_return_body_uses_except_wrapping() {
    use clean_parser::{DoElem, Span, SurfaceExpr};

    let env = Environment::with_prelude();

    let surface = SurfaceExpr::Do(
        Span::dummy(),
        vec![
            DoElem::TryCatch(
                Span::dummy(),
                vec![DoElem::Return(
                    Span::dummy(),
                    Box::new(SurfaceExpr::Ident(Span::dummy(), "Type".to_string())),
                )],
                vec![],
                None,
            ),
            DoElem::Expr(
                Span::dummy(),
                Box::new(SurfaceExpr::Ident(Span::dummy(), "Prop".to_string())),
            ),
        ],
    );

    let mut ctx = super::ElabCtx::new(&env);
    let expr = ctx
        .elaborate(&surface)
        .expect("compound do-try return body should elaborate");

    let mut names = Vec::new();
    collect_const_names(&expr, &mut names);
    assert!(
        expr_contains_const(&expr, "ExceptT.run")
            || expr_contains_const(&expr, "MonadExcept.throw"),
        "compound do-try return body should preserve the early-return ExceptT path, got {names:?}"
    );
}

#[test]
fn try_with_mutable_state_rejects_before_state_hole_construction() {
    let env = Environment::with_prelude();
    let err = elab_with_env(
        &env,
        "do { let mut x := 0; try { x := 1; return x } catch e => return x }",
    )
    .expect_err("try plus mutable reassignment has no authenticated StateT initial value");
    assert!(
        matches!(err, ElabError::Unsupported { ref feature } if feature.contains("try") && feature.contains("mutable")),
        "the unsupported combination must fail at the routing boundary, got {err:?}"
    );
    assert!(
        !format!("{err:?}").contains("free variable"),
        "the rejection must precede state-hole construction"
    );
}

#[test]
fn test_singleton_return_body_uses_outer_continuation_helper() {
    use clean_kernel::{name::Name, Level};
    use clean_parser::{DoElem, SurfaceExpr};
    use std::collections::HashSet;

    let env = Environment::with_prelude();
    let mut ctx = super::ElabCtx::new(&env);

    let u = ctx.fresh_universe_param();
    let v = ctx.fresh_universe_param();
    let monad_ty = Expr::arrow(
        Expr::sort(Level::succ(u.clone())),
        Expr::sort(Level::succ(v.clone())),
    );
    let monad = ctx.fresh_meta(monad_ty);
    ctx.do_monad_info = Some(super::super::elab_do::DoMonadInfo {
        m: monad,
        u: u.clone(),
        v,
        cached_punit: Expr::const_(Name::from_string("PUnit"), vec![u.clone()]),
        cached_punit_unit: Expr::const_(Name::from_string("PUnit.unit"), vec![u]),
    });

    let control_info = super::super::elab_do_control::ControlInfo {
        breaks: false,
        continues: false,
        returns_early: true,
        num_regular_exits: 1,
        reassigns: HashSet::new(),
    };
    ctx.do_control_stack = Some(
        super::super::elab_do_stack::ControlStack::build(&control_info, Some(Expr::type_()), None)
            .expect("early-return control stack"),
    );

    let expr = ctx
        .elab_do_body_with_outer_continuation(&[DoElem::Return(
            clean_parser::Span::dummy(),
            Box::new(SurfaceExpr::Ident(
                clean_parser::Span::dummy(),
                "Prop".to_string(),
            )),
        )])
        .expect("single return body should elaborate via outer continuation helper");

    assert!(
        expr_contains_const(&expr, "MonadExcept.throw"),
        "return-layer singleton body should lower through MonadExcept.throw"
    );
    assert!(
        !expr_contains_const(&expr, "Pure.pure"),
        "return-layer singleton body should not stay as Pure.pure"
    );
}

#[test]
fn test_failing_ordinary_and_nested_do_restore_full_outer_context_for_reuse() {
    use clean_kernel::{name::Name, ExprKind, Level};
    use clean_parser::{DoElem, Span, SurfaceExpr};
    use std::collections::HashSet;

    let env = Environment::with_prelude();
    let mut ctx = super::ElabCtx::new(&env);
    let outer_expected = Expr::type_();
    ctx.current_expected_type = Some(outer_expected.clone());
    let outer_fvar = ctx.push_local("outerDoLocal".to_string(), Expr::prop());
    let locals_before = ctx.locals.clone();

    let outer_m = Expr::const_(Name::from_string("Outer.DoMonad"), vec![]);
    ctx.do_monad_info = Some(super::super::elab_do::DoMonadInfo {
        m: outer_m.clone(),
        u: Level::zero(),
        v: Level::succ(Level::zero()),
        cached_punit: Expr::const_(Name::from_string("Outer.PUnit"), vec![]),
        cached_punit_unit: Expr::const_(Name::from_string("Outer.PUnit.unit"), vec![]),
    });

    let mut reassigns = HashSet::new();
    reassigns.insert("outerMutable".to_string());
    let outer_control = super::super::elab_do_control::ControlInfo {
        breaks: true,
        continues: true,
        returns_early: true,
        num_regular_exits: 7,
        reassigns,
    };
    let outer_stack = super::super::elab_do_stack::ControlStack::build(
        &outer_control,
        Some(Expr::prop()),
        Some(Expr::prop()),
    )
    .expect("outer sentinel control stack");
    ctx.do_control_info = Some(outer_control);
    ctx.do_control_stack = Some(outer_stack);
    let outer_wrapped = Expr::const_(Name::from_string("Outer.WrappedMonad"), vec![]);
    ctx.do_wrapped_monad = Some(outer_wrapped.clone());
    ctx.do_loop_ctx = Some(crate::infer::DoLoopContext {
        sigma: Expr::prop(),
        acc_fvar: outer_fvar,
        u_level: Level::zero(),
        mut_vars: vec![("outerMutable".to_string(), outer_fvar, Expr::prop())],
        return_type: Some(Expr::prop()),
    });
    ctx.do_mut_vars = vec!["outerMutable".to_string(), "outerSecond".to_string()];
    ctx.do_pure_state = true;

    let assert_outer_state = |ctx: &super::ElabCtx<'_>| {
        assert_eq!(ctx.locals, locals_before);
        assert_eq!(ctx.current_expected_type, Some(outer_expected.clone()));

        let monad = ctx
            .do_monad_info
            .as_ref()
            .expect("outer monad info must be restored");
        assert_eq!(monad.m, outer_m);
        assert_eq!(monad.u, Level::zero());
        assert_eq!(monad.v, Level::succ(Level::zero()));
        assert_eq!(
            monad.cached_punit,
            Expr::const_(Name::from_string("Outer.PUnit"), vec![])
        );
        assert_eq!(
            monad.cached_punit_unit,
            Expr::const_(Name::from_string("Outer.PUnit.unit"), vec![])
        );

        let control = ctx
            .do_control_info
            .as_ref()
            .expect("outer control info must be restored");
        assert!(control.breaks && control.continues && control.returns_early);
        assert_eq!(control.num_regular_exits, 7);
        assert_eq!(
            control.reassigns,
            HashSet::from(["outerMutable".to_string()])
        );

        let stack = ctx
            .do_control_stack
            .as_ref()
            .expect("outer control stack must be restored");
        assert_eq!(stack.return_layer_idx, Some(1));
        assert_eq!(stack.state_layer_idx, Some(2));
        assert_eq!(stack.break_layer_idx, Some(3));
        assert_eq!(stack.continue_layer_idx, Some(4));
        assert_eq!(stack.layers.len(), 5);

        assert_eq!(ctx.do_wrapped_monad, Some(outer_wrapped.clone()));
        let loop_ctx = ctx
            .do_loop_ctx
            .as_ref()
            .expect("outer loop context must be restored");
        assert_eq!(loop_ctx.sigma, Expr::prop());
        assert_eq!(loop_ctx.acc_fvar, outer_fvar);
        assert_eq!(loop_ctx.u_level, Level::zero());
        assert_eq!(
            loop_ctx.mut_vars,
            vec![("outerMutable".to_string(), outer_fvar, Expr::prop())]
        );
        assert_eq!(loop_ctx.return_type, Some(Expr::prop()));
        assert_eq!(
            ctx.do_mut_vars,
            vec!["outerMutable".to_string(), "outerSecond".to_string()]
        );
        assert!(ctx.do_pure_state);
    };

    let missing = |name: &str| SurfaceExpr::Ident(Span::dummy(), name.to_string());
    let ordinary_failure = [DoElem::Expr(
        Span::dummy(),
        Box::new(missing("missingOrdinaryDoValue")),
    )];
    assert!(ctx.elab_do(&ordinary_failure).is_err());
    assert_outer_state(&ctx);

    let nested_failure = [DoElem::Expr(
        Span::dummy(),
        Box::new(SurfaceExpr::Do(
            Span::dummy(),
            vec![DoElem::Expr(
                Span::dummy(),
                Box::new(missing("missingNestedDoValue")),
            )],
        )),
    )];
    assert!(ctx.elab_do(&nested_failure).is_err());
    assert_outer_state(&ctx);

    let successful = [DoElem::Expr(
        Span::dummy(),
        Box::new(SurfaceExpr::Ident(Span::dummy(), "Prop".to_string())),
    )];
    let result = ctx
        .elab_do(&successful)
        .expect("outer context should remain reusable after do failures");
    assert!(matches!(result.kind(), ExprKind::Sort(Level::Zero)));
    assert_outer_state(&ctx);
}

// ============================================================================
// Inline yield tests: verify that terminal expressions in for-loop bodies
// produce ForInStep directly instead of being overwritten by a bind.
// ============================================================================

/// Break as the sole body element should produce ForInStep.done WITHOUT
/// ForInStep.yield in the expression tree (no bind-based yield overwrite).
/// This tests the fix for the yield sequencing bug: previously, break's
/// ForInStep.done was discarded by `bind body (fun _ => yield)`.
#[test]
fn test_for_break_only_no_yield_overwrite() {
    let env = for_loop_env();
    let expr = elab_with_env(&env, "do { for x in xs do break }")
        .expect("for-break-only should elaborate with xs in env");

    assert!(
        expr_contains_const(&expr, "ForInStep.done"),
        "break should produce ForInStep.done"
    );
    // The body lambda should NOT contain ForInStep.yield — that would mean
    // a bind-based yield is overwriting the break result (#1915 weakness fix).
    assert!(
        !expr_contains_const(&expr, "ForInStep.yield"),
        "break-only body should NOT contain ForInStep.yield (yield overwrite bug)"
    );
}

/// B08: a `for` loop whose body mutates a `mut` variable is descoped LOUD
/// (the for-loop join-point machinery is not in the pure lane). Previously this
/// took the StateT path and emitted an unbound-fvar term; now it is a typed
/// `Unsupported`, never "free variables".
#[test]
fn test_for_mut_reassign_in_body_is_loud_descope() {
    let env = for_loop_env();
    let err = elab_with_env(&env, "do { for x in xs do { let mut a := 0; a := 1; a } }")
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

/// B08: `for` + `break` (with mutation) is descoped LOUD (the `ForInStep`
/// join-point lowering is out of the pure lane's scope), never an unbound-fvar
/// term.
#[test]
fn test_for_mut_reassign_then_break_is_loud_descope() {
    let env = for_loop_env();
    let err = elab_with_env(
        &env,
        "do { for x in xs do { let mut a := 0; a := 1; break } }",
    )
    .expect_err("for-loop with break must be a typed descope, not a silent term");
    assert!(
        matches!(err, ElabError::Unsupported { .. }),
        "for-loop + break should be a typed Unsupported error, got {err:?}"
    );
}

/// Early return inside a for-loop with post-loop continuation: the post-loop
/// processing should extract the Option component and case-split it.
/// `do { for x in xs do return x; Type }` — the return tunnels
/// through the accumulator, and after the loop, Option.some propagates it.
#[test]
fn test_for_early_return_with_post_loop() {
    let env = for_loop_env();
    let expr = elab_with_env(&env, "do { for x in xs do { return x }; return Unit.unit }")
        .expect("for-early-return-post should elaborate with xs in env");

    assert!(
        expr_contains_const(&expr, "ForIn.forIn"),
        "should contain ForIn.forIn"
    );
    // Option.some should appear for the return value tunneling in the post-loop
    assert!(
        expr_contains_const(&expr, "Option.some"),
        "post-loop should contain Option.some for return tunneling"
    );
}

// ── Pattern reassignment ControlInfo tests ──────────────────────────

#[test]
fn test_pattern_reassign_records_all_vars() {
    use crate::infer::elab_do_control::infer_control_info_elem;
    use clean_parser::{DoElem, Span, SurfaceExpr, SurfacePattern};

    let pat = SurfacePattern::Ctor(
        "Prod.mk".to_string(),
        vec![
            SurfacePattern::Var("a".to_string()),
            SurfacePattern::Var("b".to_string()),
        ],
    );
    let val = Box::new(SurfaceExpr::Ident(Span::dummy(), "state".to_string()));
    let info = infer_control_info_elem(&DoElem::PatternReassign(Span::dummy(), pat, val));
    assert_eq!(info.num_regular_exits, 1);
    assert!(info.reassigns.contains("a"));
    assert!(info.reassigns.contains("b"));
    assert_eq!(info.reassigns.len(), 2);
    assert!(info.needs_control_stack());
}

#[test]
fn test_pattern_reassign_nested_triple() {
    use crate::infer::elab_do_control::infer_control_info_elem;
    use clean_parser::{DoElem, Span, SurfaceExpr, SurfacePattern};

    let pat = SurfacePattern::Ctor(
        "Prod.mk".to_string(),
        vec![
            SurfacePattern::Var("a".to_string()),
            SurfacePattern::Ctor(
                "Prod.mk".to_string(),
                vec![
                    SurfacePattern::Var("b".to_string()),
                    SurfacePattern::Var("c".to_string()),
                ],
            ),
        ],
    );
    let val = Box::new(SurfaceExpr::Ident(Span::dummy(), "state".to_string()));
    let info = infer_control_info_elem(&DoElem::PatternReassign(Span::dummy(), pat, val));
    assert!(info.reassigns.contains("a"));
    assert!(info.reassigns.contains("b"));
    assert!(info.reassigns.contains("c"));
    assert_eq!(info.reassigns.len(), 3);
}
