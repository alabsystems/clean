// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for kernel-level do-notation desugaring (`do_notation_desugar`).

use crate::do_notation_desugar::*;
use clean_kernel::{Expr, ExprKind, Name};

// ---------------------------------------------------------------------------
// Helper: make a simple constant expression for use as a test value
// ---------------------------------------------------------------------------

fn action(name: &str) -> Expr {
    Expr::const_str(name)
}

fn name(s: &str) -> Name {
    Name::from_string(s)
}

fn default_config() -> DoDesugarConfig {
    DoDesugarConfig::default()
}

/// Check that the head of an application spine is a given constant name.
fn head_is_const(expr: &Expr, expected: &str) -> bool {
    let head = expr.get_app_fn();
    matches!(head.kind(), ExprKind::Const(n, _) if *n == Name::from_string(expected))
}

// ===========================================================================
// Basic Action / Return / Bind tests
// ===========================================================================

#[test]
fn test_desugar_single_action_auto_pure() {
    let stmts = vec![DoStmt::Action(action("foo"))];
    let config = default_config();
    let result = desugar_do_block(&stmts, &config).expect("should succeed");
    // auto_pure_last wraps terminal action in Pure.pure
    assert!(head_is_const(&result.desugared, "Pure.pure"));
    assert_eq!(result.bind_count, 0);
    assert!(result.mut_vars.is_empty());
}

#[test]
fn test_desugar_single_action_no_auto_pure() {
    let stmts = vec![DoStmt::Action(action("foo"))];
    let config = DoDesugarConfig {
        auto_pure_last: false,
        ..default_config()
    };
    let result = desugar_do_block(&stmts, &config).expect("should succeed");
    // Without auto_pure_last, terminal action is returned as-is
    assert!(head_is_const(&result.desugared, "foo"));
    assert_eq!(result.bind_count, 0);
}

#[test]
fn test_desugar_return_some() {
    let stmts = vec![DoStmt::Return(Some(action("val")))];
    let result = desugar_do_block(&stmts, &default_config()).expect("should succeed");
    assert!(head_is_const(&result.desugared, "Pure.pure"));
    assert_eq!(result.bind_count, 0);
}

#[test]
fn test_desugar_return_none() {
    let stmts = vec![DoStmt::Return(None)];
    let result = desugar_do_block(&stmts, &default_config()).expect("should succeed");
    assert!(head_is_const(&result.desugared, "Pure.pure"));
}

#[test]
fn test_desugar_bind_chain() {
    let stmts = vec![
        DoStmt::Bind {
            pat: name("x"),
            val: action("getLine"),
        },
        DoStmt::Action(action("putStr")),
    ];
    let result = desugar_do_block(&stmts, &default_config()).expect("should succeed");
    assert!(head_is_const(&result.desugared, "Bind.bind"));
    assert_eq!(result.bind_count, 1);
}

#[test]
fn test_desugar_two_binds() {
    let stmts = vec![
        DoStmt::Bind {
            pat: name("x"),
            val: action("getLine"),
        },
        DoStmt::Bind {
            pat: name("y"),
            val: action("getLine"),
        },
        DoStmt::Return(Some(action("result"))),
    ];
    let result = desugar_do_block(&stmts, &default_config()).expect("should succeed");
    assert!(head_is_const(&result.desugared, "Bind.bind"));
    assert_eq!(result.bind_count, 2);
}

#[test]
fn test_desugar_action_then_action() {
    // Two actions: first binds to _, second is terminal
    let stmts = vec![
        DoStmt::Action(action("print")),
        DoStmt::Action(action("done")),
    ];
    let result = desugar_do_block(&stmts, &default_config()).expect("should succeed");
    assert!(head_is_const(&result.desugared, "Bind.bind"));
    assert_eq!(result.bind_count, 1);
}

// ===========================================================================
// Let / LetMut / Assign tests
// ===========================================================================

#[test]
fn test_desugar_let_binding() {
    let stmts = vec![
        DoStmt::Let {
            name: name("x"),
            val: action("compute"),
        },
        DoStmt::Action(action("use_x")),
    ];
    let result = desugar_do_block(&stmts, &default_config()).expect("should succeed");
    // Let produces a Let node, not a Bind
    assert!(matches!(&result.desugared.kind(), ExprKind::Let(..)));
    assert_eq!(result.bind_count, 0);
}

#[test]
fn test_desugar_let_mut_tracking() {
    let stmts = vec![
        DoStmt::LetMut {
            name: name("counter"),
            val: Expr::nat_lit(0),
        },
        DoStmt::Action(action("done")),
    ];
    let result = desugar_do_block(&stmts, &default_config()).expect("should succeed");
    assert_eq!(result.mut_vars.len(), 1);
    assert_eq!(result.mut_vars[0], name("counter"));
}

#[test]
fn test_desugar_assign_let_shadowing() {
    let stmts = vec![
        DoStmt::LetMut {
            name: name("x"),
            val: Expr::nat_lit(0),
        },
        DoStmt::Assign {
            name: name("x"),
            val: Expr::nat_lit(1),
        },
        DoStmt::Action(action("done")),
    ];
    let result = desugar_do_block(&stmts, &default_config()).expect("should succeed");
    // Outer is let, inner is also let (from assign)
    assert!(matches!(&result.desugared.kind(), ExprKind::Let(..)));
    assert_eq!(result.mut_vars, vec![name("x")]);
}

#[test]
fn test_desugar_let_terminal_error() {
    let stmts = vec![DoStmt::Let {
        name: name("x"),
        val: action("val"),
    }];
    let err = desugar_do_block(&stmts, &default_config());
    assert!(err.is_err());
}

#[test]
fn test_desugar_assign_terminal_error() {
    let stmts = vec![DoStmt::Assign {
        name: name("x"),
        val: action("val"),
    }];
    let err = desugar_do_block(&stmts, &default_config());
    assert!(err.is_err());
}

// ===========================================================================
// If statement tests
// ===========================================================================

#[test]
fn test_desugar_if_terminal() {
    let stmts = vec![DoStmt::If {
        cond: action("cond"),
        then_: vec![DoStmt::Return(Some(action("a")))],
        else_: vec![DoStmt::Return(Some(action("b")))],
    }];
    let result = desugar_do_block(&stmts, &default_config()).expect("should succeed");
    assert!(head_is_const(&result.desugared, "ite"));
}

#[test]
fn test_desugar_if_non_terminal() {
    let stmts = vec![
        DoStmt::If {
            cond: action("cond"),
            then_: vec![DoStmt::Action(action("a"))],
            else_: vec![DoStmt::Action(action("b"))],
        },
        DoStmt::Action(action("rest")),
    ];
    let result = desugar_do_block(&stmts, &default_config()).expect("should succeed");
    // Non-terminal if gets wrapped in Bind.bind
    assert!(head_is_const(&result.desugared, "Bind.bind"));
    assert!(result.bind_count >= 1);
}

#[test]
fn test_desugar_if_empty_else() {
    let stmts = vec![DoStmt::If {
        cond: action("cond"),
        then_: vec![DoStmt::Action(action("a"))],
        else_: vec![],
    }];
    let result = desugar_do_block(&stmts, &default_config()).expect("should succeed");
    // Empty else branch defaults to pure ()
    assert!(head_is_const(&result.desugared, "ite"));
}

// ===========================================================================
// For loop tests
// ===========================================================================

#[test]
fn test_desugar_for_loop_terminal() {
    let stmts = vec![DoStmt::For {
        var: name("x"),
        iter: action("xs"),
        body: vec![DoStmt::Action(action("process"))],
    }];
    let result = desugar_do_block(&stmts, &default_config()).expect("should succeed");
    assert!(head_is_const(&result.desugared, "ForIn.forIn"));
    assert!(result.bind_count >= 1);
}

#[test]
fn test_desugar_for_loop_non_terminal() {
    let stmts = vec![
        DoStmt::For {
            var: name("x"),
            iter: action("xs"),
            body: vec![DoStmt::Action(action("process"))],
        },
        DoStmt::Action(action("done")),
    ];
    let result = desugar_do_block(&stmts, &default_config()).expect("should succeed");
    assert!(head_is_const(&result.desugared, "Bind.bind"));
    assert!(result.bind_count >= 2);
}

#[test]
fn test_desugar_for_loop_empty_body_error() {
    let stmts = vec![DoStmt::For {
        var: name("x"),
        iter: action("xs"),
        body: vec![],
    }];
    assert!(desugar_do_block(&stmts, &default_config()).is_err());
}

// ===========================================================================
// Try/catch tests
// ===========================================================================

#[test]
fn test_desugar_try_catch_terminal() {
    let stmts = vec![DoStmt::TryCatch {
        try_body: vec![DoStmt::Action(action("risky"))],
        catch_var: name("e"),
        catch_body: vec![DoStmt::Return(Some(action("fallback")))],
    }];
    let result = desugar_do_block(&stmts, &default_config()).expect("should succeed");
    assert!(head_is_const(&result.desugared, "MonadExcept.tryCatch"));
}

#[test]
fn test_desugar_try_catch_non_terminal() {
    let stmts = vec![
        DoStmt::TryCatch {
            try_body: vec![DoStmt::Action(action("risky"))],
            catch_var: name("e"),
            catch_body: vec![DoStmt::Action(action("handle"))],
        },
        DoStmt::Action(action("continue")),
    ];
    let result = desugar_do_block(&stmts, &default_config()).expect("should succeed");
    assert!(head_is_const(&result.desugared, "Bind.bind"));
}

#[test]
fn test_desugar_try_catch_empty_catch_body() {
    let stmts = vec![DoStmt::TryCatch {
        try_body: vec![DoStmt::Action(action("risky"))],
        catch_var: name("e"),
        catch_body: vec![],
    }];
    let result = desugar_do_block(&stmts, &default_config()).expect("should succeed");
    // Empty catch body defaults to pure ()
    assert!(head_is_const(&result.desugared, "MonadExcept.tryCatch"));
}

#[test]
fn test_desugar_try_catch_empty_try_error() {
    let stmts = vec![DoStmt::TryCatch {
        try_body: vec![],
        catch_var: name("e"),
        catch_body: vec![DoStmt::Action(action("handle"))],
    }];
    assert!(desugar_do_block(&stmts, &default_config()).is_err());
}

// ===========================================================================
// Unless tests
// ===========================================================================

#[test]
fn test_desugar_unless_terminal() {
    let stmts = vec![DoStmt::Unless {
        cond: action("done_flag"),
        body: vec![DoStmt::Action(action("work"))],
    }];
    let result = desugar_do_block(&stmts, &default_config()).expect("should succeed");
    assert!(head_is_const(&result.desugared, "ite"));
}

#[test]
fn test_desugar_unless_non_terminal() {
    let stmts = vec![
        DoStmt::Unless {
            cond: action("done_flag"),
            body: vec![DoStmt::Action(action("work"))],
        },
        DoStmt::Action(action("rest")),
    ];
    let result = desugar_do_block(&stmts, &default_config()).expect("should succeed");
    assert!(head_is_const(&result.desugared, "Bind.bind"));
}

// ===========================================================================
// Repeat tests
// ===========================================================================

#[test]
fn test_desugar_repeat_no_until() {
    let stmts = vec![DoStmt::Repeat {
        body: vec![DoStmt::Action(action("step"))],
        until: None,
    }];
    let result = desugar_do_block(&stmts, &default_config()).expect("should succeed");
    assert!(head_is_const(&result.desugared, "ForIn.forIn"));
    assert!(result.bind_count >= 1);
}

#[test]
fn test_desugar_repeat_with_until() {
    let stmts = vec![DoStmt::Repeat {
        body: vec![DoStmt::Action(action("step"))],
        until: Some(action("done_cond")),
    }];
    let result = desugar_do_block(&stmts, &default_config()).expect("should succeed");
    assert!(head_is_const(&result.desugared, "ForIn.forIn"));
}

#[test]
fn test_desugar_repeat_empty_body_error() {
    let stmts = vec![DoStmt::Repeat {
        body: vec![],
        until: None,
    }];
    assert!(desugar_do_block(&stmts, &default_config()).is_err());
}

// ===========================================================================
// Empty block tests
// ===========================================================================

#[test]
fn test_desugar_empty_block_error() {
    assert!(desugar_do_block(&[], &default_config()).is_err());
}

// ===========================================================================
// Config tests
// ===========================================================================

#[test]
fn test_config_disallow_mut() {
    let stmts = vec![
        DoStmt::LetMut {
            name: name("x"),
            val: Expr::nat_lit(0),
        },
        DoStmt::Action(action("done")),
    ];
    let config = DoDesugarConfig {
        allow_mut: false,
        ..default_config()
    };
    assert!(desugar_do_block(&stmts, &config).is_err());
}

#[test]
fn test_config_allow_mut_default() {
    let stmts = vec![
        DoStmt::LetMut {
            name: name("x"),
            val: Expr::nat_lit(0),
        },
        DoStmt::Action(action("done")),
    ];
    let result = desugar_do_block(&stmts, &default_config()).expect("should succeed");
    assert_eq!(result.mut_vars.len(), 1);
}

#[test]
fn test_config_monad_class_name() {
    let config = DoDesugarConfig {
        monad_class: Name::from_string("StateM"),
        ..default_config()
    };
    assert_eq!(config.monad_class, Name::from_string("StateM"));
}

// ===========================================================================
// collect_mut_vars tests
// ===========================================================================

#[test]
fn test_collect_mut_vars_empty() {
    assert!(collect_mut_vars(&[]).is_empty());
}

#[test]
fn test_collect_mut_vars_simple() {
    let stmts = vec![DoStmt::LetMut {
        name: name("x"),
        val: Expr::nat_lit(0),
    }];
    let vars = collect_mut_vars(&stmts);
    assert_eq!(vars, vec![name("x")]);
}

#[test]
fn test_collect_mut_vars_nested_if() {
    let stmts = vec![DoStmt::If {
        cond: action("c"),
        then_: vec![DoStmt::LetMut {
            name: name("a"),
            val: Expr::nat_lit(1),
        }],
        else_: vec![DoStmt::LetMut {
            name: name("b"),
            val: Expr::nat_lit(2),
        }],
    }];
    let vars = collect_mut_vars(&stmts);
    assert_eq!(vars.len(), 2);
    assert!(vars.contains(&name("a")));
    assert!(vars.contains(&name("b")));
}

#[test]
fn test_collect_mut_vars_nested_for() {
    let stmts = vec![DoStmt::For {
        var: name("i"),
        iter: action("items"),
        body: vec![DoStmt::LetMut {
            name: name("acc"),
            val: Expr::nat_lit(0),
        }],
    }];
    let vars = collect_mut_vars(&stmts);
    assert_eq!(vars, vec![name("acc")]);
}

#[test]
fn test_collect_mut_vars_dedup() {
    let stmts = vec![
        DoStmt::LetMut {
            name: name("x"),
            val: Expr::nat_lit(0),
        },
        DoStmt::If {
            cond: action("c"),
            then_: vec![DoStmt::LetMut {
                name: name("x"),
                val: Expr::nat_lit(1),
            }],
            else_: vec![],
        },
    ];
    let vars = collect_mut_vars(&stmts);
    // Should deduplicate same name
    assert_eq!(vars, vec![name("x")]);
}

#[test]
fn test_collect_mut_vars_try_catch() {
    let stmts = vec![DoStmt::TryCatch {
        try_body: vec![DoStmt::LetMut {
            name: name("t"),
            val: Expr::nat_lit(0),
        }],
        catch_var: name("e"),
        catch_body: vec![DoStmt::LetMut {
            name: name("c"),
            val: Expr::nat_lit(0),
        }],
    }];
    let vars = collect_mut_vars(&stmts);
    assert_eq!(vars.len(), 2);
}

#[test]
fn test_collect_mut_vars_unless() {
    let stmts = vec![DoStmt::Unless {
        cond: action("flag"),
        body: vec![DoStmt::LetMut {
            name: name("v"),
            val: Expr::nat_lit(0),
        }],
    }];
    let vars = collect_mut_vars(&stmts);
    assert_eq!(vars, vec![name("v")]);
}

#[test]
fn test_collect_mut_vars_repeat() {
    let stmts = vec![DoStmt::Repeat {
        body: vec![DoStmt::LetMut {
            name: name("r"),
            val: Expr::nat_lit(0),
        }],
        until: None,
    }];
    let vars = collect_mut_vars(&stmts);
    assert_eq!(vars, vec![name("r")]);
}

// ===========================================================================
// Complex / integration tests
// ===========================================================================

#[test]
fn test_desugar_bind_let_bind_chain() {
    // do
    //   x ← action1
    //   let y := compute x
    //   z ← action2
    //   return z
    let stmts = vec![
        DoStmt::Bind {
            pat: name("x"),
            val: action("action1"),
        },
        DoStmt::Let {
            name: name("y"),
            val: action("compute"),
        },
        DoStmt::Bind {
            pat: name("z"),
            val: action("action2"),
        },
        DoStmt::Return(Some(action("result"))),
    ];
    let result = desugar_do_block(&stmts, &default_config()).expect("should succeed");
    assert!(head_is_const(&result.desugared, "Bind.bind"));
    assert_eq!(result.bind_count, 2);
    assert!(result.mut_vars.is_empty());
}

#[test]
fn test_desugar_non_terminal_return_ignores_rest() {
    let stmts = vec![
        DoStmt::Return(Some(action("early"))),
        DoStmt::Action(action("unreachable")),
    ];
    let result = desugar_do_block(&stmts, &default_config()).expect("should succeed");
    // Non-terminal return should produce Pure.pure, ignoring rest
    assert!(head_is_const(&result.desugared, "Pure.pure"));
}

#[test]
fn test_desugar_terminal_bind_returns_action() {
    // Terminal bind with no continuation returns just the action
    let stmts = vec![DoStmt::Bind {
        pat: name("x"),
        val: action("getLine"),
    }];
    let result = desugar_do_block(&stmts, &default_config()).expect("should succeed");
    assert!(head_is_const(&result.desugared, "getLine"));
    assert_eq!(result.bind_count, 0);
}

#[test]
fn test_desugar_nested_if_in_for() {
    // for x in xs do
    //   if cond then action1 else action2
    let stmts = vec![DoStmt::For {
        var: name("x"),
        iter: action("xs"),
        body: vec![DoStmt::If {
            cond: action("cond"),
            then_: vec![DoStmt::Action(action("a1"))],
            else_: vec![DoStmt::Action(action("a2"))],
        }],
    }];
    let result = desugar_do_block(&stmts, &default_config()).expect("should succeed");
    assert!(head_is_const(&result.desugared, "ForIn.forIn"));
}

#[test]
fn test_desugar_try_catch_in_sequence() {
    // try risky catch e => handle; continue
    let stmts = vec![
        DoStmt::TryCatch {
            try_body: vec![DoStmt::Action(action("risky"))],
            catch_var: name("e"),
            catch_body: vec![DoStmt::Action(action("handle"))],
        },
        DoStmt::Return(Some(action("done"))),
    ];
    let result = desugar_do_block(&stmts, &default_config()).expect("should succeed");
    assert!(head_is_const(&result.desugared, "Bind.bind"));
}

#[test]
fn test_desugar_repeat_with_until_non_terminal() {
    let stmts = vec![
        DoStmt::Repeat {
            body: vec![DoStmt::Action(action("step"))],
            until: Some(action("done_flag")),
        },
        DoStmt::Return(Some(action("final"))),
    ];
    let result = desugar_do_block(&stmts, &default_config()).expect("should succeed");
    assert!(head_is_const(&result.desugared, "Bind.bind"));
}

#[test]
fn test_desugar_result_fields() {
    let stmts = vec![
        DoStmt::LetMut {
            name: name("x"),
            val: Expr::nat_lit(0),
        },
        DoStmt::Bind {
            pat: name("y"),
            val: action("act"),
        },
        DoStmt::Action(action("act2")),
        DoStmt::Return(Some(action("r"))),
    ];
    let result = desugar_do_block(&stmts, &default_config()).expect("should succeed");
    // 1 Bind from the bind stmt + 1 from the non-terminal action
    assert_eq!(result.bind_count, 2);
    assert_eq!(result.mut_vars, vec![name("x")]);
}

#[test]
fn test_desugar_unless_with_multiple_body_stmts() {
    let stmts = vec![DoStmt::Unless {
        cond: action("skip"),
        body: vec![
            DoStmt::Action(action("step1")),
            DoStmt::Action(action("step2")),
        ],
    }];
    let result = desugar_do_block(&stmts, &default_config()).expect("should succeed");
    assert!(head_is_const(&result.desugared, "ite"));
}

// ===========================================================================
// Chained bind variable capture tests (#3396)
// ===========================================================================
// These tests verify that variables introduced by `let x <- action` are
// properly captured as BVar references in continuation lambdas. Before the
// fix, chained binds like `do let n <- f; g n; pure n` would leave `n`
// as a free variable (Const reference) instead of abstracting it to BVar(0).

/// Helper: recursively check if an expression contains any FVar nodes,
/// which would indicate incomplete abstraction.
fn has_fvars(expr: &Expr) -> bool {
    match expr.kind() {
        ExprKind::FVar(_) => true,
        ExprKind::App(f, a) => has_fvars(f) || has_fvars(a),
        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => has_fvars(ty) || has_fvars(body),
        ExprKind::Let(_, ty, val, body, _) => has_fvars(ty) || has_fvars(val) || has_fvars(body),
        _ => false,
    }
}

/// Helper: check that no Const references to the given name remain in the expression
/// (they should have been substituted and abstracted).
fn has_const_ref(expr: &Expr, target: &str) -> bool {
    let target_name = Name::from_string(target);
    match expr.kind() {
        ExprKind::Const(n, levels) if *n == target_name && levels.is_empty() => true,
        ExprKind::App(f, a) => has_const_ref(f, target) || has_const_ref(a, target),
        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
            has_const_ref(ty, target) || has_const_ref(body, target)
        }
        ExprKind::Let(_, ty, val, body, _) => {
            has_const_ref(ty, target) || has_const_ref(val, target) || has_const_ref(body, target)
        }
        _ => false,
    }
}

/// Helper: count the number of BVar references at a specific depth in an expression.
// Test scaffolding not exercised by every including build — kept per the 2026-07-30
// keep-and-annotate sweep; see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md.
#[allow(dead_code)]
fn count_bvar(expr: &Expr, idx: u32) -> usize {
    match expr.kind() {
        ExprKind::BVar(i) if *i == idx => 1,
        ExprKind::App(f, a) => count_bvar(f, idx) + count_bvar(a, idx),
        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
            count_bvar(ty, idx) + count_bvar(body, idx + 1)
        }
        ExprKind::Let(_, ty, val, body, _) => {
            count_bvar(ty, idx) + count_bvar(val, idx) + count_bvar(body, idx + 1)
        }
        _ => 0,
    }
}

#[test]
fn test_chained_bind_single_var_reference() {
    // do
    //   let n <- incCounter
    //   return n
    //
    // Should desugar to: Bind.bind incCounter (fun n => Pure.pure n)
    // The continuation lambda body must reference n as BVar(0), not Const("n").
    let stmts = vec![
        DoStmt::Bind {
            pat: name("n"),
            val: action("incCounter"),
        },
        DoStmt::Return(Some(action("n"))),
    ];
    let result = desugar_do_block(&stmts, &default_config()).expect("should succeed");
    let expr = &result.desugared;

    // Top level should be Bind.bind
    assert!(head_is_const(expr, "Bind.bind"), "expected Bind.bind head");
    assert_eq!(result.bind_count, 1);

    // The desugared expression should have no FVars (all abstracted)
    assert!(
        !has_fvars(expr),
        "desugared expression should have no FVars"
    );

    // The Const("n") reference should have been replaced with a BVar
    assert!(
        !has_const_ref(expr, "n"),
        "Const(\"n\") should not remain in desugared expression"
    );
}

#[test]
fn test_chained_bind_double_bind_var_capture() {
    // do
    //   let n <- incCounter
    //   addValue n     -- action referencing n
    //   pure n         -- return referencing n
    //
    // Should desugar to:
    //   Bind.bind incCounter (fun n =>
    //     Bind.bind (addValue n) (fun _ =>
    //       Pure.pure n))
    //
    // Both occurrences of `n` in the continuation must be properly captured.
    let stmts = vec![
        DoStmt::Bind {
            pat: name("n"),
            val: action("incCounter"),
        },
        DoStmt::Action(Expr::app(action("addValue"), action("n"))),
        DoStmt::Return(Some(action("n"))),
    ];
    let result = desugar_do_block(&stmts, &default_config()).expect("should succeed");
    let expr = &result.desugared;

    assert!(head_is_const(expr, "Bind.bind"), "expected Bind.bind head");
    assert_eq!(result.bind_count, 2);

    // No FVars should remain
    assert!(
        !has_fvars(expr),
        "desugared expression should have no FVars after abstraction"
    );

    // No Const("n") should remain (it should be BVar)
    assert!(
        !has_const_ref(expr, "n"),
        "Const(\"n\") should not remain - should be BVar"
    );
}

#[test]
fn test_chained_bind_triple_bind_var_capture() {
    // do
    //   let a <- action1
    //   let b <- action2
    //   let c <- action3
    //   return (f a b c)
    //
    // All three variables must be properly captured at their correct
    // de Bruijn depths in the innermost continuation.
    let stmts = vec![
        DoStmt::Bind {
            pat: name("a"),
            val: action("action1"),
        },
        DoStmt::Bind {
            pat: name("b"),
            val: action("action2"),
        },
        DoStmt::Bind {
            pat: name("c"),
            val: action("action3"),
        },
        DoStmt::Return(Some(Expr::app(
            Expr::app(Expr::app(action("f"), action("a")), action("b")),
            action("c"),
        ))),
    ];
    let result = desugar_do_block(&stmts, &default_config()).expect("should succeed");
    let expr = &result.desugared;

    assert!(head_is_const(expr, "Bind.bind"), "expected Bind.bind head");
    assert_eq!(result.bind_count, 3);

    // No FVars should remain
    assert!(
        !has_fvars(expr),
        "triple-bind desugared expression should have no FVars"
    );

    // No Const references to a, b, c should remain
    assert!(!has_const_ref(expr, "a"), "Const(\"a\") should not remain");
    assert!(!has_const_ref(expr, "b"), "Const(\"b\") should not remain");
    assert!(!has_const_ref(expr, "c"), "Const(\"c\") should not remain");
}

#[test]
fn test_chained_bind_let_then_bind_var_capture() {
    // do
    //   let x := compute
    //   let y <- action
    //   return (f x y)
    //
    // Both x (let-bound) and y (bind-bound) must be properly captured.
    let stmts = vec![
        DoStmt::Let {
            name: name("x"),
            val: action("compute"),
        },
        DoStmt::Bind {
            pat: name("y"),
            val: action("action"),
        },
        DoStmt::Return(Some(Expr::app(
            Expr::app(action("f"), action("x")),
            action("y"),
        ))),
    ];
    let result = desugar_do_block(&stmts, &default_config()).expect("should succeed");
    let expr = &result.desugared;

    // Outer is Let (from let x := compute)
    assert!(
        matches!(expr.kind(), ExprKind::Let(..)),
        "expected Let at top level"
    );

    // No FVars should remain
    assert!(
        !has_fvars(expr),
        "let-then-bind desugared expression should have no FVars"
    );

    // No Const references to x or y should remain
    assert!(!has_const_ref(expr, "x"), "Const(\"x\") should not remain");
    assert!(!has_const_ref(expr, "y"), "Const(\"y\") should not remain");
}

#[test]
fn test_chained_bind_action_using_bound_var() {
    // do
    //   let n <- getLine
    //   putStr n       -- action that uses bound variable n
    //
    // The non-terminal action `putStr n` should have n properly captured.
    let stmts = vec![
        DoStmt::Bind {
            pat: name("n"),
            val: action("getLine"),
        },
        DoStmt::Action(Expr::app(action("putStr"), action("n"))),
    ];
    let result = desugar_do_block(&stmts, &default_config()).expect("should succeed");
    let expr = &result.desugared;

    assert!(head_is_const(expr, "Bind.bind"), "expected Bind.bind head");

    // No FVars or Const("n") should remain
    assert!(!has_fvars(expr), "should have no FVars");
    assert!(!has_const_ref(expr, "n"), "Const(\"n\") should not remain");
}

#[test]
fn test_bind_var_not_substituted_in_unrelated_consts() {
    // do
    //   let x <- action1
    //   someOtherConst   -- this should NOT be affected by x substitution
    //
    // Constants that aren't the bound variable name should remain as Const.
    let stmts = vec![
        DoStmt::Bind {
            pat: name("x"),
            val: action("action1"),
        },
        DoStmt::Action(action("someOtherConst")),
    ];
    let result = desugar_do_block(&stmts, &default_config()).expect("should succeed");
    let expr = &result.desugared;

    // someOtherConst should still be a Const
    // (either auto_pure_last wraps it or it appears in the continuation)
    assert!(!has_fvars(expr), "should have no FVars");
}

#[test]
fn test_nested_bind_bvar_depth() {
    // do
    //   let x <- f
    //   let y <- g x
    //   return y
    //
    // In the innermost continuation `return y`:
    // - y is BVar(0) under the y-lambda
    // - x is BVar(1) under both lambdas (but g x captures x as BVar(0) in the y-bind's action)
    //
    // Structure:
    //   Bind.bind f (fun x =>
    //     Bind.bind (g x) (fun y =>
    //       Pure.pure y))
    let stmts = vec![
        DoStmt::Bind {
            pat: name("x"),
            val: action("f"),
        },
        DoStmt::Bind {
            pat: name("y"),
            val: Expr::app(action("g"), action("x")),
        },
        DoStmt::Return(Some(action("y"))),
    ];
    let result = desugar_do_block(&stmts, &default_config()).expect("should succeed");
    let expr = &result.desugared;

    assert!(head_is_const(expr, "Bind.bind"));
    assert_eq!(result.bind_count, 2);
    assert!(!has_fvars(expr), "should have no FVars");
    assert!(!has_const_ref(expr, "x"), "Const(\"x\") should not remain");
    assert!(!has_const_ref(expr, "y"), "Const(\"y\") should not remain");
}

// ===========================================================================
// For-loop and try-catch variable capture tests (#3419)
// ===========================================================================
// These tests verify that the loop variable in for-in loops and the catch
// variable in try/catch blocks are properly captured as BVar references.
// Before the fix, these variables were silently discarded (`let _ = var;`)
// leaving Const references instead of proper de Bruijn bound variables.

#[test]
fn test_for_loop_var_capture_no_fvars() {
    // for x in xs do
    //   process x
    //
    // The step function `fun x _ => process x; yield` must capture `x` as BVar,
    // not leave it as Const("x") or FVar.
    let stmts = vec![DoStmt::For {
        var: name("x"),
        iter: action("xs"),
        body: vec![DoStmt::Action(Expr::app(action("process"), action("x")))],
    }];
    let result = desugar_do_block(&stmts, &default_config()).expect("should succeed");
    let expr = &result.desugared;

    assert!(
        head_is_const(expr, "ForIn.forIn"),
        "expected ForIn.forIn head"
    );
    assert!(
        !has_fvars(expr),
        "for-loop desugared expression should have no FVars"
    );
    assert!(
        !has_const_ref(expr, "x"),
        "Const(\"x\") should not remain in for-loop body - should be BVar"
    );
}

#[test]
fn test_for_loop_var_capture_with_continuation() {
    // for x in xs do
    //   process x
    // done
    //
    // Non-terminal for-loop: var capture must still work with rest statements.
    let stmts = vec![
        DoStmt::For {
            var: name("x"),
            iter: action("xs"),
            body: vec![DoStmt::Action(Expr::app(action("process"), action("x")))],
        },
        DoStmt::Action(action("done")),
    ];
    let result = desugar_do_block(&stmts, &default_config()).expect("should succeed");
    let expr = &result.desugared;

    assert!(!has_fvars(expr), "should have no FVars");
    assert!(
        !has_const_ref(expr, "x"),
        "Const(\"x\") should not remain after for-loop var capture"
    );
}

#[test]
fn test_for_loop_var_multiple_refs() {
    // for x in xs do
    //   f x
    //   g x
    //
    // Multiple references to the loop variable must all be captured.
    let stmts = vec![DoStmt::For {
        var: name("x"),
        iter: action("xs"),
        body: vec![
            DoStmt::Action(Expr::app(action("f"), action("x"))),
            DoStmt::Action(Expr::app(action("g"), action("x"))),
        ],
    }];
    let result = desugar_do_block(&stmts, &default_config()).expect("should succeed");
    let expr = &result.desugared;

    assert!(!has_fvars(expr), "should have no FVars");
    assert!(
        !has_const_ref(expr, "x"),
        "all Const(\"x\") references should be captured as BVar"
    );
}

#[test]
fn test_try_catch_var_capture_no_fvars() {
    // try
    //   risky
    // catch e =>
    //   handle e
    //
    // The handler `fun e => handle e` must capture `e` as BVar(0), not Const("e").
    let stmts = vec![DoStmt::TryCatch {
        try_body: vec![DoStmt::Action(action("risky"))],
        catch_var: name("e"),
        catch_body: vec![DoStmt::Action(Expr::app(action("handle"), action("e")))],
    }];
    let result = desugar_do_block(&stmts, &default_config()).expect("should succeed");
    let expr = &result.desugared;

    assert!(
        head_is_const(expr, "MonadExcept.tryCatch"),
        "expected MonadExcept.tryCatch head"
    );
    assert!(
        !has_fvars(expr),
        "try-catch desugared expression should have no FVars"
    );
    assert!(
        !has_const_ref(expr, "e"),
        "Const(\"e\") should not remain in catch handler - should be BVar"
    );
}

#[test]
fn test_try_catch_var_capture_with_continuation() {
    // try
    //   risky
    // catch e =>
    //   handle e
    // continue
    //
    // Non-terminal try/catch: var capture must work with rest statements.
    let stmts = vec![
        DoStmt::TryCatch {
            try_body: vec![DoStmt::Action(action("risky"))],
            catch_var: name("e"),
            catch_body: vec![DoStmt::Action(Expr::app(action("handle"), action("e")))],
        },
        DoStmt::Action(action("continue_action")),
    ];
    let result = desugar_do_block(&stmts, &default_config()).expect("should succeed");
    let expr = &result.desugared;

    assert!(!has_fvars(expr), "should have no FVars");
    assert!(
        !has_const_ref(expr, "e"),
        "Const(\"e\") should not remain after try-catch var capture"
    );
}

#[test]
fn test_try_catch_var_multiple_refs() {
    // try
    //   risky
    // catch e =>
    //   log e
    //   rethrow e
    //
    // Multiple references to catch variable must all be captured.
    let stmts = vec![DoStmt::TryCatch {
        try_body: vec![DoStmt::Action(action("risky"))],
        catch_var: name("e"),
        catch_body: vec![
            DoStmt::Action(Expr::app(action("log"), action("e"))),
            DoStmt::Return(Some(Expr::app(action("rethrow"), action("e")))),
        ],
    }];
    let result = desugar_do_block(&stmts, &default_config()).expect("should succeed");
    let expr = &result.desugared;

    assert!(!has_fvars(expr), "should have no FVars");
    assert!(
        !has_const_ref(expr, "e"),
        "all Const(\"e\") references should be captured as BVar"
    );
}

#[test]
fn test_for_loop_var_not_captured_in_unrelated_consts() {
    // for x in xs do
    //   someOtherAction
    //
    // Constants other than the loop variable should remain as Const.
    let stmts = vec![DoStmt::For {
        var: name("x"),
        iter: action("xs"),
        body: vec![DoStmt::Action(action("someOtherAction"))],
    }];
    let result = desugar_do_block(&stmts, &default_config()).expect("should succeed");
    let expr = &result.desugared;

    assert!(!has_fvars(expr), "should have no FVars");
    // someOtherAction should still be a Const
    assert!(
        has_const_ref(expr, "someOtherAction"),
        "unrelated Const(\"someOtherAction\") should remain unchanged"
    );
}

#[test]
fn test_for_loop_chained_with_bind() {
    // do
    //   let n <- getLine
    //   for x in xs do
    //     process n x
    //   pure n
    //
    // Both the bind variable `n` and the loop variable `x` must be captured.
    let stmts = vec![
        DoStmt::Bind {
            pat: name("n"),
            val: action("getLine"),
        },
        DoStmt::For {
            var: name("x"),
            iter: action("xs"),
            body: vec![DoStmt::Action(Expr::app(
                Expr::app(action("process"), action("n")),
                action("x"),
            ))],
        },
        DoStmt::Return(Some(action("n"))),
    ];
    let result = desugar_do_block(&stmts, &default_config()).expect("should succeed");
    let expr = &result.desugared;

    assert!(!has_fvars(expr), "should have no FVars");
    assert!(
        !has_const_ref(expr, "n"),
        "Const(\"n\") from bind should be captured"
    );
    assert!(
        !has_const_ref(expr, "x"),
        "Const(\"x\") from for-loop should be captured"
    );
}
