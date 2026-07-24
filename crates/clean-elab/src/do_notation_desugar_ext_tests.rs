// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for extended do-notation desugaring analysis (`do_notation_desugar_ext`).

use crate::do_notation_desugar::{DoDesugarConfig, DoStmt};
use crate::do_notation_desugar_ext::*;
use clean_kernel::{Expr, Name};

// ---------------------------------------------------------------------------
// Helpers
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

// ===========================================================================
// classify_stmt tests
// ===========================================================================

#[test]
fn test_classify_bind() {
    let stmt = DoStmt::Bind {
        pat: name("x"),
        val: action("act"),
    };
    assert_eq!(classify_stmt(&stmt), StmtKind::Bind);
}

#[test]
fn test_classify_let() {
    let stmt = DoStmt::Let {
        name: name("x"),
        val: action("v"),
    };
    assert_eq!(classify_stmt(&stmt), StmtKind::LetBind);
}

#[test]
fn test_classify_let_mut() {
    let stmt = DoStmt::LetMut {
        name: name("x"),
        val: action("v"),
    };
    assert_eq!(classify_stmt(&stmt), StmtKind::LetMut);
}

#[test]
fn test_classify_assign() {
    let stmt = DoStmt::Assign {
        name: name("x"),
        val: action("v"),
    };
    assert_eq!(classify_stmt(&stmt), StmtKind::Assign);
}

#[test]
fn test_classify_action() {
    let stmt = DoStmt::Action(action("foo"));
    assert_eq!(classify_stmt(&stmt), StmtKind::Action);
}

#[test]
fn test_classify_return_some() {
    let stmt = DoStmt::Return(Some(action("v")));
    assert_eq!(classify_stmt(&stmt), StmtKind::Return);
}

#[test]
fn test_classify_return_none() {
    let stmt = DoStmt::Return(None);
    assert_eq!(classify_stmt(&stmt), StmtKind::Return);
}

#[test]
fn test_classify_if() {
    let stmt = DoStmt::If {
        cond: action("c"),
        then_: vec![DoStmt::Action(action("a"))],
        else_: vec![],
    };
    assert_eq!(classify_stmt(&stmt), StmtKind::If);
}

#[test]
fn test_classify_for() {
    let stmt = DoStmt::For {
        var: name("x"),
        iter: action("xs"),
        body: vec![DoStmt::Action(action("a"))],
    };
    assert_eq!(classify_stmt(&stmt), StmtKind::For);
}

#[test]
fn test_classify_try_catch() {
    let stmt = DoStmt::TryCatch {
        try_body: vec![DoStmt::Action(action("a"))],
        catch_var: name("e"),
        catch_body: vec![DoStmt::Action(action("b"))],
    };
    assert_eq!(classify_stmt(&stmt), StmtKind::TryCatch);
}

#[test]
fn test_classify_unless() {
    let stmt = DoStmt::Unless {
        cond: action("c"),
        body: vec![DoStmt::Action(action("a"))],
    };
    assert_eq!(classify_stmt(&stmt), StmtKind::Unless);
}

#[test]
fn test_classify_repeat() {
    let stmt = DoStmt::Repeat {
        body: vec![DoStmt::Action(action("a"))],
        until: None,
    };
    assert_eq!(classify_stmt(&stmt), StmtKind::Repeat);
}

// ===========================================================================
// classify_block tests
// ===========================================================================

#[test]
fn test_classify_block_empty() {
    assert!(classify_block(&[]).is_empty());
}

#[test]
fn test_classify_block_mixed() {
    let stmts = vec![
        DoStmt::Bind {
            pat: name("x"),
            val: action("a"),
        },
        DoStmt::Let {
            name: name("y"),
            val: action("b"),
        },
        DoStmt::Return(Some(action("r"))),
    ];
    let kinds = classify_block(&stmts);
    assert_eq!(
        kinds,
        vec![StmtKind::Bind, StmtKind::LetBind, StmtKind::Return]
    );
}

// ===========================================================================
// compute_metrics tests
// ===========================================================================

#[test]
fn test_metrics_empty() {
    let m = compute_metrics(&[]);
    assert_eq!(m.statement_count, 0);
    assert_eq!(m.max_nesting_depth, 0);
    assert_eq!(m.bind_count, 0);
    assert!(!m.has_control_flow);
}

#[test]
fn test_metrics_single_action() {
    let stmts = vec![DoStmt::Action(action("foo"))];
    let m = compute_metrics(&stmts);
    assert_eq!(m.statement_count, 1);
    assert_eq!(m.bind_count, 0); // terminal action, no bind
    assert_eq!(m.max_nesting_depth, 0);
    assert!(!m.has_control_flow);
}

#[test]
fn test_metrics_bind_chain() {
    let stmts = vec![
        DoStmt::Bind {
            pat: name("x"),
            val: action("a"),
        },
        DoStmt::Bind {
            pat: name("y"),
            val: action("b"),
        },
        DoStmt::Return(Some(action("r"))),
    ];
    let m = compute_metrics(&stmts);
    assert_eq!(m.statement_count, 3);
    assert_eq!(m.bind_count, 2);
    assert_eq!(m.let_count, 0);
    assert_eq!(m.mut_var_count, 0);
}

#[test]
fn test_metrics_let_and_mut() {
    let stmts = vec![
        DoStmt::Let {
            name: name("a"),
            val: action("v1"),
        },
        DoStmt::LetMut {
            name: name("b"),
            val: action("v2"),
        },
        DoStmt::Action(action("done")),
    ];
    let m = compute_metrics(&stmts);
    assert_eq!(m.let_count, 2);
    assert_eq!(m.mut_var_count, 1);
}

#[test]
fn test_metrics_nesting_depth_if() {
    let stmts = vec![DoStmt::If {
        cond: action("c"),
        then_: vec![DoStmt::If {
            cond: action("c2"),
            then_: vec![DoStmt::Action(action("deep"))],
            else_: vec![],
        }],
        else_: vec![DoStmt::Action(action("shallow"))],
    }];
    let m = compute_metrics(&stmts);
    assert_eq!(m.max_nesting_depth, 2);
    assert!(m.has_control_flow);
}

#[test]
fn test_metrics_nesting_depth_for() {
    let stmts = vec![DoStmt::For {
        var: name("x"),
        iter: action("xs"),
        body: vec![DoStmt::Action(action("inner"))],
    }];
    let m = compute_metrics(&stmts);
    assert_eq!(m.max_nesting_depth, 1);
    assert!(m.has_control_flow);
}

#[test]
fn test_metrics_nesting_depth_try_catch() {
    let stmts = vec![DoStmt::TryCatch {
        try_body: vec![DoStmt::For {
            var: name("x"),
            iter: action("xs"),
            body: vec![DoStmt::Action(action("deep"))],
        }],
        catch_var: name("e"),
        catch_body: vec![DoStmt::Action(action("handle"))],
    }];
    let m = compute_metrics(&stmts);
    assert_eq!(m.max_nesting_depth, 2); // try (1) > for (2)
    assert!(m.has_control_flow);
}

#[test]
fn test_metrics_control_flow_false_for_pure() {
    let stmts = vec![
        DoStmt::Let {
            name: name("x"),
            val: action("v"),
        },
        DoStmt::Return(Some(action("x"))),
    ];
    let m = compute_metrics(&stmts);
    assert!(!m.has_control_flow);
}

// ===========================================================================
// compute_dependencies tests
// ===========================================================================

#[test]
fn test_deps_empty() {
    let info = compute_dependencies(&[]);
    assert!(info.deps.is_empty());
    assert!(info.defs.is_empty());
}

#[test]
fn test_deps_single_action() {
    let stmts = vec![DoStmt::Action(action("foo"))];
    let info = compute_dependencies(&stmts);
    assert_eq!(info.deps.len(), 1);
    assert!(info.deps[0].is_empty());
    assert!(info.defs[0].is_none());
}

#[test]
fn test_deps_bind_then_return() {
    let stmts = vec![
        DoStmt::Bind {
            pat: name("x"),
            val: action("getLine"),
        },
        DoStmt::Return(Some(action("x"))),
    ];
    let info = compute_dependencies(&stmts);
    assert_eq!(info.defs[0], Some(name("x")));
    // Return depends on prior bind for monadic ordering.
    assert!(info.deps[1].contains(&0));
}

#[test]
fn test_deps_independent_lets() {
    let stmts = vec![
        DoStmt::Let {
            name: name("a"),
            val: action("v1"),
        },
        DoStmt::Let {
            name: name("b"),
            val: action("v2"),
        },
        DoStmt::Return(Some(action("r"))),
    ];
    let info = compute_dependencies(&stmts);
    // Two consecutive lets: no monadic dependency between them.
    assert!(info.deps[1].is_empty());
    // Return depends on the let before it.
    assert!(info.deps[2].contains(&1));
}

#[test]
fn test_deps_if_depends_on_all_prior() {
    let stmts = vec![
        DoStmt::Let {
            name: name("x"),
            val: action("v"),
        },
        DoStmt::If {
            cond: action("c"),
            then_: vec![DoStmt::Action(action("a"))],
            else_: vec![],
        },
    ];
    let info = compute_dependencies(&stmts);
    // If has sub-blocks, so depends on all prior defs.
    assert!(info.deps[1].contains(&0));
}

// ===========================================================================
// find_independent_stmts tests
// ===========================================================================

#[test]
fn test_independent_empty() {
    let info = compute_dependencies(&[]);
    let groups = find_independent_stmts(&info);
    assert!(groups.is_empty());
}

#[test]
fn test_independent_single() {
    let stmts = vec![DoStmt::Action(action("a"))];
    let info = compute_dependencies(&stmts);
    let groups = find_independent_stmts(&info);
    assert_eq!(groups.len(), 1);
    assert_eq!(groups[0], vec![0]);
}

#[test]
fn test_independent_lets_grouped() {
    let stmts = vec![
        DoStmt::Let {
            name: name("a"),
            val: action("v1"),
        },
        DoStmt::Let {
            name: name("b"),
            val: action("v2"),
        },
        DoStmt::Return(Some(action("r"))),
    ];
    let info = compute_dependencies(&stmts);
    let groups = find_independent_stmts(&info);
    // First two lets are independent, return depends on second let.
    assert!(groups.len() >= 2);
    assert!(groups[0].contains(&0));
    assert!(groups[0].contains(&1));
}

// ===========================================================================
// suggest_optimizations tests
// ===========================================================================

#[test]
fn test_optimization_empty() {
    let hints = suggest_optimizations(&[]);
    assert!(hints.is_empty());
}

#[test]
fn test_optimization_pure_bind_fusion() {
    // x <- action; return x → pure-bind fusion
    let stmts = vec![
        DoStmt::Bind {
            pat: name("x"),
            val: action("getLine"),
        },
        DoStmt::Return(Some(action("x"))),
    ];
    let hints = suggest_optimizations(&stmts);
    assert!(hints
        .iter()
        .any(|h| matches!(h, OptimizationHint::PureBindFusion { bind_index: 0 })));
}

#[test]
fn test_optimization_could_be_expression() {
    // Single return → could be expression.
    let stmts = vec![DoStmt::Return(Some(action("v")))];
    let hints = suggest_optimizations(&stmts);
    assert!(hints
        .iter()
        .any(|h| matches!(h, OptimizationHint::CouldBeExpression)));
}

#[test]
fn test_optimization_single_action_could_be_expression() {
    let stmts = vec![DoStmt::Action(action("v"))];
    let hints = suggest_optimizations(&stmts);
    assert!(hints
        .iter()
        .any(|h| matches!(h, OptimizationHint::CouldBeExpression)));
}

#[test]
fn test_optimization_could_use_functor() {
    // x <- action; return (f x) → functor
    let stmts = vec![
        DoStmt::Bind {
            pat: name("x"),
            val: action("getLine"),
        },
        DoStmt::Return(Some(action("transform_x"))),
    ];
    let hints = suggest_optimizations(&stmts);
    assert!(hints
        .iter()
        .any(|h| matches!(h, OptimizationHint::CouldUseFunctor)));
}

#[test]
fn test_optimization_independent_lets() {
    let stmts = vec![
        DoStmt::Let {
            name: name("a"),
            val: action("v1"),
        },
        DoStmt::Let {
            name: name("b"),
            val: action("v2"),
        },
        DoStmt::Return(Some(action("r"))),
    ];
    let hints = suggest_optimizations(&stmts);
    assert!(hints.iter().any(|h| matches!(
        h,
        OptimizationHint::IndependentLetBindings { indices } if indices.len() == 2
    )));
}

#[test]
fn test_optimization_no_hints_for_complex_block() {
    // A complex block with real dependencies should not produce spurious hints.
    let stmts = vec![
        DoStmt::Bind {
            pat: name("x"),
            val: action("getLine"),
        },
        DoStmt::Bind {
            pat: name("y"),
            val: action("process"),
        },
        DoStmt::Action(action("print_result")),
    ];
    let hints = suggest_optimizations(&stmts);
    // No pure-bind fusion (return doesn't match bound name).
    // Not a single-stmt block. Not a functor pattern.
    assert!(!hints
        .iter()
        .any(|h| matches!(h, OptimizationHint::PureBindFusion { .. })));
    assert!(!hints
        .iter()
        .any(|h| matches!(h, OptimizationHint::CouldBeExpression)));
}

// ===========================================================================
// detect_monad_usage tests
// ===========================================================================

#[test]
fn test_usage_pure_only() {
    let stmts = vec![DoStmt::Return(Some(action("v")))];
    let usage = detect_monad_usage(&stmts);
    assert!(usage.uses_pure);
    assert!(!usage.uses_bind);
    assert_eq!(usage.minimum_class, "Applicative");
}

#[test]
fn test_usage_bind() {
    let stmts = vec![
        DoStmt::Bind {
            pat: name("x"),
            val: action("a"),
        },
        DoStmt::Return(Some(action("x"))),
    ];
    let usage = detect_monad_usage(&stmts);
    assert!(usage.uses_bind);
    assert!(usage.uses_pure);
    assert_eq!(usage.minimum_class, "Monad");
}

#[test]
fn test_usage_state() {
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
    let usage = detect_monad_usage(&stmts);
    assert!(usage.uses_state);
    assert_eq!(usage.minimum_class, "MonadState");
}

#[test]
fn test_usage_except() {
    let stmts = vec![DoStmt::TryCatch {
        try_body: vec![DoStmt::Action(action("risky"))],
        catch_var: name("e"),
        catch_body: vec![DoStmt::Action(action("handle"))],
    }];
    let usage = detect_monad_usage(&stmts);
    assert!(usage.uses_except);
    assert_eq!(usage.minimum_class, "MonadExcept");
}

#[test]
fn test_usage_for_in() {
    let stmts = vec![DoStmt::For {
        var: name("x"),
        iter: action("xs"),
        body: vec![DoStmt::Action(action("process"))],
    }];
    let usage = detect_monad_usage(&stmts);
    assert!(usage.uses_for_in);
    assert_eq!(usage.minimum_class, "Monad");
}

#[test]
fn test_usage_repeat_uses_for_in() {
    let stmts = vec![DoStmt::Repeat {
        body: vec![DoStmt::Action(action("step"))],
        until: None,
    }];
    let usage = detect_monad_usage(&stmts);
    assert!(usage.uses_for_in);
}

#[test]
fn test_usage_unless_uses_pure() {
    let stmts = vec![DoStmt::Unless {
        cond: action("flag"),
        body: vec![DoStmt::Action(action("work"))],
    }];
    let usage = detect_monad_usage(&stmts);
    assert!(usage.uses_pure);
}

#[test]
fn test_usage_let_only_is_functor() {
    let stmts = vec![
        DoStmt::Let {
            name: name("x"),
            val: action("v"),
        },
        DoStmt::Let {
            name: name("y"),
            val: action("w"),
        },
        // Terminal action triggers pure usage.
        DoStmt::Action(action("done")),
    ];
    let usage = detect_monad_usage(&stmts);
    // Terminal action uses pure, no bind from the lets.
    assert!(usage.uses_pure);
    assert!(!usage.uses_bind);
    assert_eq!(usage.minimum_class, "Applicative");
}

// ===========================================================================
// desugar_preview tests
// ===========================================================================

#[test]
fn test_preview_empty_block_error() {
    let result = desugar_preview(&[], &default_config());
    assert!(result.is_err());
    match result.unwrap_err() {
        DoDesugarExtError::EmptyBlock => {}
        other => panic!("expected EmptyBlock, got {other:?}"),
    }
}

#[test]
fn test_preview_single_action() {
    let stmts = vec![DoStmt::Action(action("foo"))];
    let preview = desugar_preview(&stmts, &default_config()).expect("should succeed");
    assert!(!preview.preview_text.is_empty());
    assert_eq!(preview.bind_count, 0);
    assert!(preview.mut_vars.is_empty());
    assert_eq!(preview.metrics.statement_count, 1);
}

#[test]
fn test_preview_bind_chain() {
    let stmts = vec![
        DoStmt::Bind {
            pat: name("x"),
            val: action("getLine"),
        },
        DoStmt::Action(action("putStr")),
    ];
    let preview = desugar_preview(&stmts, &default_config()).expect("should succeed");
    assert_eq!(preview.bind_count, 1);
    assert!(preview.preview_text.contains("Bind.bind"));
}

#[test]
fn test_preview_minimum_class() {
    let stmts = vec![DoStmt::Return(Some(action("v")))];
    let preview = desugar_preview(&stmts, &default_config()).expect("should succeed");
    assert_eq!(preview.minimum_class, "Applicative");
}

#[test]
fn test_preview_with_mutable() {
    let stmts = vec![
        DoStmt::LetMut {
            name: name("counter"),
            val: Expr::nat_lit(0),
        },
        DoStmt::Action(action("done")),
    ];
    let preview = desugar_preview(&stmts, &default_config()).expect("should succeed");
    assert_eq!(preview.mut_vars.len(), 1);
    assert_eq!(preview.minimum_class, "MonadState");
}

// ===========================================================================
// find_bind_chains tests
// ===========================================================================

#[test]
fn test_bind_chains_empty() {
    assert!(find_bind_chains(&[]).is_empty());
}

#[test]
fn test_bind_chains_no_binds() {
    let stmts = vec![
        DoStmt::Let {
            name: name("x"),
            val: action("v"),
        },
        DoStmt::Return(Some(action("x"))),
    ];
    assert!(find_bind_chains(&stmts).is_empty());
}

#[test]
fn test_bind_chains_single_bind() {
    let stmts = vec![
        DoStmt::Bind {
            pat: name("x"),
            val: action("a"),
        },
        DoStmt::Return(Some(action("x"))),
    ];
    let chains = find_bind_chains(&stmts);
    assert_eq!(chains.len(), 1);
    assert_eq!(chains[0].start, 0);
    assert_eq!(chains[0].length, 1);
    assert!(chains[0].ends_with_return);
}

#[test]
fn test_bind_chains_consecutive_binds() {
    let stmts = vec![
        DoStmt::Bind {
            pat: name("x"),
            val: action("a"),
        },
        DoStmt::Bind {
            pat: name("y"),
            val: action("b"),
        },
        DoStmt::Action(action("c")),
        DoStmt::Return(Some(action("r"))),
    ];
    let chains = find_bind_chains(&stmts);
    assert_eq!(chains.len(), 1);
    assert_eq!(chains[0].start, 0);
    assert_eq!(chains[0].length, 3); // bind, bind, action
    assert!(chains[0].ends_with_return);
}

#[test]
fn test_bind_chains_split_by_let() {
    let stmts = vec![
        DoStmt::Bind {
            pat: name("x"),
            val: action("a"),
        },
        DoStmt::Let {
            name: name("y"),
            val: action("b"),
        },
        DoStmt::Bind {
            pat: name("z"),
            val: action("c"),
        },
        DoStmt::Return(Some(action("r"))),
    ];
    let chains = find_bind_chains(&stmts);
    assert_eq!(chains.len(), 2);
    assert_eq!(chains[0].start, 0);
    assert_eq!(chains[0].length, 1);
    assert_eq!(chains[1].start, 2);
    assert_eq!(chains[1].length, 1);
    assert!(chains[1].ends_with_return);
}

#[test]
fn test_bind_chains_trailing_action() {
    let stmts = vec![
        DoStmt::Let {
            name: name("x"),
            val: action("v"),
        },
        DoStmt::Action(action("a")),
        DoStmt::Action(action("b")),
    ];
    let chains = find_bind_chains(&stmts);
    assert_eq!(chains.len(), 1);
    assert_eq!(chains[0].start, 1);
    assert_eq!(chains[0].length, 2);
    assert!(!chains[0].ends_with_return);
}

// ===========================================================================
// Error type tests
// ===========================================================================

#[test]
fn test_error_display_empty_block() {
    let err = DoDesugarExtError::EmptyBlock;
    assert_eq!(err.to_string(), "empty do-block: nothing to analyze");
}

#[test]
fn test_error_display_index_out_of_range() {
    let err = DoDesugarExtError::IndexOutOfRange(5, 3);
    assert_eq!(
        err.to_string(),
        "statement index 5 out of range (block has 3 statements)"
    );
}

#[test]
fn test_error_display_preview_failed() {
    let err = DoDesugarExtError::PreviewFailed("empty do block".into());
    assert_eq!(err.to_string(), "desugar preview failed: empty do block");
}

#[test]
fn test_error_converts_to_elab_error() {
    let ext_err = DoDesugarExtError::EmptyBlock;
    let elab_err: crate::ElabError = ext_err.into();
    match elab_err {
        crate::ElabError::NotImplemented(msg) => {
            assert!(msg.contains("empty do-block"));
        }
        other => panic!("expected NotImplemented, got {other:?}"),
    }
}
