// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for extended IO monad elaboration.

use crate::io_monad_ext::*;
use clean_parser::SurfaceExpr;

// ============================================================================
// Helpers
// ============================================================================

/// Extract the function name from a surface App expression.
fn app_fn_name(expr: &SurfaceExpr) -> Option<&str> {
    match expr {
        SurfaceExpr::App(_, func, _) => {
            if let SurfaceExpr::Ident(_, name) = func.as_ref() {
                Some(name.as_str())
            } else {
                None
            }
        }
        _ => None,
    }
}

/// Extract the number of arguments from a surface App expression.
fn app_arg_count(expr: &SurfaceExpr) -> usize {
    match expr {
        SurfaceExpr::App(_, _, args) => args.len(),
        _ => 0,
    }
}

/// Check if expression is a Lambda.
fn is_lambda(expr: &SurfaceExpr) -> bool {
    matches!(expr, SurfaceExpr::Lambda(..))
}

fn default_config() -> IoMonadExtConfig {
    IoMonadExtConfig::default()
}

// ============================================================================
// IO error handling tests
// ============================================================================

#[test]
fn test_mk_io_throw_structure() {
    let err_val = SurfaceExpr::ident("myError");
    let result = mk_io_throw(err_val);
    assert_eq!(app_fn_name(&result), Some(IO_THROW));
    assert_eq!(app_arg_count(&result), 1);
}

#[test]
fn test_mk_io_catch_structure() {
    let action = SurfaceExpr::ident("dangerousAction");
    let handler = SurfaceExpr::ident("handleError");
    let result = mk_io_catch(action, "e", handler);
    assert_eq!(app_fn_name(&result), Some(IO_CATCH));
    assert_eq!(app_arg_count(&result), 2);
}

#[test]
fn test_mk_io_catch_has_lambda_handler() {
    let action = SurfaceExpr::ident("act");
    let handler = SurfaceExpr::ident("recover");
    let result = mk_io_catch(action, "err", handler);
    if let SurfaceExpr::App(_, _, args) = &result {
        assert!(is_lambda(&args[1].expr), "handler should be a lambda");
    } else {
        panic!("expected App");
    }
}

#[test]
fn test_mk_io_try_catch_structure() {
    let action = SurfaceExpr::ident("tryAction");
    let handler = SurfaceExpr::ident("catchHandler");
    let result = mk_io_try_catch(action, "e", handler);
    assert_eq!(app_fn_name(&result), Some(IO_TRY_CATCH));
    assert_eq!(app_arg_count(&result), 2);
}

#[test]
fn test_mk_io_try_finally_structure() {
    let action = SurfaceExpr::ident("mainAction");
    let finalizer = SurfaceExpr::ident("cleanup");
    let result = mk_io_try_finally(action, finalizer);
    assert_eq!(app_fn_name(&result), Some(IO_TRY_FINALLY));
    assert_eq!(app_arg_count(&result), 2);
}

#[test]
fn test_mk_io_try_finally_no_lambda() {
    let action = SurfaceExpr::ident("act");
    let finalizer = SurfaceExpr::ident("fin");
    let result = mk_io_try_finally(action, finalizer);
    // tryFinally takes two direct args, no lambda wrapping
    if let SurfaceExpr::App(_, _, args) = &result {
        assert!(!is_lambda(&args[0].expr));
        assert!(!is_lambda(&args[1].expr));
    } else {
        panic!("expected App");
    }
}

// ============================================================================
// IORef operation tests
// ============================================================================

#[test]
fn test_mk_ioref_mk_structure() {
    let init = SurfaceExpr::nat(42);
    let result = mk_ioref_mk(init);
    assert_eq!(app_fn_name(&result), Some(IOREF_MK));
    assert_eq!(app_arg_count(&result), 1);
}

#[test]
fn test_mk_ioref_get_structure() {
    let ref_expr = SurfaceExpr::ident("myRef");
    let result = mk_ioref_get(ref_expr);
    assert_eq!(app_fn_name(&result), Some(IOREF_GET));
    assert_eq!(app_arg_count(&result), 1);
}

#[test]
fn test_mk_ioref_set_structure() {
    let ref_expr = SurfaceExpr::ident("myRef");
    let new_val = SurfaceExpr::nat(100);
    let result = mk_ioref_set(ref_expr, new_val);
    assert_eq!(app_fn_name(&result), Some(IOREF_SET));
    assert_eq!(app_arg_count(&result), 2);
}

#[test]
fn test_mk_ioref_modify_structure() {
    let ref_expr = SurfaceExpr::ident("counter");
    let f = SurfaceExpr::ident("Nat.succ");
    let result = mk_ioref_modify(ref_expr, f);
    assert_eq!(app_fn_name(&result), Some(IOREF_MODIFY));
    assert_eq!(app_arg_count(&result), 2);
}

#[test]
fn test_mk_ioref_swap_structure() {
    let ref_expr = SurfaceExpr::ident("slot");
    let new_val = SurfaceExpr::ident("newValue");
    let result = mk_ioref_swap(ref_expr, new_val);
    assert_eq!(app_fn_name(&result), Some(IOREF_SWAP));
    assert_eq!(app_arg_count(&result), 2);
}

// ============================================================================
// Task operation tests
// ============================================================================

#[test]
fn test_mk_task_spawn_structure() {
    let action = SurfaceExpr::ident("heavyComputation");
    let result = mk_task_spawn(action);
    assert_eq!(app_fn_name(&result), Some(TASK_SPAWN));
    assert_eq!(app_arg_count(&result), 1);
}

#[test]
fn test_mk_task_get_structure() {
    let task = SurfaceExpr::ident("myTask");
    let result = mk_task_get(task);
    assert_eq!(app_fn_name(&result), Some(TASK_GET));
    assert_eq!(app_arg_count(&result), 1);
}

// ============================================================================
// File system operation tests
// ============================================================================

#[test]
fn test_mk_fs_read_file_structure() {
    let path = SurfaceExpr::ident("filePath");
    let result = mk_fs_read_file(path);
    assert_eq!(app_fn_name(&result), Some(FS_READ_FILE));
    assert_eq!(app_arg_count(&result), 1);
}

#[test]
fn test_mk_fs_write_file_structure() {
    let path = SurfaceExpr::ident("outPath");
    let content = SurfaceExpr::ident("data");
    let result = mk_fs_write_file(path, content);
    assert_eq!(app_fn_name(&result), Some(FS_WRITE_FILE));
    assert_eq!(app_arg_count(&result), 2);
}

#[test]
fn test_mk_fs_remove_file_structure() {
    let path = SurfaceExpr::ident("tempFile");
    let result = mk_fs_remove_file(path);
    assert_eq!(app_fn_name(&result), Some(FS_REMOVE_FILE));
    assert_eq!(app_arg_count(&result), 1);
}

// ============================================================================
// Process operation tests
// ============================================================================

#[test]
fn test_mk_process_run_structure() {
    let args = SurfaceExpr::ident("processArgs");
    let result = mk_process_run(args);
    assert_eq!(app_fn_name(&result), Some(PROCESS_RUN));
    assert_eq!(app_arg_count(&result), 1);
}

#[test]
fn test_mk_process_spawn_structure() {
    let config = SurfaceExpr::ident("procConfig");
    let result = mk_process_spawn(config);
    assert_eq!(app_fn_name(&result), Some(PROCESS_SPAWN));
    assert_eq!(app_arg_count(&result), 1);
}

// ============================================================================
// Environment operation tests
// ============================================================================

#[test]
fn test_mk_io_get_env_structure() {
    let var = SurfaceExpr::ident("PATH");
    let result = mk_io_get_env(var);
    assert_eq!(app_fn_name(&result), Some(IO_GET_ENV));
    assert_eq!(app_arg_count(&result), 1);
}

#[test]
fn test_mk_io_get_cwd_is_ident() {
    let result = mk_io_get_cwd();
    assert!(matches!(result, SurfaceExpr::Ident(_, name) if name == IO_GET_CWD));
}

// ============================================================================
// Operation recognition tests
// ============================================================================

#[test]
fn test_is_extended_io_op_recognizes_all() {
    for &op in EXTENDED_IO_OPS {
        assert!(is_extended_io_op(op), "should recognize {op}");
    }
}

#[test]
fn test_is_extended_io_op_rejects_unknown() {
    assert!(!is_extended_io_op("IO.unknown"));
    assert!(!is_extended_io_op("Nat.add"));
    assert!(!is_extended_io_op(""));
}

#[test]
fn test_is_monad_transformer_recognizes_all() {
    assert!(is_monad_transformer(STATE_T));
    assert!(is_monad_transformer(EXCEPT_T));
    assert!(is_monad_transformer(READER_T));
}

#[test]
fn test_is_monad_transformer_rejects_unknown() {
    assert!(!is_monad_transformer("IO"));
    assert!(!is_monad_transformer("WriterT"));
}

// ============================================================================
// Monad transformer stacking tests
// ============================================================================

#[test]
fn test_transformer_stack_new_is_empty() {
    let stack = TransformerStack::new();
    assert_eq!(stack.depth(), 0);
}

#[test]
fn test_transformer_stack_push_increases_depth() {
    let config = default_config();
    let mut stack = TransformerStack::new();
    stack
        .push(
            TransformerLayer::StateT {
                state_type: "Nat".into(),
            },
            &config,
        )
        .unwrap();
    assert_eq!(stack.depth(), 1);
    stack
        .push(
            TransformerLayer::ExceptT {
                error_type: "String".into(),
            },
            &config,
        )
        .unwrap();
    assert_eq!(stack.depth(), 2);
}

#[test]
fn test_transformer_stack_overflow_error() {
    let config = IoMonadExtConfig {
        max_transformer_depth: 2,
        ..Default::default()
    };
    let mut stack = TransformerStack::new();
    stack
        .push(
            TransformerLayer::StateT {
                state_type: "Nat".into(),
            },
            &config,
        )
        .unwrap();
    stack
        .push(
            TransformerLayer::ExceptT {
                error_type: "String".into(),
            },
            &config,
        )
        .unwrap();
    let err = stack.push(
        TransformerLayer::ReaderT {
            env_type: "Env".into(),
        },
        &config,
    );
    assert!(err.is_err());
    match err.unwrap_err() {
        IoMonadExtError::TransformerStackOverflow { depth, max } => {
            assert_eq!(depth, 3);
            assert_eq!(max, 2);
        }
        other => panic!("unexpected error: {other:?}"),
    }
}

#[test]
fn test_transformer_stack_build_type_plain_io() {
    let stack = TransformerStack::new();
    let result = stack.build_type(SurfaceExpr::ident("Unit"));
    // Should be `IO Unit`
    assert_eq!(app_fn_name(&result), Some("IO"));
    assert_eq!(app_arg_count(&result), 1);
}

#[test]
fn test_transformer_stack_build_type_single_layer() {
    let config = default_config();
    let mut stack = TransformerStack::new();
    stack
        .push(
            TransformerLayer::StateT {
                state_type: "Nat".into(),
            },
            &config,
        )
        .unwrap();
    let result = stack.build_type(SurfaceExpr::ident("Bool"));
    // Closed in Wave 93: single-layer stack must produce `StateT Nat
    // IO Bool` with `StateT` as the outermost App head.
    assert_eq!(
        app_fn_name(&result),
        Some(STATE_T),
        "single-layer transformer stack must wrap with the layer head",
    );
}

#[test]
fn test_transformer_stack_build_type_two_layers() {
    let config = default_config();
    let mut stack = TransformerStack::new();
    stack
        .push(
            TransformerLayer::ExceptT {
                error_type: "String".into(),
            },
            &config,
        )
        .unwrap();
    stack
        .push(
            TransformerLayer::ReaderT {
                env_type: "Config".into(),
            },
            &config,
        )
        .unwrap();
    let result = stack.build_type(SurfaceExpr::ident("Unit"));
    // Closed in Wave 93: outermost layer is `ExceptT`, so the top-level
    // App head must be `ExceptT` and not another App.
    assert_eq!(
        app_fn_name(&result),
        Some(EXCEPT_T),
        "two-layer transformer stack outermost head must be ExceptT",
    );
}

#[test]
fn test_transformer_stack_build_type_zero_layers_is_io_only() {
    // Negative guard for Wave 93: an empty transformer stack must NOT
    // synthesize a phantom transformer head — the result should be a
    // bare `IO Bool` with `IO` as the App head.
    let stack = TransformerStack::new();
    let result = stack.build_type(SurfaceExpr::ident("Bool"));
    assert_eq!(
        app_fn_name(&result),
        Some("IO"),
        "empty stack must produce a bare `IO α`, not a transformer wrap",
    );
}

#[test]
fn test_transformer_stack_build_type_single_layer_inner_is_io() {
    // Negative guard for Wave 93: the `inner` arg threaded under the
    // outermost transformer must still be `IO` (not duplicated or
    // dropped). For a single-layer stack the second App arg must
    // resolve to `IO`.
    let config = default_config();
    let mut stack = TransformerStack::new();
    stack
        .push(
            TransformerLayer::ReaderT {
                env_type: "Config".into(),
            },
            &config,
        )
        .unwrap();
    let result = stack.build_type(SurfaceExpr::ident("Bool"));
    if let SurfaceExpr::App(_, _, args) = &result {
        assert_eq!(args.len(), 3, "single-layer should produce 3 App args");
        if let SurfaceExpr::Ident(_, name) = &args[1].expr {
            assert_eq!(name.as_str(), "IO", "inner stack must terminate at IO");
        } else {
            panic!(
                "expected `IO` ident as second App arg, got {:?}",
                args[1].expr
            );
        }
    } else {
        panic!("expected App, got {result:?}");
    }
}

// ============================================================================
// IO type checking tests
// ============================================================================

#[test]
fn test_check_io_type_valid() {
    let expr = SurfaceExpr::app(SurfaceExpr::ident("IO"), vec![SurfaceExpr::ident("String")]);
    let inner = check_io_type(&expr);
    assert!(inner.is_some());
    if let Some(SurfaceExpr::Ident(_, name)) = inner {
        assert_eq!(name, "String");
    } else {
        panic!("expected Ident(String)");
    }
}

#[test]
fn test_check_io_type_not_io() {
    let expr = SurfaceExpr::app(SurfaceExpr::ident("List"), vec![SurfaceExpr::ident("Nat")]);
    assert!(check_io_type(&expr).is_none());
}

#[test]
fn test_check_io_type_bare_ident() {
    let expr = SurfaceExpr::ident("IO");
    assert!(check_io_type(&expr).is_none());
}

#[test]
fn test_check_io_type_too_many_args() {
    let expr = SurfaceExpr::app(
        SurfaceExpr::ident("IO"),
        vec![SurfaceExpr::ident("A"), SurfaceExpr::ident("B")],
    );
    assert!(check_io_type(&expr).is_none());
}

#[test]
fn test_is_transformer_io_type_state_t_io() {
    // StateT Nat IO
    let expr = SurfaceExpr::app(
        SurfaceExpr::ident(STATE_T),
        vec![SurfaceExpr::ident("Nat"), SurfaceExpr::ident("IO")],
    );
    assert!(is_transformer_io_type(&expr));
}

#[test]
fn test_is_transformer_io_type_nested() {
    // ExceptT String (StateT Nat IO)
    let inner = SurfaceExpr::app(
        SurfaceExpr::ident(STATE_T),
        vec![SurfaceExpr::ident("Nat"), SurfaceExpr::ident("IO")],
    );
    let expr = SurfaceExpr::app(
        SurfaceExpr::ident(EXCEPT_T),
        vec![SurfaceExpr::ident("String"), inner],
    );
    assert!(is_transformer_io_type(&expr));
}

#[test]
fn test_is_transformer_io_type_no_io_base() {
    // StateT Nat Id — not IO-based
    let expr = SurfaceExpr::app(
        SurfaceExpr::ident(STATE_T),
        vec![SurfaceExpr::ident("Nat"), SurfaceExpr::ident("Id")],
    );
    assert!(!is_transformer_io_type(&expr));
}

// ============================================================================
// Purity boundary tests
// ============================================================================

#[test]
fn test_purity_io_context_allows_io() {
    let ctx = PurityContext::IoFunction;
    assert!(ctx.allows_io());
}

#[test]
fn test_purity_pure_function_disallows_io() {
    let ctx = PurityContext::PureFunction {
        name: "myPure".into(),
    };
    assert!(!ctx.allows_io());
}

#[test]
fn test_purity_theorem_disallows_io() {
    let ctx = PurityContext::Theorem {
        name: "thm1".into(),
    };
    assert!(!ctx.allows_io());
}

#[test]
fn test_purity_struct_field_disallows_io() {
    let ctx = PurityContext::StructField {
        struct_name: "MyStruct".into(),
    };
    assert!(!ctx.allows_io());
}

#[test]
fn test_check_io_purity_allows_in_io_context() {
    let config = default_config();
    let ctx = PurityContext::IoFunction;
    assert!(check_io_purity(IO_THROW, &ctx, &config).is_ok());
}

#[test]
fn test_check_io_purity_rejects_in_pure_context() {
    let config = default_config();
    let ctx = PurityContext::PureFunction { name: "foo".into() };
    let result = check_io_purity(IO_THROW, &ctx, &config);
    assert!(result.is_err());
    match result.unwrap_err() {
        IoMonadExtError::PurityViolation { operation, context } => {
            assert_eq!(operation, IO_THROW);
            assert!(context.contains("foo"));
        }
        other => panic!("unexpected error: {other:?}"),
    }
}

#[test]
fn test_check_io_purity_disabled() {
    let config = IoMonadExtConfig {
        enforce_purity: false,
        ..Default::default()
    };
    let ctx = PurityContext::Theorem { name: "thm".into() };
    assert!(check_io_purity(IO_THROW, &ctx, &config).is_ok());
}

#[test]
fn test_check_expr_purity_catches_io_in_pure_fn() {
    let config = default_config();
    let ctx = PurityContext::PureFunction {
        name: "pureCalc".into(),
    };
    // Expression: IO.FS.readFile "test.txt"
    let expr = SurfaceExpr::app(
        SurfaceExpr::ident(FS_READ_FILE),
        vec![SurfaceExpr::ident("path")],
    );
    let result = check_expr_purity(&expr, &ctx, &config);
    assert!(result.is_err());
}

#[test]
fn test_check_expr_purity_allows_pure_expr() {
    let config = default_config();
    let ctx = PurityContext::PureFunction {
        name: "pureCalc".into(),
    };
    // Expression: Nat.add x y (not an IO operation)
    let expr = SurfaceExpr::app(
        SurfaceExpr::ident("Nat.add"),
        vec![SurfaceExpr::ident("x"), SurfaceExpr::ident("y")],
    );
    assert!(check_expr_purity(&expr, &ctx, &config).is_ok());
}

#[test]
fn test_check_expr_purity_nested_io_in_let() {
    let config = default_config();
    let ctx = PurityContext::Theorem {
        name: "myTheorem".into(),
    };
    // let x := IO.getEnv "HOME" in x
    let io_expr = SurfaceExpr::app(
        SurfaceExpr::ident(IO_GET_ENV),
        vec![SurfaceExpr::ident("HOME")],
    );
    let binder =
        clean_parser::SurfaceBinder::new("x", None, clean_parser::SurfaceBinderInfo::Explicit);
    let expr = SurfaceExpr::Let(
        clean_parser::Span::dummy(),
        binder,
        Box::new(io_expr),
        Box::new(SurfaceExpr::ident("x")),
    );
    let result = check_expr_purity(&expr, &ctx, &config);
    assert!(result.is_err());
}

#[test]
fn test_check_expr_purity_io_in_if_branch() {
    let config = default_config();
    let ctx = PurityContext::PureFunction { name: "f".into() };
    // if cond then IO.Process.run args else pure ()
    let then_br = SurfaceExpr::app(
        SurfaceExpr::ident(PROCESS_RUN),
        vec![SurfaceExpr::ident("args")],
    );
    let expr = SurfaceExpr::If(
        clean_parser::Span::dummy(),
        Box::new(SurfaceExpr::ident("cond")),
        Box::new(then_br),
        Box::new(SurfaceExpr::ident("unit")),
    );
    let result = check_expr_purity(&expr, &ctx, &config);
    assert!(result.is_err());
}

// ============================================================================
// Edge case tests
// ============================================================================

#[test]
fn test_config_default_values() {
    let config = IoMonadExtConfig::default();
    assert!(config.enforce_purity);
    assert_eq!(config.max_transformer_depth, 8);
}

#[test]
fn test_error_display_purity_violation() {
    let err = IoMonadExtError::PurityViolation {
        operation: "IO.throw".into(),
        context: "theorem `myThm`".into(),
    };
    let msg = err.to_string();
    assert!(msg.contains("IO.throw"));
    assert!(msg.contains("pure context"));
}

#[test]
fn test_error_display_transformer_overflow() {
    let err = IoMonadExtError::TransformerStackOverflow { depth: 10, max: 8 };
    let msg = err.to_string();
    assert!(msg.contains("10"));
    assert!(msg.contains("8"));
}

#[test]
fn test_error_into_elab_error() {
    let err: ElabError = IoMonadExtError::UnrecognizedOp("foo".into()).into();
    let msg = err.to_string();
    assert!(msg.contains("foo"));
}

#[test]
fn test_name_to_ext_io_op_found() {
    let name = clean_kernel::Name::from_string("IORef.mk");
    assert_eq!(name_to_ext_io_op(&name), Some(IOREF_MK));
}

#[test]
fn test_name_to_ext_io_op_not_found() {
    let name = clean_kernel::Name::from_string("Nat.add");
    assert_eq!(name_to_ext_io_op(&name), None);
}

#[test]
fn test_purity_context_display() {
    let ctx = PurityContext::Theorem {
        name: "foo_bar".into(),
    };
    assert_eq!(ctx.to_string(), "theorem `foo_bar`");
}

use crate::error::ElabError;
