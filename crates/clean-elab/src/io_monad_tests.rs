// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for IO monad elaboration.

use crate::io_monad::*;
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

// ============================================================================
// IO type recognition tests
// ============================================================================

#[test]
fn test_is_io_type_bare_io() {
    let expr = SurfaceExpr::ident("IO");
    assert!(is_io_type(&expr));
}

#[test]
fn test_is_io_type_io_unit() {
    let expr = SurfaceExpr::app(SurfaceExpr::ident("IO"), vec![SurfaceExpr::ident("Unit")]);
    assert!(is_io_type(&expr));
}

#[test]
fn test_is_io_type_io_uint32() {
    let expr = SurfaceExpr::app(SurfaceExpr::ident("IO"), vec![SurfaceExpr::ident("UInt32")]);
    assert!(is_io_type(&expr));
}

#[test]
fn test_is_io_type_not_io() {
    let expr = SurfaceExpr::ident("Nat");
    assert!(!is_io_type(&expr));
}

#[test]
fn test_is_io_type_nested_app_not_io() {
    let expr = SurfaceExpr::app(SurfaceExpr::ident("List"), vec![SurfaceExpr::ident("Nat")]);
    assert!(!is_io_type(&expr));
}

#[test]
fn test_is_io_unit_correct() {
    let expr = SurfaceExpr::app(SurfaceExpr::ident("IO"), vec![SurfaceExpr::ident("Unit")]);
    assert!(is_io_unit(&expr));
}

#[test]
fn test_is_io_unit_wrong_arg() {
    let expr = SurfaceExpr::app(SurfaceExpr::ident("IO"), vec![SurfaceExpr::ident("Nat")]);
    assert!(!is_io_unit(&expr));
}

#[test]
fn test_is_io_uint32_correct() {
    let expr = SurfaceExpr::app(SurfaceExpr::ident("IO"), vec![SurfaceExpr::ident("UInt32")]);
    assert!(is_io_uint32(&expr));
}

#[test]
fn test_is_io_uint32_wrong_arg() {
    let expr = SurfaceExpr::app(SurfaceExpr::ident("IO"), vec![SurfaceExpr::ident("Unit")]);
    assert!(!is_io_uint32(&expr));
}

// ============================================================================
// IO result type extraction
// ============================================================================

#[test]
fn test_io_result_type_io_unit() {
    let expr = SurfaceExpr::app(SurfaceExpr::ident("IO"), vec![SurfaceExpr::ident("Unit")]);
    let result = io_result_type(&expr);
    assert!(result.is_some());
    if let Some(SurfaceExpr::Ident(_, name)) = result {
        assert_eq!(name, "Unit");
    } else {
        panic!("expected Ident(Unit)");
    }
}

#[test]
fn test_io_result_type_not_io() {
    let expr = SurfaceExpr::ident("Nat");
    assert!(io_result_type(&expr).is_none());
}

#[test]
fn test_io_result_type_bare_io() {
    let expr = SurfaceExpr::ident("IO");
    assert!(io_result_type(&expr).is_none());
}

// ============================================================================
// IO operation name recognition
// ============================================================================

#[test]
fn test_is_io_operation_known() {
    assert!(is_io_operation("IO.bind"));
    assert!(is_io_operation("IO.pure"));
    assert!(is_io_operation("IO.println"));
    assert!(is_io_operation("IO.print"));
    assert!(is_io_operation("IO.getLine"));
    assert!(is_io_operation("IO.tryCatch"));
    assert!(is_io_operation("IO.Ref.new"));
    assert!(is_io_operation("IO.Ref.get"));
    assert!(is_io_operation("IO.Ref.set"));
    assert!(is_io_operation("IO.Ref.modify"));
}

#[test]
fn test_is_io_operation_unknown() {
    assert!(!is_io_operation("IO.unknown"));
    assert!(!is_io_operation("Nat.add"));
    assert!(!is_io_operation(""));
}

// ============================================================================
// Main function validation
// ============================================================================

#[test]
fn test_validate_main_io_unit() {
    let ty = SurfaceExpr::app(SurfaceExpr::ident("IO"), vec![SurfaceExpr::ident("Unit")]);
    assert_eq!(validate_main("main", Some(&ty)), MainValidation::IoUnit);
}

#[test]
fn test_validate_main_io_uint32() {
    let ty = SurfaceExpr::app(SurfaceExpr::ident("IO"), vec![SurfaceExpr::ident("UInt32")]);
    assert_eq!(validate_main("main", Some(&ty)), MainValidation::IoUInt32);
}

#[test]
fn test_validate_main_not_main() {
    let ty = SurfaceExpr::app(SurfaceExpr::ident("IO"), vec![SurfaceExpr::ident("Unit")]);
    assert_eq!(validate_main("helper", Some(&ty)), MainValidation::NotMain);
}

#[test]
fn test_validate_main_wrong_type() {
    let ty = SurfaceExpr::ident("Nat");
    let result = validate_main("main", Some(&ty));
    assert!(matches!(result, MainValidation::InvalidMainType { .. }));
}

#[test]
fn test_validate_main_no_type() {
    let result = validate_main("main", None);
    assert!(matches!(result, MainValidation::InvalidMainType { .. }));
}

#[test]
fn test_validate_main_bare_io() {
    let ty = SurfaceExpr::ident("IO");
    let result = validate_main("main", Some(&ty));
    assert!(
        matches!(result, MainValidation::InvalidMainType { actual_type } if actual_type.contains("missing"))
    );
}

// ============================================================================
// IO.bind desugaring
// ============================================================================

#[test]
fn test_mk_io_bind_structure() {
    let action = SurfaceExpr::ident("readInput");
    let body = SurfaceExpr::ident("processInput");
    let result = mk_io_bind("x", action, body);

    assert_eq!(app_fn_name(&result), Some("IO.bind"));
    assert_eq!(app_arg_count(&result), 2);
}

#[test]
fn test_mk_io_bind_continuation_is_lambda() {
    let action = SurfaceExpr::ident("readInput");
    let body = SurfaceExpr::ident("processInput");
    let result = mk_io_bind("x", action, body);

    if let SurfaceExpr::App(_, _, args) = &result {
        assert!(is_lambda(&args[1].expr));
    } else {
        panic!("expected App");
    }
}

#[test]
fn test_desugar_io_binds_single_step() {
    let steps = vec![("x".to_owned(), SurfaceExpr::ident("getInput"))];
    let terminal = mk_io_pure(SurfaceExpr::ident("x"));
    let result = desugar_io_binds(&steps, terminal);

    assert_eq!(app_fn_name(&result), Some("IO.bind"));
}

#[test]
fn test_desugar_io_binds_multiple_steps() {
    let steps = vec![
        ("x".to_owned(), SurfaceExpr::ident("getLine")),
        ("y".to_owned(), SurfaceExpr::ident("processLine")),
    ];
    let terminal = mk_io_pure(SurfaceExpr::ident("y"));
    let result = desugar_io_binds(&steps, terminal);

    // Outermost should be IO.bind for first step
    assert_eq!(app_fn_name(&result), Some("IO.bind"));
}

#[test]
fn test_desugar_io_binds_empty_steps() {
    let steps: Vec<(String, SurfaceExpr)> = vec![];
    let terminal = SurfaceExpr::ident("done");
    let result = desugar_io_binds(&steps, terminal);

    // With no steps, should return terminal directly
    if let SurfaceExpr::Ident(_, name) = &result {
        assert_eq!(name, "done");
    } else {
        panic!("expected Ident(done)");
    }
}

// ============================================================================
// IO.pure insertion
// ============================================================================

#[test]
fn test_mk_io_pure_wraps_value() {
    let val = SurfaceExpr::ident("result");
    let result = mk_io_pure(val);

    assert_eq!(app_fn_name(&result), Some("IO.pure"));
    assert_eq!(app_arg_count(&result), 1);
}

#[test]
fn test_mk_io_pure_unit() {
    let result = mk_io_pure_unit();

    assert_eq!(app_fn_name(&result), Some("IO.pure"));
    if let SurfaceExpr::App(_, _, args) = &result {
        if let SurfaceExpr::Ident(_, name) = &args[0].expr {
            assert_eq!(name, "Unit.unit");
        } else {
            panic!("expected Ident(Unit.unit)");
        }
    } else {
        panic!("expected App");
    }
}

// ============================================================================
// IO.map
// ============================================================================

#[test]
fn test_mk_io_map_structure() {
    let f = SurfaceExpr::ident("toString");
    let action = SurfaceExpr::ident("getLine");
    let result = mk_io_map(f, action);

    assert_eq!(app_fn_name(&result), Some("IO.map"));
    assert_eq!(app_arg_count(&result), 2);
}

// ============================================================================
// IO error handling
// ============================================================================

#[test]
fn test_mk_io_try_catch_structure() {
    let action = SurfaceExpr::ident("riskyAction");
    let handler = SurfaceExpr::ident("handleError");
    let result = mk_io_try_catch(action, "e", handler);

    assert_eq!(app_fn_name(&result), Some("IO.tryCatch"));
    assert_eq!(app_arg_count(&result), 2);
}

#[test]
fn test_mk_io_try_catch_handler_is_lambda() {
    let action = SurfaceExpr::ident("riskyAction");
    let handler = SurfaceExpr::ident("handleError");
    let result = mk_io_try_catch(action, "e", handler);

    if let SurfaceExpr::App(_, _, args) = &result {
        assert!(is_lambda(&args[1].expr));
    } else {
        panic!("expected App");
    }
}

// ============================================================================
// IO.Ref operations
// ============================================================================

#[test]
fn test_mk_io_ref_new() {
    let init = SurfaceExpr::nat(0);
    let result = mk_io_ref_new(init);

    assert_eq!(app_fn_name(&result), Some("IO.Ref.new"));
    assert_eq!(app_arg_count(&result), 1);
}

#[test]
fn test_mk_io_ref_get() {
    let ref_expr = SurfaceExpr::ident("myRef");
    let result = mk_io_ref_get(ref_expr);

    assert_eq!(app_fn_name(&result), Some("IO.Ref.get"));
    assert_eq!(app_arg_count(&result), 1);
}

#[test]
fn test_mk_io_ref_set() {
    let ref_expr = SurfaceExpr::ident("myRef");
    let new_val = SurfaceExpr::nat(42);
    let result = mk_io_ref_set(ref_expr, new_val);

    assert_eq!(app_fn_name(&result), Some("IO.Ref.set"));
    assert_eq!(app_arg_count(&result), 2);
}

#[test]
fn test_mk_io_ref_modify() {
    let ref_expr = SurfaceExpr::ident("myRef");
    let f = SurfaceExpr::ident("Nat.succ");
    let result = mk_io_ref_modify(ref_expr, f);

    assert_eq!(app_fn_name(&result), Some("IO.Ref.modify"));
    assert_eq!(app_arg_count(&result), 2);
}

// ============================================================================
// Built-in IO actions
// ============================================================================

#[test]
fn test_mk_io_println() {
    let msg = SurfaceExpr::ident("msg");
    let result = mk_io_println(msg);

    assert_eq!(app_fn_name(&result), Some("IO.println"));
    assert_eq!(app_arg_count(&result), 1);
}

#[test]
fn test_mk_io_print() {
    let msg = SurfaceExpr::ident("msg");
    let result = mk_io_print(msg);

    assert_eq!(app_fn_name(&result), Some("IO.print"));
    assert_eq!(app_arg_count(&result), 1);
}

#[test]
fn test_mk_io_get_line() {
    let result = mk_io_get_line();
    if let SurfaceExpr::Ident(_, name) = &result {
        assert_eq!(name, "IO.getLine");
    } else {
        panic!("expected Ident(IO.getLine)");
    }
}

// ============================================================================
// IO entry point checking
// ============================================================================

#[test]
fn test_check_io_entry_point_valid() {
    let ty = SurfaceExpr::app(SurfaceExpr::ident("IO"), vec![SurfaceExpr::ident("Unit")]);
    let result = check_io_entry_point("main", Some(&ty));
    assert!(result.is_ok());
    assert_eq!(result.unwrap(), Some(MainValidation::IoUnit));
}

#[test]
fn test_check_io_entry_point_not_main() {
    let ty = SurfaceExpr::app(SurfaceExpr::ident("IO"), vec![SurfaceExpr::ident("Unit")]);
    let result = check_io_entry_point("helper", Some(&ty));
    assert!(result.is_ok());
    assert_eq!(result.unwrap(), None);
}

#[test]
fn test_check_io_entry_point_invalid_type() {
    let ty = SurfaceExpr::ident("Nat");
    let result = check_io_entry_point("main", Some(&ty));
    assert!(result.is_err());
}

// ============================================================================
// build_io_program
// ============================================================================

#[test]
fn test_build_io_program_empty_with_terminal() {
    let terminal = mk_io_pure(SurfaceExpr::ident("result"));
    let result = build_io_program(&[], Some(terminal)).expect("should succeed");

    assert_eq!(app_fn_name(&result), Some("IO.pure"));
}

#[test]
fn test_build_io_program_empty_no_terminal() {
    let result = build_io_program(&[], None).expect("should succeed");

    // Should produce IO.pure Unit.unit
    assert_eq!(app_fn_name(&result), Some("IO.pure"));
}

#[test]
fn test_build_io_program_with_steps() {
    let steps = vec![("_".to_owned(), mk_io_println(SurfaceExpr::ident("msg")))];
    let result = build_io_program(&steps, None).expect("should succeed");

    assert_eq!(app_fn_name(&result), Some("IO.bind"));
}

// ============================================================================
// name_to_io_op
// ============================================================================

#[test]
fn test_name_to_io_op_known() {
    let name = clean_kernel::Name::from_string("IO.bind");
    assert_eq!(name_to_io_op(&name), Some("IO.bind"));
}

#[test]
fn test_name_to_io_op_unknown() {
    let name = clean_kernel::Name::from_string("Nat.add");
    assert_eq!(name_to_io_op(&name), None);
}
