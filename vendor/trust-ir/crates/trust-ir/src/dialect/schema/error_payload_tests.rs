// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0

use super::*;
use core::mem::size_of;

fn registry() -> DialectSchemaRegistry {
    DialectSchemaRegistry::new([DialectSchema {
        namespace: "error_payload".into(),
        version: 1,
        operations: vec![OperationSchema {
            name: "callback".into(),
            operands: vec![OperandType::Function {
                params: vec![Ty::I64],
                returns: vec![Ty::Bool],
            }],
            results: vec![],
            attributes: vec![],
        }],
    }])
    .unwrap()
}

fn operation() -> DialectInst {
    DialectInst::new("error_payload", "callback").with_operand(ValueId::new(0))
}

fn signature() -> FuncTy {
    FuncTy {
        params: vec![Ty::I64],
        returns: vec![Ty::Bool],
        abi: None,
        is_vararg: false,
    }
}

#[test]
fn schema_error_does_not_inline_a_function_signature_in_every_result() {
    assert!(
        size_of::<SchemaError>() < size_of::<FuncTy>(),
        "schema error size {} must remain below a single full FuncTy size {}",
        size_of::<SchemaError>(),
        size_of::<FuncTy>(),
    );
    assert!(size_of::<Result<&OperationSchema, SchemaError>>() < size_of::<FuncTy>());
}

#[test]
fn mismatched_function_payloads_preserve_complete_values_equality_and_diagnostics() {
    let registry = registry();
    let expected = signature();
    let mut actual = expected.clone();
    actual.params = vec![Ty::I32, Ty::U64];
    actual.returns = vec![Ty::I8];
    actual.is_vararg = true;
    let operand = Ty::Func(FuncTyId::new(7));
    let error = registry
        .validate_op_with_func_types(&operation(), 0, |_| Some(&operand), |_| Some(&actual))
        .unwrap_err();
    let expected_debug =
        format!("FunctionSignature {{ index: 0, expected: {expected:?}, actual: {actual:?} }}");
    assert_eq!(format!("{error:?}"), expected_debug);
    assert_eq!(
        error.to_string(),
        format!("dialect schema mismatch: {expected_debug}")
    );
    assert_eq!(
        error.clone(),
        error,
        "boxed signatures retain value equality"
    );
    let SchemaError::FunctionSignature {
        index,
        expected: retained_expected,
        actual: retained_actual,
    } = &error
    else {
        panic!("exact function mismatch diagnostic: {error:?}");
    };
    assert_eq!(*index, 0);
    assert_eq!(retained_expected.as_ref(), &expected);
    assert_eq!(retained_actual.as_ref(), &actual);
    assert_eq!(
        error,
        SchemaError::FunctionSignature {
            index: 0,
            expected: Box::new(expected.clone()),
            actual: Box::new(actual.clone()),
        }
    );
    actual.is_vararg = false;
    assert_ne!(
        error,
        SchemaError::FunctionSignature {
            index: 0,
            expected: Box::new(expected),
            actual: Box::new(actual),
        }
    );
}

#[test]
fn matching_function_signatures_still_return_the_original_borrowed_schema() {
    let registry = registry();
    let actual = signature();
    let operand = Ty::Func(FuncTyId::new(7));
    let first = registry
        .validate_op_with_func_types(&operation(), 0, |_| Some(&operand), |_| Some(&actual))
        .unwrap();
    let second = registry
        .validate_op_with_func_types(&operation(), 0, |_| Some(&operand), |_| Some(&actual))
        .unwrap();
    assert!(core::ptr::eq(first, second));
    assert_eq!(
        actual,
        signature(),
        "success never rewrites a borrowed FuncTy"
    );
}
