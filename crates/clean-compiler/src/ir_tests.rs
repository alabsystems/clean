// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for L5IR types and utilities.

use super::*;

#[test]
fn test_ir_type_scalars() {
    assert_eq!(IRType::UInt64, IRType::UInt64);
    assert_ne!(IRType::UInt32, IRType::UInt64);
}

#[test]
fn test_var_id() {
    let v1 = VarId(0);
    let v2 = VarId(1);
    assert_ne!(v1, v2);
}

#[test]
fn test_ir_literal() {
    let lit = IRLiteral::UInt64(42);
    assert!(matches!(lit, IRLiteral::UInt64(42)));
}

#[test]
fn test_ir_body_ret() {
    let body = IRBody::Ret(IRArg::Var(VarId(0)));
    assert!(matches!(body, IRBody::Ret(_)));
}

#[test]
fn test_ir_body_inc_dec() {
    let body = IRBody::Inc {
        var: VarId(0),
        n: 1,
        rest: Box::new(IRBody::Dec {
            var: VarId(0),
            rest: Box::new(IRBody::Ret(IRArg::Var(VarId(0)))),
        }),
    };
    assert!(matches!(body, IRBody::Inc { .. }));
}

// ========================================================================
// Boxing utilities tests (#1040)
// ========================================================================

#[test]
fn test_is_scalar() {
    // All scalar types
    assert!(IRType::Bool.is_scalar());
    assert!(IRType::UInt8.is_scalar());
    assert!(IRType::UInt16.is_scalar());
    assert!(IRType::UInt32.is_scalar());
    assert!(IRType::UInt64.is_scalar());
    assert!(IRType::USize.is_scalar());
    assert!(IRType::Float32.is_scalar());
    assert!(IRType::Float64.is_scalar());

    // Non-scalar types
    assert!(!IRType::Object.is_scalar());
    assert!(!IRType::TObject.is_scalar());
    assert!(!IRType::Struct(vec![]).is_scalar());
    assert!(!IRType::Union(vec![]).is_scalar());
    assert!(!IRType::Erased.is_scalar());
    assert!(!IRType::Void.is_scalar());
}

#[test]
fn test_is_object() {
    // Object types (heap-allocated, reference-counted)
    assert!(IRType::Object.is_object());
    assert!(IRType::TObject.is_object());
    assert!(IRType::Struct(vec![]).is_object());
    assert!(IRType::Union(vec![]).is_object());

    // Non-object types
    assert!(!IRType::Bool.is_object());
    assert!(!IRType::UInt64.is_object());
    assert!(!IRType::Void.is_object());
    assert!(!IRType::Erased.is_object());
}

#[test]
fn test_is_rc_type() {
    assert!(IRType::Object.is_rc_type());
    assert!(IRType::TObject.is_rc_type());
    assert!(IRType::Struct(vec![]).is_rc_type());
    assert!(IRType::Union(vec![]).is_rc_type());

    assert!(!IRType::Bool.is_rc_type());
    assert!(!IRType::UInt64.is_rc_type());
    assert!(!IRType::Void.is_rc_type());
    assert!(!IRType::Erased.is_rc_type());
}

#[test]
fn test_is_void() {
    assert!(IRType::Void.is_void());
    assert!(!IRType::Bool.is_void());
    assert!(!IRType::Object.is_void());
}

#[test]
fn test_boxed() {
    // Scalars become Object (heap-allocated lean_object*)
    assert_eq!(IRType::Bool.boxed(), IRType::Object);
    assert_eq!(IRType::UInt8.boxed(), IRType::Object);
    assert_eq!(IRType::UInt64.boxed(), IRType::Object);
    assert_eq!(IRType::Float64.boxed(), IRType::Object);

    // Objects remain unchanged
    assert_eq!(IRType::Object.boxed(), IRType::Object);
    assert_eq!(IRType::TObject.boxed(), IRType::TObject);

    // Other types remain unchanged
    assert_eq!(IRType::Void.boxed(), IRType::Void);
    assert_eq!(IRType::Erased.boxed(), IRType::Erased);
}

#[test]
fn test_eqv_types() {
    // Same scalar types are equivalent
    assert!(eqv_types(&IRType::UInt64, &IRType::UInt64));
    assert!(eqv_types(&IRType::Bool, &IRType::Bool));

    // Different scalar types are not equivalent
    assert!(!eqv_types(&IRType::UInt64, &IRType::UInt32));
    assert!(!eqv_types(&IRType::Bool, &IRType::UInt8));

    // All object types are equivalent to each other
    assert!(eqv_types(&IRType::Object, &IRType::Object));
    assert!(eqv_types(&IRType::Object, &IRType::TObject));
    assert!(eqv_types(&IRType::TObject, &IRType::Object));

    // Scalar and non-scalar are never equivalent
    assert!(!eqv_types(&IRType::UInt64, &IRType::Object));
    assert!(!eqv_types(&IRType::Object, &IRType::UInt64));

    // Void is NOT equivalent to Object — Void means "no value"
    assert!(!eqv_types(&IRType::Void, &IRType::Object));
    assert!(eqv_types(&IRType::Void, &IRType::Void));

    // Erased is NOT equivalent to Object
    assert!(!eqv_types(&IRType::Erased, &IRType::Object));
    assert!(eqv_types(&IRType::Erased, &IRType::Erased));

    // Struct and Union ARE object types — equivalent to Object
    assert!(eqv_types(&IRType::Struct(vec![]), &IRType::Object));
    assert!(eqv_types(&IRType::Union(vec![]), &IRType::Object));
}
