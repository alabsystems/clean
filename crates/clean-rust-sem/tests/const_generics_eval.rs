// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use clean_rust_sem::eval::Interpreter;
use clean_rust_sem::expr::Expr;
use clean_rust_sem::stmt::TypeDef;
use clean_rust_sem::types::{
    validate_const_generic_bounds, ConstGenericArg, ConstGenericBound, ConstGenericEval,
    ConstGenericUnifier, ConstGenericValue, ConstParamDef,
};
use clean_rust_sem::{RustType, UintType, Value};
use std::collections::BTreeMap;
use std::collections::HashMap;

#[test]
fn test_eval_struct_with_const_generic_array_field() {
    let mut interp = Interpreter::new();

    interp.ctx.register_type(TypeDef::Struct {
        name: "Buffer".to_string(),
        fields: vec![(
            "data".to_string(),
            RustType::Array {
                element: Box::new(RustType::Uint(UintType::U8)),
                len: ConstGenericArg::Param("N".to_string()),
            },
        )],
        type_params: vec![],
        const_params: vec![ConstParamDef {
            name: "N".to_string(),
            ty: RustType::Uint(UintType::Usize),
        }],
    });

    let expr = Expr::Struct {
        name: "Buffer".to_string(),
        fields: vec![(
            "data".to_string(),
            Expr::Array(vec![
                Expr::Literal(Value::u8(1)),
                Expr::Literal(Value::u8(2)),
                Expr::Literal(Value::u8(3)),
                Expr::Literal(Value::u8(4)),
            ]),
        )],
        type_args: vec![],
        const_args: vec![ConstGenericArg::usize(4)],
    };

    let result = interp.eval(&expr);
    assert_eq!(
        result.value(),
        Some(Value::Struct {
            name: "Buffer".to_string(),
            fields: {
                let mut fields = BTreeMap::new();
                fields.insert(
                    "data".to_string(),
                    Value::Array(vec![Value::u8(1), Value::u8(2), Value::u8(3), Value::u8(4)]),
                );
                fields
            },
        })
    );
}

#[test]
fn test_public_const_generic_helpers() {
    let expr = ConstGenericArg::Add(
        Box::new(ConstGenericArg::Param("N".to_string())),
        Box::new(ConstGenericArg::Value(ConstGenericValue::Usize(1))),
    );
    let subst = HashMap::from([("N".to_string(), ConstGenericValue::Usize(4))]);
    assert_eq!(
        ConstGenericEval::eval(&expr, &subst),
        ConstGenericValue::Usize(5)
    );

    let mut unifier = ConstGenericUnifier::new();
    assert!(unifier.unify(&expr, &ConstGenericArg::Value(ConstGenericValue::Usize(5))));
    assert!(validate_const_generic_bounds(
        &[ConstGenericBound::Eq(
            expr,
            ConstGenericArg::Value(ConstGenericValue::Usize(5)),
        )],
        unifier.bindings(),
    )
    .is_ok());
}
