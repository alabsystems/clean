// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use clean_rust_sem::eval::Interpreter;
use clean_rust_sem::expr::Expr;
use clean_rust_sem::stmt::FunctionDef;
use clean_rust_sem::types::{RustType, UintType};
use clean_rust_sem::values::Value;
use std::collections::BTreeMap;

#[test]
fn test_static_method_dispatch() {
    let mut interp = Interpreter::new();

    // Static dispatch should call the method name directly.
    let impl_fn = FunctionDef {
        name: "speak".to_string(),
        params: vec![(
            "self".to_string(),
            RustType::Named {
                name: "Dog".to_string(),
                type_args: vec![],
                lifetime_args: vec![],
                const_args: vec![],
            },
        )],
        ret_ty: RustType::Uint(UintType::U32),
        body: Expr::Literal(Value::u32(7)),
        is_unsafe: false,
        is_async: false,
        type_params: vec![],
    };
    interp.ctx.register_function(impl_fn);

    let dog_value = Value::Struct {
        name: "Dog".to_string(),
        fields: BTreeMap::new(),
    };

    let expr = Expr::MethodCall {
        receiver: Box::new(Expr::Literal(dog_value)),
        method: "speak".to_string(),
        args: vec![],
        type_args: vec![],
    };

    let result = interp.eval(&expr);
    assert_eq!(result.value(), Some(Value::u32(7)));
}
