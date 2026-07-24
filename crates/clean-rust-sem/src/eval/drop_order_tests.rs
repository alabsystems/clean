// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Drop-order regressions for #3050.
//!
//! Each test proves that children of a composite type are dropped in the order
//! specified by the Rust Reference:
//! - struct fields: declaration order
//! - tuple fields: left to right (0, 1, ...)
//! - array elements: first to last
//!
//! Reference: <https://doc.rust-lang.org/reference/destructors.html>

use std::collections::BTreeMap;

use super::tests_support::{make_let, make_mut_ref_named_type, make_named_type};
use super::Interpreter;
use crate::expr::{Expr, Stmt};
use crate::stmt::FunctionDef;
use crate::types::{ConstGenericArg, RustType};
use crate::values::Value;

/// Register a drop function that sets `flag_var` to `true` when called.
fn register_flag_drop(interp: &mut Interpreter, type_name: &str, flag_var: &str) {
    let drop_fn_name = format!("{type_name}_drop");
    interp.ctx.register_function(FunctionDef {
        name: drop_fn_name.clone(),
        params: vec![("_self".to_string(), make_mut_ref_named_type(type_name))],
        ret_ty: RustType::Unit,
        body: Expr::Assign {
            target: Box::new(Expr::Var {
                name: flag_var.to_string(),
                local_idx: 0,
            }),
            value: Box::new(Expr::Literal(Value::Bool(true))),
        },
        is_unsafe: false,
        is_async: false,
        type_params: vec![],
    });
    interp
        .ctx
        .register_drop_impl(type_name.to_string(), drop_fn_name);
}

/// Register a drop function that captures the current value of `observed_var`
/// into `target_var`.
fn register_observer_drop(
    interp: &mut Interpreter,
    type_name: &str,
    observed_var: &str,
    target_var: &str,
) {
    let drop_fn_name = format!("{type_name}_drop");
    interp.ctx.register_function(FunctionDef {
        name: drop_fn_name.clone(),
        params: vec![("_self".to_string(), make_mut_ref_named_type(type_name))],
        ret_ty: RustType::Unit,
        body: Expr::Assign {
            target: Box::new(Expr::Var {
                name: target_var.to_string(),
                local_idx: 0,
            }),
            value: Box::new(Expr::Var {
                name: observed_var.to_string(),
                local_idx: 0,
            }),
        },
        is_unsafe: false,
        is_async: false,
        type_params: vec![],
    });
    interp
        .ctx
        .register_drop_impl(type_name.to_string(), drop_fn_name);
}

fn register_array_elem_drop(interp: &mut Interpreter) {
    interp.ctx.register_function(FunctionDef {
        name: "Elem_drop".to_string(),
        params: vec![("_self".to_string(), make_mut_ref_named_type("Elem"))],
        ret_ty: RustType::Unit,
        body: Expr::If {
            condition: Box::new(Expr::Field {
                base: Box::new(Expr::Deref(Box::new(Expr::Var {
                    name: "_self".to_string(),
                    local_idx: 0,
                }))),
                field: "is_first".to_string(),
            }),
            then_branch: Box::new(Expr::Assign {
                target: Box::new(Expr::Var {
                    name: "_elem0_saw_elem1".to_string(),
                    local_idx: 0,
                }),
                value: Box::new(Expr::Var {
                    name: "_elem1_dropped".to_string(),
                    local_idx: 0,
                }),
            }),
            else_branch: Some(Box::new(Expr::Assign {
                target: Box::new(Expr::Var {
                    name: "_elem1_dropped".to_string(),
                    local_idx: 0,
                }),
                value: Box::new(Expr::Literal(Value::Bool(true))),
            })),
        },
        is_unsafe: false,
        is_async: false,
        type_params: vec![],
    });
    interp
        .ctx
        .register_drop_impl("Elem".to_string(), "Elem_drop".to_string());
}

fn make_array_elem(is_first: bool) -> Value {
    Value::Struct {
        name: "Elem".to_string(),
        fields: BTreeMap::from([("is_first".to_string(), Value::Bool(is_first))]),
    }
}

#[test]
fn test_call_drop_named_struct_fields_follow_declaration_order() {
    // Rust Reference: struct fields are dropped in declaration order.
    // Outer declares z_first before a_second, so z_first drops first.
    // ZFirst_drop reads _a_dropped (still false because ASecond hasn't
    // dropped yet), proving z_first dropped before a_second.
    let mut interp = Interpreter::new();

    interp.ctx.register_type(crate::stmt::TypeDef::Struct {
        name: "Outer".to_string(),
        fields: vec![
            ("z_first".to_string(), make_named_type("ZFirst")),
            ("a_second".to_string(), make_named_type("ASecond")),
        ],
        type_params: vec![],
        const_params: vec![],
    });

    register_flag_drop(&mut interp, "ASecond", "_a_dropped");
    register_observer_drop(&mut interp, "ZFirst", "_a_dropped", "_z_saw_a");

    // Field names chosen so BTreeMap key order (a_second < z_first) differs
    // from declaration order (z_first, a_second). This catches implementations
    // that accidentally iterate in BTreeMap order.
    let mut outer_fields = BTreeMap::new();
    outer_fields.insert(
        "a_second".to_string(),
        Value::Struct {
            name: "ASecond".to_string(),
            fields: BTreeMap::new(),
        },
    );
    outer_fields.insert(
        "z_first".to_string(),
        Value::Struct {
            name: "ZFirst".to_string(),
            fields: BTreeMap::new(),
        },
    );

    let program = Expr::Block {
        stmts: vec![
            make_let(
                "_a_dropped",
                true,
                Some(RustType::Bool),
                Expr::Literal(Value::Bool(false)),
            ),
            make_let(
                "_z_saw_a",
                true,
                Some(RustType::Bool),
                Expr::Literal(Value::Bool(false)),
            ),
            Stmt::Expr(Expr::Block {
                stmts: vec![make_let(
                    "outer",
                    false,
                    Some(make_named_type("Outer")),
                    Expr::Literal(Value::Struct {
                        name: "Outer".to_string(),
                        fields: outer_fields,
                    }),
                )],
                expr: Some(Box::new(Expr::Literal(Value::Unit))),
            }),
        ],
        expr: Some(Box::new(Expr::Var {
            name: "_z_saw_a".to_string(),
            local_idx: 0,
        })),
    };

    let result = interp.eval(&program);
    assert_eq!(
        result.value(),
        Some(Value::Bool(false)),
        "z_first must drop before a_second (declaration order), so _a_dropped is still false when ZFirst reads it"
    );
}

#[test]
fn test_call_drop_tuple_fields_follow_order() {
    // Rust Reference: tuple fields drop in order (0, 1, ...).
    // Tuple is (First, Second). First_drop reads _second_dropped (still false),
    // proving field 0 drops before field 1.
    let mut interp = Interpreter::new();

    register_flag_drop(&mut interp, "Second", "_second_dropped");
    register_observer_drop(&mut interp, "First", "_second_dropped", "_first_saw_second");

    let tuple_val = Value::Tuple(vec![
        Value::Struct {
            name: "First".to_string(),
            fields: BTreeMap::new(),
        },
        Value::Struct {
            name: "Second".to_string(),
            fields: BTreeMap::new(),
        },
    ]);

    let tuple_ty = RustType::Tuple(vec![make_named_type("First"), make_named_type("Second")]);

    let program = Expr::Block {
        stmts: vec![
            make_let(
                "_second_dropped",
                true,
                Some(RustType::Bool),
                Expr::Literal(Value::Bool(false)),
            ),
            make_let(
                "_first_saw_second",
                true,
                Some(RustType::Bool),
                Expr::Literal(Value::Bool(false)),
            ),
            Stmt::Expr(Expr::Block {
                stmts: vec![make_let(
                    "tup",
                    false,
                    Some(tuple_ty),
                    Expr::Literal(tuple_val),
                )],
                expr: Some(Box::new(Expr::Literal(Value::Unit))),
            }),
        ],
        expr: Some(Box::new(Expr::Var {
            name: "_first_saw_second".to_string(),
            local_idx: 0,
        })),
    };

    let result = interp.eval(&program);
    assert_eq!(
        result.value(),
        Some(Value::Bool(false)),
        "tuple field 0 (First) must drop before field 1 (Second), so _second_dropped is still false when First reads it"
    );
}

#[test]
fn test_call_drop_tuple_element_uses_index_place_for_receiver_projection() {
    let mut interp = Interpreter::new();
    register_flag_drop(&mut interp, "Inner", "_inner_dropped");

    let program = Expr::Block {
        stmts: vec![
            make_let(
                "_inner_dropped",
                true,
                Some(RustType::Bool),
                Expr::Literal(Value::Bool(false)),
            ),
            Stmt::Expr(Expr::Block {
                stmts: vec![make_let(
                    "inner_tuple",
                    false,
                    Some(RustType::Tuple(vec![make_named_type("Inner")])),
                    Expr::Tuple(vec![Expr::Literal(Value::Struct {
                        name: "Inner".to_string(),
                        fields: BTreeMap::new(),
                    })]),
                )],
                expr: Some(Box::new(Expr::Literal(Value::Unit))),
            }),
        ],
        expr: Some(Box::new(Expr::Var {
            name: "_inner_dropped".to_string(),
            local_idx: 0,
        })),
    };

    let result = interp.eval(&program);
    assert_eq!(
        result.value(),
        Some(Value::Bool(true)),
        "tuple-element drop should call Inner::drop with a live &mut self receiver via Place::Index"
    );
}

#[test]
fn test_call_drop_array_elements_follow_order() {
    // Rust Reference: array elements drop from first to last.
    // Array is [Elem { is_first: true }, Elem { is_first: false }].
    // The shared Elem::drop impl uses `is_first` to distinguish the elements:
    // the second element sets _elem1_dropped = true, while the first element
    // reads _elem1_dropped into _elem0_saw_elem1. If element 0 drops first,
    // _elem1_dropped is still false when observed.
    let mut interp = Interpreter::new();

    register_array_elem_drop(&mut interp);

    let array_val = Value::Array(vec![make_array_elem(true), make_array_elem(false)]);

    let array_ty = RustType::Array {
        element: Box::new(make_named_type("Elem")),
        len: ConstGenericArg::usize(2),
    };

    let program = Expr::Block {
        stmts: vec![
            make_let(
                "_elem1_dropped",
                true,
                Some(RustType::Bool),
                Expr::Literal(Value::Bool(false)),
            ),
            make_let(
                "_elem0_saw_elem1",
                true,
                Some(RustType::Bool),
                Expr::Literal(Value::Bool(false)),
            ),
            Stmt::Expr(Expr::Block {
                stmts: vec![make_let(
                    "arr",
                    false,
                    Some(array_ty),
                    Expr::Literal(array_val),
                )],
                expr: Some(Box::new(Expr::Literal(Value::Unit))),
            }),
        ],
        expr: Some(Box::new(Expr::Var {
            name: "_elem0_saw_elem1".to_string(),
            local_idx: 0,
        })),
    };

    let result = interp.eval(&program);
    assert_eq!(
        result.value(),
        Some(Value::Bool(false)),
        "array element 0 must drop before element 1, so _elem1_dropped is still false when the first Elem reads it"
    );
}
