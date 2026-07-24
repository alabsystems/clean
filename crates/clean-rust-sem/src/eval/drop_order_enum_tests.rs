// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Enum drop-order regressions for #3062.

use std::collections::BTreeMap;

use super::tests_support::{make_let, make_mut_ref_named_type, make_named_type};
use super::Interpreter;
use crate::expr::{EnumVariantPayload, Expr, Stmt};
use crate::stmt::{EnumVariantDef, EnumVariantType, FunctionDef};
use crate::types::{RustType, TypeParamDef};
use crate::values::{EnumPayload, Value};

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

fn empty_struct(name: &str) -> Value {
    Value::Struct {
        name: name.to_string(),
        fields: BTreeMap::new(),
    }
}

fn register_outer_enum(interp: &mut Interpreter, variants: Vec<EnumVariantDef>) {
    interp.ctx.register_type(crate::stmt::TypeDef::Enum {
        name: "Outer".to_string(),
        variants,
        type_params: vec![],
        const_params: vec![],
    });
}

fn make_generic_outer_type(inner: RustType) -> RustType {
    RustType::Named {
        name: "Outer".to_string(),
        type_args: vec![inner],
        lifetime_args: vec![],
        const_args: vec![],
    }
}

fn make_type_param(id: u32, name: &str) -> RustType {
    RustType::TypeParam(crate::types::TypeVar {
        id,
        name: Some(name.to_string()),
    })
}

fn register_generic_outer_enum(interp: &mut Interpreter, variants: Vec<EnumVariantDef>) {
    interp.ctx.register_type(crate::stmt::TypeDef::Enum {
        name: "Outer".to_string(),
        variants,
        type_params: vec![TypeParamDef {
            id: 0,
            name: "T".to_string(),
            bounds: vec![],
        }],
        const_params: vec![],
    });
}

#[test]
fn test_call_drop_enum_tuple_variant_drops_payload() {
    let mut interp = Interpreter::new();
    register_outer_enum(
        &mut interp,
        vec![
            EnumVariantDef {
                name: "Live".to_string(),
                payload: EnumVariantType::Tuple(vec![make_named_type("Payload")]),
                discriminant: None,
            },
            EnumVariantDef {
                name: "Dead".to_string(),
                payload: EnumVariantType::Unit,
                discriminant: None,
            },
        ],
    );
    register_flag_drop(&mut interp, "Payload", "_payload_dropped");

    let program = Expr::Block {
        stmts: vec![
            make_let(
                "_payload_dropped",
                true,
                Some(RustType::Bool),
                Expr::Literal(Value::Bool(false)),
            ),
            Stmt::Expr(Expr::Block {
                stmts: vec![make_let(
                    "outer",
                    false,
                    Some(make_named_type("Outer")),
                    Expr::Literal(Value::Enum {
                        name: "Outer".to_string(),
                        variant: "Live".to_string(),
                        payload: Box::new(EnumPayload::Tuple(vec![empty_struct("Payload")])),
                    }),
                )],
                expr: Some(Box::new(Expr::Literal(Value::Unit))),
            }),
        ],
        expr: Some(Box::new(Expr::Var {
            name: "_payload_dropped".to_string(),
            local_idx: 0,
        })),
    };

    let result = interp.eval(&program);
    assert_eq!(
        result.value(),
        Some(Value::Bool(true)),
        "enum tuple variant payload must be dropped when enum leaves scope"
    );
}

#[test]
fn test_call_drop_enum_struct_variant_drops_payload() {
    let mut interp = Interpreter::new();
    register_outer_enum(
        &mut interp,
        vec![EnumVariantDef {
            name: "Named".to_string(),
            payload: EnumVariantType::Struct(vec![(
                "inner".to_string(),
                make_named_type("Payload"),
            )]),
            discriminant: None,
        }],
    );
    register_flag_drop(&mut interp, "Payload", "_payload_dropped");

    let program = Expr::Block {
        stmts: vec![
            make_let(
                "_payload_dropped",
                true,
                Some(RustType::Bool),
                Expr::Literal(Value::Bool(false)),
            ),
            Stmt::Expr(Expr::Block {
                stmts: vec![make_let(
                    "outer",
                    false,
                    Some(make_named_type("Outer")),
                    Expr::Literal(Value::Enum {
                        name: "Outer".to_string(),
                        variant: "Named".to_string(),
                        payload: Box::new(EnumPayload::Struct(BTreeMap::from([(
                            "inner".to_string(),
                            empty_struct("Payload"),
                        )]))),
                    }),
                )],
                expr: Some(Box::new(Expr::Literal(Value::Unit))),
            }),
        ],
        expr: Some(Box::new(Expr::Var {
            name: "_payload_dropped".to_string(),
            local_idx: 0,
        })),
    };

    let result = interp.eval(&program);
    assert_eq!(
        result.value(),
        Some(Value::Bool(true)),
        "enum struct variant payload must be dropped when enum leaves scope"
    );
}

#[test]
fn test_call_drop_enum_tuple_variant_fields_follow_order() {
    let mut interp = Interpreter::new();
    register_outer_enum(
        &mut interp,
        vec![EnumVariantDef {
            name: "Live".to_string(),
            payload: EnumVariantType::Tuple(vec![
                make_named_type("First"),
                make_named_type("Second"),
            ]),
            discriminant: None,
        }],
    );
    register_flag_drop(&mut interp, "Second", "_second_dropped");
    register_observer_drop(&mut interp, "First", "_second_dropped", "_first_saw_second");

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
                    "outer",
                    false,
                    Some(make_named_type("Outer")),
                    Expr::Literal(Value::Enum {
                        name: "Outer".to_string(),
                        variant: "Live".to_string(),
                        payload: Box::new(EnumPayload::Tuple(vec![
                            empty_struct("First"),
                            empty_struct("Second"),
                        ])),
                    }),
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
        "tuple enum payload field 0 must drop before field 1"
    );
}

#[test]
fn test_call_drop_enum_struct_variant_fields_follow_declaration_order() {
    let mut interp = Interpreter::new();
    register_outer_enum(
        &mut interp,
        vec![EnumVariantDef {
            name: "Live".to_string(),
            payload: EnumVariantType::Struct(vec![
                ("z_first".to_string(), make_named_type("ZFirst")),
                ("a_second".to_string(), make_named_type("ASecond")),
            ]),
            discriminant: None,
        }],
    );
    register_flag_drop(&mut interp, "ASecond", "_a_dropped");
    register_observer_drop(&mut interp, "ZFirst", "_a_dropped", "_z_saw_a");

    let mut payload_fields = BTreeMap::new();
    payload_fields.insert("a_second".to_string(), empty_struct("ASecond"));
    payload_fields.insert("z_first".to_string(), empty_struct("ZFirst"));

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
                    Expr::Literal(Value::Enum {
                        name: "Outer".to_string(),
                        variant: "Live".to_string(),
                        payload: Box::new(EnumPayload::Struct(payload_fields)),
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
        "struct enum payload fields must drop in variant declaration order, not payload map order"
    );
}

#[test]
fn test_call_drop_enum_unit_variant_no_panic() {
    let mut interp = Interpreter::new();
    register_outer_enum(
        &mut interp,
        vec![EnumVariantDef {
            name: "Empty".to_string(),
            payload: EnumVariantType::Unit,
            discriminant: None,
        }],
    );

    let program = Expr::Block {
        stmts: vec![Stmt::Expr(Expr::Block {
            stmts: vec![make_let(
                "outer",
                false,
                Some(make_named_type("Outer")),
                Expr::Literal(Value::Enum {
                    name: "Outer".to_string(),
                    variant: "Empty".to_string(),
                    payload: Box::new(EnumPayload::Unit),
                }),
            )],
            expr: Some(Box::new(Expr::Literal(Value::Unit))),
        })],
        expr: Some(Box::new(Expr::Literal(Value::Bool(true)))),
    };

    let result = interp.eval(&program);
    assert_eq!(
        result.value(),
        Some(Value::Bool(true)),
        "unit variant drop must not panic"
    );
}

#[test]
fn test_call_drop_generic_enum_tuple_variant_drops_payload() {
    let mut interp = Interpreter::new();
    register_generic_outer_enum(
        &mut interp,
        vec![
            EnumVariantDef {
                name: "Live".to_string(),
                payload: EnumVariantType::Tuple(vec![make_type_param(0, "T")]),
                discriminant: None,
            },
            EnumVariantDef {
                name: "Dead".to_string(),
                payload: EnumVariantType::Unit,
                discriminant: None,
            },
        ],
    );
    register_flag_drop(&mut interp, "Payload", "_payload_dropped");

    let payload_ty = make_named_type("Payload");
    let program = Expr::Block {
        stmts: vec![
            make_let(
                "_payload_dropped",
                true,
                Some(RustType::Bool),
                Expr::Literal(Value::Bool(false)),
            ),
            Stmt::Expr(Expr::Block {
                stmts: vec![make_let(
                    "outer",
                    false,
                    Some(make_generic_outer_type(payload_ty.clone())),
                    Expr::EnumVariant {
                        enum_name: "Outer".to_string(),
                        variant: "Live".to_string(),
                        payload: EnumVariantPayload::Tuple(vec![Expr::Literal(empty_struct(
                            "Payload",
                        ))]),
                        type_args: vec![payload_ty],
                        const_args: vec![],
                    },
                )],
                expr: Some(Box::new(Expr::Literal(Value::Unit))),
            }),
        ],
        expr: Some(Box::new(Expr::Var {
            name: "_payload_dropped".to_string(),
            local_idx: 0,
        })),
    };

    let result = interp.eval(&program);
    assert_eq!(
        result.value(),
        Some(Value::Bool(true)),
        "generic enum tuple payload must use the runtime child type so Drop runs"
    );
}

#[test]
fn test_call_drop_generic_enum_struct_variant_drops_payload() {
    let mut interp = Interpreter::new();
    register_generic_outer_enum(
        &mut interp,
        vec![EnumVariantDef {
            name: "Live".to_string(),
            payload: EnumVariantType::Struct(vec![("inner".to_string(), make_type_param(0, "T"))]),
            discriminant: None,
        }],
    );
    register_flag_drop(&mut interp, "Payload", "_payload_dropped");

    let payload_ty = make_named_type("Payload");
    let program = Expr::Block {
        stmts: vec![
            make_let(
                "_payload_dropped",
                true,
                Some(RustType::Bool),
                Expr::Literal(Value::Bool(false)),
            ),
            Stmt::Expr(Expr::Block {
                stmts: vec![make_let(
                    "outer",
                    false,
                    Some(make_generic_outer_type(payload_ty.clone())),
                    Expr::EnumVariant {
                        enum_name: "Outer".to_string(),
                        variant: "Live".to_string(),
                        payload: EnumVariantPayload::Struct(vec![(
                            "inner".to_string(),
                            Expr::Literal(empty_struct("Payload")),
                        )]),
                        type_args: vec![payload_ty],
                        const_args: vec![],
                    },
                )],
                expr: Some(Box::new(Expr::Literal(Value::Unit))),
            }),
        ],
        expr: Some(Box::new(Expr::Var {
            name: "_payload_dropped".to_string(),
            local_idx: 0,
        })),
    };

    let result = interp.eval(&program);
    assert_eq!(
        result.value(),
        Some(Value::Bool(true)),
        "generic enum struct payload must use the runtime child type so Drop runs"
    );
}
