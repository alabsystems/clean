// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn test_coerce_runtime_value_matches_function_item_signature() {
    let mut interp = Interpreter::new();
    let target = RustType::Function {
        params: vec![RustType::Uint(UintType::U32)],
        ret: Box::new(RustType::Uint(UintType::U32)),
    };
    interp.ctx.register_function(FunctionDef {
        name: "inc".to_string(),
        params: vec![("x".to_string(), RustType::Uint(UintType::U32))],
        ret_ty: RustType::Uint(UintType::U32),
        body: Expr::Var {
            name: "x".to_string(),
            local_idx: 0,
        },
        is_unsafe: false,
        is_async: false,
        type_params: vec![],
    });

    assert_eq!(
        interp.coerce_runtime_value(
            &Value::FnPtr {
                name: "inc".to_string()
            },
            &target
        ),
        Some(Value::FnPtr {
            name: "inc".to_string()
        })
    );
}

#[test]
fn test_coerce_runtime_value_rejects_mismatched_function_item_signature() {
    let mut interp = Interpreter::new();
    interp.ctx.register_function(FunctionDef {
        name: "inc".to_string(),
        params: vec![("x".to_string(), RustType::Uint(UintType::U32))],
        ret_ty: RustType::Uint(UintType::U32),
        body: Expr::Var {
            name: "x".to_string(),
            local_idx: 0,
        },
        is_unsafe: false,
        is_async: false,
        type_params: vec![],
    });

    assert_eq!(
        interp.coerce_runtime_value(
            &Value::FnPtr {
                name: "inc".to_string()
            },
            &RustType::Function {
                params: vec![RustType::Uint(UintType::U64)],
                ret: Box::new(RustType::Uint(UintType::U32)),
            }
        ),
        None
    );
}

#[test]
fn test_let_annotation_coerces_concrete_value_to_dyn_trait() {
    let mut interp = Interpreter::new();
    register_animal_dispatch(&mut interp, 33);

    let expr = Expr::Block {
        stmts: vec![Stmt::Let {
            pattern: Pattern::Binding {
                name: "pet".to_string(),
                mutable: false,
                subpattern: None,
            },
            ty: Some(animal_trait_type()),
            init: Some(Box::new(Expr::Struct {
                name: "Dog".to_string(),
                fields: vec![],
                type_args: vec![],
                const_args: vec![],
            })),
            else_block: None,
        }],
        expr: Some(Box::new(Expr::MethodCall {
            receiver: Box::new(Expr::Var {
                name: "pet".to_string(),
                local_idx: 0,
            }),
            method: "speak".to_string(),
            args: vec![],
            type_args: vec![],
        })),
    };

    assert_eq!(interp.eval(&expr).value(), Some(Value::u32(33)));
}

#[test]
fn test_call_argument_coerces_concrete_value_to_dyn_trait() {
    let mut interp = Interpreter::new();
    register_animal_dispatch(&mut interp, 17);
    interp.ctx.register_function(FunctionDef {
        name: "hear".to_string(),
        params: vec![("animal".to_string(), animal_trait_type())],
        ret_ty: RustType::Uint(UintType::U32),
        body: Expr::MethodCall {
            receiver: Box::new(Expr::Var {
                name: "animal".to_string(),
                local_idx: 0,
            }),
            method: "speak".to_string(),
            args: vec![],
            type_args: vec![],
        },
        is_unsafe: false,
        is_async: false,
        type_params: vec![],
    });

    let expr = Expr::Call {
        func: Box::new(Expr::Var {
            name: "hear".to_string(),
            local_idx: 0,
        }),
        args: vec![Expr::Struct {
            name: "Dog".to_string(),
            fields: vec![],
            type_args: vec![],
            const_args: vec![],
        }],
        type_args: vec![],
    };

    assert_eq!(interp.eval(&expr).value(), Some(Value::u32(17)));
}

#[test]
fn test_bind_call_params_coerces_mut_ref_to_shared_ref() {
    let mut interp = Interpreter::new();
    interp.ctx.register_function(FunctionDef {
        name: "peek".to_string(),
        params: vec![("x".to_string(), shared_u32_ref_type())],
        ret_ty: RustType::Uint(UintType::U32),
        body: Expr::Deref(Box::new(Expr::Var {
            name: "x".to_string(),
            local_idx: 0,
        })),
        is_unsafe: false,
        is_async: false,
        type_params: vec![],
    });

    let arg = Value::Reference {
        addr: Address::new(AllocId(50), 0),
        mutability: Mutability::Mutable,
        lifetime: Lifetime::Named("a".to_string()),
        referent: Some(Box::new(Value::u32(9))),
    };

    let params = interp.ctx.get_function("peek").unwrap().params.clone();
    interp
        .bind_call_params(&params, vec![arg])
        .expect("binding call params should coerce &mut T to &T");
    match interp.lookup("x").expect("parameter should be bound") {
        Value::Reference { mutability, .. } => {
            assert_eq!(mutability, Mutability::Shared);
        }
        other => panic!("expected shared reference after coercion, got {other:?}"),
    }
}

#[test]
fn test_function_return_coerces_concrete_value_to_dyn_trait() {
    let mut interp = Interpreter::new();
    register_animal_dispatch(&mut interp, 12);
    interp.ctx.register_function(FunctionDef {
        name: "make_pet".to_string(),
        params: vec![],
        ret_ty: animal_trait_type(),
        body: Expr::Struct {
            name: "Dog".to_string(),
            fields: vec![],
            type_args: vec![],
            const_args: vec![],
        },
        is_unsafe: false,
        is_async: false,
        type_params: vec![],
    });

    let expr = Expr::MethodCall {
        receiver: Box::new(Expr::Call {
            func: Box::new(Expr::Var {
                name: "make_pet".to_string(),
                local_idx: 0,
            }),
            args: vec![],
            type_args: vec![],
        }),
        method: "speak".to_string(),
        args: vec![],
        type_args: vec![],
    };

    assert_eq!(interp.eval(&expr).value(), Some(Value::u32(12)));
}

#[test]
fn test_let_annotation_coerces_mut_ref_to_shared_ref() {
    let mut interp = Interpreter::new();
    let expr = Expr::Block {
        stmts: vec![Stmt::Let {
            pattern: Pattern::Binding {
                name: "r".to_string(),
                mutable: false,
                subpattern: None,
            },
            ty: Some(shared_u32_ref_type()),
            init: Some(Box::new(Expr::AddrOf {
                mutability: Mutability::Mutable,
                expr: Box::new(Expr::Literal(Value::u32(5))),
            })),
            else_block: None,
        }],
        expr: Some(Box::new(Expr::Var {
            name: "r".to_string(),
            local_idx: 0,
        })),
    };

    match interp.eval(&expr).value() {
        Some(Value::Reference { mutability, .. }) => {
            assert_eq!(mutability, Mutability::Shared);
        }
        other => panic!("expected shared reference, got {other:?}"),
    }
}

#[test]
fn test_struct_field_coerces_concrete_to_dyn_trait() {
    use crate::stmt::TypeDef;

    let mut interp = Interpreter::new();
    register_animal_dispatch(&mut interp, 27);
    interp.ctx.register_type(TypeDef::Struct {
        name: "Kennel".to_string(),
        fields: vec![("pet".to_string(), animal_trait_type())],
        type_params: vec![],
        const_params: vec![],
    });

    let expr = Expr::Block {
        stmts: vec![Stmt::Let {
            pattern: Pattern::Binding {
                name: "kennel".to_string(),
                mutable: false,
                subpattern: None,
            },
            ty: Some(RustType::Named {
                name: "Kennel".to_string(),
                type_args: vec![],
                lifetime_args: vec![],
                const_args: vec![],
            }),
            init: Some(Box::new(Expr::Struct {
                name: "Kennel".to_string(),
                fields: vec![(
                    "pet".to_string(),
                    Expr::Struct {
                        name: "Dog".to_string(),
                        fields: vec![],
                        type_args: vec![],
                        const_args: vec![],
                    },
                )],
                type_args: vec![],
                const_args: vec![],
            })),
            else_block: None,
        }],
        expr: Some(Box::new(Expr::Field {
            base: Box::new(Expr::Var {
                name: "kennel".to_string(),
                local_idx: 0,
            }),
            field: "pet".to_string(),
        })),
    };

    match interp.eval(&expr).value() {
        Some(Value::TraitObject { .. }) => {}
        other => panic!("expected trait object in struct field, got {other:?}"),
    }
}

#[test]
fn test_enum_tuple_variant_coerces_concrete_to_dyn_trait() {
    use crate::{
        expr::EnumVariantPayload,
        stmt::{EnumVariantDef, EnumVariantType, TypeDef},
    };

    let mut interp = Interpreter::new();
    register_animal_dispatch(&mut interp, 19);
    interp.ctx.register_type(TypeDef::Enum {
        name: "Holder".to_string(),
        variants: vec![EnumVariantDef {
            name: "Pet".to_string(),
            payload: EnumVariantType::Tuple(vec![animal_trait_type()]),
            discriminant: None,
        }],
        type_params: vec![],
        const_params: vec![],
    });

    let expr = Expr::EnumVariant {
        enum_name: "Holder".to_string(),
        variant: "Pet".to_string(),
        payload: EnumVariantPayload::Tuple(vec![Expr::Struct {
            name: "Dog".to_string(),
            fields: vec![],
            type_args: vec![],
            const_args: vec![],
        }]),
        type_args: vec![],
        const_args: vec![],
    };

    match interp.eval(&expr).value() {
        Some(Value::Enum { payload, .. }) => match payload.as_ref() {
            crate::values::EnumPayload::Tuple(vals) => {
                assert!(
                    matches!(&vals[0], Value::TraitObject { .. }),
                    "expected trait object in tuple variant, got {:?}",
                    vals.first()
                );
            }
            other => panic!("expected Tuple payload, got {other:?}"),
        },
        other => panic!("expected Enum value, got {other:?}"),
    }
}

#[test]
fn test_enum_struct_variant_coerces_concrete_to_dyn_trait() {
    use crate::{
        expr::EnumVariantPayload,
        stmt::{EnumVariantDef, EnumVariantType, TypeDef},
    };

    let mut interp = Interpreter::new();
    register_animal_dispatch(&mut interp, 21);
    interp.ctx.register_type(TypeDef::Enum {
        name: "Holder".to_string(),
        variants: vec![EnumVariantDef {
            name: "Pet".to_string(),
            payload: EnumVariantType::Struct(vec![("pet".to_string(), animal_trait_type())]),
            discriminant: None,
        }],
        type_params: vec![],
        const_params: vec![],
    });

    let expr = Expr::EnumVariant {
        enum_name: "Holder".to_string(),
        variant: "Pet".to_string(),
        payload: EnumVariantPayload::Struct(vec![(
            "pet".to_string(),
            Expr::Struct {
                name: "Dog".to_string(),
                fields: vec![],
                type_args: vec![],
                const_args: vec![],
            },
        )]),
        type_args: vec![],
        const_args: vec![],
    };

    let result = interp.eval(&expr);
    match result.value() {
        Some(Value::Enum { payload, .. }) => match payload.as_ref() {
            crate::values::EnumPayload::Struct(fields) => {
                assert!(
                    matches!(fields.get("pet"), Some(Value::TraitObject { .. })),
                    "expected trait object in struct variant field, got {:?}",
                    fields.get("pet")
                );
            }
            other => panic!("expected Struct payload, got {other:?}"),
        },
        other => panic!("expected Enum value, got {other:?}"),
    }
}
