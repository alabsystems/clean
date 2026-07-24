// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;

// --- Unsized coercion: Box<T> → Box<dyn Trait> ---

#[test]
fn test_box_concrete_to_box_dyn_trait() {
    let mut interp = Interpreter::new();
    register_animal_dispatch(&mut interp, 88);

    let target = RustType::Box {
        inner: Box::new(animal_trait_type()),
    };

    let dog_value = Value::Struct {
        name: "Dog".to_string(),
        fields: Default::default(),
    };

    let coerced = interp.coerce_runtime_value(&dog_value, &target);
    match &coerced {
        Some(Value::FatPtr(FatPointer {
            data_pointer,
            metadata: FatPtrMetadata::VtablePtr(vtable_ptr),
        })) => {
            assert_eq!(vtable_ptr.trait_name, "Animal");
            assert_eq!(data_pointer.concrete_type_name(), Some("Dog"));
        }
        other => panic!("expected fat pointer for Box<Dog> -> Box<dyn Animal>, got {other:?}"),
    }
}

#[test]
fn test_box_dyn_trait_let_annotation() {
    let mut interp = Interpreter::new();
    register_animal_dispatch(&mut interp, 44);

    let box_dyn_animal = RustType::Box {
        inner: Box::new(animal_trait_type()),
    };

    let expr = Expr::Block {
        stmts: vec![Stmt::Let {
            pattern: Pattern::Binding {
                name: "boxed".to_string(),
                mutable: false,
                subpattern: None,
            },
            ty: Some(box_dyn_animal),
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
                name: "boxed".to_string(),
                local_idx: 0,
            }),
            method: "speak".to_string(),
            args: vec![],
            type_args: vec![],
        })),
    };

    assert_eq!(interp.eval(&expr).value(), Some(Value::u32(44)));
}

#[test]
fn test_box_dyn_trait_rejects_non_impl() {
    let mut interp = Interpreter::new();
    register_animal_dispatch(&mut interp, 1);

    let cat_value = Value::Struct {
        name: "Cat".to_string(),
        fields: Default::default(),
    };

    let target = RustType::Box {
        inner: Box::new(animal_trait_type()),
    };

    assert_eq!(
        interp.coerce_runtime_value(&cat_value, &target),
        None,
        "Box<Cat> should not coerce to Box<dyn Animal> when Cat doesn't impl Animal"
    );
}
