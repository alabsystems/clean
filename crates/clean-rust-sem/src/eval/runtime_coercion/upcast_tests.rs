// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::expr::Expr;
use crate::memory::{Address, AllocId};
use crate::stmt::{FunctionDef, TraitDef};
use crate::types::{FunctionSignature, Lifetime, Mutability, ReceiverMode, RustType, UintType};
use crate::values::{FatPointer, FatPtrMetadata};

fn dog_type() -> RustType {
    RustType::Named {
        name: "Dog".to_string(),
        type_args: vec![],
        lifetime_args: vec![],
        const_args: vec![],
    }
}

fn animal_trait_type() -> RustType {
    RustType::DynTrait {
        trait_name: "Animal".to_string(),
        auto_traits: vec![],
    }
}

fn guide_dog_trait_type() -> RustType {
    RustType::DynTrait {
        trait_name: "GuideDog".to_string(),
        auto_traits: vec![],
    }
}

fn vehicle_trait_type() -> RustType {
    RustType::DynTrait {
        trait_name: "Vehicle".to_string(),
        auto_traits: vec![],
    }
}

fn trait_method(name: &str) -> FunctionSignature {
    FunctionSignature {
        name: name.to_string(),
        receiver: ReceiverMode::ByValue,
        params: vec![],
        ret: RustType::Uint(UintType::U32),
        is_async: false,
        type_params: vec![],
    }
}

fn register_trait(interp: &mut Interpreter, name: &str, supertraits: &[&str], method: &str) {
    let mut trait_def = TraitDef::new(name.to_string(), vec![trait_method(method)]);
    trait_def.supertraits = supertraits.iter().map(|name| (*name).to_string()).collect();
    interp.ctx.register_full_trait_def(trait_def);
}

fn register_dog_impl(interp: &mut Interpreter, trait_name: &str, method: &str, impl_fn: &str) {
    interp
        .ctx
        .register_trait_impl(trait_name.to_string(), dog_type());
    interp
        .ctx
        .add_impl_method(trait_name, "Dog", method.to_string(), impl_fn.to_string());
}

fn register_dog_method(interp: &mut Interpreter, name: &str, ret_value: u32) {
    interp.ctx.register_function(FunctionDef {
        name: name.to_string(),
        params: vec![("self".to_string(), dog_type())],
        ret_ty: RustType::Uint(UintType::U32),
        body: Expr::Literal(Value::u32(ret_value)),
        is_unsafe: false,
        is_async: false,
        type_params: vec![],
    });
}

fn register_dog_trait_hierarchy(interp: &mut Interpreter) {
    register_trait(interp, "Animal", &[], "speak");
    register_trait(interp, "Pet", &["Animal"], "play");
    register_trait(interp, "GuideDog", &["Pet"], "guide");
    register_trait(interp, "Vehicle", &[], "drive");

    register_dog_impl(interp, "Animal", "speak", "Dog_speak");
    register_dog_impl(interp, "Pet", "play", "Dog_play");
    register_dog_impl(interp, "GuideDog", "guide", "Dog_guide");

    register_dog_method(interp, "Dog_speak", 11);
    register_dog_method(interp, "Dog_play", 22);
    register_dog_method(interp, "Dog_guide", 33);
}

fn dog_value() -> Value {
    Value::Struct {
        name: "Dog".to_string(),
        fields: Default::default(),
    }
}

#[test]
fn test_trait_object_upcast_transitive_to_supertrait() {
    let mut interp = Interpreter::new();
    register_dog_trait_hierarchy(&mut interp);

    let guide_object = interp
        .coerce_runtime_value(&dog_value(), &guide_dog_trait_type())
        .expect("Dog should coerce to dyn GuideDog");
    let animal_object = interp
        .coerce_runtime_value(&guide_object, &animal_trait_type())
        .expect("dyn GuideDog should upcast to dyn Animal");

    match &animal_object {
        Value::TraitObject {
            data,
            vtable,
            lifetime,
        } => {
            assert_eq!(vtable.trait_name, "Animal");
            assert_eq!(vtable.concrete_type, "Dog");
            assert!(vtable.get_impl("speak").is_some());
            assert!(vtable.get_impl("guide").is_none());
            assert_eq!(data.concrete_type_name(), Some("Dog"));
            assert_eq!(*lifetime, Lifetime::Static);
        }
        other => panic!("expected trait object after upcast, got {other:?}"),
    }

    let result = interp.eval(&Expr::MethodCall {
        receiver: Box::new(Expr::Literal(animal_object)),
        method: "speak".to_string(),
        args: vec![],
        type_args: vec![],
    });
    assert_eq!(result.value(), Some(Value::u32(11)));
}

#[test]
fn test_trait_object_upcast_rejects_unrelated_trait() {
    let mut interp = Interpreter::new();
    register_dog_trait_hierarchy(&mut interp);

    let guide_object = interp
        .coerce_runtime_value(&dog_value(), &guide_dog_trait_type())
        .expect("Dog should coerce to dyn GuideDog");

    assert_eq!(
        interp.coerce_runtime_value(&guide_object, &vehicle_trait_type()),
        None,
        "dyn GuideDog should not upcast to unrelated dyn Vehicle"
    );
}

#[test]
fn test_ref_trait_object_upcast_to_supertrait() {
    let mut interp = Interpreter::new();
    register_dog_trait_hierarchy(&mut interp);

    let guide_object = interp
        .coerce_runtime_value(&dog_value(), &guide_dog_trait_type())
        .expect("Dog should coerce to dyn GuideDog");
    let guide_ref = Value::Reference {
        addr: Address::new(AllocId(777), 0),
        mutability: Mutability::Shared,
        lifetime: Lifetime::Named("a".to_string()),
        referent: Some(Box::new(guide_object)),
    };
    let target = RustType::Reference {
        lifetime: Lifetime::Named("a".to_string()),
        mutability: Mutability::Shared,
        inner: Box::new(animal_trait_type()),
    };

    let coerced = interp
        .coerce_runtime_value(&guide_ref, &target)
        .expect("&dyn GuideDog should upcast to &dyn Animal");

    match coerced {
        Value::FatPtr(FatPointer {
            data_pointer,
            metadata: FatPtrMetadata::VtablePtr(vtable_ptr),
        }) => {
            assert_eq!(vtable_ptr.trait_name, "Animal");
            match data_pointer.as_ref() {
                Value::Reference {
                    mutability: Mutability::Shared,
                    referent: Some(inner),
                    ..
                } => {
                    assert!(matches!(inner.as_ref(), Value::TraitObject { .. }));
                }
                other => {
                    panic!("expected fat-pointer data to be a shared reference, got {other:?}")
                }
            }
        }
        other => panic!("expected fat pointer after upcast, got {other:?}"),
    }
}
