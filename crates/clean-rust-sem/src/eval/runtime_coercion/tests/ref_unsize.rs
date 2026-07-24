// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;

// --- Unsized coercion: &T → &dyn Trait ---

#[test]
fn test_ref_concrete_to_ref_dyn_trait() {
    let mut interp = Interpreter::new();
    register_animal_dispatch(&mut interp, 66);

    let target = RustType::Reference {
        lifetime: Lifetime::Named("a".to_string()),
        mutability: Mutability::Shared,
        inner: Box::new(animal_trait_type()),
    };

    let dog_ref = Value::Reference {
        addr: Address::new(AllocId(100), 0),
        mutability: Mutability::Shared,
        lifetime: Lifetime::Named("a".to_string()),
        referent: Some(Box::new(Value::Struct {
            name: "Dog".to_string(),
            fields: Default::default(),
        })),
    };

    let coerced = interp.coerce_runtime_value(&dog_ref, &target);
    match &coerced {
        Some(Value::FatPtr(FatPointer {
            data_pointer,
            metadata: FatPtrMetadata::VtablePtr(vtable_ptr),
        })) => {
            assert_eq!(vtable_ptr.trait_name, "Animal");
            match data_pointer.as_ref() {
                Value::Reference {
                    mutability: Mutability::Shared,
                    referent: Some(inner),
                    ..
                } => {
                    assert_eq!(inner.concrete_type_name(), Some("Dog"));
                }
                other => {
                    panic!("expected fat-pointer data to be a shared reference, got {other:?}")
                }
            }
        }
        other => panic!("expected fat pointer for &Dog -> &dyn Animal, got {other:?}"),
    }
}

#[test]
fn test_mut_ref_to_shared_ref_dyn_trait() {
    let mut interp = Interpreter::new();
    register_animal_dispatch(&mut interp, 22);

    let target = RustType::Reference {
        lifetime: Lifetime::Named("a".to_string()),
        mutability: Mutability::Shared,
        inner: Box::new(animal_trait_type()),
    };

    let dog_mut_ref = Value::Reference {
        addr: Address::new(AllocId(200), 0),
        mutability: Mutability::Mutable,
        lifetime: Lifetime::Named("a".to_string()),
        referent: Some(Box::new(Value::Struct {
            name: "Dog".to_string(),
            fields: Default::default(),
        })),
    };

    let coerced = interp.coerce_runtime_value(&dog_mut_ref, &target);
    match &coerced {
        Some(Value::FatPtr(FatPointer {
            data_pointer,
            metadata: FatPtrMetadata::VtablePtr(vtable_ptr),
        })) => {
            assert_eq!(vtable_ptr.trait_name, "Animal");
            match data_pointer.as_ref() {
                Value::Reference {
                    mutability: Mutability::Shared,
                    referent: Some(inner),
                    ..
                } => {
                    assert_eq!(inner.concrete_type_name(), Some("Dog"));
                }
                other => {
                    panic!("expected fat-pointer data to be a shared reference, got {other:?}")
                }
            }
        }
        other => panic!("expected fat pointer for &mut Dog -> &dyn Animal, got {other:?}"),
    }
}

#[test]
fn test_shared_ref_to_mut_ref_dyn_trait_rejected() {
    let mut interp = Interpreter::new();
    register_animal_dispatch(&mut interp, 1);

    let target = RustType::Reference {
        lifetime: Lifetime::Named("a".to_string()),
        mutability: Mutability::Mutable,
        inner: Box::new(animal_trait_type()),
    };

    let dog_shared_ref = Value::Reference {
        addr: Address::new(AllocId(300), 0),
        mutability: Mutability::Shared,
        lifetime: Lifetime::Named("a".to_string()),
        referent: Some(Box::new(Value::Struct {
            name: "Dog".to_string(),
            fields: Default::default(),
        })),
    };

    assert_eq!(
        interp.coerce_runtime_value(&dog_shared_ref, &target),
        None,
        "&Dog should not coerce to &mut dyn Animal"
    );
}

#[test]
fn test_ref_dyn_trait_rejects_no_referent() {
    let mut interp = Interpreter::new();
    register_animal_dispatch(&mut interp, 1);

    let target = RustType::Reference {
        lifetime: Lifetime::Named("a".to_string()),
        mutability: Mutability::Shared,
        inner: Box::new(animal_trait_type()),
    };

    let opaque_ref = Value::Reference {
        addr: Address::new(AllocId(400), 0),
        mutability: Mutability::Shared,
        lifetime: Lifetime::Named("a".to_string()),
        referent: None,
    };

    assert_eq!(
        interp.coerce_runtime_value(&opaque_ref, &target),
        None,
        "reference without referent should not coerce to &dyn Trait"
    );
}

#[test]
fn test_ref_dyn_trait_uses_memory_type_metadata_when_referent_is_opaque() {
    let mut interp = Interpreter::new();
    register_animal_dispatch(&mut interp, 1);

    let addr = interp.ctx.memory.allocate(8).expect("allocate opaque dog");
    interp
        .ctx
        .memory
        .set_allocation_type(addr, dog_type())
        .expect("record dog type");

    let target = RustType::Reference {
        lifetime: Lifetime::Named("a".to_string()),
        mutability: Mutability::Shared,
        inner: Box::new(animal_trait_type()),
    };
    let opaque_ref = Value::Reference {
        addr,
        mutability: Mutability::Shared,
        lifetime: Lifetime::Named("a".to_string()),
        referent: None,
    };

    let coerced = interp
        .coerce_runtime_value(&opaque_ref, &target)
        .expect("opaque dog reference should still coerce via memory type metadata");

    match coerced {
        Value::FatPtr(FatPointer {
            metadata: FatPtrMetadata::VtablePtr(vtable_ptr),
            ..
        }) => assert_eq!(vtable_ptr.trait_name, "Animal"),
        other => panic!("expected trait-object fat pointer, got {other:?}"),
    }
}

#[test]
fn test_array_ref_to_slice_uses_memory_slice_len_when_referent_is_opaque() {
    let mut interp = Interpreter::new();
    let array_ty = RustType::Array {
        element: Box::new(RustType::Uint(UintType::U32)),
        len: crate::types::ConstGenericArg::usize(3),
    };
    let addr = interp
        .ctx
        .memory
        .allocate_typed(&array_ty)
        .expect("allocate typed array");

    let target = RustType::Reference {
        lifetime: Lifetime::Named("a".to_string()),
        mutability: Mutability::Shared,
        inner: Box::new(RustType::Slice {
            elem: Box::new(RustType::Uint(UintType::U32)),
        }),
    };
    let opaque_ref = Value::Reference {
        addr,
        mutability: Mutability::Shared,
        lifetime: Lifetime::Named("a".to_string()),
        referent: None,
    };

    let coerced = interp
        .coerce_runtime_value(&opaque_ref, &target)
        .expect("opaque array reference should still coerce via slice metadata");

    match coerced {
        Value::FatPtr(FatPointer {
            data_pointer,
            metadata: FatPtrMetadata::SliceLen(len),
        }) => {
            assert_eq!(len, 3);
            assert!(matches!(data_pointer.as_ref(), Value::Reference { .. }));
        }
        other => panic!("expected slice fat pointer, got {other:?}"),
    }
}
