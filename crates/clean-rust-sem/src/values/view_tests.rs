// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn test_value_constructors() {
    assert_eq!(
        Value::u32(42),
        Value::Uint {
            value: 42,
            ty: UintType::U32,
        }
    );

    assert_eq!(
        Value::i64(-1),
        Value::Int {
            value: -1,
            ty: IntType::I64,
        }
    );
}

#[test]
fn test_view_scalar_and_flatten() {
    let value = Value::i32(-5);
    let view = value.view();

    assert_eq!(view, ValueView::Scalar(Value::i32(-5)));
    assert_eq!(view.flatten(), vec![Value::i32(-5)]);
}

#[test]
fn test_view_nested_struct_reference_and_collection() {
    use crate::memory::{Address, AllocId};

    let mut fields = BTreeMap::new();
    fields.insert(
        "items".to_string(),
        Value::Array(vec![Value::u32(1), Value::u32(2)]),
    );
    fields.insert(
        "payload".to_string(),
        Value::Reference {
            addr: Address::new(AllocId(7), 0),
            mutability: Mutability::Shared,
            lifetime: Lifetime::Static,
            referent: Some(Box::new(Value::Tuple(vec![
                Value::Bool(true),
                Value::i32(-3),
            ]))),
        },
    );

    let value = Value::Struct {
        name: "Wrapper".to_string(),
        fields,
    };
    let view = value.view();

    assert_eq!(
        view.flatten(),
        vec![
            Value::u32(1),
            Value::u32(2),
            Value::Bool(true),
            Value::i32(-3)
        ]
    );

    match view {
        ValueView::Aggregate(fields) => {
            assert!(matches!(fields[0], (ref name, ValueView::Collection(_)) if name == "items"));
            assert!(matches!(fields[1], (ref name, ValueView::Reference(_)) if name == "payload"));
        }
        other => panic!("expected aggregate view, got {other:?}"),
    }
}

#[test]
fn test_view_variant_and_opaque_flatten() {
    use crate::memory::{Address, AllocId};

    let some_val = Value::Enum {
        name: "Option".to_string(),
        variant: "Some".to_string(),
        payload: Box::new(EnumPayload::Tuple(vec![Value::u32(42)])),
    };
    let opaque_ptr = Value::RawPtr {
        addr: Address::new(AllocId(9), 4),
        mutability: Mutability::Shared,
        tag: None,
    };

    assert_eq!(some_val.view().flatten(), vec![Value::u32(42)]);
    assert!(opaque_ptr.view().flatten().is_empty());
}

#[test]
fn test_struct_value() {
    let mut fields = BTreeMap::new();
    fields.insert("x".to_string(), Value::f64(1.0));
    fields.insert("y".to_string(), Value::f64(2.0));

    let point = Value::Struct {
        name: "Point".to_string(),
        fields,
    };

    match point.get_type() {
        RustType::Named { name, .. } => assert_eq!(name, "Point"),
        _ => panic!("expected named type"),
    }
}

#[test]
fn test_enum_value() {
    let some_val = Value::Enum {
        name: "Option".to_string(),
        variant: "Some".to_string(),
        payload: Box::new(EnumPayload::Tuple(vec![Value::u32(42)])),
    };

    let none_val = Value::Enum {
        name: "Option".to_string(),
        variant: "None".to_string(),
        payload: Box::new(EnumPayload::Unit),
    };

    assert!(matches!(some_val.get_type(), RustType::Named { .. }));
    assert!(matches!(none_val.get_type(), RustType::Named { .. }));
}

#[test]
fn test_fat_ptr_slice_len_and_boxed_slice_type() {
    let fat_ptr = Value::FatPtr(FatPointer::slice(
        Value::Array(vec![Value::u32(1), Value::u32(2), Value::u32(3)]),
        3,
    ));

    assert_eq!(fat_ptr.slice_len(), Some(3));
    assert_eq!(
        fat_ptr.get_type(),
        RustType::Box {
            inner: Box::new(RustType::Slice {
                elem: Box::new(RustType::Uint(UintType::U32)),
            }),
        }
    );
}

#[test]
fn test_fat_ptr_ref_to_dyn_trait_type_uses_vtable_metadata() {
    use crate::memory::{Address, AllocId};

    let fat_ptr = Value::FatPtr(FatPointer::vtable(
        Value::Reference {
            addr: Address::new(AllocId(17), 0),
            mutability: Mutability::Shared,
            lifetime: Lifetime::Named("a".to_string()),
            referent: Some(Box::new(Value::Struct {
                name: "Dog".to_string(),
                fields: Default::default(),
            })),
        },
        "Animal",
    ));

    assert_eq!(
        fat_ptr.get_type(),
        RustType::Reference {
            lifetime: Lifetime::Named("a".to_string()),
            mutability: Mutability::Shared,
            inner: Box::new(RustType::DynTrait {
                trait_name: "Animal".to_string(),
                auto_traits: vec![],
            }),
        }
    );
}

#[test]
fn test_fat_ptr_owned_dyn_trait_type_maps_to_box() {
    let fat_ptr = Value::FatPtr(FatPointer::vtable(
        Value::Struct {
            name: "Dog".to_string(),
            fields: Default::default(),
        },
        "Animal",
    ));

    assert_eq!(
        fat_ptr.get_type(),
        RustType::Box {
            inner: Box::new(RustType::DynTrait {
                trait_name: "Animal".to_string(),
                auto_traits: vec![],
            }),
        }
    );
}
