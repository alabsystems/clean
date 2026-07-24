// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::memory::{Address, AllocId};
use crate::types::{Lifetime, Mutability};

#[test]
fn test_view_struct_and_borrowed_reference_shape() {
    let referent = Value::Tuple(vec![Value::Bool(true), Value::i32(-3)]);
    let value = Value::Struct {
        name: "Wrapper".to_string(),
        fields: BTreeMap::from([
            (
                "items".to_string(),
                Value::Array(vec![Value::u32(1), Value::u32(2)]),
            ),
            (
                "payload".to_string(),
                Value::Reference {
                    addr: Address::new(AllocId(7), 0),
                    mutability: Mutability::Shared,
                    lifetime: Lifetime::Static,
                    referent: Some(Box::new(referent.clone())),
                },
            ),
        ]),
    };

    match view(&value) {
        ValueView::Struct { name, fields } => {
            assert_eq!(name, "Wrapper");
            assert!(
                matches!(view(fields.get("items").expect("missing items field")), ValueView::Array(values) if values.len() == 2)
            );
            assert!(
                matches!(view(fields.get("payload").expect("missing payload field")), ValueView::Reference { referent: Some(inner), .. } if inner == &referent)
            );
        }
        other => panic!("expected struct view, got {other:?}"),
    }
}

#[test]
fn test_matches_struct_with_nested_reference_and_enum_payload() {
    let value = Value::Struct {
        name: "State".to_string(),
        fields: BTreeMap::from([(
            "slot".to_string(),
            Value::Reference {
                addr: Address::new(AllocId(11), 4),
                mutability: Mutability::Shared,
                lifetime: Lifetime::Static,
                referent: Some(Box::new(Value::Enum {
                    name: "Option".to_string(),
                    variant: "Some".to_string(),
                    payload: Box::new(EnumPayload::Tuple(vec![Value::i64(-5)])),
                })),
            },
        )]),
    };

    let pattern = ValuePattern::IsStruct {
        name: "State".to_string(),
        fields: vec![(
            "slot".to_string(),
            ValuePattern::IsRef {
                mutability: Some(Mutability::Shared),
                inner: Some(Box::new(ValuePattern::IsEnum {
                    name: "Option".to_string(),
                    variant: "Some".to_string(),
                    payload: Some(EnumPayloadPattern::Tuple(vec![ValuePattern::IsInt(-5)])),
                })),
            },
        )],
    };

    assert!(matches(&value, &pattern));
    assert!(!matches(
        &value,
        &ValuePattern::IsStruct {
            name: "State".to_string(),
            fields: vec![(
                "slot".to_string(),
                ValuePattern::IsRef {
                    mutability: Some(Mutability::Mutable),
                    inner: None,
                },
            )],
        }
    ));
}

#[test]
fn test_extract_walks_nested_wrappers_and_payloads() {
    let value = Value::Struct {
        name: "Outer".to_string(),
        fields: BTreeMap::from([(
            "state".to_string(),
            Value::Reference {
                addr: Address::new(AllocId(4), 0),
                mutability: Mutability::Shared,
                lifetime: Lifetime::Static,
                referent: Some(Box::new(Value::Enum {
                    name: "Option".to_string(),
                    variant: "Some".to_string(),
                    payload: Box::new(EnumPayload::Tuple(vec![
                        Value::u32(1),
                        Value::Struct {
                            name: "Inner".to_string(),
                            fields: BTreeMap::from([("flag".to_string(), Value::Bool(true))]),
                        },
                    ])),
                })),
            },
        )]),
    };

    let path = [
        ValueAccessor::Field("state".to_string()),
        ValueAccessor::Deref,
        ValueAccessor::Index(1),
        ValueAccessor::Field("flag".to_string()),
    ];

    assert_eq!(extract(&value, &path), Some(&Value::Bool(true)));
}

#[test]
fn test_extract_handles_inner_and_range_accessors() {
    let value = Value::Atomic {
        inner: Box::new(Value::Range {
            start: Some(Box::new(Value::u32(3))),
            end: Some(Box::new(Value::u32(9))),
            inclusive: true,
        }),
    };

    assert_eq!(
        extract(&value, &[ValueAccessor::Inner, ValueAccessor::Start]),
        Some(&Value::u32(3))
    );
    assert_eq!(
        extract(&value, &[ValueAccessor::Inner, ValueAccessor::End]),
        Some(&Value::u32(9))
    );
}
