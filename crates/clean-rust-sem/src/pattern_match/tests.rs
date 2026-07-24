// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::values::EnumPayload;
use std::collections::BTreeMap;

#[test]
fn test_match_wildcard() {
    let pattern = Pattern::Wildcard;
    let value = Value::u32(42);

    let result = match_pattern(&pattern, &value).expect("wildcard should match any value");
    assert!(result.bindings.is_empty());
}

#[test]
fn test_match_binding() {
    let pattern = Pattern::Binding {
        name: "x".to_string(),
        mutable: false,
        subpattern: None,
    };
    let value = Value::u32(42);

    let bindings = match_pattern(&pattern, &value).expect("binding pattern should match any value");
    assert_eq!(bindings.bindings.len(), 1);
    assert_eq!(bindings.bindings[0].0, "x");
    assert_eq!(bindings.bindings[0].1, Value::u32(42));
}

#[test]
fn test_match_literal() {
    let pat = Pattern::Literal(Value::u32(42));
    assert!(match_pattern(&pat, &Value::u32(42)).is_some());
    assert!(match_pattern(&pat, &Value::u32(43)).is_none());
}

#[test]
fn test_match_tuple() {
    let pattern = Pattern::Tuple(vec![
        Pattern::Binding {
            name: "a".to_string(),
            mutable: false,
            subpattern: None,
        },
        Pattern::Binding {
            name: "b".to_string(),
            mutable: false,
            subpattern: None,
        },
    ]);
    let value = Value::Tuple(vec![Value::u32(1), Value::u32(2)]);

    let bindings = match_pattern(&pattern, &value).expect("tuple pattern should match tuple value");
    assert_eq!(bindings.bindings.len(), 2);
}

#[test]
fn test_match_pattern_typed_preserves_tuple_element_drop_type() {
    let pattern = Pattern::Tuple(vec![Pattern::Binding {
        name: "outer".to_string(),
        mutable: false,
        subpattern: None,
    }]);
    let value = Value::Tuple(vec![Value::Struct {
        name: "Outer".to_string(),
        fields: BTreeMap::from([("marker".to_string(), Value::Bool(true))]),
    }]);
    let elem_ty = RustType::Named {
        name: "Outer".to_string(),
        type_args: vec![RustType::Bool],
        lifetime_args: vec![],
        const_args: vec![],
    };
    let tuple_ty = RustType::Tuple(vec![elem_ty.clone()]);

    let bindings = match_pattern_typed(&pattern, &value, Some(&tuple_ty))
        .expect("typed tuple pattern should propagate element drop types");
    assert_eq!(bindings.bindings.len(), 1);
    assert_eq!(bindings.bindings[0].3.as_ref(), Some(&elem_ty));
}

#[test]
fn test_match_enum_unit() {
    let pattern = Pattern::EnumVariant {
        enum_name: "Option".to_string(),
        variant: "None".to_string(),
        payload: crate::expr::EnumPatternPayload::Unit,
    };
    let value = Value::Enum {
        name: "Option".to_string(),
        variant: "None".to_string(),
        payload: Box::new(EnumPayload::Unit),
    };

    assert!(
        match_pattern(&pattern, &value).is_some(),
        "unit enum variant Option::None should match"
    );
}

#[test]
fn test_match_enum_tuple() {
    let pattern = Pattern::EnumVariant {
        enum_name: "Option".to_string(),
        variant: "Some".to_string(),
        payload: crate::expr::EnumPatternPayload::Tuple(vec![Pattern::Binding {
            name: "x".to_string(),
            mutable: false,
            subpattern: None,
        }]),
    };
    let value = Value::Enum {
        name: "Option".to_string(),
        variant: "Some".to_string(),
        payload: Box::new(EnumPayload::Tuple(vec![Value::u32(42)])),
    };

    let bindings =
        match_pattern(&pattern, &value).expect("tuple enum variant Option::Some(42) should match");
    assert_eq!(bindings.bindings.len(), 1);
}

#[test]
fn test_match_or_pattern() {
    let pattern = Pattern::Or(vec![
        Pattern::Literal(Value::u32(1)),
        Pattern::Literal(Value::u32(2)),
        Pattern::Literal(Value::u32(3)),
    ]);

    assert!(match_pattern(&pattern, &Value::u32(1)).is_some());
    assert!(match_pattern(&pattern, &Value::u32(2)).is_some());
    assert!(match_pattern(&pattern, &Value::u32(3)).is_some());
    assert!(match_pattern(&pattern, &Value::u32(4)).is_none());
}

#[test]
fn test_match_slice_exact() {
    let pattern = Pattern::Slice(vec![
        Pattern::Binding {
            name: "a".to_string(),
            mutable: false,
            subpattern: None,
        },
        Pattern::Binding {
            name: "b".to_string(),
            mutable: false,
            subpattern: None,
        },
    ]);
    let value = Value::Array(vec![Value::u32(1), Value::u32(2)]);

    let bindings = match_pattern(&pattern, &value).expect("exact slice pattern should match");
    assert_eq!(bindings.bindings.len(), 2);
    assert_eq!(bindings.bindings[0].0, "a");
    assert_eq!(bindings.bindings[1].0, "b");
}

#[test]
fn test_match_slice_exact_wrong_length() {
    let pattern = Pattern::Slice(vec![Pattern::Binding {
        name: "a".to_string(),
        mutable: false,
        subpattern: None,
    }]);
    let value = Value::Array(vec![Value::u32(1), Value::u32(2)]);

    assert!(
        match_pattern(&pattern, &value).is_none(),
        "slice [a] should not match 2-element array"
    );
}

#[test]
fn test_match_slice_with_rest() {
    let pattern = Pattern::Slice(vec![
        Pattern::Binding {
            name: "first".to_string(),
            mutable: false,
            subpattern: None,
        },
        Pattern::Rest,
        Pattern::Binding {
            name: "last".to_string(),
            mutable: false,
            subpattern: None,
        },
    ]);
    let value = Value::Array(vec![
        Value::u32(1),
        Value::u32(2),
        Value::u32(3),
        Value::u32(4),
    ]);

    let bindings = match_pattern(&pattern, &value).expect("slice with rest should match");
    assert_eq!(bindings.bindings.len(), 2);
    assert_eq!(bindings.bindings[0].0, "first");
    assert_eq!(bindings.bindings[0].1, Value::u32(1));
    assert_eq!(bindings.bindings[1].0, "last");
    assert_eq!(bindings.bindings[1].1, Value::u32(4));
}

#[test]
fn test_match_slice_rest_too_short() {
    let pattern = Pattern::Slice(vec![
        Pattern::Binding {
            name: "a".to_string(),
            mutable: false,
            subpattern: None,
        },
        Pattern::Rest,
        Pattern::Binding {
            name: "b".to_string(),
            mutable: false,
            subpattern: None,
        },
        Pattern::Binding {
            name: "c".to_string(),
            mutable: false,
            subpattern: None,
        },
    ]);
    let value = Value::Array(vec![Value::u32(1), Value::u32(2)]);

    assert!(
        match_pattern(&pattern, &value).is_none(),
        "slice [a, .., b, c] should not match 2-element array"
    );
}
