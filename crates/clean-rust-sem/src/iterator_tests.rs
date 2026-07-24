// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::types::{ConstGenericArg, IntType};

// --- IteratorProtocol::item_type ---

#[test]
fn test_range_protocol_item_type_returns_element() {
    let proto = IteratorProtocol::Range {
        element_ty: RustType::Int(IntType::I32),
        inclusive: false,
    };
    assert_eq!(proto.item_type(), RustType::Int(IntType::I32));
}

#[test]
fn test_vec_protocol_item_type_returns_element() {
    let proto = IteratorProtocol::Vec {
        element_ty: RustType::Bool,
    };
    assert_eq!(proto.item_type(), RustType::Bool);
}

#[test]
fn test_array_protocol_item_type_returns_element() {
    let proto = IteratorProtocol::Array {
        element_ty: RustType::Char,
        len: 3,
    };
    assert_eq!(proto.item_type(), RustType::Char);
}

#[test]
fn test_slice_protocol_item_type_returns_shared_ref() {
    let proto = IteratorProtocol::Slice {
        element_ty: RustType::Uint(UintType::U8),
    };
    let item = proto.item_type();
    assert!(matches!(
        item,
        RustType::Reference {
            mutability: Mutability::Shared,
            ..
        }
    ));
}

#[test]
fn test_hashmap_protocol_item_type_returns_tuple_pair() {
    let proto = IteratorProtocol::HashMap {
        key_ty: RustType::Str,
        value_ty: RustType::Int(IntType::I32),
    };
    let item = proto.item_type();
    assert_eq!(
        item,
        RustType::Tuple(vec![RustType::Str, RustType::Int(IntType::I32)])
    );
}

// --- resolve_into_iterator ---

#[test]
fn test_resolve_array_into_iterator() {
    let ty = RustType::Array {
        element: Box::new(RustType::Bool),
        len: ConstGenericArg::usize(5),
    };
    let proto = resolve_into_iterator(&ty).expect("array should be iterable");
    assert!(matches!(proto, IteratorProtocol::Array { len: 5, .. }));
}

#[test]
fn test_resolve_vec_into_iterator() {
    let ty = RustType::Vec {
        element: Box::new(RustType::Int(IntType::I64)),
    };
    let proto = resolve_into_iterator(&ty).expect("Vec should be iterable");
    assert!(matches!(proto, IteratorProtocol::Vec { .. }));
    assert_eq!(proto.item_type(), RustType::Int(IntType::I64));
}

#[test]
fn test_resolve_slice_ref_into_iterator() {
    let ty = RustType::Reference {
        lifetime: Lifetime::Anonymous(0),
        mutability: Mutability::Shared,
        inner: Box::new(RustType::Slice {
            elem: Box::new(RustType::Uint(UintType::U32)),
        }),
    };
    let proto = resolve_into_iterator(&ty).expect("&[T] should be iterable");
    assert!(matches!(proto, IteratorProtocol::Slice { .. }));
}

#[test]
fn test_resolve_array_ref_into_iterator() {
    let ty = RustType::Reference {
        lifetime: Lifetime::Anonymous(0),
        mutability: Mutability::Shared,
        inner: Box::new(RustType::Array {
            element: Box::new(RustType::Bool),
            len: ConstGenericArg::usize(3),
        }),
    };
    let proto = resolve_into_iterator(&ty).expect("&[T; N] should be iterable");
    assert!(matches!(proto, IteratorProtocol::Slice { .. }));
}

#[test]
fn test_resolve_named_hashmap_into_iterator() {
    let ty = RustType::Named {
        name: "HashMap".to_string(),
        type_args: vec![RustType::Str, RustType::Int(IntType::I32)],
        lifetime_args: vec![],
        const_args: vec![],
    };
    let proto = resolve_into_iterator(&ty).expect("HashMap should be iterable");
    assert!(matches!(proto, IteratorProtocol::HashMap { .. }));
}

#[test]
fn test_resolve_named_vec_into_iterator() {
    let ty = RustType::Named {
        name: "Vec".to_string(),
        type_args: vec![RustType::Bool],
        lifetime_args: vec![],
        const_args: vec![],
    };
    let proto = resolve_into_iterator(&ty).expect("Named Vec should be iterable");
    assert_eq!(proto.item_type(), RustType::Bool);
}

#[test]
fn test_resolve_unit_fails() {
    let result = resolve_into_iterator(&RustType::Unit);
    assert!(result.is_err());
}

#[test]
fn test_resolve_bool_fails() {
    let result = resolve_into_iterator(&RustType::Bool);
    assert!(result.is_err());
}

// --- resolve_value_iterator ---

#[test]
fn test_value_iterator_array() {
    let val = Value::Array(vec![Value::u32(1), Value::u32(2)]);
    let proto = resolve_value_iterator(&val).expect("array value should be iterable");
    assert!(matches!(proto, IteratorProtocol::Array { len: 2, .. }));
}

#[test]
fn test_value_iterator_range() {
    let val = Value::Range {
        start: Some(Box::new(Value::Int {
            value: 0,
            ty: IntType::I32,
        })),
        end: Some(Box::new(Value::Int {
            value: 5,
            ty: IntType::I32,
        })),
        inclusive: false,
    };
    let proto = resolve_value_iterator(&val).expect("range value should be iterable");
    assert!(matches!(
        proto,
        IteratorProtocol::Range {
            inclusive: false,
            ..
        }
    ));
}

// --- extract_iter_elements ---

#[test]
fn test_extract_array_elements() {
    let val = Value::Array(vec![Value::Bool(true), Value::Bool(false)]);
    let elems = extract_iter_elements(&val).expect("should extract array elements");
    assert_eq!(elems.len(), 2);
}

#[test]
fn test_extract_tuple_elements() {
    let val = Value::Tuple(vec![Value::u32(1), Value::u32(2), Value::u32(3)]);
    let elems = extract_iter_elements(&val).expect("should extract tuple elements");
    assert_eq!(elems.len(), 3);
}

#[test]
fn test_extract_int_range_exclusive() {
    let val = Value::Range {
        start: Some(Box::new(Value::Int {
            value: 0,
            ty: IntType::I32,
        })),
        end: Some(Box::new(Value::Int {
            value: 3,
            ty: IntType::I32,
        })),
        inclusive: false,
    };
    let elems = extract_iter_elements(&val).expect("should extract range elements");
    assert_eq!(elems.len(), 3);
    assert_eq!(
        elems[0],
        Value::Int {
            value: 0,
            ty: IntType::I32
        }
    );
    assert_eq!(
        elems[2],
        Value::Int {
            value: 2,
            ty: IntType::I32
        }
    );
}

#[test]
fn test_extract_uint_range_inclusive() {
    let val = Value::Range {
        start: Some(Box::new(Value::u32(1))),
        end: Some(Box::new(Value::u32(3))),
        inclusive: true,
    };
    let elems = extract_iter_elements(&val).expect("should extract inclusive range");
    assert_eq!(elems.len(), 3);
}

#[test]
fn test_extract_mismatched_range_types_fails() {
    let val = Value::Range {
        start: Some(Box::new(Value::Int {
            value: 0,
            ty: IntType::I32,
        })),
        end: Some(Box::new(Value::Int {
            value: 3,
            ty: IntType::I64,
        })),
        inclusive: false,
    };
    let result = extract_iter_elements(&val);
    assert!(result.is_err());
}

// --- desugar_for_loop ---

#[test]
fn test_desugar_for_loop_produces_block_with_loop() {
    let var = Pattern::Binding {
        name: "x".to_string(),
        mutable: false,
        subpattern: None,
    };
    let iterable = Expr::Var {
        name: "items".to_string(),
        local_idx: 0,
    };
    let body = Expr::Literal(Value::Unit);
    let ty = RustType::Vec {
        element: Box::new(RustType::Int(IntType::I32)),
    };

    let result = desugar_for_loop(&var, &iterable, &ty, &body, None);
    let desugared = result.expect("desugar should succeed for Vec");
    assert!(matches!(desugared, Expr::Block { .. }));

    // The block should contain a let stmt and a loop expr
    if let Expr::Block { stmts, expr } = &desugared {
        assert_eq!(stmts.len(), 1);
        assert!(matches!(stmts[0], Stmt::Let { .. }));
        assert!(expr.is_some());
        assert!(matches!(expr.as_deref(), Some(Expr::Loop { .. })));
    }
}

#[test]
fn test_desugar_for_loop_with_label() {
    let var = Pattern::Binding {
        name: "i".to_string(),
        mutable: false,
        subpattern: None,
    };
    let iterable = Expr::Var {
        name: "arr".to_string(),
        local_idx: 0,
    };
    let body = Expr::Literal(Value::Unit);
    let ty = RustType::Array {
        element: Box::new(RustType::Uint(UintType::U32)),
        len: ConstGenericArg::usize(5),
    };

    let desugared =
        desugar_for_loop(&var, &iterable, &ty, &body, Some("outer")).expect("should succeed");

    if let Expr::Block { expr, .. } = &desugared {
        if let Some(Expr::Loop { label, .. }) = expr.as_deref() {
            assert_eq!(label.as_deref(), Some("outer"));
        } else {
            panic!("expected Loop expr");
        }
    }
}

#[test]
fn test_desugar_non_iterable_type_fails() {
    let var = Pattern::Wildcard;
    let iterable = Expr::Literal(Value::Bool(true));
    let body = Expr::Literal(Value::Unit);

    let result = desugar_for_loop(&var, &iterable, &RustType::Bool, &body, None);
    assert!(result.is_err());
}

// --- build_desugar ---

#[test]
fn test_build_desugar_captures_protocol() {
    let var = Pattern::Binding {
        name: "kv".to_string(),
        mutable: false,
        subpattern: None,
    };
    let iterable = Expr::Var {
        name: "map".to_string(),
        local_idx: 0,
    };
    let body = Expr::Literal(Value::Unit);
    let ty = RustType::Named {
        name: "HashMap".to_string(),
        type_args: vec![RustType::Str, RustType::Int(IntType::I32)],
        lifetime_args: vec![],
        const_args: vec![],
    };

    let desugar = build_desugar(&var, &iterable, &ty, &body, None).expect("HashMap should desugar");
    assert_eq!(desugar.iter_var, "__iter");
    assert!(matches!(desugar.protocol, IteratorProtocol::HashMap { .. }));
}

#[test]
fn test_extract_char_range_elements() {
    let val = Value::Range {
        start: Some(Box::new(Value::Char('a'))),
        end: Some(Box::new(Value::Char('d'))),
        inclusive: false,
    };
    let elems = extract_iter_elements(&val).expect("char range should work");
    assert_eq!(
        elems,
        vec![Value::Char('a'), Value::Char('b'), Value::Char('c')]
    );
}

#[test]
fn test_extract_int_range_inclusive_at_i128_max_no_overflow() {
    // Regression: an inclusive range ending at i128::MAX must not be re-expressed
    // as `end + 1`, which overflows. It should yield exactly the single endpoint.
    let val = Value::Range {
        start: Some(Box::new(Value::Int {
            value: i128::MAX,
            ty: IntType::I64,
        })),
        end: Some(Box::new(Value::Int {
            value: i128::MAX,
            ty: IntType::I64,
        })),
        inclusive: true,
    };
    let elems = extract_iter_elements(&val).expect("inclusive range at MAX must not overflow");
    assert_eq!(
        elems,
        vec![Value::Int {
            value: i128::MAX,
            ty: IntType::I64,
        }]
    );
}

#[test]
fn test_extract_uint_range_inclusive_at_u128_max_no_overflow() {
    // Regression: u128::MAX inclusive endpoint must not overflow `end + 1`.
    let val = Value::Range {
        start: Some(Box::new(Value::Uint {
            value: u128::MAX,
            ty: UintType::U64,
        })),
        end: Some(Box::new(Value::Uint {
            value: u128::MAX,
            ty: UintType::U64,
        })),
        inclusive: true,
    };
    let elems = extract_iter_elements(&val).expect("inclusive range at MAX must not overflow");
    assert_eq!(
        elems,
        vec![Value::Uint {
            value: u128::MAX,
            ty: UintType::U64,
        }]
    );
}

#[test]
fn test_extract_int_range_inclusive_single_endpoint() {
    // `5..=5` yields exactly `[5]`.
    let val = Value::Range {
        start: Some(Box::new(Value::Int {
            value: 5,
            ty: IntType::I32,
        })),
        end: Some(Box::new(Value::Int {
            value: 5,
            ty: IntType::I32,
        })),
        inclusive: true,
    };
    let elems = extract_iter_elements(&val).expect("single-endpoint inclusive range");
    assert_eq!(
        elems,
        vec![Value::Int {
            value: 5,
            ty: IntType::I32,
        }]
    );
}

#[test]
fn test_extract_int_range_inclusive_start_greater_than_end_is_empty() {
    // `5..=3` (start > end) yields no elements, matching Rust RangeInclusive.
    let val = Value::Range {
        start: Some(Box::new(Value::Int {
            value: 5,
            ty: IntType::I32,
        })),
        end: Some(Box::new(Value::Int {
            value: 3,
            ty: IntType::I32,
        })),
        inclusive: true,
    };
    let elems = extract_iter_elements(&val).expect("descending inclusive range is empty");
    assert!(elems.is_empty());
}

#[test]
fn test_extract_uint_range_exclusive_start_equals_end_is_empty() {
    // `3..3` yields no elements.
    let val = Value::Range {
        start: Some(Box::new(Value::u32(3))),
        end: Some(Box::new(Value::u32(3))),
        inclusive: false,
    };
    let elems = extract_iter_elements(&val).expect("empty exclusive range");
    assert!(elems.is_empty());
}

#[test]
fn test_extract_char_range_inclusive_includes_endpoint() {
    let val = Value::Range {
        start: Some(Box::new(Value::Char('a'))),
        end: Some(Box::new(Value::Char('c'))),
        inclusive: true,
    };
    let elems = extract_iter_elements(&val).expect("inclusive char range");
    assert_eq!(
        elems,
        vec![Value::Char('a'), Value::Char('b'), Value::Char('c')]
    );
}
