// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;

// ---- coerce_value ----

#[test]
fn test_coerce_value_mut_to_shared() {
    use crate::memory::{Address, AllocId};

    let val = Value::Reference {
        addr: Address::new(AllocId(1), 0),
        mutability: Mutability::Mutable,
        lifetime: anon_lifetime(),
        referent: Some(Box::new(Value::i32(7))),
    };
    let from = mut_ref(RustType::Int(IntType::I32));
    let to = shared_ref(RustType::Int(IntType::I32));

    let coerced = coerce_value(&val, &from, &to).expect("coercion should succeed");
    match coerced {
        Value::Reference { mutability, .. } => {
            assert_eq!(mutability, Mutability::Shared);
        }
        _ => panic!("expected reference"),
    }
}

#[test]
fn test_coerce_value_ref_to_raw_ptr() {
    use crate::memory::{Address, AllocId};

    let addr = Address::new(AllocId(2), 0);
    let val = Value::Reference {
        addr,
        mutability: Mutability::Shared,
        lifetime: anon_lifetime(),
        referent: None,
    };
    let from = shared_ref(RustType::Int(IntType::I32));
    let to = RustType::RawPtr {
        mutability: Mutability::Shared,
        inner: Box::new(RustType::Int(IntType::I32)),
    };

    let coerced = coerce_value(&val, &from, &to).expect("coercion should succeed");
    match coerced {
        Value::RawPtr {
            addr: result_addr,
            mutability,
            ..
        } => {
            assert_eq!(result_addr, addr);
            assert_eq!(mutability, Mutability::Shared);
        }
        _ => panic!("expected raw pointer"),
    }
}

#[test]
fn test_coerce_value_transitive_rc_string_to_str() {
    use crate::memory::{Address, AllocId};

    let addr = Address::new(AllocId(3), 0);
    let val = Value::Reference {
        addr,
        mutability: Mutability::Shared,
        lifetime: anon_lifetime(),
        referent: None,
    };
    let from = shared_ref(rc_type(string_type()));
    let to = shared_ref(RustType::Str);

    let coerced = coerce_value(&val, &from, &to).expect("coercion should succeed");
    match coerced {
        Value::Reference {
            addr: result_addr,
            mutability,
            ..
        } => {
            assert_eq!(result_addr, addr);
            assert_eq!(mutability, Mutability::Shared);
        }
        _ => panic!("expected reference"),
    }
}

#[test]
fn test_coerce_value_no_coercion_returns_none() {
    let val = Value::Bool(true);
    let from = RustType::Bool;
    let to = RustType::Int(IntType::I32);
    assert_eq!(coerce_value(&val, &from, &to), None);
}

#[test]
fn test_coerce_value_array_to_slice_uses_source_type_when_referent_is_opaque() {
    use crate::memory::{Address, AllocId};

    let val = Value::Reference {
        addr: Address::new(AllocId(4), 0),
        mutability: Mutability::Shared,
        lifetime: anon_lifetime(),
        referent: None,
    };
    let from = shared_ref(RustType::Array {
        element: Box::new(RustType::Int(IntType::I32)),
        len: crate::types::ConstGenericArg::usize(3),
    });
    let to = shared_ref(RustType::Slice {
        elem: Box::new(RustType::Int(IntType::I32)),
    });

    let coerced = coerce_value(&val, &from, &to).expect("coercion should succeed");
    match coerced {
        Value::FatPtr(FatPointer {
            data_pointer,
            metadata: FatPtrMetadata::SliceLen(len),
        }) => {
            assert_eq!(len, 3);
            assert!(matches!(data_pointer.as_ref(), Value::Reference { .. }));
        }
        other => panic!("expected fat pointer, got {other:?}"),
    }
}

// --- Non-capturing closure → fn pointer ---

#[test]
fn test_non_capturing_closure_to_fn_ptr() {
    let closure_type = RustType::Closure {
        params: vec![RustType::Uint(UintType::U32)],
        ret: Box::new(RustType::Uint(UintType::U32)),
        captures: vec![],
        kind: ClosureKind::Fn,
    };
    let fn_ptr_type = RustType::Function {
        params: vec![RustType::Uint(UintType::U32)],
        ret: Box::new(RustType::Uint(UintType::U32)),
    };

    assert_eq!(
        try_coerce(&closure_type, &fn_ptr_type),
        Some(CoercionKind::ClosureToFnPtr)
    );
}

#[test]
fn test_capturing_closure_rejects_fn_ptr() {
    let closure_type = RustType::Closure {
        params: vec![RustType::Uint(UintType::U32)],
        ret: Box::new(RustType::Uint(UintType::U32)),
        captures: vec![(
            "x".to_string(),
            RustType::Uint(UintType::U32),
            Mutability::Shared,
        )],
        kind: ClosureKind::Fn,
    };
    let fn_ptr_type = RustType::Function {
        params: vec![RustType::Uint(UintType::U32)],
        ret: Box::new(RustType::Uint(UintType::U32)),
    };

    assert_eq!(try_coerce(&closure_type, &fn_ptr_type), None);
}

#[test]
fn test_closure_to_fn_ptr_param_mismatch_rejected() {
    let closure_type = RustType::Closure {
        params: vec![RustType::Uint(UintType::U32)],
        ret: Box::new(RustType::Uint(UintType::U32)),
        captures: vec![],
        kind: ClosureKind::Fn,
    };
    let fn_ptr_type = RustType::Function {
        params: vec![RustType::Uint(UintType::U64)],
        ret: Box::new(RustType::Uint(UintType::U32)),
    };

    assert_eq!(try_coerce(&closure_type, &fn_ptr_type), None);
}

#[test]
fn test_closure_to_fn_ptr_ret_mismatch_rejected() {
    let closure_type = RustType::Closure {
        params: vec![RustType::Uint(UintType::U32)],
        ret: Box::new(RustType::Uint(UintType::U32)),
        captures: vec![],
        kind: ClosureKind::Fn,
    };
    let fn_ptr_type = RustType::Function {
        params: vec![RustType::Uint(UintType::U32)],
        ret: Box::new(RustType::Uint(UintType::U64)),
    };

    assert_eq!(try_coerce(&closure_type, &fn_ptr_type), None);
}

#[test]
fn test_is_coercible_non_capturing_closure_to_fn_ptr() {
    let closure_type = RustType::Closure {
        params: vec![RustType::Uint(UintType::U32)],
        ret: Box::new(RustType::Uint(UintType::U32)),
        captures: vec![],
        kind: ClosureKind::Fn,
    };
    let fn_ptr_type = RustType::Function {
        params: vec![RustType::Uint(UintType::U32)],
        ret: Box::new(RustType::Uint(UintType::U32)),
    };

    assert!(is_coercible(&closure_type, &fn_ptr_type));
}
