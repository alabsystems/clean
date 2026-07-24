// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;

// ---- MutToSharedRef ----

#[test]
fn test_mut_to_shared_ref() {
    let from = mut_ref(RustType::Int(IntType::I32));
    let to = shared_ref(RustType::Int(IntType::I32));
    assert_eq!(try_coerce(&from, &to), Some(CoercionKind::MutToSharedRef));
}

#[test]
fn test_mut_to_shared_ref_different_inner_no_coerce() {
    let from = mut_ref(RustType::Int(IntType::I32));
    let to = shared_ref(RustType::Int(IntType::I64));
    assert_eq!(try_coerce(&from, &to), None);
}

// ---- DerefCoercion ----

#[test]
fn test_deref_string_to_str() {
    let from = shared_ref(string_type());
    let to = shared_ref(RustType::Str);
    assert!(matches!(
        try_coerce(&from, &to),
        Some(CoercionKind::DerefCoercion { source }) if source == "String"
    ));
}

#[test]
fn test_deref_vec_to_slice() {
    let from = shared_ref(RustType::Vec {
        element: Box::new(RustType::Int(IntType::I32)),
    });
    let to = shared_ref(RustType::Slice {
        elem: Box::new(RustType::Int(IntType::I32)),
    });
    assert!(matches!(
        try_coerce(&from, &to),
        Some(CoercionKind::DerefCoercion { source }) if source == "Vec"
    ));
}

#[test]
fn test_deref_box_to_inner() {
    let from = shared_ref(RustType::Box {
        inner: Box::new(RustType::Bool),
    });
    let to = shared_ref(RustType::Bool);
    assert!(matches!(
        try_coerce(&from, &to),
        Some(CoercionKind::DerefCoercion { source }) if source == "Box"
    ));
}

#[test]
fn test_deref_rc_to_inner() {
    let from = shared_ref(rc_type(RustType::Bool));
    let to = shared_ref(RustType::Bool);
    assert!(matches!(
        try_coerce(&from, &to),
        Some(CoercionKind::DerefCoercion { source }) if source == "Rc"
    ));
}

#[test]
fn test_deref_arc_to_inner() {
    let from = shared_ref(arc_type(RustType::Bool));
    let to = shared_ref(RustType::Bool);
    assert!(matches!(
        try_coerce(&from, &to),
        Some(CoercionKind::DerefCoercion { source }) if source == "Arc"
    ));
}

#[test]
fn test_deref_rc_string_to_str_transitive() {
    let from = shared_ref(rc_type(string_type()));
    let to = shared_ref(RustType::Str);
    assert_eq!(
        try_coerce(&from, &to),
        Some(CoercionKind::Transitive(vec![
            CoercionKind::DerefCoercion {
                source: "Rc".to_string(),
            },
            CoercionKind::DerefCoercion {
                source: "String".to_string(),
            },
        ]))
    );
}

#[test]
fn test_deref_arc_vec_to_slice_transitive() {
    let from = shared_ref(arc_type(RustType::Vec {
        element: Box::new(RustType::Bool),
    }));
    let to = shared_ref(RustType::Slice {
        elem: Box::new(RustType::Bool),
    });
    assert_eq!(
        try_coerce(&from, &to),
        Some(CoercionKind::Transitive(vec![
            CoercionKind::DerefCoercion {
                source: "Arc".to_string(),
            },
            CoercionKind::DerefCoercion {
                source: "Vec".to_string(),
            },
        ]))
    );
}

#[test]
fn test_deref_shared_string_to_mut_str_no_coerce() {
    let from = shared_ref(string_type());
    let to = mut_ref(RustType::Str);
    assert_eq!(try_coerce(&from, &to), None);
}

#[test]
fn test_deref_mut_box_to_mut_inner() {
    let from = mut_ref(RustType::Box {
        inner: Box::new(RustType::Bool),
    });
    let to = mut_ref(RustType::Bool);
    assert!(matches!(
        try_coerce(&from, &to),
        Some(CoercionKind::DerefCoercion { source }) if source == "Box"
    ));
}

#[test]
fn test_deref_mut_box_string_to_mut_str_transitive() {
    let from = mut_ref(RustType::Box {
        inner: Box::new(string_type()),
    });
    let to = mut_ref(RustType::Str);
    assert_eq!(
        try_coerce(&from, &to),
        Some(CoercionKind::Transitive(vec![
            CoercionKind::DerefCoercion {
                source: "Box".to_string(),
            },
            CoercionKind::DerefCoercion {
                source: "String".to_string(),
            },
        ]))
    );
}

#[test]
fn test_deref_mut_rc_to_mut_inner_no_coerce() {
    let from = mut_ref(rc_type(RustType::Bool));
    let to = mut_ref(RustType::Bool);
    assert_eq!(try_coerce(&from, &to), None);
}

#[test]
fn test_deref_mut_arc_string_to_mut_str_no_coerce() {
    let from = mut_ref(arc_type(string_type()));
    let to = mut_ref(RustType::Str);
    assert_eq!(try_coerce(&from, &to), None);
}

// ---- UnsizeArrayToSlice ----

#[test]
fn test_array_to_slice() {
    let from = shared_ref(RustType::Array {
        element: Box::new(RustType::Uint(UintType::U8)),
        len: crate::types::ConstGenericArg::usize(4),
    });
    let to = shared_ref(RustType::Slice {
        elem: Box::new(RustType::Uint(UintType::U8)),
    });
    assert_eq!(
        try_coerce(&from, &to),
        Some(CoercionKind::UnsizeArrayToSlice)
    );
}

#[test]
fn test_array_to_slice_different_element_no_coerce() {
    let from = shared_ref(RustType::Array {
        element: Box::new(RustType::Uint(UintType::U8)),
        len: crate::types::ConstGenericArg::usize(4),
    });
    let to = shared_ref(RustType::Slice {
        elem: Box::new(RustType::Uint(UintType::U32)),
    });
    assert_eq!(try_coerce(&from, &to), None);
}

#[test]
fn test_shared_array_to_mut_slice_no_coerce() {
    let from = shared_ref(RustType::Array {
        element: Box::new(RustType::Uint(UintType::U8)),
        len: crate::types::ConstGenericArg::usize(4),
    });
    let to = mut_ref(RustType::Slice {
        elem: Box::new(RustType::Uint(UintType::U8)),
    });
    assert_eq!(try_coerce(&from, &to), None);
}

#[test]
fn test_mut_array_to_shared_slice() {
    let from = mut_ref(RustType::Array {
        element: Box::new(RustType::Uint(UintType::U8)),
        len: crate::types::ConstGenericArg::usize(4),
    });
    let to = shared_ref(RustType::Slice {
        elem: Box::new(RustType::Uint(UintType::U8)),
    });
    assert_eq!(
        try_coerce(&from, &to),
        Some(CoercionKind::UnsizeArrayToSlice)
    );
}

#[test]
fn test_mut_array_to_mut_slice() {
    let from = mut_ref(RustType::Array {
        element: Box::new(RustType::Uint(UintType::U8)),
        len: crate::types::ConstGenericArg::usize(4),
    });
    let to = mut_ref(RustType::Slice {
        elem: Box::new(RustType::Uint(UintType::U8)),
    });
    assert_eq!(
        try_coerce(&from, &to),
        Some(CoercionKind::UnsizeArrayToSlice)
    );
}

// ---- Deref mutability: additional coverage ----

#[test]
fn test_deref_mut_string_to_mut_str() {
    let from = mut_ref(string_type());
    let to = mut_ref(RustType::Str);
    assert!(matches!(
        try_coerce(&from, &to),
        Some(CoercionKind::DerefCoercion { source }) if source == "String"
    ));
}

#[test]
fn test_deref_mut_string_to_shared_str() {
    let from = mut_ref(string_type());
    let to = shared_ref(RustType::Str);
    assert!(matches!(
        try_coerce(&from, &to),
        Some(CoercionKind::DerefCoercion { source }) if source == "String"
    ));
}

#[test]
fn test_deref_mut_arc_to_mut_inner_no_coerce() {
    let from = mut_ref(arc_type(RustType::Bool));
    let to = mut_ref(RustType::Bool);
    assert_eq!(try_coerce(&from, &to), None);
}

// ---- RefToRawPtr ----

#[test]
fn test_shared_ref_to_const_ptr() {
    let from = shared_ref(RustType::Int(IntType::I32));
    let to = RustType::RawPtr {
        mutability: Mutability::Shared,
        inner: Box::new(RustType::Int(IntType::I32)),
    };
    assert_eq!(try_coerce(&from, &to), Some(CoercionKind::RefToRawPtr));
}

#[test]
fn test_mut_ref_to_mut_ptr() {
    let from = mut_ref(RustType::Int(IntType::I32));
    let to = RustType::RawPtr {
        mutability: Mutability::Mutable,
        inner: Box::new(RustType::Int(IntType::I32)),
    };
    assert_eq!(try_coerce(&from, &to), Some(CoercionKind::RefToRawPtr));
}

#[test]
fn test_mut_ref_to_const_ptr() {
    let from = mut_ref(RustType::Int(IntType::I32));
    let to = RustType::RawPtr {
        mutability: Mutability::Shared,
        inner: Box::new(RustType::Int(IntType::I32)),
    };
    assert_eq!(try_coerce(&from, &to), Some(CoercionKind::RefToRawPtr));
}

// ---- MutPtrToConstPtr ----

#[test]
fn test_mut_ptr_to_const_ptr() {
    let from = RustType::RawPtr {
        mutability: Mutability::Mutable,
        inner: Box::new(RustType::Bool),
    };
    let to = RustType::RawPtr {
        mutability: Mutability::Shared,
        inner: Box::new(RustType::Bool),
    };
    assert_eq!(try_coerce(&from, &to), Some(CoercionKind::MutPtrToConstPtr));
}

// ---- NeverToAny ----

#[test]
fn test_never_to_any() {
    assert_eq!(
        try_coerce(&RustType::Never, &RustType::Bool),
        Some(CoercionKind::NeverToAny)
    );
    assert_eq!(
        try_coerce(&RustType::Never, &RustType::Int(IntType::I32)),
        Some(CoercionKind::NeverToAny)
    );
}

// ---- ClosureKindUpcast ----

#[test]
fn test_closure_fn_to_fnmut() {
    let params = vec![RustType::Int(IntType::I32)];
    let ret = Box::new(RustType::Bool);
    let from = RustType::Closure {
        params: params.clone(),
        ret: ret.clone(),
        captures: vec![],
        kind: ClosureKind::Fn,
    };
    let to = RustType::Closure {
        params,
        ret,
        captures: vec![],
        kind: ClosureKind::FnMut,
    };
    assert_eq!(
        try_coerce(&from, &to),
        Some(CoercionKind::ClosureKindUpcast)
    );
}

// ---- Negative cases ----

#[test]
fn test_no_coercion_same_type() {
    let ty = RustType::Int(IntType::I32);
    assert_eq!(try_coerce(&ty, &ty), None);
}

#[test]
fn test_no_coercion_unrelated() {
    assert_eq!(
        try_coerce(&RustType::Bool, &RustType::Int(IntType::I32)),
        None
    );
}

#[test]
fn test_no_coercion_shared_to_mut() {
    let from = shared_ref(RustType::Int(IntType::I32));
    let to = mut_ref(RustType::Int(IntType::I32));
    assert_eq!(try_coerce(&from, &to), None);
}

// ---- is_coercible ----

#[test]
fn test_is_coercible_identity() {
    assert!(is_coercible(
        &RustType::Int(IntType::I32),
        &RustType::Int(IntType::I32)
    ));
}

#[test]
fn test_is_coercible_mut_to_shared() {
    assert!(is_coercible(
        &mut_ref(RustType::Bool),
        &shared_ref(RustType::Bool)
    ));
}

#[test]
fn test_is_coercible_unrelated() {
    assert!(!is_coercible(
        &RustType::Bool,
        &RustType::Float(FloatType::F64)
    ));
}
