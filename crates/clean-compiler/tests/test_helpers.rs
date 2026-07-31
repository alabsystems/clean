// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Shared test helpers for clean-compiler integration tests.
//!
//! Part of #1978

use clean_compiler::ir::{CtorInfo, IRArg, IRBody, IRDecl, IRExpr, IRType, VarId};
use clean_kernel::Name;

pub fn var(n: u32) -> VarId {
    VarId(n)
}

pub fn name(s: &str) -> Name {
    Name::from_string(s)
}

pub fn arg(n: u32) -> IRArg {
    IRArg::Var(VarId(n))
}

/// Build a function that computes one expression and returns it.
///
/// `params` are `(var_id, type)` pairs.
/// `result_var` is the VarId for the VDecl that holds the expression result.
pub fn simple_fn(
    fname: &str,
    params: &[(u32, IRType)],
    ret_ty: IRType,
    result_var: u32,
    expr: IRExpr,
) -> IRDecl {
    IRDecl {
        name: name(fname),
        params: params.iter().map(|(v, t)| (VarId(*v), t.clone())).collect(),
        return_type: ret_ty.clone(),
        body: IRBody::VDecl {
            var: VarId(result_var),
            ty: ret_ty,
            value: expr,
            rest: Box::new(IRBody::Ret(IRArg::Var(VarId(result_var)))),
        },
    }
}

/// Build a CtorInfo with only object fields.
pub fn obj_ctor(tag: u32, num_objects: u32) -> CtorInfo {
    CtorInfo {
        name: name("Ctor"),
        tag,
        num_scalars: 0,
        num_objects,
        field_types: vec![IRType::Object; num_objects as usize],
    }
}

/// Build a CtorInfo with object fields followed by scalar fields.
pub fn mixed_ctor(tag: u32, num_objects: u32, scalar_types: &[IRType]) -> CtorInfo {
    let mut field_types = vec![IRType::Object; num_objects as usize];
    field_types.extend_from_slice(scalar_types);
    CtorInfo {
        name: name("MixedCtor"),
        tag,
        num_scalars: scalar_types.len() as u32,
        num_objects,
        field_types,
    }
}

/// Parity check: verify a pattern appears in both C and Rust output.
pub fn assert_both_contain(c_code: &str, rust_code: &str, pattern: &str) {
    assert!(
        c_code.contains(pattern),
        "C emitter missing pattern: {}\n---C output---\n{}",
        pattern,
        c_code
    );
    assert!(
        rust_code.contains(pattern),
        "Rust emitter missing pattern: {}\n---Rust output---\n{}",
        pattern,
        rust_code
    );
}
