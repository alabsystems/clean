// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Shared test helpers for clean-compiler integration tests.
//!
//! Part of #1978

use clean_compiler::ir::{CtorInfo, IRArg, IRType, VarId};
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
