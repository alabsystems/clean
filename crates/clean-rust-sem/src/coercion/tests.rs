// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

mod type_level;
mod value_level;

use super::*;
use crate::types::{ClosureKind, FloatType, IntType, Lifetime, UintType};
use crate::values::{FatPointer, FatPtrMetadata};

fn anon_lifetime() -> Lifetime {
    Lifetime::Anonymous(0)
}

fn shared_ref(inner: RustType) -> RustType {
    RustType::Reference {
        lifetime: anon_lifetime(),
        mutability: Mutability::Shared,
        inner: Box::new(inner),
    }
}

fn mut_ref(inner: RustType) -> RustType {
    RustType::Reference {
        lifetime: anon_lifetime(),
        mutability: Mutability::Mutable,
        inner: Box::new(inner),
    }
}

fn string_type() -> RustType {
    RustType::Named {
        name: "String".to_string(),
        type_args: vec![],
        lifetime_args: vec![],
        const_args: vec![],
    }
}

fn rc_type(inner: RustType) -> RustType {
    RustType::Named {
        name: "std::rc::Rc".to_string(),
        type_args: vec![inner],
        lifetime_args: vec![],
        const_args: vec![],
    }
}

fn arc_type(inner: RustType) -> RustType {
    RustType::Named {
        name: "std::sync::Arc".to_string(),
        type_args: vec![inner],
        lifetime_args: vec![],
        const_args: vec![],
    }
}
