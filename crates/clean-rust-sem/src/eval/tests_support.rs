// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Shared test constructors for eval drop tests.

use crate::expr::{Expr, Pattern, Stmt};
use crate::types::{Lifetime, Mutability, RustType};

pub(super) fn make_let(name: &str, mutable: bool, ty: Option<RustType>, init: Expr) -> Stmt {
    Stmt::Let {
        pattern: Pattern::Binding {
            name: name.to_string(),
            mutable,
            subpattern: None,
        },
        ty,
        init: Some(Box::new(init)),
        else_block: None,
    }
}

pub(super) fn make_named_type(name: &str) -> RustType {
    RustType::Named {
        name: name.to_string(),
        type_args: vec![],
        lifetime_args: vec![],
        const_args: vec![],
    }
}

pub(super) fn make_mut_ref_named_type(name: &str) -> RustType {
    RustType::Reference {
        lifetime: Lifetime::Static,
        mutability: Mutability::Mutable,
        inner: Box::new(make_named_type(name)),
    }
}
