// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Shared VIR body builders for NLL tests.

use crate::ownership::Place;
use crate::types::{Mutability as TyMut, RustType, UintType};
use crate::vir::*;

pub(super) fn u32_local(body: &mut Body, name: &str) -> LocalId {
    body.add_local(LocalDecl::new(RustType::Uint(UintType::U32), TyMut::Mutable).with_name(name))
}

pub(super) fn ref_local(body: &mut Body, name: &str, mutability: TyMut, anon_id: u32) -> LocalId {
    use crate::types::Lifetime;
    body.add_local(
        LocalDecl::new(
            RustType::Reference {
                lifetime: Lifetime::Anonymous(anon_id),
                mutability,
                inner: Box::new(RustType::Uint(UintType::U32)),
            },
            TyMut::Mutable,
        )
        .with_name(name),
    )
}

pub(super) fn assign_const(local: u32, val: u128) -> Stmt {
    Stmt::Assign {
        place: Place::Local(local),
        rvalue: Rvalue::Use(Operand::Constant(Constant::Scalar(ScalarValue::Uint(val)))),
    }
}

pub(super) fn assign_ref(dst: u32, src: u32, kind: BorrowKind) -> Stmt {
    Stmt::Assign {
        place: Place::Local(dst),
        rvalue: Rvalue::Ref {
            borrow_kind: kind,
            place: Place::Local(src),
        },
    }
}

pub(super) fn assign_copy(dst: u32, src: u32) -> Stmt {
    Stmt::Assign {
        place: Place::Local(dst),
        rvalue: Rvalue::Use(Operand::Copy(Place::Local(src))),
    }
}
