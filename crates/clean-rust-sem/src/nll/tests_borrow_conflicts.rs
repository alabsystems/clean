// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! NLL borrow conflict pattern tests: ref-vs-ref, shared/mut interactions.

use super::test_helpers::*;
use super::*;
use crate::types::{Mutability as TyMut, RustType};
use crate::vir::*;

/// Double mutable borrow: both r1 and r2 borrow x mutably, both used later.
fn build_double_mut_body() -> Body {
    let mut body = Body::new();
    body.add_local(LocalDecl::new(RustType::Unit, TyMut::Mutable));
    u32_local(&mut body, "x");
    ref_local(&mut body, "r1", TyMut::Mutable, 0);
    ref_local(&mut body, "r2", TyMut::Mutable, 1);

    let mut bb0 = BasicBlock::new(Term::Return);
    bb0.add_statement(assign_const(1, 1)); // x = 1
    let mk = BorrowKind::Mut {
        kind: MutBorrowKind::Default,
    };
    bb0.add_statement(assign_ref(2, 1, mk)); // r1 = &mut x
    bb0.add_statement(assign_ref(3, 1, mk)); // r2 = &mut x
    bb0.add_statement(assign_copy(1, 2)); // use r1
    bb0.add_statement(assign_copy(1, 3)); // use r2
    body.add_block(bb0);
    body
}

#[test]
fn test_nll_double_mut_borrow() {
    let body = build_double_mut_body();
    let result = check_body(&body);
    assert_eq!(result.borrows.len(), 2);
    // r1 = &mut x at stmt1, r2 = &mut x at stmt2.
    // r1 is live at stmt2 (used at stmt3), so creating r2 conflicts with r1.
    assert!(
        result
            .errors
            .iter()
            .any(|e| matches!(e, NllError::ConflictingBorrow { .. })),
        "double mutable borrow should be detected: {:?}",
        result.errors
    );
}

/// Shared borrow followed by mutable borrow while shared is live.
fn build_shared_then_mut_body() -> Body {
    let mut body = Body::new();
    body.add_local(LocalDecl::new(RustType::Unit, TyMut::Mutable)); // _0
    let _x = u32_local(&mut body, "x"); // _1
    let _r1 = ref_local(&mut body, "r1", TyMut::Shared, 0); // _2
    let _r2 = ref_local(&mut body, "r2", TyMut::Mutable, 1); // _3
    let _y = u32_local(&mut body, "y"); // _4

    let mut bb0 = BasicBlock::new(Term::Return);
    bb0.add_statement(assign_const(1, 1)); // x = 1
    bb0.add_statement(assign_ref(2, 1, BorrowKind::Shared)); // r1 = &x
    let mk = BorrowKind::Mut {
        kind: MutBorrowKind::Default,
    };
    bb0.add_statement(assign_ref(3, 1, mk)); // r2 = &mut x (conflicts with r1)
    bb0.add_statement(assign_copy(4, 2)); // y = *r1 (use r1)
    bb0.add_statement(assign_copy(1, 3)); // x = *r2 (use r2)
    body.add_block(bb0);
    body
}

#[test]
fn test_nll_shared_then_mut_conflict() {
    let body = build_shared_then_mut_body();
    let result = check_body(&body);
    assert_eq!(result.borrows.len(), 2);
    // r1 = &x at stmt1, r2 = &mut x at stmt2.
    // r1 is live at stmt2 (used at stmt3), so &mut conflicts with &.
    assert!(
        result
            .errors
            .iter()
            .any(|e| matches!(e, NllError::ConflictingBorrow { .. })),
        "shared+mut borrow conflict should be detected: {:?}",
        result.errors
    );
}

/// Multiple shared borrows of the same place — should be allowed.
fn build_double_shared_body() -> Body {
    let mut body = Body::new();
    body.add_local(LocalDecl::new(RustType::Unit, TyMut::Mutable)); // _0
    let _x = u32_local(&mut body, "x"); // _1
    let _r1 = ref_local(&mut body, "r1", TyMut::Shared, 0); // _2
    let _r2 = ref_local(&mut body, "r2", TyMut::Shared, 1); // _3
    let _y = u32_local(&mut body, "y"); // _4

    let mut bb0 = BasicBlock::new(Term::Return);
    bb0.add_statement(assign_const(1, 1)); // x = 1
    bb0.add_statement(assign_ref(2, 1, BorrowKind::Shared)); // r1 = &x
    bb0.add_statement(assign_ref(3, 1, BorrowKind::Shared)); // r2 = &x (OK)
    bb0.add_statement(assign_copy(4, 2)); // y = *r1
    bb0.add_statement(assign_copy(4, 3)); // y = *r2
    body.add_block(bb0);
    body
}

#[test]
fn test_nll_double_shared_borrow_ok() {
    let body = build_double_shared_body();
    let result = check_body(&body);
    assert_eq!(result.borrows.len(), 2);
    // Both borrows are shared — no conflict.
    assert!(
        result.errors.is_empty(),
        "double shared borrow should be accepted: {:?}",
        result.errors
    );
}

/// Mutable borrow followed by shared borrow while mutable is live.
fn build_mut_then_shared_body() -> Body {
    let mut body = Body::new();
    body.add_local(LocalDecl::new(RustType::Unit, TyMut::Mutable)); // _0
    let _x = u32_local(&mut body, "x"); // _1
    let _r1 = ref_local(&mut body, "r1", TyMut::Mutable, 0); // _2
    let _r2 = ref_local(&mut body, "r2", TyMut::Shared, 1); // _3
    let _y = u32_local(&mut body, "y"); // _4

    let mut bb0 = BasicBlock::new(Term::Return);
    bb0.add_statement(assign_const(1, 1)); // x = 1
    let mk = BorrowKind::Mut {
        kind: MutBorrowKind::Default,
    };
    bb0.add_statement(assign_ref(2, 1, mk)); // r1 = &mut x
    bb0.add_statement(assign_ref(3, 1, BorrowKind::Shared)); // r2 = &x (conflicts)
    bb0.add_statement(assign_copy(1, 2)); // use r1
    bb0.add_statement(assign_copy(4, 3)); // use r2
    body.add_block(bb0);
    body
}

#[test]
fn test_nll_mut_then_shared_conflict() {
    let body = build_mut_then_shared_body();
    let result = check_body(&body);
    assert_eq!(result.borrows.len(), 2);
    // r1 = &mut x at stmt1, r2 = &x at stmt2.
    // r1 is live at stmt2 (used at stmt3), so &x conflicts with active &mut x.
    assert!(
        result
            .errors
            .iter()
            .any(|e| matches!(e, NllError::ConflictingBorrow { .. })),
        "mut+shared borrow conflict should be detected: {:?}",
        result.errors
    );
}

/// Mutable borrow expires before shared borrow — should be allowed (NLL).
fn build_mut_expires_then_shared_body() -> Body {
    let mut body = Body::new();
    body.add_local(LocalDecl::new(RustType::Unit, TyMut::Mutable)); // _0
    let _x = u32_local(&mut body, "x"); // _1
    let _r1 = ref_local(&mut body, "r1", TyMut::Mutable, 0); // _2
    let _y = u32_local(&mut body, "y"); // _3
    let _r2 = ref_local(&mut body, "r2", TyMut::Shared, 1); // _4
    let _z = u32_local(&mut body, "z"); // _5

    let mut bb0 = BasicBlock::new(Term::Return);
    bb0.add_statement(assign_const(1, 1)); // x = 1
    let mk = BorrowKind::Mut {
        kind: MutBorrowKind::Default,
    };
    bb0.add_statement(assign_ref(2, 1, mk)); // r1 = &mut x
    bb0.add_statement(assign_copy(3, 2)); // y = *r1 (last use of r1)
    bb0.add_statement(assign_ref(4, 1, BorrowKind::Shared)); // r2 = &x (r1 dead)
    bb0.add_statement(assign_copy(5, 4)); // z = *r2
    body.add_block(bb0);
    body
}

#[test]
fn test_nll_mut_expires_then_shared_ok() {
    let body = build_mut_expires_then_shared_body();
    let result = check_body(&body);
    assert_eq!(result.borrows.len(), 2);
    // r1 = &mut x at stmt1, used at stmt2 (last use), so r1's region ends at stmt2.
    // r2 = &x at stmt3 — r1 is dead, so no conflict.
    assert!(
        result.errors.is_empty(),
        "NLL should accept: mut expires before shared: {:?}",
        result.errors
    );
}
