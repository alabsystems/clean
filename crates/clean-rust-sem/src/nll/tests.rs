// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Core NLL tests: liveness, region computation, basic flow-sensitive borrow checking.

use super::test_helpers::*;
use super::*;
use crate::types::{Mutability as TyMut, RustType};
use crate::vir::*;

/// NLL canonical: borrow dies at last use, write to x after last use is OK.
fn build_nll_basic_body() -> Body {
    let mut body = Body::new();
    body.add_local(LocalDecl::new(RustType::Unit, TyMut::Mutable)); // _0
    let _x = u32_local(&mut body, "x"); // _1
    let _r = ref_local(&mut body, "r", TyMut::Shared, 0); // _2
    let _y = u32_local(&mut body, "y"); // _3

    let mut bb0 = BasicBlock::new(Term::Return);
    bb0.add_statement(assign_const(1, 1)); // x = 1
    bb0.add_statement(assign_ref(2, 1, BorrowKind::Shared)); // r = &x
    bb0.add_statement(assign_copy(3, 2)); // y = *r
    bb0.add_statement(assign_const(1, 2)); // x = 2 (borrow dead)
    body.add_block(bb0);
    body
}

#[test]
fn test_nll_borrow_dies_at_last_use() {
    let body = build_nll_basic_body();
    let result = check_body(&body);

    assert_eq!(result.borrows.len(), 1);
    assert_eq!(result.borrows[0].ref_local, 2);
    assert_eq!(result.borrows[0].origin, ProgramPoint::new(0, 1));

    let region = &result.regions[0];
    assert!(
        region.contains(&ProgramPoint::new(0, 1)),
        "active at origin"
    );
    assert!(region.contains(&ProgramPoint::new(0, 2)), "active at use");
    assert!(
        !region.contains(&ProgramPoint::new(0, 3)),
        "dead after last use"
    );

    assert!(
        result.errors.is_empty(),
        "NLL accepts this: {:?}",
        result.errors
    );
}

/// Conflict: write to x while r (which borrows x) is still live.
fn build_conflict_body() -> Body {
    let mut body = Body::new();
    body.add_local(LocalDecl::new(RustType::Unit, TyMut::Mutable));
    u32_local(&mut body, "x");
    ref_local(&mut body, "r", TyMut::Shared, 0);
    u32_local(&mut body, "y");

    let mut bb0 = BasicBlock::new(Term::Return);
    bb0.add_statement(assign_const(1, 1)); // x = 1
    bb0.add_statement(assign_ref(2, 1, BorrowKind::Shared)); // r = &x
    bb0.add_statement(assign_const(1, 2)); // x = 2 (CONFLICT)
    bb0.add_statement(assign_copy(3, 2)); // y = *r
    body.add_block(bb0);
    body
}

#[test]
fn test_nll_detects_use_after_write() {
    let body = build_conflict_body();
    let result = check_body(&body);

    assert_eq!(result.borrows.len(), 1);
    assert!(result.regions[0].contains(&ProgramPoint::new(0, 2)));
    assert!(!result.errors.is_empty(), "should detect conflict");
    assert!(matches!(
        &result.errors[0],
        NllError::AssignWhileBorrowed { .. }
    ));
}

/// Multi-block: borrow used on one branch only.
fn build_branching_body() -> Body {
    let mut body = Body::new();
    body.add_local(LocalDecl::new(RustType::Unit, TyMut::Mutable));
    u32_local(&mut body, "x");
    ref_local(&mut body, "r", TyMut::Shared, 0);
    u32_local(&mut body, "y");
    body.add_local(LocalDecl::new(RustType::Bool, TyMut::Mutable).with_name("cond"));

    // bb0: create borrow, then switch
    let mut bb0 = BasicBlock::new(Term::Unreachable);
    bb0.add_statement(assign_const(1, 1));
    bb0.add_statement(assign_ref(2, 1, BorrowKind::Shared));
    let mut targets = SwitchTargets::new(2);
    targets.add(0, 1);
    bb0.terminator = Term::SwitchInt {
        discriminant: Operand::Copy(Place::Local(4)),
        targets,
    };
    body.add_block(bb0);

    // bb1: uses r
    let mut bb1 = BasicBlock::new(Term::Goto {
        target: 3,
        args: vec![],
    });
    bb1.add_statement(assign_copy(3, 2));
    body.add_block(bb1);

    // bb2: does NOT use r, writes x
    let mut bb2 = BasicBlock::new(Term::Goto {
        target: 3,
        args: vec![],
    });
    bb2.add_statement(assign_const(1, 2));
    body.add_block(bb2);

    // bb3: return
    body.add_block(BasicBlock::new(Term::Return));
    body
}

#[test]
fn test_nll_branching_borrow() {
    let body = build_branching_body();
    let result = check_body(&body);

    assert_eq!(result.borrows.len(), 1);
    let region = &result.regions[0];
    assert!(region.contains(&ProgramPoint::new(0, 1))); // origin
    assert!(region.contains(&ProgramPoint::new(1, 0))); // y = *r in bb1
                                                        // Conservative NLL: r is live at branch point (may-analysis).
                                                        // bb2 write to x may or may not be flagged depending on propagation.
}

#[test]
fn test_liveness_basic() {
    let body = build_nll_basic_body();
    let liveness = liveness::compute_liveness(&body);

    let r_points = liveness
        .live_points
        .get(&2)
        .expect("r should have live points");
    assert!(r_points.contains(&ProgramPoint::new(0, 2)), "r live at use");
    assert!(
        !r_points.contains(&ProgramPoint::new(0, 1)),
        "r not live at def"
    );
    assert!(
        !r_points.contains(&ProgramPoint::new(0, 3)),
        "r dead after use"
    );
}

#[test]
fn test_extract_borrows() {
    let body = build_nll_basic_body();
    let borrows = extract_borrows(&body);

    assert_eq!(borrows.len(), 1);
    assert_eq!(borrows[0].ref_local, 2);
    assert_eq!(borrows[0].borrowed_place, Place::Local(1));
    assert_eq!(borrows[0].kind, BorrowKind::Shared);
}

#[test]
fn test_no_borrows_no_errors() {
    let mut body = Body::new();
    body.add_local(LocalDecl::new(RustType::Unit, TyMut::Mutable));
    u32_local(&mut body, "x");

    let mut bb0 = BasicBlock::new(Term::Return);
    bb0.add_statement(assign_const(1, 42));
    body.add_block(bb0);

    let result = check_body(&body);
    assert!(result.borrows.is_empty());
    assert!(result.errors.is_empty());
}

#[test]
fn test_program_point_ordering() {
    let p1 = ProgramPoint::new(0, 0);
    let p2 = ProgramPoint::new(0, 1);
    let p3 = ProgramPoint::new(1, 0);
    assert!(p1 < p2);
    assert!(p2 < p3);
    assert!(p1 < p3);
}
