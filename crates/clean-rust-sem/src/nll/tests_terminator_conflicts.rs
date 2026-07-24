// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! NLL terminator-specific conflict tests: Call, Goto, Assert.

use super::test_helpers::*;
use super::*;
use crate::types::{Mutability as TyMut, RustType, UintType};
use crate::vir::*;

/// Regression: `Term::Call` writing its destination to a borrowed place must
/// be caught as `AssignWhileBorrowed`.
///
/// Equivalent Rust:
/// ```text
/// let r = &x;
/// x = foo();   // ERROR: cannot assign to `x` — borrowed by `r`
/// use(r);
/// ```
#[test]
fn test_nll_call_destination_conflicts_with_active_borrow() {
    let mut body = Body::new();
    body.add_local(LocalDecl::new(RustType::Unit, TyMut::Mutable)); // _0
    let _x = u32_local(&mut body, "x"); // _1
    let _r = ref_local(&mut body, "r", TyMut::Shared, 0); // _2
    let _y = u32_local(&mut body, "y"); // _3

    // bb0: x = 1; r = &x; call foo() -> x  (destination = x, conflicts with r)
    let mut bb0 = BasicBlock::new(Term::Call {
        func: Operand::Constant(Constant::FnDef {
            name: "foo".to_string(),
            substs: vec![],
        }),
        args: vec![],
        destination: Place::Local(1), // x — overwrites borrowed place
        target: Some(1),
        target_args: vec![],
        unwind: UnwindAction::Cleanup(2),
    });
    bb0.add_statement(assign_const(1, 1)); // x = 1
    bb0.add_statement(assign_ref(2, 1, BorrowKind::Shared)); // r = &x
    body.add_block(bb0);

    // bb1: y = *r; return  (uses r, so the borrow is live across the call)
    let mut bb1 = BasicBlock::new(Term::Return);
    bb1.add_statement(assign_copy(3, 2)); // y = *r
    body.add_block(bb1);

    // bb2: unwind
    body.add_block(BasicBlock::new(Term::UnwindResume));

    let result = check_body(&body);
    let assign_errors: Vec<_> = result
        .errors
        .iter()
        .filter(|e| matches!(e, NllError::AssignWhileBorrowed { .. }))
        .collect();
    assert!(
        !assign_errors.is_empty(),
        "call destination overwriting borrowed place must be caught: {:?}",
        result.errors
    );
}

#[test]
fn test_nll_goto_move_arg_conflicts_with_active_borrow() {
    let mut body = Body::new();
    body.add_local(LocalDecl::new(RustType::Unit, TyMut::Mutable)); // _0
    let _x = u32_local(&mut body, "x"); // _1
    let _r = ref_local(&mut body, "r", TyMut::Shared, 0); // _2
    let _p = u32_local(&mut body, "p"); // _3
    let _y = u32_local(&mut body, "y"); // _4

    let mut bb0 = BasicBlock::new(Term::Goto {
        target: 1,
        args: vec![Operand::Move(Place::Local(1))],
    });
    bb0.add_statement(assign_const(1, 1)); // x = 1
    bb0.add_statement(assign_ref(2, 1, BorrowKind::Shared)); // r = &x
    body.add_block(bb0);

    let mut bb1 = BasicBlock::new(Term::Return);
    bb1.params
        .push(BlockParam::new(3, RustType::Uint(UintType::U32)).with_name("p"));
    bb1.add_statement(assign_copy(4, 2)); // y = *r keeps borrow live across the goto
    body.add_block(bb1);

    let result = check_body(&body);
    assert!(
        result
            .errors
            .iter()
            .any(|e| matches!(e, NllError::MoveWhileBorrowed { .. })),
        "goto move args must respect active borrows: {:?}",
        result.errors
    );
}

#[test]
fn test_nll_assert_message_keeps_borrow_live_for_move_conflict() {
    let mut body = Body::new();
    body.add_local(LocalDecl::new(RustType::Unit, TyMut::Mutable)); // _0
    let _x = u32_local(&mut body, "x"); // _1
    let _r = ref_local(&mut body, "r", TyMut::Shared, 0); // _2

    let mut bb0 = BasicBlock::new(Term::Assert {
        cond: Operand::Constant(Constant::Scalar(ScalarValue::Bool(true))),
        expected: true,
        msg: AssertMessage::BoundsCheck {
            len: Operand::Copy(Place::Local(2)), // keeps r live at the assert terminator
            index: Operand::Move(Place::Local(1)), // moving x while r borrows x must fail
        },
        target: 1,
        target_args: vec![],
        unwind: UnwindAction::Continue,
    });
    bb0.add_statement(assign_const(1, 1)); // x = 1
    bb0.add_statement(assign_ref(2, 1, BorrowKind::Shared)); // r = &x
    body.add_block(bb0);
    body.add_block(BasicBlock::new(Term::Return));

    let result = check_body(&body);
    assert!(
        result
            .errors
            .iter()
            .any(|e| matches!(e, NllError::MoveWhileBorrowed { .. })),
        "assert message operands must keep borrows live for move checking: {:?}",
        result.errors
    );
}
