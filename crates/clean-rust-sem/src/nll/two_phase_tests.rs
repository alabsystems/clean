// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::types::{Lifetime, Mutability as TyMut, RustType, UintType};
use crate::vir::*;

fn u32_local(body: &mut Body, name: &str) -> LocalId {
    body.add_local(LocalDecl::new(RustType::Uint(UintType::U32), TyMut::Mutable).with_name(name))
}

fn ref_local(body: &mut Body, name: &str, mutability: TyMut, anon_id: u32) -> LocalId {
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

fn assign_const(local: u32, val: u128) -> Stmt {
    Stmt::Assign {
        place: Place::Local(local),
        rvalue: Rvalue::Use(Operand::Constant(Constant::Scalar(ScalarValue::Uint(val)))),
    }
}

fn assign_ref(dst: u32, src: u32, kind: BorrowKind) -> Stmt {
    Stmt::Assign {
        place: Place::Local(dst),
        rvalue: Rvalue::Ref {
            borrow_kind: kind,
            place: Place::Local(src),
        },
    }
}

fn assign_copy(dst: u32, src: u32) -> Stmt {
    Stmt::Assign {
        place: Place::Local(dst),
        rvalue: Rvalue::Use(Operand::Copy(Place::Local(src))),
    }
}

fn two_phase_mut() -> BorrowKind {
    BorrowKind::Mut {
        kind: MutBorrowKind::TwoPhaseBorrow,
    }
}

fn call_with_arg(arg_local: u32, target: BasicBlockId) -> Term {
    Term::Call {
        func: Operand::Constant(Constant::FnDef {
            name: "consume".to_string(),
            substs: vec![],
        }),
        args: vec![Operand::Copy(Place::Local(arg_local))],
        destination: Place::Local(0),
        target: Some(target),
        target_args: vec![],
        unwind: UnwindAction::Continue,
    }
}

fn build_two_phase_shared_then_activate_body() -> Body {
    let mut body = Body::new();
    body.add_local(LocalDecl::new(RustType::Unit, TyMut::Mutable)); // _0
    let _x = u32_local(&mut body, "x"); // _1
    let _shared = ref_local(&mut body, "shared", TyMut::Shared, 0); // _2
    let _pending = ref_local(&mut body, "pending", TyMut::Mutable, 1); // _3
    let _y = u32_local(&mut body, "y"); // _4

    let mut bb0 = BasicBlock::new(call_with_arg(3, 1));
    bb0.add_statement(assign_const(1, 1)); // x = 1
    bb0.add_statement(assign_ref(2, 1, BorrowKind::Shared)); // shared = &x
    bb0.add_statement(assign_ref(3, 1, two_phase_mut())); // pending = &two-phase mut x
    bb0.add_statement(assign_copy(4, 2)); // y = *shared (shared dies here)
    body.add_block(bb0);
    body.add_block(BasicBlock::new(Term::Return));
    body
}

#[test]
fn test_nll_two_phase_allows_shared_until_activation() {
    let body = build_two_phase_shared_then_activate_body();
    let result = check_body(&body);

    assert_eq!(result.borrows.len(), 2);
    assert!(
        result.errors.is_empty(),
        "two-phase borrow should coexist with shared borrow before activation: {:?}",
        result.errors
    );
}

fn build_two_phase_retag_then_shared_body() -> Body {
    let mut body = Body::new();
    body.add_local(LocalDecl::new(RustType::Unit, TyMut::Mutable)); // _0
    let _x = u32_local(&mut body, "x"); // _1
    let _pending = ref_local(&mut body, "pending", TyMut::Mutable, 0); // _2
    let _shared = ref_local(&mut body, "shared", TyMut::Shared, 1); // _3

    let mut bb0 = BasicBlock::new(call_with_arg(2, 1));
    bb0.add_statement(assign_const(1, 1)); // x = 1
    bb0.add_statement(assign_ref(2, 1, two_phase_mut())); // pending = &two-phase mut x
    bb0.add_statement(Stmt::Retag {
        kind: RetagKind::TwoPhase,
        place: Place::Local(2),
    }); // bookkeeping should not activate the borrow
    bb0.add_statement(assign_ref(3, 1, BorrowKind::Shared)); // shared = &x
    body.add_block(bb0);
    body.add_block(BasicBlock::new(Term::Return));
    body
}

#[test]
fn test_nll_two_phase_retag_does_not_activate_pending_borrow() {
    let body = build_two_phase_retag_then_shared_body();
    let result = check_body(&body);

    assert_eq!(result.borrows.len(), 2);
    assert!(
        result.errors.is_empty(),
        "RetagKind::TwoPhase should not activate a pending two-phase borrow: {:?}",
        result.errors
    );
}

fn build_two_phase_activation_conflict_body() -> Body {
    let mut body = Body::new();
    body.add_local(LocalDecl::new(RustType::Unit, TyMut::Mutable)); // _0
    let _x = u32_local(&mut body, "x"); // _1
    let _shared = ref_local(&mut body, "shared", TyMut::Shared, 0); // _2
    let _pending = ref_local(&mut body, "pending", TyMut::Mutable, 1); // _3
    let _y = u32_local(&mut body, "y"); // _4

    let mut bb0 = BasicBlock::new(call_with_arg(3, 1));
    bb0.add_statement(assign_const(1, 1)); // x = 1
    bb0.add_statement(assign_ref(2, 1, BorrowKind::Shared)); // shared = &x
    bb0.add_statement(assign_ref(3, 1, two_phase_mut())); // pending = &two-phase mut x
    body.add_block(bb0);

    let mut bb1 = BasicBlock::new(Term::Return);
    bb1.add_statement(assign_copy(4, 2)); // y = *shared (shared still live at call)
    body.add_block(bb1);
    body
}

#[test]
fn test_nll_two_phase_activation_detects_shared_conflict() {
    let body = build_two_phase_activation_conflict_body();
    let result = check_body(&body);

    assert_eq!(result.borrows.len(), 2);
    assert!(
        result
            .errors
            .iter()
            .any(|e| matches!(e, NllError::ConflictingBorrow { .. })),
        "activation should reject still-live shared borrow: {:?}",
        result.errors
    );
}

fn build_two_phase_reservation_conflict_body() -> Body {
    let mut body = Body::new();
    body.add_local(LocalDecl::new(RustType::Unit, TyMut::Mutable)); // _0
    let _x = u32_local(&mut body, "x"); // _1
    let _active = ref_local(&mut body, "active", TyMut::Mutable, 0); // _2
    let _pending = ref_local(&mut body, "pending", TyMut::Mutable, 1); // _3
    let _y = u32_local(&mut body, "y"); // _4

    let mut bb0 = BasicBlock::new(Term::Return);
    bb0.add_statement(assign_const(1, 1)); // x = 1
    bb0.add_statement(assign_ref(
        2,
        1,
        BorrowKind::Mut {
            kind: MutBorrowKind::Default,
        },
    )); // active = &mut x
    bb0.add_statement(assign_ref(3, 1, two_phase_mut())); // pending = &two-phase mut x
    bb0.add_statement(assign_copy(4, 2)); // y = *active
    body.add_block(bb0);
    body
}

#[test]
fn test_nll_two_phase_reservation_still_conflicts_with_live_mut() {
    let body = build_two_phase_reservation_conflict_body();
    let result = check_body(&body);

    assert_eq!(result.borrows.len(), 2);
    assert!(
        result
            .errors
            .iter()
            .any(|e| matches!(e, NllError::ConflictingBorrow { .. })),
        "reservation should still reject an existing mutable borrow: {:?}",
        result.errors
    );
}
