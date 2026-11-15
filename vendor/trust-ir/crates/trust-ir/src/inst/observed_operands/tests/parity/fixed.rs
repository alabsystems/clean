// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

fn memory_single() -> Vec<Inst> {
    vec![
        Inst::Drop {
            ty: Ty::U32,
            ptr: v(1),
        },
        Inst::Load {
            ty: Ty::U32,
            ptr: v(1),
            volatile: true,
            align: Some(4),
        },
        Inst::PtrData {
            ptr_ty: Ty::Ptr,
            ptr: v(1),
        },
        Inst::PtrMetadata {
            ptr_ty: Ty::Ptr,
            metadata_ty: Ty::U32,
            ptr: v(1),
        },
        Inst::AtomicLoad {
            ty: Ty::U32,
            ptr: v(1),
            ordering: Ordering::Acquire,
        },
        Inst::Borrow { ptr: v(1) },
        Inst::BorrowMut { ptr: v(1) },
        Inst::Retain { ptr: v(1) },
        Inst::Release { ptr: v(1) },
        Inst::IsUnique { ptr: v(1) },
        Inst::Dealloc { ptr: v(1) },
    ]
}
fn other_single() -> Vec<Inst> {
    vec![
        Inst::SeqMapAddK {
            ty: Ty::Sequence(TyId::new(70)),
            seq: v(1),
            k: u64::MAX,
        },
        Inst::SeqMapNot {
            ty: Ty::Sequence(TyId::new(70)),
            seq: v(1),
        },
        Inst::SeqMap {
            ty: Ty::Sequence(TyId::new(70)),
            seq: v(1),
            fwd: FuncId::new(71),
        },
        Inst::UnOp {
            op: UnOp::Not,
            ty: Ty::U32,
            operand: v(1),
        },
        Inst::Cast {
            op: CastOp::Bitcast,
            src_ty: Ty::U32,
            dst_ty: Ty::F32,
            operand: v(1),
        },
        Inst::Copy {
            ty: Ty::U32,
            operand: v(1),
        },
        Inst::ExtractField {
            ty: Ty::U32,
            aggregate: v(1),
            field: 72,
        },
        Inst::Assume { cond: v(1) },
        Inst::EndBorrow { borrow_ptr: v(1) },
        Inst::LoadSlot {
            frame: v(1),
            slot: 73,
            ty: Ty::U32,
        },
        Inst::CloseFrame { frame: v(1) },
        Inst::Resume { exn: v(1) },
        Inst::TensorReduce {
            ty: Ty::Tensor(Box::new(Ty::U32), 1),
            src: v(1),
            op: crate::TensorReduceOp::Add,
            axes: vec![74],
            order: crate::TensorReduceOrder::RowMajor,
        },
    ]
}

#[test]
fn every_single_operand_variant_includes_only_its_actual_value_field() {
    for instruction in memory_single().into_iter().chain(other_single()) {
        assert_eq!(parity(&instruction), ids(&[1]));
    }
}

#[test]
fn every_two_operand_variant_preserves_field_order_and_duplicates() {
    let instructions = vec![
        Inst::BinOp {
            op: BinOp::Add,
            ty: Ty::U32,
            lhs: v(1),
            rhs: v(2),
        },
        Inst::Overflow {
            op: OverflowOp::AddOverflow,
            ty: Ty::U32,
            lhs: v(1),
            rhs: v(2),
        },
        Inst::ICmp {
            op: ICmpOp::Eq,
            ty: Ty::U32,
            lhs: v(1),
            rhs: v(2),
        },
        Inst::FCmp {
            op: FCmpOp::OEq,
            ty: Ty::F32,
            lhs: v(1),
            rhs: v(2),
        },
        Inst::Store {
            ty: Ty::U32,
            ptr: v(1),
            value: v(2),
            volatile: false,
            align: None,
        },
        Inst::AtomicStore {
            ty: Ty::U32,
            ptr: v(1),
            value: v(2),
            ordering: Ordering::Release,
        },
        Inst::AtomicRMW {
            op: AtomicRMWOp::Xchg,
            ty: Ty::U32,
            ptr: v(1),
            value: v(2),
            ordering: Ordering::SeqCst,
        },
        Inst::PtrFromParts {
            ptr_ty: Ty::Ptr,
            metadata_ty: Ty::U32,
            data: v(1),
            metadata: v(2),
        },
        Inst::InsertField {
            ty: Ty::U32,
            aggregate: v(1),
            field: 70,
            value: v(2),
        },
        Inst::ExtractElement {
            ty: Ty::U32,
            array: v(1),
            index: v(2),
        },
        Inst::BindSlot {
            frame: v(1),
            slot: 71,
            value: v(2),
        },
        Inst::CoroSuspend {
            frame: v(1),
            state_slot: 72,
            next_state: 73,
            value: v(2),
        },
        Inst::TensorContract {
            ty: Ty::Tensor(Box::new(Ty::U32), 2),
            lhs: v(1),
            rhs: v(2),
            batch: vec![(74, 75)],
            contract: vec![(76, 77)],
        },
        // Lane and node numbers are not operands.
        Inst::TensorMap {
            ty: Ty::Tensor(Box::new(Ty::U32), 2),
            args: vec![v(1), v(2)],
            body: vec![crate::TensorMapNode::BinOp {
                op: BinOp::Add,
                ty: Ty::U32,
                lhs: 78,
                rhs: 79,
            }],
        },
        // The data, then its one coordinate tensor.
        Inst::TensorGather {
            ty: Ty::Tensor(Box::new(Ty::U32), 1),
            data: v(1),
            coords: vec![v(2)],
        },
    ];
    for instruction in instructions {
        assert_eq!(parity(&instruction), ids(&[1, 2]));
    }
    assert_eq!(
        parity(&Inst::BinOp {
            op: BinOp::Add,
            ty: Ty::U32,
            lhs: v(1),
            rhs: v(1)
        }),
        ids(&[1, 1])
    );
}

#[test]
fn every_three_operand_variant_preserves_its_real_field_order() {
    let instructions = vec![
        Inst::MemCopy {
            dst: v(1),
            src: v(2),
            bytes: v(3),
            overlap: true,
        },
        Inst::MemSet {
            dst: v(1),
            byte: v(2),
            bytes: v(3),
        },
        Inst::CmpXchg {
            ty: Ty::U32,
            ptr: v(1),
            expected: v(2),
            desired: v(3),
            success: Ordering::SeqCst,
            failure: Ordering::Relaxed,
            weak: true,
        },
        Inst::InsertElement {
            ty: Ty::U32,
            array: v(1),
            index: v(2),
            value: v(3),
        },
        Inst::Select {
            ty: Ty::U32,
            cond: v(1),
            then_val: v(2),
            else_val: v(3),
        },
        // The source, the parameter, then the fill; node ids are not operands.
        Inst::TensorView {
            ty: Ty::Tensor(Box::new(Ty::U32), 1),
            src: v(1),
            params: vec![v(2)],
            exprs: vec![
                crate::TensorIndexExpr::Param(0),
                crate::TensorIndexExpr::Coord(0),
            ],
            shape: vec![0],
            index: vec![1],
            fill: Some(v(3)),
        },
        // The initial tensor, the source, then the coordinate tensor.
        Inst::TensorScatter {
            ty: Ty::Tensor(Box::new(Ty::U32), 1),
            init: v(1),
            src: v(2),
            coords: vec![v(3)],
        },
    ];
    for instruction in instructions {
        assert_eq!(parity(&instruction), ids(&[1, 2, 3]));
    }
}
