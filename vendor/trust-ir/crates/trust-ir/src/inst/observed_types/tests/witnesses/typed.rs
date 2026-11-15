// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
use super::*;

pub(super) fn all() -> Vec<Inst> {
    let mut all = arithmetic();
    all.extend(memory());
    all.extend(aggregate());
    all
}
fn arithmetic() -> Vec<Inst> {
    vec![
        Inst::BinOp {
            op: BinOp::Add,
            ty: Ty::U32,
            lhs: v(),
            rhs: v(),
        },
        Inst::SeqMapAddK {
            ty: Ty::Sequence(TyId::new(8)),
            seq: v(),
            k: 1,
        },
        Inst::SeqMapNot {
            ty: Ty::Sequence(TyId::new(8)),
            seq: v(),
        },
        Inst::SeqMap {
            ty: Ty::Sequence(TyId::new(8)),
            seq: v(),
            fwd: FuncId::new(9),
        },
        Inst::UnOp {
            op: UnOp::Not,
            ty: Ty::U32,
            operand: v(),
        },
        Inst::Overflow {
            op: OverflowOp::AddOverflow,
            ty: Ty::U32,
            lhs: v(),
            rhs: v(),
        },
        Inst::ICmp {
            op: ICmpOp::Eq,
            ty: Ty::U32,
            lhs: v(),
            rhs: v(),
        },
        Inst::FCmp {
            op: FCmpOp::OEq,
            ty: Ty::F32,
            lhs: v(),
            rhs: v(),
        },
        Inst::Copy {
            ty: Ty::U32,
            operand: v(),
        },
        Inst::Select {
            ty: Ty::U32,
            cond: v(),
            then_val: v(),
            else_val: v(),
        },
    ]
}
fn memory() -> Vec<Inst> {
    vec![
        Inst::Drop {
            ty: Ty::U32,
            ptr: v(),
        },
        Inst::DropInvoke {
            ty: Ty::U32,
            ptr: v(),
            normal_dest: BlockId::new(1),
            normal_args: vec![],
            unwind_dest: BlockId::new(2),
        },
        Inst::Load {
            ty: Ty::U32,
            ptr: v(),
            volatile: true,
            align: Some(4),
        },
        Inst::Store {
            ty: Ty::U32,
            ptr: v(),
            value: v(),
            volatile: false,
            align: None,
        },
        Inst::Alloca {
            ty: Ty::U32,
            count: Some(v()),
            align: None,
        },
        Inst::HeapAlloc {
            ty: Ty::U32,
            count: None,
            align: None,
            origin: AllocOrigin::RustHeap,
        },
        Inst::AtomicLoad {
            ty: Ty::U32,
            ptr: v(),
            ordering: Ordering::Acquire,
        },
        Inst::AtomicStore {
            ty: Ty::U32,
            ptr: v(),
            value: v(),
            ordering: Ordering::Release,
        },
        Inst::AtomicRMW {
            op: AtomicRMWOp::Xchg,
            ty: Ty::U32,
            ptr: v(),
            value: v(),
            ordering: Ordering::SeqCst,
        },
        Inst::CmpXchg {
            ty: Ty::U32,
            ptr: v(),
            expected: v(),
            desired: v(),
            success: Ordering::SeqCst,
            failure: Ordering::Relaxed,
            weak: false,
        },
        Inst::LoadSlot {
            frame: v(),
            slot: 5,
            ty: Ty::U32,
        },
    ]
}
fn aggregate() -> Vec<Inst> {
    vec![
        Inst::MakeAggregate {
            ty: Ty::Tuple(vec![Ty::U32]),
            variant: None,
            fields: vec![v()],
        },
        Inst::ArraySplat {
            ty: Ty::Array(TyId::new(8), u64::MAX),
            value: v(),
        },
        Inst::TensorContract {
            ty: Ty::Tensor(Box::new(Ty::U32), 2),
            lhs: v(),
            rhs: v(),
            batch: Vec::new(),
            contract: vec![(1, 0)],
        },
        Inst::TensorMap {
            ty: Ty::Tensor(Box::new(Ty::U32), 2),
            args: vec![v(), v()],
            body: vec![crate::TensorMapNode::BinOp {
                op: crate::inst::BinOp::Add,
                ty: Ty::U32,
                lhs: 0,
                rhs: 1,
            }],
        },
        Inst::TensorReduce {
            ty: Ty::Tensor(Box::new(Ty::U32), 1),
            src: v(),
            op: crate::TensorReduceOp::Add,
            axes: vec![1],
            order: crate::TensorReduceOrder::RowMajor,
        },
        Inst::TensorView {
            ty: Ty::Tensor(Box::new(Ty::U32), 1),
            src: v(),
            params: vec![],
            exprs: vec![
                crate::TensorIndexExpr::SrcExtent(0),
                crate::TensorIndexExpr::Coord(0),
            ],
            shape: vec![0],
            index: vec![1],
            fill: None,
        },
        Inst::TensorGather {
            ty: Ty::Tensor(Box::new(Ty::U32), 1),
            data: v(),
            coords: vec![v()],
        },
        Inst::TensorScatter {
            ty: Ty::Tensor(Box::new(Ty::U32), 1),
            init: v(),
            src: v(),
            coords: vec![v()],
        },
        Inst::ExtractField {
            ty: Ty::U32,
            aggregate: v(),
            field: 0,
        },
        Inst::InsertField {
            ty: Ty::U32,
            aggregate: v(),
            field: 0,
            value: v(),
        },
        Inst::ExtractElement {
            ty: Ty::U32,
            array: v(),
            index: v(),
        },
        Inst::InsertElement {
            ty: Ty::U32,
            array: v(),
            index: v(),
            value: v(),
        },
        Inst::Const {
            ty: Ty::U32,
            value: Constant::Int(0),
        },
        Inst::Undef { ty: Ty::U32 },
    ]
}
