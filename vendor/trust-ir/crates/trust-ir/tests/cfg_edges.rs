// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `Inst::successor_edges` / `Inst::unwind_dest`: the ONE exhaustive
//! control-flow accessor (amendment D §1.3,
//! `docs/amendment-d-executable-drop-proposal-2026-10-01.md`).
//!
//! Before it, every CFG walk (dominance, the allocation-bound advisory, the
//! semantic diff's block order, the validator's control-flow / unwind /
//! block-argument / refinement / binding-frame passes, the give-back loop
//! probe) spelled its own `match` with a `_ => no successors` arm, so a new
//! terminator silently became a sink in every walk that was not updated:
//! its targets unchecked, unreached and undominated (fail-open). The accessor
//! has no wildcard, so a new variant is a compile error there; this census
//! pins the runtime half: one sample of EVERY `Inst` shape, the exact edges
//! each answers, and agreement with the public walk that reads them
//! (`DominatorTree`, whose edge numbering is the accessor's order).

use trust_ir::analysis::DominatorTree;
use trust_ir::constant::Constant;
use trust_ir::inst::{
    AllocOrigin, AssertKind, AtomicRMWOp, BinOp, BindingFrameDef, BindingSlot, CastOp, Edge,
    EdgeKind, FCmpOp, ICmpOp, Inst, InstShape, Ordering, OverflowOp, PanicLocation, PanicSite,
    SwitchCase, UnOp,
};
use trust_ir::ty::Ty;
use trust_ir::value::{BindingFrameId, BlockId, FuncId, FuncTyId, GlobalId, ValueId};
use trust_ir::{Block, Function, InstrNode};

fn v(n: u32) -> ValueId {
    ValueId::new(n)
}
fn b(n: u32) -> BlockId {
    BlockId::new(n)
}

/// One instance of every `Inst` variant, each terminator with DISTINCT edge
/// targets (bb1, bb2, ...) and distinct argument lists, so an edge read from
/// the wrong field is visible.
fn sample_of_every_instruction() -> Vec<Inst> {
    vec![
        Inst::BinOp {
            op: BinOp::Add,
            ty: Ty::I64,
            lhs: v(0),
            rhs: v(1),
        },
        Inst::UnOp {
            op: UnOp::Neg,
            ty: Ty::I64,
            operand: v(0),
        },
        Inst::Overflow {
            op: OverflowOp::AddOverflow,
            ty: Ty::I64,
            lhs: v(0),
            rhs: v(1),
        },
        Inst::ICmp {
            op: ICmpOp::Eq,
            ty: Ty::I64,
            lhs: v(0),
            rhs: v(1),
        },
        Inst::FCmp {
            op: FCmpOp::OEq,
            ty: Ty::F64,
            lhs: v(0),
            rhs: v(1),
        },
        Inst::Cast {
            op: CastOp::ZExt,
            src_ty: Ty::I8,
            dst_ty: Ty::I64,
            operand: v(0),
        },
        Inst::Load {
            ty: Ty::I64,
            ptr: v(0),
            volatile: false,
            align: None,
        },
        Inst::Store {
            ty: Ty::I64,
            ptr: v(0),
            value: v(1),
            volatile: false,
            align: None,
        },
        Inst::Alloca {
            ty: Ty::I64,
            count: None,
            align: None,
        },
        Inst::Drop {
            ty: Ty::I64,
            ptr: v(0),
        },
        Inst::HeapAlloc {
            ty: Ty::I64,
            count: None,
            align: None,
            origin: AllocOrigin::CMalloc,
        },
        Inst::GEP {
            pointee_ty: Ty::I64,
            base: v(0),
            indices: vec![v(1)],
            inbounds: false,
        },
        Inst::PtrData {
            ptr_ty: Ty::Ptr,
            ptr: v(0),
        },
        Inst::PtrMetadata {
            ptr_ty: Ty::Ptr,
            metadata_ty: Ty::Unit,
            ptr: v(0),
        },
        Inst::PtrFromParts {
            ptr_ty: Ty::Ptr,
            metadata_ty: Ty::Unit,
            data: v(0),
            metadata: v(1),
        },
        Inst::AtomicLoad {
            ty: Ty::I64,
            ptr: v(0),
            ordering: Ordering::SeqCst,
        },
        Inst::AtomicStore {
            ty: Ty::I64,
            ptr: v(0),
            value: v(1),
            ordering: Ordering::SeqCst,
        },
        Inst::AtomicRMW {
            op: AtomicRMWOp::Xchg,
            ty: Ty::I64,
            ptr: v(0),
            value: v(1),
            ordering: Ordering::SeqCst,
        },
        Inst::CmpXchg {
            ty: Ty::I64,
            ptr: v(0),
            expected: v(1),
            desired: v(2),
            success: Ordering::SeqCst,
            failure: Ordering::SeqCst,
            weak: false,
        },
        Inst::Fence {
            ordering: Ordering::SeqCst,
        },
        Inst::Br {
            target: b(1),
            args: vec![v(10)],
        },
        Inst::CondBr {
            cond: v(0),
            then_target: b(1),
            then_args: vec![v(10)],
            else_target: b(2),
            else_args: vec![v(11), v(12)],
        },
        Inst::Switch {
            value: v(0),
            default: b(3),
            default_args: vec![v(13)],
            cases: vec![
                SwitchCase {
                    value: Constant::Int(0),
                    target: b(1),
                    args: vec![v(10)],
                },
                SwitchCase {
                    value: Constant::Int(1),
                    target: b(2),
                    args: vec![],
                },
            ],
            exhaustive_enum_unreachable: false,
        },
        Inst::Call {
            callee: FuncId::new(0),
            args: vec![],
        },
        Inst::CallIndirect {
            callee: v(0),
            sig: FuncTyId::new(0),
            args: vec![],
            calling_conv: trust_ir::CallingConv::C,
        },
        Inst::Return { values: vec![] },
        Inst::ExtractField {
            ty: Ty::I64,
            aggregate: v(0),
            field: 0,
        },
        Inst::InsertField {
            ty: Ty::I64,
            aggregate: v(0),
            field: 0,
            value: v(1),
        },
        Inst::ExtractElement {
            ty: Ty::I64,
            array: v(0),
            index: v(1),
        },
        Inst::InsertElement {
            ty: Ty::I64,
            array: v(0),
            index: v(1),
            value: v(2),
        },
        Inst::Const {
            ty: Ty::I64,
            value: Constant::Int(0),
        },
        Inst::NullPtr,
        Inst::GlobalAddr {
            global: GlobalId::new(0),
        },
        Inst::Undef { ty: Ty::I64 },
        Inst::Assume { cond: v(0) },
        Inst::Assert {
            cond: v(0),
            kind: AssertKind::Unspecified,
            site: None,
        },
        Inst::Unreachable,
        Inst::Copy {
            ty: Ty::I64,
            operand: v(0),
        },
        Inst::Select {
            ty: Ty::I64,
            cond: v(0),
            then_val: v(1),
            else_val: v(2),
        },
        Inst::SeqMapAddK {
            ty: Ty::I64,
            seq: v(0),
            k: 1,
        },
        Inst::SeqMapNot {
            ty: Ty::I64,
            seq: v(0),
        },
        Inst::SeqMap {
            ty: Ty::I64,
            seq: v(0),
            fwd: FuncId::new(0),
        },
        Inst::Borrow { ptr: v(0) },
        Inst::BorrowMut { ptr: v(0) },
        Inst::EndBorrow { borrow_ptr: v(0) },
        Inst::Retain { ptr: v(0) },
        Inst::Release { ptr: v(0) },
        Inst::IsUnique { ptr: v(0) },
        Inst::Dealloc { ptr: v(0) },
        Inst::MemCopy {
            dst: v(0),
            src: v(1),
            bytes: v(2),
            overlap: false,
        },
        Inst::MemSet {
            dst: v(0),
            byte: v(1),
            bytes: v(2),
        },
        Inst::OpenFrame {
            def: BindingFrameDef::new(
                BindingFrameId::new(0),
                "frame",
                vec![BindingSlot::new("s", Ty::I64)],
            ),
        },
        Inst::BindSlot {
            frame: v(0),
            slot: 0,
            value: v(1),
        },
        Inst::LoadSlot {
            frame: v(0),
            slot: 0,
            ty: Ty::I64,
        },
        Inst::CloseFrame { frame: v(0) },
        Inst::CoroSuspend {
            frame: v(0),
            state_slot: 0,
            next_state: 1,
            value: v(1),
        },
        Inst::Invoke {
            callee: FuncId::new(0),
            args: vec![v(5)],
            normal_dest: b(1),
            normal_args: vec![v(10)],
            unwind_dest: b(2),
        },
        Inst::LandingPad {
            is_cleanup: true,
            catch_type_indices: vec![],
        },
        Inst::Resume { exn: v(0) },
        Inst::AssertInvoke {
            cond: v(0),
            kind: AssertKind::DivByZero,
            site: PanicSite {
                entry: FuncId::new(0),
                location: PanicLocation::Global(GlobalId::new(0)),
            },
            normal_dest: b(1),
            normal_args: vec![v(10)],
            unwind_dest: b(2),
        },
        Inst::DialectOp(Box::new(trust_ir::dialect::DialectInst::new(
            "verif", "probe",
        ))),
        Inst::MakeAggregate {
            ty: Ty::Tuple(vec![Ty::I64]),
            variant: None,
            fields: vec![v(0)],
        },
        Inst::MakeClosure {
            ty: trust_ir::value::ClosureTyId::new(8),
            func: FuncId::new(9),
            captures: vec![v(0)],
        },
        Inst::ArraySplat {
            ty: Ty::Unit,
            value: v(0),
        },
        Inst::CallCannotUnwind {
            callee: FuncId::new(0),
            args: vec![],
        },
        Inst::CallIndirectCannotUnwind {
            callee: v(0),
            sig: FuncTyId::new(0),
            args: vec![],
            calling_conv: trust_ir::CallingConv::C,
        },
        // Amendment D: the unwinding twin of a drop.
        Inst::DropInvoke {
            ty: Ty::I64,
            ptr: v(0),
            normal_dest: b(1),
            normal_args: vec![v(10)],
            unwind_dest: b(2),
        },
        // Amendment D, Part 2: the unwinding twin of an indirect call.
        Inst::InvokeIndirect {
            callee: v(0),
            sig: FuncTyId::new(0),
            args: vec![v(1)],
            calling_conv: trust_ir::CallingConv::C,
            normal_dest: b(1),
            normal_args: vec![v(10)],
            unwind_dest: b(2),
        },
        // PKG-U13a: a pure value op over two tensors; it leaves by falling
        // through.
        Inst::TensorContract {
            ty: Ty::Tensor(Box::new(Ty::I64), 2),
            lhs: v(0),
            rhs: v(1),
            batch: vec![],
            contract: vec![(1, 0)],
        },
        // PKG-U13c: pure value ops over tensors; each leaves by falling
        // through.
        Inst::TensorMap {
            ty: Ty::Tensor(Box::new(Ty::I64), 2),
            args: vec![v(0), v(1)],
            body: vec![trust_ir::TensorMapNode::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: 0,
                rhs: 1,
            }],
        },
        Inst::TensorReduce {
            ty: Ty::Tensor(Box::new(Ty::I64), 1),
            src: v(0),
            op: trust_ir::TensorReduceOp::Add,
            axes: vec![1],
            order: trust_ir::TensorReduceOrder::RowMajor,
        },
        Inst::TensorView {
            ty: Ty::Tensor(Box::new(Ty::I64), 1),
            src: v(0),
            params: vec![],
            exprs: vec![
                trust_ir::TensorIndexExpr::SrcExtent(0),
                trust_ir::TensorIndexExpr::Coord(0),
            ],
            shape: vec![0],
            index: vec![1],
            fill: None,
        },
        // PKG-U13d: likewise the gather and the scatter.
        Inst::TensorGather {
            ty: Ty::Tensor(Box::new(Ty::I64), 1),
            data: v(0),
            coords: vec![v(1)],
        },
        Inst::TensorScatter {
            ty: Ty::Tensor(Box::new(Ty::I64), 1),
            init: v(0),
            src: v(1),
            coords: vec![v(2)],
        },
    ]
}

/// The edges each terminator must answer, in canonical order, written out
/// independently of the accessor; empty for a shape with no edges.
fn expected_edges(inst: &Inst) -> Vec<(BlockId, Vec<ValueId>, EdgeKind)> {
    use EdgeKind::{Normal, Unwind};
    match inst.shape() {
        InstShape::Br => vec![(b(1), vec![v(10)], Normal)],
        InstShape::CondBr => vec![
            (b(1), vec![v(10)], Normal),
            (b(2), vec![v(11), v(12)], Normal),
        ],
        // Cases in order, THEN the default (the order `edge_dominates`
        // numbers).
        InstShape::Switch => vec![
            (b(1), vec![v(10)], Normal),
            (b(2), vec![], Normal),
            (b(3), vec![v(13)], Normal),
        ],
        InstShape::Invoke
        | InstShape::AssertInvoke
        | InstShape::DropInvoke
        | InstShape::InvokeIndirect => {
            vec![(b(1), vec![v(10)], Normal), (b(2), vec![], Unwind)]
        }
        _ => vec![],
    }
}

fn owned(edges: &[Edge<'_>]) -> Vec<(BlockId, Vec<ValueId>, EdgeKind)> {
    edges
        .iter()
        .map(|edge| (edge.target, edge.args.to_vec(), edge.kind))
        .collect()
}

#[test]
fn successor_edges_is_exhaustive_and_matches_every_cfg_walk() {
    let samples = sample_of_every_instruction();

    // The sample covers EVERY shape exactly once, so a new variant without a
    // sample fails here even though it compiled.
    let mut shapes: Vec<InstShape> = samples.iter().map(Inst::shape).collect();
    shapes.sort_by_key(|shape| shape.name());
    shapes.dedup();
    assert_eq!(shapes.len(), samples.len(), "a shape is sampled twice");
    assert_eq!(
        shapes.len(),
        InstShape::ALL.len(),
        "every InstShape needs a sample here; sampled {shapes:?}"
    );

    for inst in &samples {
        let edges = inst.successor_edges();
        let name = inst.shape().name();

        // A non-terminator leaves its block by falling through: no edges.
        if !inst.is_terminator() {
            assert!(edges.is_empty(), "{name} is not a terminator but has edges");
        }

        // The exact edges, read field by field.
        assert_eq!(owned(&edges), expected_edges(inst), "{name}: wrong edges");

        // `unwind_dest` is exactly the target of the one unwind edge, and an
        // unwind edge carries no arguments.
        let unwind: Vec<&Edge<'_>> = edges
            .iter()
            .filter(|edge| edge.kind == EdgeKind::Unwind)
            .collect();
        assert!(unwind.len() <= 1, "{name}: more than one unwind edge");
        assert_eq!(
            inst.unwind_dest(),
            unwind.first().map(|edge| edge.target),
            "{name}: unwind_dest disagrees with its unwind edge"
        );
        assert!(unwind.iter().all(|edge| edge.args.is_empty()), "{name}");

        // Agreement with the public walk that reads these edges: the
        // dominator tree reaches exactly the listed targets, and numbers
        // the edges in the accessor's order (edge i dominates target i, and
        // only it, because every target here is distinct).
        if inst.is_terminator() {
            let function = function_ending_in(inst.clone(), &edges);
            let tree = DominatorTree::new(&function);
            assert!(tree.is_well_formed(), "{name}: the probe CFG is malformed");
            for (index, edge) in edges.iter().enumerate() {
                assert!(
                    tree.is_reachable(edge.target),
                    "{name}: edge {index} unreached"
                );
                for (other, target) in edges.iter().enumerate() {
                    assert_eq!(
                        tree.edge_dominates(b(0), index, target.target),
                        index == other,
                        "{name}: edge {index} vs target of edge {other}"
                    );
                }
            }
            assert!(
                !tree.is_reachable(b(9)),
                "{name}: an unreferenced block was reached"
            );
        }
    }
}

/// `bb0` ends in `terminator`; every edge target exists (a landing pad heads
/// an unwind target), and `bb9` is referenced by nothing.
fn function_ending_in(terminator: Inst, edges: &[Edge<'_>]) -> Function {
    let mut function = Function::new(FuncId::new(0), "probe", FuncTyId::new(0), b(0));
    let mut entry = Block::new(b(0));
    entry.body.push(InstrNode::new(terminator));
    function.blocks.push(entry);
    let mut targets: Vec<(BlockId, EdgeKind)> =
        edges.iter().map(|edge| (edge.target, edge.kind)).collect();
    targets.push((b(9), EdgeKind::Normal));
    for (target, kind) in targets {
        let mut block = Block::new(target);
        if kind == EdgeKind::Unwind {
            block.body.push(
                InstrNode::new(Inst::LandingPad {
                    is_cleanup: true,
                    catch_type_indices: vec![],
                })
                .with_results(vec![v(100 + target.index()), v(200 + target.index())]),
            );
        }
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        function.blocks.push(block);
    }
    function
}
