// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
use super::*;

pub(super) fn all() -> Vec<Inst> {
    let mut all = calls();
    all.extend(branches());
    all.extend(other());
    all
}
fn calls() -> Vec<Inst> {
    let site = PanicSite {
        entry: FuncId::new(9),
        location: PanicLocation::Value(v()),
    };
    vec![
        Inst::Call {
            callee: FuncId::new(9),
            args: vec![v()],
        },
        Inst::CallCannotUnwind {
            callee: FuncId::new(9),
            args: vec![v()],
        },
        Inst::CallIndirect {
            callee: v(),
            sig: FuncTyId::new(8),
            args: vec![v()],
            calling_conv: crate::CallingConv::C,
        },
        Inst::CallIndirectCannotUnwind {
            callee: v(),
            sig: FuncTyId::new(8),
            args: vec![v()],
            calling_conv: crate::CallingConv::C,
        },
        Inst::Invoke {
            callee: FuncId::new(9),
            args: vec![v()],
            normal_dest: BlockId::new(1),
            normal_args: vec![v()],
            unwind_dest: BlockId::new(2),
        },
        Inst::InvokeIndirect {
            callee: v(),
            sig: FuncTyId::new(8),
            args: vec![v()],
            calling_conv: crate::CallingConv::C,
            normal_dest: BlockId::new(1),
            normal_args: vec![v()],
            unwind_dest: BlockId::new(2),
        },
        Inst::Assert {
            cond: v(),
            kind: AssertKind::NullPtr,
            site: Some(site),
        },
        Inst::AssertInvoke {
            cond: v(),
            kind: AssertKind::DivByZero,
            site,
            normal_dest: BlockId::new(1),
            normal_args: vec![v()],
            unwind_dest: BlockId::new(2),
        },
    ]
}
fn branches() -> Vec<Inst> {
    vec![
        Inst::Br {
            target: BlockId::new(1),
            args: vec![v()],
        },
        Inst::CondBr {
            cond: v(),
            then_target: BlockId::new(1),
            then_args: vec![],
            else_target: BlockId::new(2),
            else_args: vec![v()],
        },
        Inst::Switch {
            value: v(),
            default: BlockId::new(1),
            default_args: vec![],
            exhaustive_enum_unreachable: false,
            cases: vec![SwitchCase {
                value: Constant::Int(0),
                target: BlockId::new(2),
                args: vec![v()],
            }],
        },
        Inst::Return { values: vec![v()] },
        Inst::Unreachable,
        Inst::CoroSuspend {
            frame: v(),
            state_slot: 1,
            next_state: 2,
            value: v(),
        },
        Inst::LandingPad {
            is_cleanup: true,
            catch_type_indices: vec![4, 4],
        },
        Inst::Resume { exn: v() },
    ]
}
fn other() -> Vec<Inst> {
    vec![
        Inst::Fence {
            ordering: Ordering::SeqCst,
        },
        Inst::NullPtr,
        Inst::GlobalAddr {
            global: GlobalId::new(8),
        },
        Inst::Assume { cond: v() },
        Inst::Borrow { ptr: v() },
        Inst::BorrowMut { ptr: v() },
        Inst::EndBorrow { borrow_ptr: v() },
        Inst::Retain { ptr: v() },
        Inst::Release { ptr: v() },
        Inst::IsUnique { ptr: v() },
        Inst::Dealloc { ptr: v() },
        Inst::MemCopy {
            dst: v(),
            src: v(),
            bytes: v(),
            overlap: true,
        },
        Inst::MemSet {
            dst: v(),
            byte: v(),
            bytes: v(),
        },
        Inst::BindSlot {
            frame: v(),
            slot: 1,
            value: v(),
        },
        Inst::CloseFrame { frame: v() },
        Inst::MakeClosure {
            ty: crate::value::ClosureTyId::new(8),
            func: FuncId::new(9),
            captures: vec![v()],
        },
    ]
}
