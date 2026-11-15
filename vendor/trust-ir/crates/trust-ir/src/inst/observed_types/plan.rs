// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
use super::*;

#[derive(Clone, Copy)]
pub(super) enum Plan<'a> {
    One(&'a Ty),
    Pair(&'a Ty, &'a Ty),
    Slots(&'a [BindingSlot]),
    Types(&'a [Ty]),
    /// A tensor map's result type, then each body node's types in order.
    Map(&'a Ty, &'a [crate::TensorMapNode<crate::level::NoExt>]),
    Empty,
}

pub(super) fn for_instruction(instruction: &Inst) -> Plan<'_> {
    match instruction {
        Inst::Drop { ty, .. }
        | Inst::DropInvoke { ty, .. }
        | Inst::BinOp { ty, .. }
        | Inst::SeqMapAddK { ty, .. }
        | Inst::SeqMapNot { ty, .. }
        | Inst::SeqMap { ty, .. }
        | Inst::UnOp { ty, .. }
        | Inst::Overflow { ty, .. }
        | Inst::ICmp { ty, .. }
        | Inst::FCmp { ty, .. }
        | Inst::Load { ty, .. }
        | Inst::Store { ty, .. }
        | Inst::Alloca { ty, .. }
        | Inst::HeapAlloc { ty, .. }
        | Inst::AtomicLoad { ty, .. }
        | Inst::AtomicStore { ty, .. }
        | Inst::AtomicRMW { ty, .. }
        | Inst::CmpXchg { ty, .. }
        | Inst::MakeAggregate { ty, .. }
        | Inst::ArraySplat { ty, .. }
        | Inst::TensorContract { ty, .. }
        | Inst::TensorReduce { ty, .. }
        | Inst::TensorView { ty, .. }
        | Inst::TensorGather { ty, .. }
        | Inst::TensorScatter { ty, .. }
        | Inst::ExtractField { ty, .. }
        | Inst::InsertField { ty, .. }
        | Inst::ExtractElement { ty, .. }
        | Inst::InsertElement { ty, .. }
        | Inst::Const { ty, .. }
        | Inst::Undef { ty }
        | Inst::Copy { ty, .. }
        | Inst::Select { ty, .. }
        | Inst::LoadSlot { ty, .. } => Plan::One(ty),
        Inst::Cast { src_ty, dst_ty, .. } => Plan::Pair(src_ty, dst_ty),
        Inst::GEP { pointee_ty, .. } => Plan::One(pointee_ty),
        Inst::PtrData { ptr_ty, .. } => Plan::One(ptr_ty),
        Inst::PtrMetadata {
            ptr_ty,
            metadata_ty,
            ..
        }
        | Inst::PtrFromParts {
            ptr_ty,
            metadata_ty,
            ..
        } => Plan::Pair(ptr_ty, metadata_ty),
        Inst::OpenFrame { def } => Plan::Slots(&def.slots),
        Inst::DialectOp(op) => Plan::Types(&op.result_tys),
        Inst::TensorMap { ty, body, .. } => Plan::Map(ty, body),
        // No wildcard: a new instruction must be explicitly classified.
        Inst::MakeClosure { .. }
        | Inst::Fence { .. }
        | Inst::Br { .. }
        | Inst::CondBr { .. }
        | Inst::Switch { .. }
        | Inst::Call { .. }
        | Inst::CallIndirect { .. }
        | Inst::CallCannotUnwind { .. }
        | Inst::CallIndirectCannotUnwind { .. }
        | Inst::Return { .. }
        | Inst::NullPtr
        | Inst::GlobalAddr { .. }
        | Inst::Assume { .. }
        | Inst::Assert { .. }
        | Inst::AssertInvoke { .. }
        | Inst::Unreachable
        | Inst::Borrow { .. }
        | Inst::BorrowMut { .. }
        | Inst::EndBorrow { .. }
        | Inst::Retain { .. }
        | Inst::Release { .. }
        | Inst::IsUnique { .. }
        | Inst::Dealloc { .. }
        | Inst::MemCopy { .. }
        | Inst::MemSet { .. }
        | Inst::BindSlot { .. }
        | Inst::CloseFrame { .. }
        | Inst::CoroSuspend { .. }
        | Inst::Invoke { .. }
        | Inst::InvokeIndirect { .. }
        | Inst::LandingPad { .. }
        | Inst::Resume { .. } => Plan::Empty,
    }
}
