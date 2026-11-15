// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Exact retained ordinary exhaustive rule body. Only explicit borrow lifetimes
//! are added to its signature so pointer parity can retain the visitor refs.
use super::*;

pub(super) fn collect(instruction: &Inst) -> Vec<&Ty> {
    let mut types = Vec::new();
    visit_instruction_types(instruction, |ty| types.push(ty));
    types
}

fn visit_instruction_types<'a>(inst: &'a Inst, mut visit: impl FnMut(&'a Ty)) {
    match inst {
        // Trust (wave-DS): the dropped type is spelled inline and must be refined like any
        // other, or a refinement validator would never see it.
        Inst::Drop { ty, .. } | Inst::DropInvoke { ty, .. } => visit(ty),
        Inst::BinOp { ty, .. }
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
        | Inst::LoadSlot { ty, .. } => visit(ty),
        Inst::Cast { src_ty, dst_ty, .. } => {
            visit(src_ty);
            visit(dst_ty);
        }
        Inst::TensorMap { ty, body, .. } => {
            visit(ty);
            for node in body {
                for node_ty in node.types() {
                    visit(node_ty);
                }
            }
        }
        Inst::GEP { pointee_ty, .. } => visit(pointee_ty),
        Inst::PtrData { ptr_ty, .. } => visit(ptr_ty),
        Inst::PtrMetadata {
            ptr_ty,
            metadata_ty,
            ..
        }
        | Inst::PtrFromParts {
            ptr_ty,
            metadata_ty,
            ..
        } => {
            visit(ptr_ty);
            visit(metadata_ty);
        }
        Inst::OpenFrame { def } => {
            for slot in &def.slots {
                visit(&slot.ty);
            }
        }
        Inst::DialectOp(op) => {
            for ty in &op.result_tys {
                visit(ty);
            }
        }
        Inst::Fence { .. }
        | Inst::Br { .. }
        | Inst::CondBr { .. }
        | Inst::Switch { .. }
        | Inst::Call { .. }
        | Inst::MakeClosure { .. }
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
        // WS3.20: the bulk ops spell no type (byte-granular).
        | Inst::MemCopy { .. }
        | Inst::MemSet { .. }
        | Inst::BindSlot { .. }
        | Inst::CloseFrame { .. }
        | Inst::CoroSuspend { .. }
        | Inst::Invoke { .. }
        | Inst::InvokeIndirect { .. }
        | Inst::LandingPad { .. }
        | Inst::Resume { .. } => {}
    }
}
