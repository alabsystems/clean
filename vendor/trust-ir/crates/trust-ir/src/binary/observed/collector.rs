// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
use crate::Constant;

enum TypeTask<'a> {
    Value(&'a Ty),
    Tail(&'a [Ty]),
}

pub(super) fn observed_collect_type_strings<O: ExecutionObserver>(
    ty: &Ty,
    pool: &mut Builder,
    out: &mut Output<'_, '_, O>,
) -> R {
    let mut tasks = Vec::new();
    let result = (|| {
        out.push_value(&mut tasks, TypeTask::Value(ty))?;
        while !tasks.is_empty() {
            out.poll()?;
            let Some(task) = tasks.pop() else { break };
            match task {
                TypeTask::Value(ty) => {
                    observed_collect_type_identity_strings(ty, pool, out)?;
                    match ty {
                        // The tensor element (v67) is an inline child, as a
                        // vector's is.
                        Ty::Vector(inner, _)
                        | Ty::Tensor(inner, _)
                        | Ty::Ref(inner)
                        | Ty::RefMut(inner)
                        | Ty::PtrConst(inner)
                        | Ty::PtrMut(inner)
                        | Ty::Rc(inner) => out.push_value(&mut tasks, TypeTask::Value(inner))?,
                        Ty::Tuple(rows) => out.push_value(&mut tasks, TypeTask::Tail(rows))?,
                        _ => {}
                    }
                }
                TypeTask::Tail(rows) => {
                    if let Some((first, rest)) = rows.split_first() {
                        if !rest.is_empty() {
                            out.push_value(&mut tasks, TypeTask::Tail(rest))?;
                        }
                        out.push_value(&mut tasks, TypeTask::Value(first))?;
                    }
                }
            }
        }
        Ok(())
    })();
    out.finish_child(result, tasks)
}

enum ConstantTask<'a> {
    Value(&'a Constant),
    Tail(&'a [Constant]),
    Fields(&'a [(String, Constant)]),
}

pub(super) fn observed_collect_constant_strings<O: ExecutionObserver>(
    constant: &Constant,
    pool: &mut Builder,
    out: &mut Output<'_, '_, O>,
) -> R {
    let mut tasks = Vec::new();
    let result = (|| {
        out.push_value(&mut tasks, ConstantTask::Value(constant))?;
        while !tasks.is_empty() {
            out.poll()?;
            let Some(task) = tasks.pop() else { break };
            match task {
                ConstantTask::Value(value) => constant_head(value, pool, out, &mut tasks)?,
                ConstantTask::Tail(rows) => {
                    if let Some((first, rest)) = rows.split_first() {
                        if !rest.is_empty() {
                            out.push_value(&mut tasks, ConstantTask::Tail(rest))?;
                        }
                        out.push_value(&mut tasks, ConstantTask::Value(first))?;
                    }
                }
                ConstantTask::Fields(rows) => {
                    if let Some(((name, value), rest)) = rows.split_first() {
                        if !rest.is_empty() {
                            out.push_value(&mut tasks, ConstantTask::Fields(rest))?;
                        }
                        pool.intern(name, out)?;
                        out.push_value(&mut tasks, ConstantTask::Value(value))?;
                    }
                }
            }
        }
        Ok(())
    })();
    out.finish_child(result, tasks)
}
fn constant_head<'a, O: ExecutionObserver>(
    value: &'a Constant,
    pool: &mut Builder,
    out: &mut Output<'_, '_, O>,
    tasks: &mut Vec<ConstantTask<'a>>,
) -> R {
    match value {
        Constant::Splat { elem, .. } => {
            pool.raise_to(ARRAY_SPLAT_FORMAT_VERSION);
            out.push_value(tasks, ConstantTask::Value(elem))?;
        }
        Constant::Aggregate(rows)
        | Constant::Array(rows)
        | Constant::Vector(rows)
        | Constant::Sequence(rows)
        | Constant::Set(rows) => out.push_value(tasks, ConstantTask::Tail(rows))?,
        Constant::Record(fields) => out.push_value(tasks, ConstantTask::Fields(fields))?,
        Constant::Closure { captures, .. } => {
            out.push_value(tasks, ConstantTask::Tail(captures))?
        }
        Constant::SymbolAddr { symbol, .. } => {
            pool.intern(symbol, out)?;
        }
        Constant::Uninit => pool.raise_to(UNINIT_LANE_FORMAT_VERSION),
        Constant::TensorBlob { .. } => pool.raise_to(TENSOR_BLOB_FORMAT_VERSION),
        _ => {}
    }
    Ok(())
}

pub(super) fn observed_collect_inst_strings<O: ExecutionObserver>(
    inst: &InstG<NoExt>,
    pool: &mut Builder,
    out: &mut Output<'_, '_, O>,
) -> R {
    out.poll()?;
    if matches!(inst, InstG::MakeClosure { .. }) {
        pool.raise_to(MAKE_CLOSURE_FORMAT_VERSION);
    }
    // v67: Inst tag 71 is read-gated, so a contraction raises the header even
    // before its (tensor) result type does below.
    if matches!(inst, InstG::TensorContract { .. }) {
        pool.raise_to(TENSOR_FORMAT_VERSION);
    }
    // v68: Inst tags 72..=74 are read-gated likewise.
    if matches!(
        inst,
        InstG::TensorMap { .. } | InstG::TensorReduce { .. } | InstG::TensorView { .. }
    ) {
        pool.raise_to(TENSOR_MAP_REDUCE_VIEW_FORMAT_VERSION);
    }
    // v69: Inst tags 75 and 76 are read-gated likewise.
    if matches!(
        inst,
        InstG::TensorGather { .. } | InstG::TensorScatter { .. }
    ) {
        pool.raise_to(TENSOR_GATHER_SCATTER_FORMAT_VERSION);
    }

    if matches!(
        inst,
        InstG::CallCannotUnwind { .. } | InstG::CallIndirectCannotUnwind { .. }
    ) {
        pool.raise_to(CALL_UNWIND_BOUNDARY_FORMAT_VERSION);
    }
    // Crystal lane (wave-DS): a module containing a drop is v47; one that does not is untouched.
    if matches!(inst, InstG::Drop { .. }) {
        pool.raise_to(DROP_INST_FORMAT_VERSION);
    }
    // v51: every INST wire batch tag is read-gated, so a module carrying one
    // raises the header; a module with none keeps its bytes.
    if carries_inst_wire_batch_member(inst) {
        pool.raise_to(INST_WIRE_BATCH_FORMAT_VERSION);
    }
    // Crystal lane (D3): a module containing a WEAK compare-exchange is v48; a module whose
    // compare-exchanges are all strong is untouched.
    if matches!(inst, InstG::CmpXchg { weak: true, .. }) {
        pool.raise_to(WEAK_CMPXCHG_FORMAT_VERSION);
    }
    // v52 (plan item P): a module carrying a KINDED assert (Inst tag 63) is
    // v52; one whose every assert is `Unspecified` keeps tag 29 and its bytes.
    if matches!(inst, InstG::Assert { kind, .. } if !kind.is_unspecified()) {
        pool.raise_to(ASSERT_KIND_FORMAT_VERSION);
    }
    // v54 (amendment P): a module carrying a panic site (Inst tag 66 or 67) is
    // v54; one without keeps its version and its bytes.
    if inst.panic_site().is_some() {
        pool.raise_to(PANIC_SITE_FORMAT_VERSION);
    }
    // v55 (amendment D): a module carrying a `DropInvoke` (Inst tag 68) is
    // v55; a plain `Drop` keeps tag 57 and v47.
    if matches!(inst, InstG::DropInvoke { .. }) {
        pool.raise_to(DROP_GLUE_FORMAT_VERSION);
    }
    // v56 (amendment D, Part 2): a module carrying an `InvokeIndirect` (Inst
    // tag 69) is v56; one without keeps its version and its bytes.
    if matches!(inst, InstG::InvokeIndirect { .. }) {
        pool.raise_to(UNWIND_TWINS_FORMAT_VERSION);
    }
    collect_instruction_types(inst, pool, out)?;

    // v45 (WS3.12): an indirect call site carries its own convention, so it
    // raises the writer exactly as a function's does.
    if let InstG::CallIndirect { calling_conv, .. }
    | InstG::CallIndirectCannotUnwind { calling_conv, .. }
    | InstG::InvokeIndirect { calling_conv, .. } = inst
        && calling_conv.is_abi_surface()
    {
        observed_raise_to_abi_surface(pool, out)?;
    }
    match inst {
        InstG::OpenFrame { def } => {
            pool.intern(&def.name, out)?;
            for slot in &def.slots {
                out.poll()?;
                pool.intern(&slot.name, out)?;
            }
        }
        InstG::DialectOp(op) => {
            pool.intern(&op.dialect, out)?;
            pool.intern(&op.op, out)?;
            for entry in &op.attrs {
                out.poll()?;
                pool.intern(&entry.name, out)?;
                if let crate::dialect::AttrValue::Str(s) = &entry.value {
                    pool.intern(s, out)?;
                }
            }
        }
        InstG::Const { value, .. } => {
            observed_collect_constant_strings(value, pool, out)?;
        }
        // v50: Inst tag 59 is read-gated, so it raises the header.
        InstG::ArraySplat { .. } => {
            pool.raise_to(ARRAY_SPLAT_FORMAT_VERSION);
        }
        InstG::Switch { cases, .. } => {
            for case in cases {
                out.poll()?;
                observed_collect_constant_strings(&case.value, pool, out)?;
            }
        }
        _ => {}
    }
    Ok(())
}

fn collect_instruction_types<O: ExecutionObserver>(
    inst: &InstG<NoExt>,
    pool: &mut Builder,
    out: &mut Output<'_, '_, O>,
) -> R {
    out.poll()?;
    match inst {
            // Trust (wave-DS): the dropped type is spelled here and must be walked, or a
            // splice would not remap a struct/enum id occurring only in a drop.
            InstG::Drop { ty, .. } | InstG::DropInvoke { ty, .. } => observed_collect_type_strings(ty, pool, out)?,
            InstG::BinOp { ty, .. }
            | InstG::SeqMapAddK { ty, .. }
            | InstG::SeqMapNot { ty, .. }
            | InstG::SeqMap { ty, .. }
            | InstG::UnOp { ty, .. }
            | InstG::Overflow { ty, .. }
            | InstG::ICmp { ty, .. }
            | InstG::FCmp { ty, .. }
            | InstG::Load { ty, .. }
            | InstG::Store { ty, .. }
            | InstG::Alloca { ty, .. }
            | InstG::HeapAlloc { ty, .. }
            | InstG::AtomicLoad { ty, .. }
            | InstG::AtomicStore { ty, .. }
            | InstG::AtomicRMW { ty, .. }
            | InstG::CmpXchg { ty, .. }
            | InstG::MakeAggregate { ty, .. }
            | InstG::ArraySplat { ty, .. }
            | InstG::TensorContract { ty, .. }
            | InstG::TensorReduce { ty, .. }
            | InstG::TensorView { ty, .. }
            | InstG::TensorGather { ty, .. }
            | InstG::TensorScatter { ty, .. }
            | InstG::ExtractField { ty, .. }
            | InstG::InsertField { ty, .. }
            | InstG::ExtractElement { ty, .. }
            | InstG::InsertElement { ty, .. }
            | InstG::Const { ty, .. }
            | InstG::Undef { ty }
            | InstG::Copy { ty, .. }
            | InstG::Select { ty, .. }
            | InstG::LoadSlot { ty, .. } => observed_collect_type_strings(ty, pool, out)?,
            InstG::Cast { src_ty, dst_ty, .. } => {
                observed_collect_type_strings(src_ty, pool, out)?;
                observed_collect_type_strings(dst_ty, pool, out)?;
            }
            // v68: the result type, then every type the body spells, in order.
            InstG::TensorMap { ty, body, .. } => {
                observed_collect_type_strings(ty, pool, out)?;
                for node in body {
                    for node_ty in node.types() {
                        observed_collect_type_strings(node_ty, pool, out)?;
                    }
                }
            }
            InstG::GEP { pointee_ty, .. } => observed_collect_type_strings(pointee_ty, pool, out)?,
            InstG::PtrData { ptr_ty, .. } => observed_collect_type_strings(ptr_ty, pool, out)?,
            InstG::PtrMetadata {
                ptr_ty,
                metadata_ty,
                ..
            }
            | InstG::PtrFromParts {
                ptr_ty,
                metadata_ty,
                ..
            } => {
                observed_collect_type_strings(ptr_ty, pool, out)?;
                observed_collect_type_strings(metadata_ty, pool, out)?;
            }
            InstG::OpenFrame { def } => {
                for slot in &def.slots {
        out.poll()?;
                    observed_collect_type_strings(&slot.ty, pool, out)?;
                }
            }
            InstG::DialectOp(op) => {
                for ty in &op.result_tys {
        out.poll()?;
                    observed_collect_type_strings(ty, pool, out)?;
                }
                for attr in &op.attrs {
        out.poll()?;
                    if let crate::dialect::AttrValue::Ty(ty) = &attr.value {
                        observed_collect_type_strings(ty, pool, out)?;
                    }
                }
            }
            InstG::Fence { .. }
            | InstG::Br { .. }
            | InstG::CondBr { .. }
            | InstG::Switch { .. }
            | InstG::Call { .. }
            | InstG::MakeClosure { .. }
            | InstG::CallIndirect { .. }
            | InstG::CallCannotUnwind { .. }
            | InstG::CallIndirectCannotUnwind { .. }
            | InstG::InvokeIndirect { .. }
            | InstG::Return { .. }
            | InstG::NullPtr
            | InstG::GlobalAddr { .. }
            | InstG::Assume { .. }
            | InstG::Assert { .. }
            | InstG::Unreachable
            | InstG::Borrow { .. }
            | InstG::BorrowMut { .. }
            | InstG::EndBorrow { .. }
            | InstG::Retain { .. }
            | InstG::Release { .. }
            | InstG::IsUnique { .. }
            | InstG::Dealloc { .. }
            // WS3.20: the bulk ops are byte-granular and spell no type.
            | InstG::MemCopy { .. }
            | InstG::MemSet { .. }
            | InstG::BindSlot { .. }
            | InstG::CloseFrame { .. }
            | InstG::CoroSuspend { .. }
            | InstG::Invoke { .. }
            | InstG::LandingPad { .. }
            | InstG::Resume { .. }
            | InstG::AssertInvoke { .. } => {}
        }
    Ok(())
}
