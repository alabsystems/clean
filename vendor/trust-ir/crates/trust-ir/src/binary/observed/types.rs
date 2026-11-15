// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;

enum TypeTask<'a> {
    Value(&'a Ty),
    Tail(&'a [Ty]),
}

pub(super) fn observed_write_ty<O: ExecutionObserver>(
    buf: &mut Output<'_, '_, O>,
    pool: &SealedPool,
    ty: &Ty,
) -> R {
    let mut tasks = Vec::new();
    let result = (|| {
        buf.push_value(&mut tasks, TypeTask::Value(ty))?;
        while !tasks.is_empty() {
            buf.poll()?;
            let Some(task) = tasks.pop() else { break };
            match task {
                TypeTask::Value(ty) => type_head(buf, pool, ty, &mut tasks)?,
                TypeTask::Tail(rows) => {
                    if let Some((first, rest)) = rows.split_first() {
                        if !rest.is_empty() {
                            buf.push_value(&mut tasks, TypeTask::Tail(rest))?;
                        }
                        buf.push_value(&mut tasks, TypeTask::Value(first))?;
                    }
                }
            }
        }
        Ok(())
    })();
    buf.finish_child(result, tasks)
}

fn type_head<'a, O: ExecutionObserver>(
    buf: &mut Output<'_, '_, O>,
    pool: &SealedPool,
    ty: &'a Ty,
    tasks: &mut Vec<TypeTask<'a>>,
) -> R {
    buf.poll()?;

    match ty {
        TyG::Storage(layout) => {
            if !layout.is_well_formed(64) {
                buf.refuse(|| WireRefusal::InvalidStorageGeometry(*layout))?;
                return Ok(());
            }
            observed_write_u8(buf, 40)?;
            observed_write_v64(buf, layout.size_bytes)?;
            observed_write_v64(buf, layout.align_bytes)?;
        }
        TyG::I8 => observed_write_u8(buf, 0)?,
        TyG::I16 => observed_write_u8(buf, 1)?,
        TyG::I32 => observed_write_u8(buf, 2)?,
        TyG::I64 => observed_write_u8(buf, 3)?,
        TyG::I128 => observed_write_u8(buf, 4)?,
        TyG::U8 => observed_write_u8(buf, 5)?,
        TyG::U16 => observed_write_u8(buf, 6)?,
        TyG::U32 => observed_write_u8(buf, 7)?,
        TyG::U64 => observed_write_u8(buf, 8)?,
        TyG::U128 => observed_write_u8(buf, 9)?,
        // v25 B1 scalars (tags 33-35; Error is UNENCODABLE - see below).
        TyG::Isize => observed_write_u8(buf, 33)?,
        TyG::Usize => observed_write_u8(buf, 34)?,
        TyG::Char => observed_write_u8(buf, 35)?,
        // Ty::Error is producer-internal (a fail-closed typing placeholder)
        // with no wire spelling at any version; JSON and MessagePack can spell
        // one, so a decoded module CAN reach this arm. Refused here, by the
        // writer's own arm — never an invented tag for a typing hole.
        TyG::Error => buf.refuse(|| WireRefusal::ProducerInternalType)?,
        TyG::F16 => observed_write_u8(buf, 31)?,
        TyG::F32 => observed_write_u8(buf, 10)?,
        TyG::F64 => observed_write_u8(buf, 11)?,
        TyG::Bool => observed_write_u8(buf, 12)?,
        TyG::Ptr => observed_write_u8(buf, 13)?,
        TyG::Unit => observed_write_u8(buf, 14)?,
        TyG::Never => observed_write_u8(buf, 15)?,
        TyG::Struct(id) => {
            observed_write_u8(buf, 16)?;
            observed_write_struct_id(buf, *id)?;
        }
        TyG::Array(tid, len) => {
            observed_write_u8(buf, 17)?;
            observed_write_ty_id(buf, *tid)?;
            observed_write_v64(buf, *len)?;
        }
        TyG::Tuple(elems) => {
            observed_write_u8(buf, 18)?;
            observed_write_count(buf, "Ty::Tuple elements", elems.len())?;
            buf.push_value(tasks, TypeTask::Tail(elems))?;
        }
        TyG::Enum(id) => {
            observed_write_u8(buf, 19)?;
            observed_write_enum_id(buf, *id)?;
        }
        TyG::Func(id) => {
            observed_write_u8(buf, 20)?;
            observed_write_func_ty_id(buf, *id)?;
        }
        TyG::Ref(inner) => {
            observed_write_u8(buf, 21)?;
            buf.push_value(tasks, TypeTask::Value(inner))?;
        }
        TyG::RefMut(inner) => {
            observed_write_u8(buf, 22)?;
            buf.push_value(tasks, TypeTask::Value(inner))?;
        }
        TyG::PtrConst(inner) => {
            observed_write_u8(buf, 23)?;
            buf.push_value(tasks, TypeTask::Value(inner))?;
        }
        TyG::PtrMut(inner) => {
            observed_write_u8(buf, 24)?;
            buf.push_value(tasks, TypeTask::Value(inner))?;
        }
        TyG::Rc(inner) => {
            observed_write_u8(buf, 25)?;
            buf.push_value(tasks, TypeTask::Value(inner))?;
        }
        TyG::Set(elem, repr) => {
            observed_write_u8(buf, 26)?;
            observed_write_ty_id(buf, *elem)?;
            observed_write_set_repr(buf, repr)?;
        }
        TyG::Sequence(elem) => {
            observed_write_u8(buf, 27)?;
            observed_write_ty_id(buf, *elem)?;
        }
        TyG::Record(id) => {
            observed_write_u8(buf, 28)?;
            observed_write_record_id(buf, *id)?;
        }
        TyG::Closure(id) => {
            observed_write_u8(buf, 29)?;
            observed_write_closure_ty_id(buf, *id)?;
        }
        TyG::FatPtr(kind) => {
            observed_write_u8(buf, 30)?;
            observed_write_fat_ptr_kind(buf, pool, kind)?;
        }
        TyG::Vector(elem, lanes) => {
            observed_write_u8(buf, 32)?;
            observed_write_v32(buf, *lanes)?;
            buf.push_value(tasks, TypeTask::Value(elem))?;
        }
        // v30: refinement carrier. Representation-preserving — the base `TyId`
        // is what any consumer lays out; the `PredId` is proof surface.
        TyG::Refine(base, pred) => {
            observed_write_u8(buf, 36)?;
            observed_write_ty_id(buf, *base)?;
            observed_write_v32(buf, pred.index())?;
        }
        TyG::Dialect(ty) => {
            // Identity hashing may precede structural validation on untrusted
            // input. Encode the claim exactly; readers/validators reject its
            // malformed lexical identity rather than turning hashing into a
            // new panic boundary.
            observed_write_u8(buf, 37)?;
            observed_write_str(buf, pool, &ty.namespace)?;
            observed_write_str(buf, pool, &ty.name)?;
            observed_write_v32(buf, ty.version)?;
        }
        // v43. Encoded exactly as claimed (the reader/validator reject a
        // malformed pair) so identity hashing never becomes a panic boundary.
        TyG::Handle(ty) => {
            observed_write_u8(buf, 38)?;
            observed_write_str(buf, pool, &ty.name)?;
            observed_write_str(buf, pool, &ty.runtime)?;
        }
        // v67 (tensor region): the rank, then the inline element, as `Vector`
        // spells its lanes and element.
        TyG::Tensor(elem, rank) => {
            observed_write_u8(buf, 41)?;
            observed_write_v32(buf, *rank)?;
            buf.push_value(tasks, TypeTask::Value(elem))?;
        }
        TyG::Ext(e) => {
            e.unreachable();
        }
    }
    Ok(())
}
