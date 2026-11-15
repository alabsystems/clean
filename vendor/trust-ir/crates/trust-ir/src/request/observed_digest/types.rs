// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;

// A lazy tail keeps the frontier proportional to nesting, not tuple width.
enum TyTask<'a> {
    Value(&'a Ty),
    Tail(&'a [Ty]),
}

pub(super) fn write_ty<O: ExecutionObserver>(out: &mut Writer<'_, '_, O>, ty: &Ty) -> Result {
    let mut tasks = Vec::new();
    let result: Result = (|| {
        out.push_value(&mut tasks, TyTask::Value(ty))?;
        while !tasks.is_empty() {
            out.poll()?;
            let Some(task) = tasks.pop() else { break };
            match task {
                TyTask::Value(ty) => write_head(out, ty, &mut tasks)?,
                TyTask::Tail(rows) => {
                    if let Some((first, rest)) = rows.split_first() {
                        if !rest.is_empty() {
                            out.push_value(&mut tasks, TyTask::Tail(rest))?;
                        }
                        out.push_value(&mut tasks, TyTask::Value(first))?;
                    }
                }
            }
        }
        Ok(())
    })();
    out.retire_value(tasks);
    result?;
    out.poll()
}

fn write_head<'a, O: ExecutionObserver>(
    out: &mut Writer<'_, '_, O>,
    ty: &'a Ty,
    tasks: &mut Vec<TyTask<'a>>,
) -> Result {
    out.poll()?;

    match ty {
        Ty::Storage(layout) => {
            write_u8(out, 40)?;
            write_u64(out, layout.size_bytes)?;
            write_u64(out, layout.align_bytes)?;
        }
        Ty::I8 => write_u8(out, 0)?,
        Ty::I16 => write_u8(out, 1)?,
        Ty::I32 => write_u8(out, 2)?,
        Ty::I64 => write_u8(out, 3)?,
        Ty::I128 => write_u8(out, 4)?,
        Ty::U8 => write_u8(out, 5)?,
        Ty::U16 => write_u8(out, 6)?,
        Ty::U32 => write_u8(out, 7)?,
        Ty::U64 => write_u8(out, 8)?,
        Ty::U128 => write_u8(out, 9)?,
        // v25 B1 scalars (stable tags match the binary codec's 33-35).
        Ty::Isize => write_u8(out, 33)?,
        Ty::Usize => write_u8(out, 34)?,
        Ty::Char => write_u8(out, 35)?,
        // Producer-internal typing placeholder: an obligation digest over a
        // module carrying Ty::Error would hash a typing hole - fail closed.
        Ty::Error => return Err(ObservedValueError::UnsupportedValue),
        Ty::F16 => write_u8(out, 31)?,
        Ty::F32 => write_u8(out, 10)?,
        Ty::F64 => write_u8(out, 11)?,
        Ty::Bool => write_u8(out, 12)?,
        Ty::Ptr => write_u8(out, 13)?,
        Ty::FatPtr(kind) => {
            write_u8(out, 14)?;
            write_fat_ptr_kind(out, kind)?;
        }
        Ty::Unit => write_u8(out, 15)?,
        Ty::Never => write_u8(out, 16)?,
        Ty::Struct(id) => {
            write_u8(out, 17)?;
            write_struct_id(out, *id)?;
        }
        Ty::Array(elem, len) => {
            write_u8(out, 18)?;
            write_ty_id(out, *elem)?;
            write_u64(out, *len)?;
        }
        Ty::Tuple(elems) => {
            write_u8(out, 19)?;
            write_len(out, elems.len())?;
            out.push_value(tasks, TyTask::Tail(elems))?;
        }
        Ty::Enum(id) => {
            write_u8(out, 20)?;
            write_enum_id(out, *id)?;
        }
        Ty::Func(id) => {
            write_u8(out, 21)?;
            write_func_ty_id(out, *id)?;
        }
        Ty::Ref(inner) => {
            write_u8(out, 22)?;
            out.push_value(tasks, TyTask::Value(inner))?;
        }
        Ty::RefMut(inner) => {
            write_u8(out, 23)?;
            out.push_value(tasks, TyTask::Value(inner))?;
        }
        Ty::PtrConst(inner) => {
            write_u8(out, 24)?;
            out.push_value(tasks, TyTask::Value(inner))?;
        }
        Ty::PtrMut(inner) => {
            write_u8(out, 25)?;
            out.push_value(tasks, TyTask::Value(inner))?;
        }
        Ty::Rc(inner) => {
            write_u8(out, 26)?;
            out.push_value(tasks, TyTask::Value(inner))?;
        }
        Ty::Set(elem, repr) => {
            write_u8(out, 27)?;
            write_ty_id(out, *elem)?;
            write_set_repr(out, *repr)?;
        }
        Ty::Sequence(elem) => {
            write_u8(out, 28)?;
            write_ty_id(out, *elem)?;
        }
        Ty::Record(id) => {
            write_u8(out, 29)?;
            write_record_id(out, *id)?;
        }
        Ty::Closure(id) => {
            write_u8(out, 30)?;
            write_closure_ty_id(out, *id)?;
        }
        // Compiler-facts v5 repairs the old Refine=33 / Isize=33 collision.
        // These are request-identity tags, not binary module codec tags.
        Ty::Refine(base, pred) => {
            write_u8(out, 37)?;
            write_ty_id(out, *base)?;
            write_u32(out, pred.index())?;
        }
        Ty::Vector(elem, lanes) => {
            write_u8(out, 32)?;
            write_u32(out, *lanes)?;
            out.push_value(tasks, TyTask::Value(elem))?;
        }
        Ty::Dialect(ty) => {
            // Nominal identities have no machine representation.
            write_u8(out, 36)?;
            write_str(out, &ty.namespace)?;
            write_str(out, &ty.name)?;
            write_u32(out, ty.version)?;
        }
        // v43: the pair IS the identity; deliberately not `Ptr`'s tag 13,
        // because a handle and a pointer must never hash equal.
        Ty::Handle(ty) => {
            write_u8(out, 38)?;
            write_str(out, &ty.name)?;
            write_str(out, &ty.runtime)?;
        }
        // PKG-U13a: tag 41, the rank, then the inline element (as `Vector`).
        Ty::Tensor(elem, rank) => {
            write_u8(out, 41)?;
            write_u32(out, *rank)?;
            out.push_value(tasks, TyTask::Value(elem))?;
        }
        Ty::Ext(e) => e.unreachable(),
    }
    Ok(())
}
