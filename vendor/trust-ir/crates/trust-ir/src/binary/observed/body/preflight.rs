// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
use state::{TypeTask, append};
impl<'a> State<'a> {
    pub(super) fn drop_rows<O: ExecutionObserver>(
        &mut self,
        module: &'a Module,
        f: &'a Function,
        out: &mut Output<'_, '_, O>,
    ) -> R<bool> {
        for block in &f.blocks {
            out.poll()?;
            for node in &block.body {
                out.admit(1, 2 * size_of::<Option<&Ty>>())?;
                let ty = match &node.inst {
                    Inst::Drop { ty, .. } | Inst::DropInvoke { ty, .. } => ty,
                    _ => continue,
                };
                let mut hit = None;
                let mut ambiguous = false;
                for row in &module.drop_glue {
                    out.admit(1, size_of::<Option<FuncId>>())?;
                    if out.body_type_eq(ty, &row.ty)? {
                        if hit.is_some() {
                            ambiguous = true;
                        } else {
                            hit = Some(row.glue);
                        }
                    }
                }
                if ambiguous {
                    self.first_text = out.body_type_text(ty)?;
                    append(&mut self.reason, "function #", out)?;
                    state::decimal(&mut self.reason, f.id.index() as usize, out)?;
                    append(&mut self.reason, " drops ", out)?;
                    append(&mut self.reason, &self.first_text, out)?;
                    append(
                        &mut self.reason,
                        ", which two or more drop-glue rows name, so the body has no identity to state",
                        out,
                    )?;
                    return Ok(false);
                }
                let Some(glue) = hit else {
                    continue;
                };
                if !self.add_drop_row(f, ty, glue, out)? {
                    return Ok(false);
                }
            }
        }
        Ok(true)
    }
    fn add_drop_row<O: ExecutionObserver>(
        &mut self,
        f: &Function,
        ty: &'a Ty,
        glue: FuncId,
        out: &mut Output<'_, '_, O>,
    ) -> R<bool> {
        let mut duplicate = false;
        for row in &self.rows {
            out.admit(1 + size_of::<Row<'_>>(), 0)?;
            if row.glue != glue {
                continue;
            }
            if !out.body_type_eq(row.ty, ty)? {
                self.first_text = out.body_type_text(row.ty)?;
                self.second_text = out.body_type_text(ty)?;
                append(&mut self.reason, "function #", out)?;
                state::decimal(&mut self.reason, f.id.index() as usize, out)?;
                append(&mut self.reason, " drops ", out)?;
                append(&mut self.reason, &self.first_text, out)?;
                append(&mut self.reason, " and ", out)?;
                append(&mut self.reason, &self.second_text, out)?;
                append(&mut self.reason, " through the one glue @func.", out)?;
                state::decimal(&mut self.reason, glue.index() as usize, out)?;
                append(
                    &mut self.reason,
                    ", so the body has no identity to state",
                    out,
                )?;
                return Ok(false);
            }
            duplicate = true;
            break;
        }
        if duplicate {
            return Ok(true);
        }
        let mut at = 0usize;
        loop {
            out.admit(1 + size_of::<Option<Row<'_>>>(), 0)?;
            let Some(row) = self.rows.get(at) else {
                break;
            };
            if row.glue.index() >= glue.index() {
                break;
            }
            at = at
                .checked_add(1)
                .ok_or(ObservedValueError::CapacityOverflow)?;
        }
        out.body_prepare::<Row<'_>>()?;
        out.reserve(&mut self.rows, 1)?;
        let moved = self
            .rows
            .len()
            .checked_sub(at)
            .ok_or(ObservedValueError::InvalidRange)?;
        let bytes = moved
            .checked_add(2)
            .and_then(|n| n.checked_mul(size_of::<Row<'_>>()))
            .ok_or(ObservedValueError::CapacityOverflow)?;
        out.admit(
            bytes
                .checked_mul(2)
                .and_then(|n| n.checked_add(3))
                .ok_or(ObservedValueError::CapacityOverflow)?,
            bytes,
        )?;
        self.rows.insert(at, Row { glue, ty });
        Ok(true)
    }
    pub(super) fn spells_error<O: ExecutionObserver>(
        &mut self,
        f: &'a Function,
        out: &mut Output<'_, '_, O>,
    ) -> R<bool> {
        let mut found = false;
        for at in 0..self.rows.len() {
            out.admit(1, size_of::<Row<'_>>())?;
            let row = *self.rows.get(at).ok_or(ObservedValueError::InvalidRange)?;
            found |= self.type_error(row.ty, out)?;
        }
        for block in &f.blocks {
            out.poll()?;
            for (_, ty) in &block.params {
                out.poll()?;
                found |= self.type_error(ty, out)?;
            }
            for node in &block.body {
                out.poll()?;
                self.roots = out.body_inline_types(&node.inst)?;
                for at in 0..self.roots.len() {
                    out.admit(1, size_of::<&Ty>())?;
                    let ty = *self.roots.get(at).ok_or(ObservedValueError::InvalidRange)?;
                    found |= self.type_error(ty, out)?;
                }
                while !self.roots.is_empty() {
                    out.body_retire(self.roots.pop());
                }
                out.body_retire(core::mem::take(&mut self.roots));
                out.admit(1, size_of::<Option<&crate::dialect::DialectInst>>())?;
                if let Inst::DialectOp(op) = &node.inst {
                    for attr in &op.attrs {
                        out.poll()?;
                        if let crate::dialect::AttrValue::Ty(ty) = &attr.value {
                            found |= self.type_error(ty, out)?;
                        }
                    }
                }
            }
        }
        found |= self.attribute_types_error(f, out)?;
        Ok(found)
    }
    fn attribute_types_error<O: ExecutionObserver>(
        &mut self,
        f: &'a Function,
        out: &mut Output<'_, '_, O>,
    ) -> R<bool> {
        let mut found = false;
        for slot in f.attrs.params.iter().chain(core::iter::once(&f.attrs.ret)) {
            out.admit(1, size_of::<Option<&PassMode>>())?;
            if let Some(PassMode::Cast { pieces }) = &slot.pass {
                for ty in pieces {
                    out.poll()?;
                    found |= self.type_error(ty, out)?;
                }
            }
        }
        Ok(found)
    }
    fn type_error<O: ExecutionObserver>(
        &mut self,
        ty: &'a Ty,
        out: &mut Output<'_, '_, O>,
    ) -> R<bool> {
        out.body_push(&mut self.frames, TypeTask::Value(ty))?;
        let mut found = false;
        while !self.frames.is_empty() {
            out.admit(1, size_of::<Option<TypeTask<'_>>>())?;
            self.current = self.frames.pop();
            let Some(task) = self.current else {
                break;
            };
            out.admit(1 + size_of::<TypeTask<'_>>(), 0)?;
            match task {
                TypeTask::Value(ty) => {
                    found |= matches!(ty, Ty::Error);
                    match ty {
                        Ty::Storage(_) => {}
                        // The tensor element (v67) is an inline child, as a
                        // vector's is: an element spelling `Ty::Error` has
                        // no identity either.
                        Ty::Vector(inner, _)
                        | Ty::Tensor(inner, _)
                        | Ty::Ref(inner)
                        | Ty::RefMut(inner)
                        | Ty::PtrConst(inner)
                        | Ty::PtrMut(inner)
                        | Ty::Rc(inner) => {
                            out.body_push(&mut self.frames, TypeTask::Value(inner))?
                        }
                        Ty::Tuple(items) => {
                            out.body_push(&mut self.frames, TypeTask::Tail(items))?
                        }
                        Ty::I8
                        | Ty::I16
                        | Ty::I32
                        | Ty::I64
                        | Ty::I128
                        | Ty::U8
                        | Ty::U16
                        | Ty::U32
                        | Ty::U64
                        | Ty::U128
                        | Ty::Isize
                        | Ty::Usize
                        | Ty::Char
                        | Ty::Error
                        | Ty::F16
                        | Ty::F32
                        | Ty::F64
                        | Ty::Bool
                        | Ty::Ptr
                        | Ty::FatPtr(_)
                        | Ty::Unit
                        | Ty::Never
                        | Ty::Struct(_)
                        | Ty::Array(_, _)
                        | Ty::Enum(_)
                        | Ty::Func(_)
                        | Ty::Set(_, _)
                        | Ty::Sequence(_)
                        | Ty::Record(_)
                        | Ty::Closure(_)
                        | Ty::Refine(_, _)
                        | Ty::Dialect(_)
                        | Ty::Handle(_)
                        | Ty::Ext(_) => {}
                    }
                }
                TypeTask::Tail(items) => {
                    out.poll()?;
                    if let Some((first, rest)) = items.split_first() {
                        if !rest.is_empty() {
                            out.body_push(&mut self.frames, TypeTask::Tail(rest))?;
                        }
                        out.body_push(&mut self.frames, TypeTask::Value(first))?;
                    }
                }
            }
            out.body_retire(self.current.take());
        }
        Ok(found)
    }
}
