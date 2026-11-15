// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
impl State<'_> {
    pub(super) fn width<O: ExecutionObserver>(
        &mut self,
        ty: &Ty,
        mode: Width,
        work: &mut Work<'_, '_, O>,
    ) -> R<Option<u32>> {
        work.admit(1, size_of::<&Ty>())?;
        let mut current = ty;
        let mut result = loop {
            work.admit(1, size_of::<&Ty>())?;
            if let Ty::Vector(inner, lanes) = current {
                work.push(&mut self.lanes, *lanes)?;
                current = inner;
            } else {
                break leaf(current, mode, work)?;
            }
        };
        while !self.lanes.is_empty() {
            work.admit(1, size_of::<u32>() + size_of::<Option<u32>>())?;
            let lanes = self.lanes.pop().ok_or(ObservedValueError::InvalidRange)?;
            // Inner overflow remains None even under a zero outer multiplier.
            // A forward accumulated product would incorrectly recover Some(0).
            if let Some(bits) = result {
                work.admit(1, size_of::<Option<u32>>())?;
                result = bits.checked_mul(lanes);
            }
        }
        Ok(result)
    }
}
fn leaf<O: ExecutionObserver>(ty: &Ty, mode: Width, work: &mut Work<'_, '_, O>) -> R<Option<u32>> {
    work.admit(41, size_of::<Option<u32>>())?;
    Ok(match ty {
        Ty::Storage(_) => None,
        Ty::Bool => Some(1),
        Ty::I8 | Ty::U8 => Some(8),
        Ty::I16 | Ty::U16 | Ty::F16 => Some(16),
        Ty::I32 | Ty::U32 | Ty::F32 | Ty::Char => Some(32),
        Ty::I64 | Ty::U64 | Ty::F64 => Some(64),
        Ty::I128 | Ty::U128 => Some(128),
        Ty::Ptr
        | Ty::PtrConst(_)
        | Ty::PtrMut(_)
        | Ty::Ref(_)
        | Ty::RefMut(_)
        | Ty::Rc(_)
        | Ty::Isize
        | Ty::Usize
        | Ty::Handle(_) => match mode {
            Width::Unresolved => None,
            Width::Pointer(bits) => Some(bits),
        },
        Ty::FatPtr(_) => match mode {
            Width::Unresolved => None,
            Width::Pointer(bits) => bits.checked_mul(2),
        },
        Ty::Error
        | Ty::Unit
        | Ty::Never
        | Ty::Struct(_)
        | Ty::Array(_, _)
        | Ty::Tuple(_)
        | Ty::Enum(_)
        | Ty::Func(_)
        | Ty::Set(_, _)
        | Ty::Sequence(_)
        | Ty::Record(_)
        | Ty::Closure(_)
        | Ty::Refine(_, _)
        | Ty::Dialect(_)
        | Ty::Tensor(_, _) => None,
        Ty::Vector(_, _) => return Err(ObservedValueError::InvalidRange),
        Ty::Ext(extension) => extension.unreachable(),
    })
}
