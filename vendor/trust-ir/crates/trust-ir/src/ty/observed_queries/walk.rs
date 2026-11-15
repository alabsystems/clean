// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
impl<'a> State<'a> {
    pub(super) fn predicate<O: ExecutionObserver>(
        &mut self,
        ty: &'a Ty,
        which: Predicate,
        work: &mut Work<'_, '_, O>,
    ) -> R<bool> {
        work.admit(1, size_of::<bool>())?;
        let mut found = false;
        work.push(&mut self.frames, Frame::Visit(ty))?;
        while !self.frames.is_empty() {
            work.admit(41, size_of::<Frame<'_>>())?;
            match self.frames.pop().ok_or(ObservedValueError::InvalidRange)? {
                Frame::Tail(elements) => {
                    work.admit(1, 0)?;
                    if let Some((first, rest)) = elements.split_first() {
                        if !rest.is_empty() {
                            work.push(&mut self.frames, Frame::Tail(rest))?;
                        }
                        work.push(&mut self.frames, Frame::Visit(first))?;
                    }
                }
                Frame::Visit(ty) => {
                    work.admit(2, 0)?;
                    found |= match which {
                        Predicate::Handle => matches!(ty, Ty::Handle(_)),
                        Predicate::Dialect => matches!(ty, Ty::Dialect(_)),
                    };
                    // The original contains_* visitor NEVER short-circuits
                    // after found=true. Every later actual node still visits.
                    match ty {
                        Ty::Storage(_) => {}
                        Ty::Vector(inner, _)
                        | Ty::Tensor(inner, _)
                        | Ty::Ref(inner)
                        | Ty::RefMut(inner)
                        | Ty::PtrConst(inner)
                        | Ty::PtrMut(inner)
                        | Ty::Rc(inner) => work.push(&mut self.frames, Frame::Visit(inner))?,
                        Ty::Tuple(elements) => {
                            work.push(&mut self.frames, Frame::Tail(elements))?
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
                        | Ty::Handle(_) => {}
                        Ty::Ext(extension) => extension.unreachable(),
                    }
                }
            }
        }
        Ok(found)
    }
}
