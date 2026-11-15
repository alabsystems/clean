// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[derive(Clone, Copy)]
enum Frame<'a> {
    Visit(&'a Ty),
    Children(&'a [Ty], usize),
}
#[derive(Default)]
pub(super) struct Inline<'a> {
    frames: Vec<Frame<'a>>,
}
impl<'a> Inline<'a> {
    pub(super) fn start<O: ExecutionObserver>(
        &mut self,
        root: &'a Ty,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(1, size_of::<Frame<'_>>())?;
        if !self.frames.is_empty() {
            return Err(ObservedValueError::InvalidRange);
        }
        work.push(&mut self.frames, Frame::Visit(root))
    }
    pub(super) fn next<O: ExecutionObserver>(
        &mut self,
        work: &mut Work<'_, '_, O>,
    ) -> R<Option<&'a Ty>> {
        loop {
            let Some(frame) = work.pop(&mut self.frames)? else {
                return Ok(None);
            };
            work.admit(42, 2 * size_of::<Frame<'_>>())?;
            match frame {
                Frame::Visit(ty) => {
                    match ty {
                        Ty::Storage(_) => {}
                        Ty::Vector(t, _)
                        | Ty::Tensor(t, _)
                        | Ty::Ref(t)
                        | Ty::RefMut(t)
                        | Ty::PtrConst(t)
                        | Ty::PtrMut(t)
                        | Ty::Rc(t) => work.push(&mut self.frames, Frame::Visit(t))?,
                        Ty::Tuple(items) => {
                            work.push(&mut self.frames, Frame::Children(items, 0))?
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
                    return Ok(Some(ty));
                }
                Frame::Children(items, index) => {
                    if let Some(ty) = work.at(items, index)? {
                        let mut next = index;
                        work.next(&mut next)?;
                        work.push(&mut self.frames, Frame::Children(items, next))?;
                        work.push(&mut self.frames, Frame::Visit(ty))?;
                    }
                }
            }
        }
    }
    pub(super) fn retire<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        work.retire_copy(&mut self.frames);
    }
}
