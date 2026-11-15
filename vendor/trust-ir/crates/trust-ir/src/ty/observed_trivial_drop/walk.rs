// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
impl<'a> State<'a> {
    pub(super) fn run<O: ExecutionObserver>(
        &mut self,
        ty: &'a Ty,
        types: &'a [Ty],
        work: &mut Work<'_, '_, O>,
    ) -> R<bool> {
        work.push(&mut self.stack, Frame::Visit(ty))?;
        loop {
            work.admit(1, size_of::<Option<Frame<'_>>>())?;
            let Some(frame) = self.stack.pop() else {
                return Ok(true);
            };
            work.admit(3, size_of::<Frame<'_>>())?;
            let ty = match frame {
                Frame::Exit(id) => {
                    let slot = self
                        .find(id, work)?
                        .ok_or(ObservedValueError::InvalidRange)?;
                    work.admit(1, size_of::<Mark>())?;
                    self.marks[slot].1 = Mark::Done;
                    continue;
                }
                Frame::Tail(elements) => {
                    work.admit(1, size_of::<Option<(&Ty, &[Ty])>>())?;
                    if let Some((last, rest)) = elements.split_last() {
                        work.push(&mut self.stack, Frame::Tail(rest))?;
                        work.push(&mut self.stack, Frame::Visit(last))?;
                    }
                    continue;
                }
                Frame::Visit(ty) => ty,
            };
            work.admit(3, size_of::<&Ty>())?;
            match ty {
                Ty::Storage(_) => return Ok(false),
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
                | Ty::F16
                | Ty::F32
                | Ty::F64
                | Ty::Bool
                | Ty::Unit
                | Ty::Never
                | Ty::Ptr
                | Ty::PtrConst(_)
                | Ty::PtrMut(_)
                | Ty::Ref(_)
                | Ty::RefMut(_)
                | Ty::FatPtr(_)
                | Ty::Func(_)
                | Ty::Vector(_, _) => {}
                Ty::Tuple(elements) => work.push(&mut self.stack, Frame::Tail(elements))?,
                Ty::Array(element, len) => {
                    work.admit(2, size_of::<u64>() + size_of::<u32>())?;
                    if *len == 0 {
                        continue;
                    }
                    if let Some(slot) = self.find(element.index(), work)? {
                        work.admit(1, size_of::<Mark>())?;
                        match self.marks[slot].1 {
                            Mark::Done => continue,
                            Mark::OnPath => return Ok(false),
                        }
                    }
                    work.admit(1, size_of::<Option<&Ty>>())?;
                    let Some(element_ty) = types.get(element.as_usize()) else {
                        return Ok(false);
                    };
                    work.push(&mut self.marks, (element.index(), Mark::OnPath))?;
                    work.push(&mut self.stack, Frame::Exit(element.index()))?;
                    work.push(&mut self.stack, Frame::Visit(element_ty))?;
                }
                Ty::Struct(_)
                | Ty::Enum(_)
                | Ty::Record(_)
                | Ty::Closure(_)
                | Ty::Rc(_)
                | Ty::Handle(_)
                | Ty::Dialect(_)
                | Ty::Sequence(_)
                | Ty::Set(_, _)
                | Ty::Tensor(_, _)
                | Ty::Refine(_, _)
                | Ty::Error => return Ok(false),
                Ty::Ext(e) => e.unreachable(),
            }
        }
    }
}
