// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;

enum BoxTag {
    Vector(u32),
    Tensor(u32),
    Ref,
    RefMut,
    PtrConst,
    PtrMut,
    Rc,
}
impl State<'_> {
    pub(super) fn boxed<O: ExecutionObserver>(
        &mut self,
        parent: &Ty,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        let tag = match parent {
            Ty::Vector(_, lanes) => BoxTag::Vector(*lanes),
            Ty::Tensor(_, rank) => BoxTag::Tensor(*rank),
            Ty::Ref(_) => BoxTag::Ref,
            Ty::RefMut(_) => BoxTag::RefMut,
            Ty::PtrConst(_) => BoxTag::PtrConst,
            Ty::PtrMut(_) => BoxTag::PtrMut,
            Ty::Rc(_) => BoxTag::Rc,
            _ => return Err(ObservedValueError::InvalidRange),
        };
        work.admit(2, size_of::<Ty>() * 2)?;
        // No fallible operation follows moving the owned child until it is
        // stored in values. Box allocation remains subject to allocator OOM.
        if let Some(child) = self.values.pop() {
            let child = Box::new(child);
            let value = match tag {
                BoxTag::Vector(lanes) => Ty::Vector(child, lanes),
                BoxTag::Tensor(rank) => Ty::Tensor(child, rank),
                BoxTag::Ref => Ty::Ref(child),
                BoxTag::RefMut => Ty::RefMut(child),
                BoxTag::PtrConst => Ty::PtrConst(child),
                BoxTag::PtrMut => Ty::PtrMut(child),
                BoxTag::Rc => Ty::Rc(child),
            };
            self.values.push(value);
            Ok(())
        } else {
            Err(ObservedValueError::InvalidRange)
        }
    }
    pub(super) fn tuple<O: ExecutionObserver>(
        &mut self,
        count: usize,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(1, 0)?;
        if count > self.values.len() || !self.tuple.is_empty() {
            return Err(ObservedValueError::InvalidRange);
        }
        work.reserve(&mut self.tuple, count)?;
        for _ in 0..count {
            work.admit(1, size_of::<Ty>())?;
            if let Some(value) = self.values.pop() {
                self.tuple.push(value);
            }
        }
        for left in 0..count / 2 {
            work.admit(1, size_of::<Ty>() * 2)?;
            self.tuple.swap(left, count - left - 1);
        }
        self.output_slot(work)?;
        self.values
            .push(Ty::Tuple(core::mem::take(&mut self.tuple)));
        Ok(())
    }
    pub(super) fn dialect<O: ExecutionObserver>(
        &mut self,
        source: &DialectTy,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        self.output_slot(work)?;
        work.text(&source.namespace, &mut self.first)?;
        work.text(&source.name, &mut self.second)?;
        work.admit(1, size_of::<DialectTy>())?;
        self.values.push(Ty::Dialect(Box::new(DialectTy {
            namespace: core::mem::take(&mut self.first),
            name: core::mem::take(&mut self.second),
            version: source.version,
        })));
        Ok(())
    }
    pub(super) fn handle<O: ExecutionObserver>(
        &mut self,
        source: &HandleTy,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        self.output_slot(work)?;
        work.text(&source.name, &mut self.first)?;
        work.text(&source.runtime, &mut self.second)?;
        work.admit(1, size_of::<HandleTy>())?;
        self.values.push(Ty::Handle(Box::new(HandleTy {
            name: core::mem::take(&mut self.first),
            runtime: core::mem::take(&mut self.second),
        })));
        Ok(())
    }
}
