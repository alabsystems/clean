// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;

#[cfg(test)]
mod retirement;

enum Action<'q> {
    Enter(&'q Ty),
    Give,
}
enum Frame<'q> {
    Vector { elem: &'q Ty, lanes: u32 },
    Array { elem: TyId, len: u64 },
    Entry(Key),
    Aggregate(Aggregate<'q>),
    Enum(enums::Frame<'q>),
}

impl<O: ExecutionObserver> Work<'_, '_, O> {
    pub(super) fn walk<'q>(
        &mut self,
        table: &'q LayoutTable<'_>,
        root: &'q Ty,
    ) -> R<Arc<TyLayoutShape>> {
        let mut stack = Vec::new();
        let result = (|| {
            let mut action = Action::Enter(root);
            loop {
                self.poll()?;
                action = match action {
                    Action::Enter(ty) => self.enter(table, &mut stack, ty)?,
                    Action::Give if stack.is_empty() => {
                        return self
                            .value
                            .take()
                            .ok_or(Error::Resource(ObservedValueError::UnsupportedValue));
                    }
                    Action::Give => self.resume(table, &mut stack)?,
                };
            }
        })();
        self.retire_frames(stack);
        if let Err(stop) = self.poll() {
            match result {
                Ok(value) => self.retire_layout(value),
                Err(error) => self.retire_error(error),
            }
            return Err(stop);
        }
        result
    }

    fn retire_frames(&mut self, mut stack: Vec<Frame<'_>>) {
        loop {
            self.session
                .retirement_step(self.site, size_of::<Option<Frame<'_>>>().saturating_add(1));
            let Some(frame) = stack.pop() else { break };
            frame.retire(self);
        }
        self.session
            .retirement_step(self.site, size_of::<Vec<Frame<'_>>>().saturating_add(1));
        // The loop consumed every Aggregate/Enum owned payload even if stopped.
        drop(stack);
        self.session.retirement_poll(self.site);
    }

    fn enter<'q>(
        &mut self,
        table: &'q LayoutTable<'_>,
        stack: &mut Vec<Frame<'q>>,
        ty: &'q Ty,
    ) -> R<Action<'q>> {
        if let Some(layout) = self.leaf(table, ty)? {
            self.give(layout)?;
            return Ok(Action::Give);
        }
        let key = match ty {
            Ty::Vector(elem, lanes) => {
                self.push_frame(
                    stack,
                    Frame::Vector {
                        elem,
                        lanes: *lanes,
                    },
                )?;
                return Ok(Action::Enter(elem));
            }
            Ty::Array(elem, len) => {
                if table.module.types.get(elem.as_usize()).is_none() {
                    return Err(LayoutError::MissingType(*elem).into());
                }
                self.push_frame(
                    stack,
                    Frame::Array {
                        elem: *elem,
                        len: *len,
                    },
                )?;
                (2, elem.as_usize())
            }
            Ty::Refine(base, _) => {
                if table.module.types.get(base.as_usize()).is_none() {
                    return Err(LayoutError::UnsupportedTyShape(TyShape::Refine).into());
                }
                (2, base.as_usize())
            }
            Ty::Struct(id) => (
                0,
                self.definition(table, 0, id.index())?
                    .ok_or(LayoutError::MissingStruct(*id))?,
            ),
            Ty::Enum(id) => (
                1,
                self.definition(table, 1, id.index())?
                    .ok_or(LayoutError::EnumLayoutUnavailable(*id))?,
            ),
            Ty::Tuple(elems) => match self.tuple(table.module, ty)? {
                None if elems.is_empty() => {
                    let layout = self.arc(TyLayoutShape {
                        size_bits: 0,
                        align_bits: Some(8),
                        kind: TyLayoutKind::Unit,
                    })?;
                    self.give(layout)?;
                    return Ok(Action::Give);
                }
                None => return Err(LayoutError::UnsupportedTyShape(ty.shape()).into()),
                Some(_) if table.module.target_info.is_none() => {
                    return Err(LayoutError::TupleLayoutTargetMissing.into());
                }
                Some(index) => (3, index),
            },
            Ty::Closure(id) => match self.closure(table.module, *id)? {
                None => return Err(LayoutError::UnsupportedTyShape(ty.shape()).into()),
                Some(_) if table.module.target_info.is_none() => {
                    return Err(LayoutError::ClosureLayoutTargetMissing.into());
                }
                Some(index) => (4, index),
            },
            _ => return Err(LayoutError::UnsupportedTyShape(ty.shape()).into()),
        };
        self.open_node(table, stack, key)
    }

    fn open_node<'q>(
        &mut self,
        table: &'q LayoutTable<'_>,
        stack: &mut Vec<Frame<'q>>,
        key: Key,
    ) -> R<Action<'q>> {
        self.lookup(self.cache.len())?;
        self.admit(1, size_of::<Arc<TyLayoutShape>>())?;
        if let Some(value) = self.cache.get(&key).map(Arc::clone) {
            self.give(value)?;
            return Ok(Action::Give);
        }
        self.lookup(self.open.len())?;
        if self.open.contains(&key) {
            return Err(reentry(table.module, key).into());
        }
        self.tree::<Key, ()>(self.open.len())?;
        self.open.insert(key);
        if key.0 == 2 {
            self.push_frame(stack, Frame::Entry(key))?;
            return Ok(Action::Enter(&table.module.types[key.1]));
        }
        if key.0 == 1 {
            let frame = enums::Frame::begin(table, key.1, self)?;
            self.push_frame(stack, Frame::Enum(frame))?;
            return self.progress_enum(table, stack);
        }
        let aggregate = Aggregate::begin(table.module, key)?;
        if let Some(field) = aggregate.next() {
            self.push_frame(stack, Frame::Aggregate(aggregate))?;
            Ok(Action::Enter(field))
        } else {
            self.push_frame(stack, Frame::Aggregate(aggregate))?;
            self.finish_aggregate(stack)?;
            Ok(Action::Give)
        }
    }

    fn resume<'q>(
        &mut self,
        table: &'q LayoutTable<'_>,
        stack: &mut Vec<Frame<'q>>,
    ) -> R<Action<'q>> {
        self.admit(1, size_of::<Arc<TyLayoutShape>>())?;
        let layout = self
            .value
            .as_ref()
            .map(Arc::clone)
            .ok_or(ObservedValueError::UnsupportedValue)?;
        let result = self.resume_with_layout(table, stack, &layout);
        // give() may replace the held original. Retire the temporary explicitly
        // even on failure, so its final owned field payload is never dropped
        // by an unobserved return path.
        self.retire_layout(layout);
        if let Err(stop) = self.poll() {
            if let Err(error) = result {
                self.retire_error(error);
            }
            return Err(stop);
        }
        result
    }

    fn resume_with_layout<'q>(
        &mut self,
        table: &'q LayoutTable<'_>,
        stack: &mut Vec<Frame<'q>>,
        layout: &TyLayoutShape,
    ) -> R<Action<'q>> {
        let Some(frame) = stack.last_mut() else {
            return Ok(Action::Give);
        };
        match frame {
            Frame::Vector { elem, lanes } => {
                let shape = TyLayoutShape {
                    size_bits: layout
                        .size_bits
                        .checked_mul(u64::from(*lanes))
                        .ok_or(LayoutError::SizeOverflow)?,
                    align_bits: layout.align_bits,
                    kind: TyLayoutKind::Vector {
                        elem_shape: elem.shape(),
                        lanes: *lanes,
                        lane_bits: layout.size_bits,
                    },
                };
                let value = self.arc(shape)?;
                self.give(value)?;
                self.pop_frame(stack);
            }
            Frame::Array { elem, len } => {
                let shape = TyLayoutShape {
                    size_bits: layout
                        .size_bits
                        .checked_mul(*len)
                        .ok_or(LayoutError::SizeOverflow)?,
                    align_bits: layout.align_bits,
                    kind: TyLayoutKind::Array {
                        elem: *elem,
                        len: *len,
                        stride_bits: layout.size_bits,
                    },
                };
                let value = self.arc(shape)?;
                self.give(value)?;
                self.pop_frame(stack);
            }
            Frame::Entry(key) => {
                let key = *key;
                self.record(key)?;
                self.pop_frame(stack);
            }
            Frame::Aggregate(aggregate) => {
                aggregate.take(layout, self)?;
                if let Some(field) = aggregate.next() {
                    return Ok(Action::Enter(field));
                }
                self.finish_aggregate(stack)?;
            }
            Frame::Enum(frame) => {
                frame.take(layout, self)?;
                return self.progress_enum(table, stack);
            }
        }
        self.poll()?;
        Ok(Action::Give)
    }

    fn progress_enum<'q>(
        &mut self,
        table: &'q LayoutTable<'_>,
        stack: &mut Vec<Frame<'q>>,
    ) -> R<Action<'q>> {
        let Some(Frame::Enum(frame)) = stack.last_mut() else {
            return Err(ObservedValueError::UnsupportedValue.into());
        };
        if let Some(field) = frame.next(self)? {
            return Ok(Action::Enter(field));
        }
        let index = frame.index;
        let shape = frame.finish(table.module, self)?;
        let size_bits = shape.size_bits;
        let align_bits = shape.align_bits;
        let id = shape.id;
        let variants = shape.discriminants.len();
        let shape = self.arc_enum(shape)?;
        self.cache_enum(index, shape)?;
        let layout = self.arc(TyLayoutShape {
            size_bits,
            align_bits: Some(align_bits),
            kind: TyLayoutKind::Enum { id, variants },
        })?;
        self.give(layout)?;
        self.record((1, index))?;
        self.pop_frame(stack);
        self.poll()?;
        Ok(Action::Give)
    }

    fn finish_aggregate(&mut self, stack: &mut Vec<Frame<'_>>) -> R {
        let Some(Frame::Aggregate(aggregate)) = stack.last_mut() else {
            return Err(ObservedValueError::UnsupportedValue.into());
        };
        let key = aggregate.key;
        let shape = aggregate.finish(self)?;
        let layout = self.arc(shape)?;
        self.give(layout)?;
        self.record(key)?;
        self.pop_frame(stack);
        self.poll()
    }

    fn record(&mut self, key: Key) -> R {
        self.lookup(self.cache.len())?;
        if self.cache.contains_key(&key) {
            return Err(ObservedValueError::UnsupportedValue.into());
        }
        self.tree::<Key, Arc<TyLayoutShape>>(self.cache.len())?;
        self.admit(1, size_of::<Arc<TyLayoutShape>>())?;
        let value = self
            .value
            .as_ref()
            .map(Arc::clone)
            .ok_or(ObservedValueError::UnsupportedValue)?;
        self.cache.insert(key, value);
        self.lookup(self.open.len())?;
        self.open.remove(&key);
        Ok(())
    }

    fn push_frame<'q>(&mut self, stack: &mut Vec<Frame<'q>>, frame: Frame<'q>) -> R {
        let result = self
            .reserve(stack)
            .and_then(|()| self.admit(1, size_of::<Frame<'_>>()));
        if let Err(error) = result {
            frame.retire(self);
            self.poll()?;
            return Err(error);
        }
        stack.push(frame);
        Ok(())
    }
    fn pop_frame(&mut self, stack: &mut Vec<Frame<'_>>) {
        if let Some(frame) = stack.pop() {
            frame.retire(self);
        }
    }

    pub(super) fn leaf(
        &mut self,
        table: &LayoutTable<'_>,
        ty: &Ty,
    ) -> R<Option<Arc<TyLayoutShape>>> {
        self.poll()?;
        if ty_uses_scalar_layout_table(ty) && !table.canonical_scalars {
            let triple = self.copy_text(
                table
                    .module
                    .target_info
                    .as_ref()
                    .map_or("", |target| target.triple.as_str()),
            )?;
            return Err(LayoutError::TargetScalarLayoutUnavailable { triple }.into());
        }
        // This helper is the original exhaustive constant-sized scalar arm:
        // no reference traversal, loop, field copy or heap allocation occurs.
        match leaf_layout(ty, table.pointer_bits) {
            Some(Ok(shape)) => Ok(Some(self.arc(shape)?)),
            Some(Err(error)) => Err(error.into()),
            None => Ok(None),
        }
    }

    pub(super) fn definition(
        &mut self,
        table: &LayoutTable<'_>,
        kind: u8,
        id: u32,
    ) -> R<Option<usize>> {
        self.lookup(self.definitions.len())?;
        if let Some(index) = self.definitions.get(&(kind, id)) {
            return Ok(Some(*index));
        }
        let count = if kind == 0 {
            table.module.structs.len()
        } else {
            table.module.enums.len()
        };
        while self.scanned[kind as usize] < count {
            self.poll()?;
            let index = self.scanned[kind as usize];
            self.scanned[kind as usize] += 1;
            let found = if kind == 0 {
                table.module.structs[index].id.index()
            } else {
                table.module.enums[index].id.index()
            };
            self.lookup(self.definitions.len())?;
            if !self.definitions.contains_key(&(kind, found)) {
                self.tree::<(u8, u32), usize>(self.definitions.len())?;
                self.definitions.insert((kind, found), index);
                if found == id {
                    return Ok(Some(index));
                }
            }
        }
        Ok(None)
    }

    fn tuple(&mut self, module: &Module, ty: &Ty) -> R<Option<usize>> {
        let mut found = None;
        for (index, desc) in module.tuple_layouts.iter().enumerate() {
            self.poll()?;
            let declared = module
                .types
                .get(desc.tuple_type.as_usize())
                .ok_or(LayoutError::MissingType(desc.tuple_type))?;
            if !matches!(declared, Ty::Tuple(_)) {
                return Err(LayoutError::TupleLayoutIncoherent(desc.tuple_type).into());
            }
            if equality::types(declared, ty, self)? {
                if found.is_some() {
                    return Err(LayoutError::TupleLayoutIncoherent(desc.tuple_type).into());
                }
                found = Some(index);
            }
        }
        Ok(found)
    }

    fn closure(&mut self, module: &Module, id: ClosureTyId) -> R<Option<usize>> {
        let mut found = None;
        for (index, desc) in module.closure_layouts.iter().enumerate() {
            self.poll()?;
            if module.closure_types.get(desc.closure.as_usize()).is_none() {
                return Err(LayoutError::ClosureLayoutIncoherent(desc.closure).into());
            }
            if desc.closure == id {
                if found.is_some() {
                    return Err(LayoutError::ClosureLayoutIncoherent(desc.closure).into());
                }
                found = Some(index);
            }
        }
        Ok(found)
    }
}

impl Frame<'_> {
    fn retire<O: ExecutionObserver>(self, work: &mut Work<'_, '_, O>) {
        match self {
            Self::Aggregate(aggregate) => aggregate.retire(work),
            Self::Enum(frame) => frame.retire(work),
            Self::Vector { elem, lanes } => work.retire_fixed((elem, lanes)),
            Self::Array { elem, len } => work.retire_fixed((elem, len)),
            Self::Entry(key) => work.retire_fixed(key),
        }
    }
}

fn reentry(module: &Module, key: Key) -> LayoutError {
    match key {
        (0, index) => LayoutError::StructLayoutIncoherent(module.structs[index].id),
        (1, index) => LayoutError::EnumLayoutUnavailable(module.enums[index].id),
        (2, index) => LayoutError::TyLayoutCycle(TyId::new(index as u32)),
        (3, index) => LayoutError::TupleLayoutIncoherent(module.tuple_layouts[index].tuple_type),
        (4, index) => LayoutError::ClosureLayoutIncoherent(module.closure_layouts[index].closure),
        _ => LayoutError::SizeOverflow,
    }
}
