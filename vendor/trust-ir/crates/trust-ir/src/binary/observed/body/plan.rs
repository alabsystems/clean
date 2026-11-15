// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Stable block sort and first-definition dense IDs, no RandomState or opaque sort.
use super::*;
#[derive(Default)]
pub(in crate::binary::observed) struct Plan {
    pub(super) blocks: Vec<usize>,
    values: Vec<(ValueId, ValueId)>,
    defined: u32,
    pub(super) params: usize,
}
impl Plan {
    pub(super) fn build<O: ExecutionObserver>(
        &mut self,
        f: &Function,
        out: &mut Output<'_, '_, O>,
    ) -> R {
        // Stable insertion: an equal block ID follows all earlier equal IDs,
        // exactly sort_by_key's stable relation, including malformed duplicates.
        for (index, block) in f.blocks.iter().enumerate() {
            out.admit(2, size_of::<(usize, &Block)>())?;
            let mut at = 0usize;
            loop {
                out.admit(2, size_of::<usize>() + size_of::<Block>())?;
                let Some(old) = self.blocks.get(at) else {
                    break;
                };
                let prior = f.blocks.get(*old).ok_or(ObservedValueError::InvalidRange)?;
                if prior.id.index() > block.id.index() {
                    break;
                }
                at = at
                    .checked_add(1)
                    .ok_or(ObservedValueError::CapacityOverflow)?;
            }
            out.body_prepare::<usize>()?;
            out.reserve(&mut self.blocks, 1)?;
            let moved = self
                .blocks
                .len()
                .checked_sub(at)
                .ok_or(ObservedValueError::InvalidRange)?;
            let bytes = moved
                .checked_add(2)
                .and_then(|n| n.checked_mul(size_of::<usize>()))
                .ok_or(ObservedValueError::CapacityOverflow)?;
            out.admit(
                bytes
                    .checked_mul(2)
                    .and_then(|n| n.checked_add(3))
                    .ok_or(ObservedValueError::CapacityOverflow)?,
                bytes,
            )?;
            self.blocks.insert(at, index);
        }
        // All parameters across sorted blocks precede ALL instruction results.
        for at in 0..self.blocks.len() {
            out.admit(1, size_of::<usize>())?;
            let index = *self
                .blocks
                .get(at)
                .ok_or(ObservedValueError::InvalidRange)?;
            let block = f
                .blocks
                .get(index)
                .ok_or(ObservedValueError::InvalidRange)?;
            for (value, _) in &block.params {
                out.admit(1, size_of::<ValueId>())?;
                self.define(*value, out)?;
            }
        }
        for at in 0..self.blocks.len() {
            out.admit(1, size_of::<usize>())?;
            let index = *self
                .blocks
                .get(at)
                .ok_or(ObservedValueError::InvalidRange)?;
            let block = f
                .blocks
                .get(index)
                .ok_or(ObservedValueError::InvalidRange)?;
            for node in &block.body {
                out.admit(1, size_of::<&InstrNode>())?;
                for value in &node.results {
                    out.admit(1, size_of::<ValueId>())?;
                    self.define(*value, out)?;
                }
            }
        }
        out.admit(1, size_of::<u32>() + size_of::<usize>())?;
        self.defined = u32::try_from(self.values.len()).unwrap_or(u32::MAX);
        self.params = f.attrs.params.len();
        while self.params != 0 {
            out.admit(10 + size_of::<ParamAttrs>(), size_of::<usize>())?;
            let last = f
                .attrs
                .params
                .get(self.params - 1)
                .ok_or(ObservedValueError::InvalidRange)?;
            // Exactly9 fixed scalar/Option-presence fields; pass payload is not read.
            if !last.is_empty() {
                break;
            }
            self.params -= 1;
        }
        Ok(())
    }
    fn define<O: ExecutionObserver>(&mut self, value: ValueId, out: &mut Output<'_, '_, O>) -> R {
        for (old, _) in &self.values {
            out.admit(1 + size_of::<(ValueId, ValueId)>(), 0)?;
            if *old == value {
                return Ok(());
            }
        }
        let id =
            u32::try_from(self.values.len()).map_err(|_| ObservedValueError::CapacityOverflow)?;
        out.body_push(&mut self.values, (value, ValueId::new(id)))
    }
    pub(super) fn map<O: ExecutionObserver>(
        &self,
        value: ValueId,
        out: &mut Output<'_, '_, O>,
    ) -> R<ValueId> {
        for (old, dense) in &self.values {
            out.admit(1 + size_of::<(ValueId, ValueId)>(), 0)?;
            if *old == value {
                return Ok(*dense);
            }
        }
        Ok(value)
    }
    pub(super) fn binding<O: ExecutionObserver>(
        &self,
        value: ValueId,
        out: &mut Output<'_, '_, O>,
    ) -> R<ValueId> {
        for (old, dense) in &self.values {
            out.admit(1 + size_of::<(ValueId, ValueId)>(), 0)?;
            if *old == value {
                return Ok(*dense);
            }
        }
        out.admit(2, size_of::<ValueId>())?;
        if value.index() < self.defined {
            Ok(ValueId::new(self.defined.saturating_add(value.index())))
        } else {
            Ok(value)
        }
    }
    pub(super) fn retire<O: ExecutionObserver>(&mut self, out: &mut Output<'_, '_, O>) {
        while !self.blocks.is_empty() {
            out.body_retire(self.blocks.pop());
        }
        while !self.values.is_empty() {
            out.body_retire(self.values.pop());
        }
        out.body_retire(core::mem::take(&mut self.blocks));
        out.body_retire(core::mem::take(&mut self.values));
        out.body_retirement(size_of::<Self>() + 1, size_of::<Self>());
    }
}
