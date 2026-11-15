// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
use super::*;
impl State {
    pub(super) fn collect<O: ExecutionObserver>(
        &mut self,
        function: &Function,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(1, size_of::<usize>())?;
        let mut block_index = 0usize;
        loop {
            work.admit(1, size_of::<&crate::Block>())?;
            let Some(block) = function.blocks.get(block_index) else {
                return Ok(());
            };
            work.admit(1, size_of::<usize>())?;
            let mut node_index = 0usize;
            loop {
                work.admit(1, size_of::<&crate::InstrNode>())?;
                let Some(node) = block.body.get(node_index) else {
                    break;
                };
                if let Inst::Borrow { ptr } | Inst::BorrowMut { ptr } = &node.inst {
                    work.admit(1, size_of::<&[ValueId]>() + 2 * size_of::<u32>())?;
                    if let Some(result) = node.results.first() {
                        work.record(&mut self.operands, result.index(), ptr.index())?;
                    }
                }
                work.admit(1, size_of::<usize>())?;
                node_index = node_index
                    .checked_add(1)
                    .ok_or(ObservedValueError::CapacityOverflow)?;
            }
            work.admit(1, size_of::<usize>())?;
            block_index = block_index
                .checked_add(1)
                .ok_or(ObservedValueError::CapacityOverflow)?;
        }
    }
}
impl<O: ExecutionObserver> Work<'_, '_, O> {
    pub(super) fn record(&mut self, rows: &mut Vec<(u32, u32)>, result: u32, operand: u32) -> R {
        self.admit(1, size_of::<usize>())?;
        let mut position = 0usize;
        loop {
            self.admit(1, size_of::<(u32, u32)>())?;
            let Some(&(key, _)) = rows.get(position) else {
                break;
            };
            if key == result {
                self.admit(1, size_of::<u32>())?;
                rows[position].1 = operand;
                return Ok(());
            }
            if key > result {
                break;
            }
            self.admit(1, size_of::<usize>())?;
            position = position
                .checked_add(1)
                .ok_or(ObservedValueError::CapacityOverflow)?;
        }
        self.reserve(rows)?;
        self.admit(1, size_of::<(u32, u32)>())?;
        rows.push((result, operand));
        self.admit(1, size_of::<usize>())?;
        let mut cursor = rows.len() - 1;
        while cursor > position {
            self.admit(1, 2 * size_of::<(u32, u32)>())?;
            rows.swap(cursor - 1, cursor);
            cursor -= 1;
        }
        Ok(())
    }
    pub(super) fn operand(&mut self, rows: &[(u32, u32)], key: u32) -> R<Option<u32>> {
        self.admit(1, 2 * size_of::<usize>())?;
        let (mut lower, mut upper) = (0usize, rows.len());
        // The completed index is sorted/unique by record(). Binary search
        // observes every actual probe instead of scanning a chain's index
        // anew linearly at every hop. No library search hides traversal.
        while lower < upper {
            self.admit(3, 3 * size_of::<usize>() + size_of::<(u32, u32)>())?;
            let middle = lower + (upper - lower) / 2;
            let &(result, operand) = rows.get(middle).ok_or(ObservedValueError::InvalidRange)?;
            if result == key {
                return Ok(Some(operand));
            }
            if result > key {
                upper = middle;
            } else {
                lower = middle
                    .checked_add(1)
                    .ok_or(ObservedValueError::CapacityOverflow)?;
            }
        }
        Ok(None)
    }
}
