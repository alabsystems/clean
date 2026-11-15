// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;

impl State<'_> {
    pub(super) fn solve<O: ExecutionObserver>(
        &mut self,
        entry: u32,
        work: &mut Work<'_, '_, O>,
    ) -> R<bool> {
        work.insert(&mut self.tree.immediate_dominator, entry, entry)?;
        let mut changed = true;
        while changed {
            work.poll()?;
            changed = false;
            for &block in &self.rpo {
                work.poll()?;
                if block == entry {
                    continue;
                }
                let mut candidate = None;
                let row = work
                    .row(&self.predecessors, block)?
                    .ok_or(ObservedValueError::InvalidRange)?;
                for &predecessor in row {
                    work.poll()?;
                    if work
                        .read(&self.tree.immediate_dominator, &predecessor)?
                        .is_none()
                    {
                        continue;
                    }
                    candidate = match candidate {
                        None => Some(predecessor),
                        Some(current) => intersect(
                            predecessor,
                            current,
                            &self.tree.immediate_dominator,
                            &self.rpo_number,
                            work,
                        )?,
                    };
                    if candidate.is_none() {
                        return Ok(false);
                    }
                }
                if let Some(candidate) = candidate
                    && work.read(&self.tree.immediate_dominator, &block)? != Some(candidate)
                {
                    work.insert(&mut self.tree.immediate_dominator, block, candidate)?;
                    changed = true;
                }
            }
        }
        Ok(self.tree.immediate_dominator.len() == self.tree.reachable.len())
    }
    pub(super) fn children<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) -> R {
        let mut dominators = work.entries(&self.tree.immediate_dominator)?;
        while let Some((&block, &parent)) = dominators.next(work)? {
            work.poll()?;
            if block != parent {
                work.append(&mut self.children, parent, block)?;
            }
        }
        // Stable adjacent insertion sort has observed comparisons and swaps,
        // without delegating a variable sort or moving an unobserved suffix.
        // It preserves the ordinary stable sort's RPO keys/ties; can be quadratic.
        let mut children = work.rows(&mut self.children)?;
        while let Some(row) = children.next(work)? {
            work.poll()?;
            for index in 1..row.len() {
                work.poll()?;
                let mut position = index;
                while position > 0 {
                    work.poll()?;
                    let left = work
                        .read(&self.rpo_number, &row[position - 1])?
                        .unwrap_or(usize::MAX);
                    let right = work
                        .read(&self.rpo_number, &row[position])?
                        .unwrap_or(usize::MAX);
                    if left <= right {
                        break;
                    }
                    work.admit(1, 2 * size_of::<u32>())?;
                    row.swap(position - 1, position);
                    position -= 1;
                }
            }
        }
        Ok(())
    }
    pub(super) fn tour<O: ExecutionObserver>(
        &mut self,
        entry: u32,
        work: &mut Work<'_, '_, O>,
    ) -> R<bool> {
        let mut timer = 0usize;
        work.insert(&mut self.tree.preorder, entry, timer)?;
        timer = timer
            .checked_add(1)
            .ok_or(ObservedValueError::CapacityOverflow)?;
        work.push(&mut self.frames, (entry, 0))?;
        while let Some((block, next)) = self.frames.last().copied() {
            work.poll()?;
            let child = work
                .row(&self.children, block)?
                .and_then(|row| row.get(next))
                .copied();
            if let Some(child) = child {
                if let Some(frame) = self.frames.last_mut() {
                    frame.1 = frame
                        .1
                        .checked_add(1)
                        .ok_or(ObservedValueError::CapacityOverflow)?;
                }
                if work.read(&self.tree.preorder, &child)?.is_none() {
                    work.insert(&mut self.tree.preorder, child, timer)?;
                    timer = timer
                        .checked_add(1)
                        .ok_or(ObservedValueError::CapacityOverflow)?;
                    work.push(&mut self.frames, (child, 0))?;
                }
            } else {
                work.insert(&mut self.tree.postorder, block, timer)?;
                timer = timer
                    .checked_add(1)
                    .ok_or(ObservedValueError::CapacityOverflow)?;
                self.frames.pop();
            }
        }
        Ok(self.tree.preorder.len() == self.tree.reachable.len()
            && self.tree.postorder.len() == self.tree.reachable.len())
    }
}

fn intersect<O: ExecutionObserver>(
    mut left: u32,
    mut right: u32,
    idom: &BTreeMap<u32, u32>,
    rpo: &BTreeMap<u32, usize>,
    work: &mut Work<'_, '_, O>,
) -> R<Option<u32>> {
    while left != right {
        work.poll()?;
        let Some(left_number) = work.read(rpo, &left)? else {
            return Ok(None);
        };
        let Some(right_number) = work.read(rpo, &right)? else {
            return Ok(None);
        };
        if left_number > right_number {
            let Some(parent) = work.read(idom, &left)? else {
                return Ok(None);
            };
            left = parent;
        } else {
            let Some(parent) = work.read(idom, &right)? else {
                return Ok(None);
            };
            right = parent;
        }
    }
    Ok(Some(left))
}
