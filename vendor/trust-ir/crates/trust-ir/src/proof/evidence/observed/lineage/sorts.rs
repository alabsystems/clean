// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
use crate::proof::ClauseSort;
#[derive(Clone, Copy)]
enum Task<'a> {
    Sort(&'a ClauseSort),
    Constructors(&'a [(String, Vec<(String, ClauseSort)>)], usize),
    Fields(&'a [(String, ClauseSort)], usize),
}
#[derive(Default)]
pub(super) struct Machine<'a> {
    pending: Vec<Task<'a>>,
}
impl State {
    pub(super) fn sort<O: ExecutionObserver>(
        &mut self,
        root: &ClauseSort,
        w: &mut Work<'_, '_, O>,
    ) -> R {
        w.admit(1, size_of::<Machine<'_>>())?;
        let mut machine = Machine::default();
        let result = machine.run(self, root, w);
        machine.retire(w);
        result.and_then(|()| w.admit(1, 0))
    }
    fn sort_node<'a, O: ExecutionObserver>(
        &mut self,
        sort: &'a ClauseSort,
        pending: &mut Vec<Task<'a>>,
        w: &mut Work<'_, '_, O>,
    ) -> R {
        w.admit(32, size_of::<&ClauseSort>())?;
        match sort {
            ClauseSort::Bool => self.u8(0, w),
            ClauseSort::Int => self.u8(1, w),
            ClauseSort::BitVec(width) => {
                self.u8(2, w)?;
                self.u32(*width, w)
            }
            ClauseSort::Array(key, value) => {
                self.u8(3, w)?;
                push(pending, Task::Sort(value), w)?;
                push(pending, Task::Sort(key), w)
            }
            ClauseSort::Float { eb, sb } => {
                self.u8(4, w)?;
                self.u32(*eb, w)?;
                self.u32(*sb, w)
            }
            ClauseSort::RoundingMode => self.u8(5, w),
            ClauseSort::Datatype { name, constructors } => {
                self.u8(6, w)?;
                self.blob(name.as_bytes(), w)?;
                self.length(constructors.len(), w)?;
                push(pending, Task::Constructors(constructors, 0), w)
            }
        }
    }
}
impl<'a> Machine<'a> {
    pub(super) fn run<O: ExecutionObserver>(
        &mut self,
        state: &mut State,
        root: &'a ClauseSort,
        w: &mut Work<'_, '_, O>,
    ) -> R {
        push(&mut self.pending, Task::Sort(root), w)?;
        loop {
            w.admit(1, size_of::<Option<Task<'a>>>())?;
            let Some(task) = self.pending.pop() else {
                return Ok(());
            };
            match task {
                Task::Sort(sort) => state.sort_node(sort, &mut self.pending, w)?,
                Task::Constructors(rows, index) => {
                    if let Some((name, fields)) = w.at(rows, index)? {
                        state.blob(name.as_bytes(), w)?;
                        state.length(fields.len(), w)?;
                        let mut next = index;
                        w.next(&mut next)?;
                        push(&mut self.pending, Task::Constructors(rows, next), w)?;
                        push(&mut self.pending, Task::Fields(fields, 0), w)?;
                    }
                }
                Task::Fields(rows, index) => {
                    if let Some((name, sort)) = w.at(rows, index)? {
                        state.blob(name.as_bytes(), w)?;
                        let mut next = index;
                        w.next(&mut next)?;
                        push(&mut self.pending, Task::Fields(rows, next), w)?;
                        push(&mut self.pending, Task::Sort(sort), w)?;
                    }
                }
            }
        }
    }
    pub(super) fn retire<O: ExecutionObserver>(&mut self, w: &mut Work<'_, '_, O>) {
        loop {
            w.step(size_of::<Option<Task<'a>>>().saturating_add(1));
            if self.pending.pop().is_none() {
                break;
            }
        }
        w.step(size_of::<Vec<Task<'a>>>().saturating_add(1));
        drop(take(&mut self.pending));
        w.poll();
    }
    #[cfg(test)]
    pub(super) fn storage(&self) -> (usize, usize) {
        (self.pending.len(), self.pending.capacity())
    }
}
fn push<'a, O: ExecutionObserver>(
    rows: &mut Vec<Task<'a>>,
    value: Task<'a>,
    w: &mut Work<'_, '_, O>,
) -> R {
    w.admit(1, 0)?;
    if rows.len() == rows.capacity() {
        let wanted = rows
            .len()
            .checked_mul(2)
            .and_then(|n| n.checked_add(1))
            .ok_or(ObservedValueError::CapacityOverflow)?;
        let images = wanted
            .checked_add(rows.capacity())
            .ok_or(ObservedValueError::CapacityOverflow)?;
        w.admit(
            images,
            images
                .checked_mul(size_of::<Task<'a>>())
                .ok_or(ObservedValueError::CapacityOverflow)?,
        )?;
        rows.try_reserve_exact(wanted - rows.len())
            .map_err(|_| ObservedValueError::AllocationFailed)?;
    }
    w.admit(1, size_of::<Task<'a>>())?;
    rows.push(value);
    Ok(())
}
