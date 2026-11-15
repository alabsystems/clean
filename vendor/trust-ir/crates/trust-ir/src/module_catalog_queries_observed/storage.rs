// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
pub(super) struct Work<'s, 'o, O: ExecutionObserver> {
    pub(super) session: &'s mut ObservedSession<'o, O>,
    pub(super) site: ExecutionSite,
}
impl<O: ExecutionObserver> Work<'_, '_, O> {
    pub(super) fn admit(&mut self, work: usize, copy_bytes: usize) -> R {
        self.session
            .admit(ExecutionProgress {
                phase: ExecutionPhase::ModuleLookup,
                site: self.site,
                work,
                copy_bytes,
            })
            .map_err(Into::into)
    }
    pub(super) fn lookup(&mut self, len: usize) -> R {
        self.admit(1, size_of::<usize>())?;
        self.admit(observed_btree::population_work(len)?, 0)
    }
    pub(super) fn publication(&mut self, copy_bytes: usize) -> R {
        self.session
            .admit(ExecutionProgress {
                phase: ExecutionPhase::Publication,
                site: self.site,
                work: usize::from(copy_bytes != 0),
                copy_bytes,
            })
            .map_err(Into::into)
    }
    pub(super) fn reserve(&mut self, rows: &mut Vec<u32>) -> R {
        self.admit(1, 0)?;
        if rows.len() == rows.capacity() {
            let wanted = rows
                .len()
                .checked_mul(2)
                .and_then(|n| n.checked_add(1))
                .ok_or(ObservedValueError::CapacityOverflow)?;
            let images = wanted
                .checked_add(rows.capacity())
                .ok_or(ObservedValueError::CapacityOverflow)?;
            self.admit(
                images,
                images
                    .checked_mul(size_of::<u32>())
                    .ok_or(ObservedValueError::CapacityOverflow)?,
            )?;
            rows.try_reserve_exact(wanted - rows.len())
                .map_err(|_| ObservedValueError::AllocationFailed)?;
        }
        Ok(())
    }
    pub(super) fn finish_roster(&mut self, result: R, output: Vec<u32>) -> R<Vec<u32>> {
        match result.and_then(|()| self.publication(size_of::<Vec<u32>>())) {
            Ok(()) => Ok(output),
            Err(error) => {
                self.rows(output);
                Err(self.terminal(error))
            }
        }
    }
    pub(super) fn terminal(&self, error: ObservedValueError) -> ObservedValueError {
        // A consuming cleanup refusal keeps the original session's first
        // cause but cannot replace a typed error already held by the query.
        error
    }
    pub(super) fn step(&mut self, work: usize) {
        self.session.retirement_step(self.site, work);
    }
    pub(super) fn poll(&mut self) {
        self.session.retirement_poll(self.site);
    }
    pub(super) fn rows<T: Copy>(&mut self, mut rows: Vec<T>) {
        loop {
            self.step(size_of::<Option<T>>() + 1);
            if rows.pop().is_none() {
                break;
            }
        }
        self.step(
            rows.capacity()
                .saturating_mul(size_of::<T>())
                .saturating_add(size_of::<Vec<T>>()),
        );
        drop(rows);
        self.poll();
    }
}
