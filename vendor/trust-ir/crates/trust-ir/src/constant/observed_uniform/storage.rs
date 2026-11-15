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
                phase: ExecutionPhase::Validation,
                site: self.site,
                work,
                copy_bytes,
            })
            .map_err(Into::into)
    }
    pub(super) fn publication(&mut self, bytes: usize) -> R {
        self.session
            .admit(ExecutionProgress {
                phase: ExecutionPhase::Publication,
                site: self.site,
                work: usize::from(bytes != 0),
                copy_bytes: bytes,
            })
            .map_err(Into::into)
    }
    pub(super) fn at<'a, T>(&mut self, rows: &'a [T], at: usize) -> R<Option<&'a T>> {
        self.admit(1, size_of::<Option<&T>>())?;
        Ok(rows.get(at))
    }
    pub(super) fn next(&mut self, at: &mut usize) -> R {
        self.admit(1, size_of::<usize>())?;
        *at = at
            .checked_add(1)
            .ok_or(ObservedValueError::CapacityOverflow)?;
        Ok(())
    }
    pub(super) fn step(&mut self, work: usize) {
        self.session.retirement_step(self.site, work);
    }
    pub(super) fn poll(&mut self) {
        self.session.retirement_poll(self.site);
    }
    pub(super) fn terminal(&self, error: ObservedValueError) -> ObservedValueError {
        if self.session.first_refusal().is_some() {
            ObservedValueError::AdmissionRefused
        } else {
            error
        }
    }
    pub(super) fn reserve<T>(&mut self, rows: &mut Vec<T>) -> R {
        self.admit(1, 0)?;
        if rows.len() == rows.capacity() {
            let requested = rows
                .len()
                .checked_mul(2)
                .and_then(|n| n.checked_add(1))
                .ok_or(ObservedValueError::CapacityOverflow)?;
            let images = requested
                .checked_add(rows.capacity())
                .ok_or(ObservedValueError::CapacityOverflow)?;
            self.admit(
                images,
                images
                    .checked_mul(size_of::<T>())
                    .ok_or(ObservedValueError::CapacityOverflow)?,
            )?;
            rows.try_reserve_exact(requested - rows.len())
                .map_err(|_| ObservedValueError::AllocationFailed)?;
        }
        Ok(())
    }
    pub(super) fn rows<T: Copy>(&mut self, mut rows: Vec<T>) {
        loop {
            self.step(size_of::<Option<T>>().saturating_add(1));
            if rows.pop().is_none() {
                break;
            }
        }
        self.step(size_of::<Vec<T>>().saturating_add(1));
        drop(rows);
        self.poll();
    }
    pub(super) fn retire<T>(&mut self, value: T) {
        self.step(size_of::<T>().saturating_add(1));
        drop(value);
        self.poll();
    }
    pub(super) fn lookup(&mut self, len: usize) -> R {
        let n = observed_btree::population_work(len)?
            .checked_mul(64)
            .ok_or(ObservedValueError::CapacityOverflow)?;
        self.admit(n, 0)
    }
    pub(super) fn insertion(&mut self, len: usize) -> R {
        let cost = observed_btree::insertion_cost::<[u8; 32], Vec<usize>>(len)?;
        self.admit(
            cost.work
                .checked_mul(64)
                .ok_or(ObservedValueError::CapacityOverflow)?,
            cost.copy_bytes,
        )
    }
    pub(super) fn bytes_equal(&mut self, a: &[u8], b: &[u8]) -> R<bool> {
        self.admit(2, size_of::<bool>())?;
        if a.len() != b.len() {
            return Ok(false);
        }
        let mut at = 0;
        loop {
            self.admit(1, size_of::<usize>())?;
            if at == a.len() {
                return Ok(true);
            }
            let end = at
                .checked_add((a.len() - at).min(1024))
                .ok_or(ObservedValueError::CapacityOverflow)?;
            self.admit(end - at, end - at)?;
            if a[at..end] != b[at..end] {
                return Ok(false);
            }
            at = end;
        }
    }
}
