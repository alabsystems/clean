// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

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
    pub(super) fn push(&mut self, values: &mut Vec<ValueId>, value: ValueId) -> R {
        self.admit(1, 0)?;
        if values.len() == values.capacity() {
            let requested = values
                .len()
                .checked_mul(2)
                .and_then(|n| n.checked_add(1))
                .ok_or(ObservedValueError::CapacityOverflow)?;
            let images = requested
                .checked_add(values.len())
                .ok_or(ObservedValueError::CapacityOverflow)?;
            self.admit(
                images,
                images
                    .checked_mul(size_of::<ValueId>())
                    .ok_or(ObservedValueError::CapacityOverflow)?,
            )?;
            values
                .try_reserve_exact(requested - values.len())
                .map_err(|_| ObservedValueError::AllocationFailed)?;
        }
        self.admit(1, size_of::<ValueId>())?;
        values.push(value);
        Ok(())
    }
    pub(super) fn publication(&mut self) -> R {
        self.session
            .admit(ExecutionProgress {
                phase: ExecutionPhase::Publication,
                site: self.site,
                work: 1,
                copy_bytes: size_of::<Vec<ValueId>>(),
            })
            .map_err(Into::into)
    }
    pub(super) fn retire<T>(&mut self, value: T) {
        self.session.retirement_step(self.site, 1);
        drop(value);
        self.session.retirement_poll(self.site);
    }
    pub(super) fn retire_values(&mut self, values: &mut Vec<ValueId>) {
        while !values.is_empty() {
            self.session.retirement_step(self.site, 1);
            let _ = values.pop();
        }
        self.retire(core::mem::take(values));
    }
    pub(super) fn terminal(&self, error: ObservedValueError) -> ObservedValueError {
        if self.session.first_refusal().is_some() {
            ObservedValueError::AdmissionRefused
        } else {
            error
        }
    }
}
