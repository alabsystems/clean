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
    pub(super) fn reserve<T>(&mut self, values: &mut Vec<T>, additional: usize) -> R {
        self.admit(1, 0)?;
        let needed = values
            .len()
            .checked_add(additional)
            .ok_or(ObservedValueError::CapacityOverflow)?;
        if needed > values.capacity() {
            let requested = values
                .len()
                .checked_mul(2)
                .and_then(|len| len.checked_add(additional))
                .ok_or(ObservedValueError::CapacityOverflow)?;
            let images = requested
                .checked_add(values.len())
                .ok_or(ObservedValueError::CapacityOverflow)?;
            self.admit(
                images,
                images
                    .checked_mul(size_of::<T>())
                    .ok_or(ObservedValueError::CapacityOverflow)?,
            )?;
            values
                .try_reserve_exact(requested - values.len())
                .map_err(|_| ObservedValueError::AllocationFailed)?;
        }
        Ok(())
    }
    pub(super) fn text(&mut self, mut source: &str, output: &mut String) -> R {
        while !source.is_empty() {
            self.admit(4, 0)?;
            let mut end = source.len().min(1024);
            while !source.is_char_boundary(end) {
                end -= 1;
            }
            let chunk = &source[..end];
            let needed = output
                .len()
                .checked_add(chunk.len())
                .ok_or(ObservedValueError::CapacityOverflow)?;
            if needed > output.capacity() {
                let requested = output
                    .len()
                    .checked_mul(2)
                    .and_then(|len| len.checked_add(chunk.len()))
                    .ok_or(ObservedValueError::CapacityOverflow)?;
                let bytes = requested
                    .checked_add(output.len())
                    .ok_or(ObservedValueError::CapacityOverflow)?;
                self.admit(bytes, bytes)?;
                output
                    .try_reserve_exact(requested - output.len())
                    .map_err(|_| ObservedValueError::AllocationFailed)?;
            }
            self.admit(chunk.len(), chunk.len())?;
            output.push_str(chunk);
            source = &source[end..];
        }
        Ok(())
    }
    pub(super) fn publication(&mut self) -> R {
        self.session
            .admit(ExecutionProgress {
                phase: ExecutionPhase::Publication,
                site: self.site,
                work: 1,
                copy_bytes: size_of::<Ty>(),
            })
            .map_err(Into::into)
    }
    pub(super) fn retire<T>(&mut self, value: T) {
        // Only borrowed tasks, strings and known-empty Vec<Ty> are passed.
        self.session.retirement_step(self.site, 1);
        drop(value);
        self.session.retirement_poll(self.site);
    }
    pub(super) fn terminal(&self, error: ObservedValueError) -> ObservedValueError {
        if self.session.first_refusal().is_some() {
            ObservedValueError::AdmissionRefused
        } else {
            error
        }
    }
}
