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
    pub(super) fn text(&mut self, left: &str, right: &str) -> R<bool> {
        self.admit(1, 2 * size_of::<usize>())?;
        if left.len() != right.len() {
            return Ok(false);
        }
        let mut index = 0usize;
        while index < left.len() {
            self.admit(3, 2 * size_of::<&[u8]>())?;
            let end = index.saturating_add(1024).min(left.len());
            self.admit(end - index, 0)?;
            if left.as_bytes()[index..end] != right.as_bytes()[index..end] {
                return Ok(false);
            }
            self.admit(1, size_of::<usize>())?;
            index = end;
        }
        Ok(true)
    }
    pub(super) fn optional_text(
        &mut self,
        left: &Option<String>,
        right: &Option<String>,
    ) -> R<bool> {
        self.admit(2, 2 * size_of::<Option<&str>>())?;
        match (left, right) {
            (Some(a), Some(b)) => self.text(a, b),
            (None, None) => Ok(true),
            (Some(_), None) | (None, Some(_)) => Ok(false),
        }
    }
    pub(super) fn at<'a, T>(&mut self, rows: &'a [T], index: usize) -> R<Option<&'a T>> {
        self.admit(1, size_of::<Option<&T>>())?;
        Ok(rows.get(index))
    }
    pub(super) fn next(&mut self, index: &mut usize) -> R {
        self.admit(1, size_of::<usize>())?;
        *index = index
            .checked_add(1)
            .ok_or(ObservedValueError::CapacityOverflow)?;
        Ok(())
    }
    pub(super) fn push<T: Copy>(&mut self, rows: &mut Vec<T>, row: T) -> R {
        self.admit(1, 0)?;
        if rows.len() == rows.capacity() {
            let requested = rows
                .len()
                .checked_mul(2)
                .and_then(|n| n.checked_add(1))
                .ok_or(ObservedValueError::CapacityOverflow)?;
            let images = requested
                .checked_add(rows.len())
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
        self.admit(1, size_of::<T>())?;
        rows.push(row);
        Ok(())
    }
    pub(super) fn step(&mut self, n: usize) {
        self.session.retirement_step(self.site, n);
    }
    pub(super) fn poll(&mut self) {
        self.session.retirement_poll(self.site);
    }
    pub(super) fn fixed<T: Copy>(&mut self, value: T) {
        self.step(size_of::<T>().saturating_add(1));
        let _ = value;
    }
    fn terminal(&self, error: ObservedValueError) -> ObservedValueError {
        if self.session.first_refusal().is_some() {
            ObservedValueError::AdmissionRefused
        } else {
            error
        }
    }
    pub(super) fn finish(&mut self, result: R<bool>) -> R<bool> {
        let answer = result.map_err(|e| self.terminal(e))?;
        self.session.admit(ExecutionProgress {
            phase: ExecutionPhase::Publication,
            site: self.site,
            work: 1,
            copy_bytes: size_of::<bool>(),
        })?;
        Ok(answer)
    }
}
