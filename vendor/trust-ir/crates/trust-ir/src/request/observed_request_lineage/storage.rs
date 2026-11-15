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
    pub(super) fn record(&mut self, work: usize, copy_bytes: usize) {
        self.session.retirement_record(self.site, work, copy_bytes);
    }
    pub(super) fn poll(&mut self) {
        self.session.retirement_poll(self.site);
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

    pub(super) fn equal<T: Copy + PartialEq>(&mut self, a: &T, b: &T) -> R<bool> {
        let images = size_of::<T>()
            .checked_mul(2)
            .ok_or(ObservedValueError::CapacityOverflow)?;
        self.admit(
            images
                .checked_add(2)
                .ok_or(ObservedValueError::CapacityOverflow)?,
            images
                .checked_add(size_of::<bool>())
                .ok_or(ObservedValueError::CapacityOverflow)?,
        )?;
        Ok(a == b)
    }
    pub(super) fn contains<T: Copy + PartialEq>(&mut self, rows: &[T], needle: &T) -> R<bool> {
        let mut at = 0;
        while let Some(row) = self.at(rows, at)? {
            if self.equal(row, needle)? {
                return Ok(true);
            }
            self.next(&mut at)?;
        }
        Ok(false)
    }
    pub(super) fn push<T: Copy>(&mut self, rows: &mut Vec<T>, value: &T) -> R {
        self.reserve(rows)?;
        self.admit(1, size_of::<T>())?;
        rows.push(*value);
        Ok(())
    }
    pub(super) fn insert<T: Copy + PartialEq>(&mut self, rows: &mut Vec<T>, value: &T) -> R<bool> {
        if self.contains(rows, value)? {
            return Ok(false);
        }
        self.push(rows, value)?;
        Ok(true)
    }
    pub(super) fn rows<T: Copy>(&mut self, rows: &mut Vec<T>) {
        self.record(1, size_of::<Vec<T>>());
        let mut owned = take(rows);
        loop {
            self.record(1, size_of::<Option<T>>());
            if owned.pop().is_none() {
                break;
            }
        }
        self.record(1, owned.capacity().saturating_mul(size_of::<T>()));
        drop(owned);
        self.poll();
    }
    pub(super) fn publish(&mut self, bytes: usize) -> R {
        self.session
            .admit(ExecutionProgress {
                phase: ExecutionPhase::Publication,
                site: self.site,
                work: 1,
                copy_bytes: bytes,
            })
            .map_err(Into::into)
    }
    pub(super) fn publish_bool(&mut self, value: bool) -> R<bool> {
        self.publish(size_of::<bool>())?;
        Ok(value)
    }
    pub(super) fn terminal(&mut self) -> R {
        self.session
            .admit(ExecutionProgress {
                phase: ExecutionPhase::Publication,
                site: self.site,
                work: 0,
                copy_bytes: 0,
            })
            .map_err(Into::into)
    }
}
