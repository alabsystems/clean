// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
pub(super) struct Work<'s, 'o, O: ExecutionObserver> {
    pub session: &'s mut ObservedSession<'o, O>,
    pub site: ExecutionSite,
}
impl<O: ExecutionObserver> Work<'_, '_, O> {
    pub fn admit(&mut self, work: usize, copy_bytes: usize) -> R {
        self.session
            .admit(ExecutionProgress {
                phase: ExecutionPhase::Validation,
                site: self.site,
                work,
                copy_bytes,
            })
            .map_err(Into::into)
    }
    pub fn publication(&mut self, bytes: usize) -> R {
        self.session
            .admit(ExecutionProgress {
                phase: ExecutionPhase::Publication,
                site: self.site,
                work: 1,
                copy_bytes: bytes,
            })
            .map_err(Into::into)
    }
    pub fn reserve<T>(&mut self, rows: &mut Vec<T>) -> R {
        self.admit(1, size_of::<usize>())?;
        if rows.len() == rows.capacity() {
            let requested = rows
                .len()
                .checked_mul(2)
                .and_then(|n| n.checked_add(1))
                .ok_or(ObservedValueError::CapacityOverflow)?;
            let images = requested
                .checked_add(rows.len())
                .ok_or(ObservedValueError::CapacityOverflow)?;
            let bytes = images
                .checked_mul(size_of::<T>())
                .ok_or(ObservedValueError::CapacityOverflow)?;
            self.admit(
                images
                    .checked_add(bytes)
                    .ok_or(ObservedValueError::CapacityOverflow)?,
                bytes,
            )?;
            rows.try_reserve_exact(requested - rows.len())
                .map_err(|_| ObservedValueError::AllocationFailed)?;
        }
        Ok(())
    }
    pub fn text(&mut self, mut a: &[u8], mut b: &[u8]) -> R<bool> {
        self.admit(1, 2 * size_of::<&[u8]>())?;
        if a.len() != b.len() {
            return Ok(false);
        }
        loop {
            self.admit(1, size_of::<usize>())?;
            if a.is_empty() {
                return Ok(true);
            }
            let count = a.len().min(1024);
            self.admit(2 * count + 2, 2 * size_of::<&[u8]>())?;
            if a[..count] != b[..count] {
                return Ok(false);
            }
            a = &a[count..];
            b = &b[count..];
        }
    }
    pub fn copy_text(&mut self, source: &str) -> R<String> {
        self.admit(1, size_of::<String>() + size_of::<core::str::Chars<'_>>())?;
        let mut output = String::new();
        let result = (|| {
            self.admit(source.len(), source.len())?;
            output
                .try_reserve_exact(source.len())
                .map_err(|_| ObservedValueError::AllocationFailed)?;
            let mut chars = source.chars();
            loop {
                self.admit(1 + 2 * size_of::<char>(), size_of::<Option<char>>())?;
                let Some(ch) = chars.next() else {
                    return Ok(());
                };
                output.push(ch);
            }
        })();
        match result {
            Ok(()) => Ok(output),
            Err(error) => {
                self.retire_text(output);
                Err(error)
            }
        }
    }
    pub fn retire_text(&mut self, text: String) {
        self.session
            .retirement_step(self.site, size_of::<String>() + 1);
        drop(text);
        self.session.retirement_poll(self.site);
    }
    pub fn retire_rows<T>(&mut self, rows: &mut Vec<T>) {
        while !rows.is_empty() {
            self.session
                .retirement_step(self.site, size_of::<T>().saturating_add(1));
            drop(rows.pop());
        }
        self.session
            .retirement_step(self.site, size_of::<Vec<T>>() + 1);
        drop(core::mem::take(rows));
        self.session.retirement_poll(self.site);
    }
    pub fn terminal(&self, error: ObservedValueError) -> ObservedValueError {
        if self.session.first_refusal().is_some() {
            ObservedValueError::AdmissionRefused
        } else {
            error
        }
    }
}
