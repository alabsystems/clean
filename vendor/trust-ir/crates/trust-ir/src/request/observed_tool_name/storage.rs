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
                work: 1,
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
    pub(super) fn record(&mut self, work: usize, copy_bytes: usize) {
        self.session.retirement_record(self.site, work, copy_bytes);
    }
    pub(super) fn poll(&mut self) {
        self.session.retirement_poll(self.site);
    }
    pub(super) fn text(&mut self, mut source: &str, output: &mut String) -> R {
        loop {
            self.admit(1, size_of::<usize>())?;
            if source.is_empty() {
                return Ok(());
            }
            let mut end = source.len().min(1024);
            loop {
                self.admit(1, 0)?;
                if source.is_char_boundary(end) {
                    break;
                }
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
                    .and_then(|n| n.checked_add(chunk.len()))
                    .ok_or(ObservedValueError::CapacityOverflow)?;
                let images = requested
                    .checked_add(output.capacity())
                    .ok_or(ObservedValueError::CapacityOverflow)?;
                self.admit(images, images)?;
                output
                    .try_reserve_exact(requested - output.len())
                    .map_err(|_| ObservedValueError::AllocationFailed)?;
            }
            self.admit(chunk.len(), chunk.len())?;
            output.push_str(chunk);
            source = &source[end..];
        }
    }

    pub(super) fn equal(&mut self, a: &str, b: &str) -> R<bool> {
        self.admit(1, 2 * size_of::<usize>())?;
        if a.len() != b.len() {
            return Ok(false);
        }
        let mut at = 0;
        while at < a.len() {
            self.admit(1, 2 * size_of::<&[u8]>())?;
            let end = at.saturating_add(1024).min(a.len());
            self.admit(
                (end - at)
                    .checked_mul(2)
                    .ok_or(ObservedValueError::CapacityOverflow)?,
                0,
            )?;
            if a.as_bytes()[at..end] != b.as_bytes()[at..end] {
                return Ok(false);
            }
            self.admit(1, size_of::<usize>())?;
            at = end;
        }
        Ok(true)
    }

    pub(super) fn byte(&mut self, byte: u8, output: &mut String) -> R {
        self.admit(2, size_of::<u8>() + size_of::<usize>())?;
        if !byte.is_ascii() {
            return Err(ObservedValueError::InvalidRange);
        }
        let needed = output
            .len()
            .checked_add(1)
            .ok_or(ObservedValueError::CapacityOverflow)?;
        if needed > output.capacity() {
            let requested = output
                .len()
                .checked_mul(2)
                .and_then(|n| n.checked_add(1))
                .ok_or(ObservedValueError::CapacityOverflow)?;
            let images = requested
                .checked_add(output.capacity())
                .ok_or(ObservedValueError::CapacityOverflow)?;
            self.admit(images, images)?;
            output
                .try_reserve_exact(requested - output.len())
                .map_err(|_| ObservedValueError::AllocationFailed)?;
        }
        self.admit(1, 1)?;
        output.push(char::from(byte));
        Ok(())
    }
    pub(super) fn text_drop(&mut self, text: String) {
        self.record(1, size_of::<String>());
        self.record(1, text.capacity());
        drop(text);
        self.poll();
    }
}
