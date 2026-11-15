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
                phase: ExecutionPhase::CanonicalDigest,
                site: self.site,
                work,
                copy_bytes,
            })
            .map_err(Into::into)
    }
    pub(super) fn publication(&mut self) -> R {
        self.session
            .admit(ExecutionProgress {
                phase: ExecutionPhase::Publication,
                site: self.site,
                work: 1,
                copy_bytes: size_of::<Option<ProofCertificateRef>>(),
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
    fn reserve(&mut self, length: usize, capacity: usize, chunk: usize) -> R<Option<usize>> {
        self.admit(3, 3 * size_of::<usize>())?;
        let needed = length
            .checked_add(chunk)
            .ok_or(ObservedValueError::CapacityOverflow)?;
        if needed <= capacity {
            return Ok(None);
        }
        let requested = length
            .checked_mul(2)
            .and_then(|n| n.checked_add(chunk))
            .ok_or(ObservedValueError::CapacityOverflow)?;
        let images = requested
            .checked_add(capacity)
            .ok_or(ObservedValueError::CapacityOverflow)?;
        self.admit(images, images)?;
        Ok(Some(requested - length))
    }
    pub(super) fn append(&mut self, mut source: &[u8], out: &mut Vec<u8>) -> R {
        loop {
            self.admit(1, size_of::<usize>())?;
            if source.is_empty() {
                return Ok(());
            }
            let count = source.len().min(1024);
            if let Some(additional) = self.reserve(out.len(), out.capacity(), count)? {
                out.try_reserve_exact(additional)
                    .map_err(|_| ObservedValueError::AllocationFailed)?;
            }
            self.admit(count, count)?;
            out.extend_from_slice(&source[..count]);
            source = &source[count..];
        }
    }
    pub(super) fn text(&mut self, mut source: &str, out: &mut String) -> R {
        loop {
            self.admit(1, size_of::<usize>())?;
            if source.is_empty() {
                return Ok(());
            }
            let mut count = source.len().min(1024);
            loop {
                self.admit(1, 0)?;
                if source.is_char_boundary(count) {
                    break;
                }
                count -= 1;
            }
            if let Some(additional) = self.reserve(out.len(), out.capacity(), count)? {
                out.try_reserve_exact(additional)
                    .map_err(|_| ObservedValueError::AllocationFailed)?;
            }
            self.admit(count, count)?;
            out.push_str(&source[..count]);
            source = &source[count..];
        }
    }
    pub(super) fn step(&mut self, work: usize) {
        self.session.retirement_step(self.site, work);
    }
    pub(super) fn poll(&mut self) {
        self.session.retirement_poll(self.site);
    }
    pub(super) fn bytes(&mut self, mut value: Vec<u8>) {
        while !value.is_empty() {
            let count = value.len().min(1024);
            self.step(count.saturating_add(1));
            value.truncate(value.len() - count);
            self.poll();
        }
        self.step(size_of::<Vec<u8>>().saturating_add(1));
        drop(value);
        self.poll();
    }
    pub(super) fn string(&mut self, value: String) {
        self.step(
            value
                .len()
                .saturating_add(size_of::<String>())
                .saturating_add(1),
        );
        drop(value);
        self.poll();
    }
    pub(super) fn terminal(&self, error: ObservedValueError) -> ObservedValueError {
        // Keep a typed traversal result already held BEFORE cleanup. A later
        // observer refusal remains independently sticky in the same session.
        error
    }
}
