// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
pub(super) struct Writer<'s, 'o, O: ExecutionObserver> {
    pub(super) session: &'s mut ObservedSession<'o, O>,
    pub(super) site: ExecutionSite,
    pub(super) bytes: Vec<u8>,
}
impl<O: ExecutionObserver> Writer<'_, '_, O> {
    pub(super) fn admit(&mut self, work: usize, copy_bytes: usize) -> R {
        self.session
            .admit(ExecutionProgress {
                phase: ExecutionPhase::CanonicalSerialization,
                site: self.site,
                work,
                copy_bytes,
            })
            .map_err(Into::into)
    }
    pub(super) fn append(&mut self, source: &[u8]) -> R {
        self.admit(1, 0)?;
        for chunk in source.chunks(1024) {
            let needed = self
                .bytes
                .len()
                .checked_add(chunk.len())
                .ok_or(ObservedValueError::CapacityOverflow)?;
            if needed > self.bytes.capacity() {
                let requested = self
                    .bytes
                    .len()
                    .checked_mul(2)
                    .and_then(|n| n.checked_add(chunk.len()))
                    .ok_or(ObservedValueError::CapacityOverflow)?;
                let copies = requested
                    .checked_add(self.bytes.len())
                    .ok_or(ObservedValueError::CapacityOverflow)?;
                self.admit(copies, copies)?;
                self.bytes
                    .try_reserve_exact(requested - self.bytes.len())
                    .map_err(|_| ObservedValueError::AllocationFailed)?;
            }
            self.admit(chunk.len(), chunk.len())?;
            self.bytes.extend_from_slice(chunk);
        }
        Ok(())
    }
    pub(super) fn retire(&mut self) {
        self.session.retirement_step(self.site, 1);
        drop(take(&mut self.bytes));
        self.session.retirement_poll(self.site);
    }
    pub(super) fn publication(&mut self) -> R {
        self.session
            .admit(ExecutionProgress {
                phase: ExecutionPhase::Publication,
                site: self.site,
                work: 0,
                copy_bytes: 0,
            })
            .map_err(Into::into)
    }
    pub(super) fn terminal(&self, error: ObservedValueError) -> ObservedValueError {
        if self.session.first_refusal().is_some() {
            ObservedValueError::AdmissionRefused
        } else {
            error
        }
    }
}
