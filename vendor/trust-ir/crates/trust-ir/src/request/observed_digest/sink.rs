// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
use core::mem::size_of;

const CHUNK: usize = 1024;

pub(super) struct Writer<'s, 'o, O: ExecutionObserver> {
    pub(super) session: &'s mut ObservedSession<'o, O>,
    pub(super) site: ExecutionSite,
    bytes: Vec<u8>,
}

impl<'s, 'o, O: ExecutionObserver> Writer<'s, 'o, O> {
    fn new(session: &'s mut ObservedSession<'o, O>, site: ExecutionSite) -> Result<Self> {
        session.admit(ExecutionProgress {
            phase: ExecutionPhase::CanonicalSerialization,
            site,
            work: 1,
            copy_bytes: size_of::<Self>(),
        })?;
        Ok(Self {
            session,
            site,
            bytes: Vec::new(),
        })
    }

    pub(super) fn admit(&mut self, work: usize, copy_bytes: usize) -> Result {
        self.session
            .admit(ExecutionProgress {
                phase: ExecutionPhase::CanonicalSerialization,
                site: self.site,
                work,
                copy_bytes,
            })
            .map_err(Into::into)
    }

    pub(super) fn poll(&mut self) -> Result {
        self.admit(1, 0)
    }

    pub(super) fn push(&mut self, byte: u8) -> Result {
        self.append(&[byte])
    }

    pub(super) fn append(&mut self, bytes: &[u8]) -> Result {
        self.poll()?;
        for chunk in bytes.chunks(CHUNK) {
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

    pub(super) fn reserve<T>(&mut self, values: &mut Vec<T>, additional: usize) -> Result {
        self.poll()?;
        let needed = values
            .len()
            .checked_add(additional)
            .ok_or(ObservedValueError::CapacityOverflow)?;
        if needed > values.capacity() {
            let requested = values
                .len()
                .checked_mul(2)
                .and_then(|n| n.checked_add(additional))
                .ok_or(ObservedValueError::CapacityOverflow)?;
            let copies = requested
                .checked_add(values.len())
                .ok_or(ObservedValueError::CapacityOverflow)?;
            let bytes = copies
                .checked_mul(size_of::<T>())
                .ok_or(ObservedValueError::CapacityOverflow)?;
            self.admit(copies, bytes)?;
            values
                .try_reserve_exact(requested - values.len())
                .map_err(|_| ObservedValueError::AllocationFailed)?;
        }
        Ok(())
    }

    pub(super) fn push_value<T>(&mut self, values: &mut Vec<T>, value: T) -> Result {
        self.reserve(values, 1)?;
        self.admit(1, size_of::<T>())?;
        values.push(value);
        Ok(())
    }

    pub(super) fn retire_value<T>(&mut self, value: T) {
        self.session.retirement_poll(self.site);
        drop(value);
        self.session.retirement_poll(self.site);
    }

    fn retire(&mut self) {
        self.session.retirement_poll(self.site);
        let bytes = core::mem::take(&mut self.bytes);
        drop(bytes);
        self.session.retirement_poll(self.site);
    }
}

impl<O: ExecutionObserver> Drop for Writer<'_, '_, O> {
    fn drop(&mut self) {
        if self.bytes.capacity() != 0 {
            self.retire();
        }
    }
}

pub(super) fn digest<O: ExecutionObserver>(
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
    domain: &str,
    write: impl FnOnce(&mut Writer<'_, '_, O>) -> Result,
) -> Result<ProofDigest> {
    let mut writer = Writer::new(session, site)?;
    let result = write(&mut writer).and_then(|()| {
        ProofDigest::sha256_domain_observed(domain, &writer.bytes, writer.session, site)
    });
    writer.retire();
    // Cleanup records its own stop, but cannot replace an already held error.
    let value = result?;
    writer.session.admit(ExecutionProgress {
        phase: ExecutionPhase::Publication,
        site,
        work: 0,
        copy_bytes: 0,
    })?;
    Ok(value)
}
