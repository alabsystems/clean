// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
impl<'a> State<'a> {
    pub(super) fn intern<O: ExecutionObserver>(
        &mut self,
        source: Option<&Constant>,
        work: &mut Work<'_, '_, O>,
    ) -> R<usize> {
        let key = self
            .pending_key
            .as_ref()
            .ok_or(ObservedValueError::InvalidRange)?;
        let fingerprint = fingerprint::of(key, source, work)?;
        self.intern_fingerprint(fingerprint, work)
    }
    // Private data seam allows controls to force collisions; public constructor
    // always computes the actual key fingerprint above. Full key equality is
    // mandatory even for matching fingerprints; no callback/flag controls it.
    pub(super) fn intern_fingerprint<O: ExecutionObserver>(
        &mut self,
        fingerprint: [u8; 32],
        work: &mut Work<'_, '_, O>,
    ) -> R<usize> {
        work.lookup(self.buckets.len())?;
        let existing = self.buckets.get(&fingerprint);
        if let Some(bucket) = existing {
            let mut at = 0;
            while let Some(index) = work.at(bucket, at)? {
                let stored = work
                    .at(&self.classes, *index)?
                    .ok_or(ObservedValueError::InvalidRange)?;
                let key = self
                    .pending_key
                    .as_ref()
                    .ok_or(ObservedValueError::InvalidRange)?;
                if key.equal(stored, work)? {
                    let answer = *index;
                    retirement::key(self.pending_key.take(), work);
                    work.admit(1, 0)?;
                    return Ok(answer);
                }
                work.next(&mut at)?;
            }
        }
        work.admit(1, size_of::<usize>())?;
        let index = self.classes.len();
        work.reserve(&mut self.classes)?;
        work.lookup(self.buckets.len())?;
        if let Some(bucket) = self.buckets.get_mut(&fingerprint) {
            work.reserve(bucket)?;
            work.admit(2, size_of::<Key<'_>>() + size_of::<usize>())?;
            let key = self
                .pending_key
                .take()
                .ok_or(ObservedValueError::InvalidRange)?;
            self.classes.push(key);
            bucket.push(index);
        } else {
            if self.pending_bucket.capacity() != 0 {
                return Err(ObservedValueError::InvalidRange);
            }
            work.reserve(&mut self.pending_bucket)?;
            work.admit(1, size_of::<usize>())?;
            self.pending_bucket.push(index);
            work.insertion(self.buckets.len())?;
            work.admit(2, size_of::<Key<'_>>() + size_of::<Vec<usize>>())?;
            let key = self
                .pending_key
                .take()
                .ok_or(ObservedValueError::InvalidRange)?;
            self.classes.push(key);
            if let Some(displaced) = self
                .buckets
                .insert(fingerprint, take(&mut self.pending_bucket))
            {
                self.pending_bucket = displaced;
                return Err(ObservedValueError::InvalidRange);
            }
        }
        work.admit(1, 0)?;
        Ok(index)
    }
}
