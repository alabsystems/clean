// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
pub(super) struct Work<'s, 'o, O: ExecutionObserver> {
    pub(super) session: &'s mut ObservedSession<'o, O>,
    pub(super) site: ExecutionSite,
}
impl<O: ExecutionObserver> Work<'_, '_, O> {
    pub(super) fn admit(&mut self, work: usize, copy_bytes: usize) -> R<()> {
        self.session
            .admit(ExecutionProgress {
                phase: ExecutionPhase::Validation,
                site: self.site,
                work,
                copy_bytes,
            })
            .map_err(Into::into)
    }
    pub(super) fn text(&mut self, a: &str, b: &str) -> R<bool> {
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
    pub(super) fn optional(&mut self, a: &Option<String>, b: &Option<String>) -> R<bool> {
        self.admit(1, 2 * size_of::<Option<&str>>())?;
        match (a.as_deref(), b.as_deref()) {
            (None, None) => Ok(true),
            (Some(a), Some(b)) => self.text(a, b),
            (None, Some(_)) | (Some(_), None) => Ok(false),
        }
    }
    pub(super) fn digest(&mut self, a: &Option<ProofDigest>, b: &Option<ProofDigest>) -> R<bool> {
        self.admit(
            2 * size_of::<ProofDigest>() + 2,
            2 * size_of::<Option<ProofDigest>>(),
        )?;
        Ok(copy_equal(a, b))
    }
    pub(super) fn publish(&mut self, value: bool) -> R<bool> {
        self.session
            .admit(ExecutionProgress {
                phase: ExecutionPhase::Publication,
                site: self.site,
                work: 1,
                copy_bytes: size_of::<bool>(),
            })
            .map_err(ObservedValueError::from)?;
        Ok(value)
    }
}

// Keep the scalar child closed to owning future digest representations.
fn copy_equal<T: Copy + PartialEq>(a: &T, b: &T) -> bool {
    a == b
}
