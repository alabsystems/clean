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
    pub(super) fn equal(&mut self, a: &str, b: &str) -> R<bool> {
        self.admit(1, 2 * size_of::<usize>())?;
        if a.len() != b.len() {
            return Ok(false);
        }
        let mut index = 0usize;
        while index < a.len() {
            self.admit(4, 2 * size_of::<&[u8]>() + size_of::<usize>())?;
            let end = index.saturating_add(1024).min(a.len());
            self.admit(end - index, 0)?;
            if a.as_bytes()[index..end] != b.as_bytes()[index..end] {
                return Ok(false);
            }
            self.admit(1, size_of::<usize>())?;
            index = end;
        }
        Ok(true)
    }
    pub(super) fn publish(&mut self, answer: bool) -> R<bool> {
        self.session.admit(ExecutionProgress {
            phase: ExecutionPhase::Publication,
            site: self.site,
            work: 1,
            copy_bytes: size_of::<bool>(),
        })?;
        Ok(answer)
    }
}
