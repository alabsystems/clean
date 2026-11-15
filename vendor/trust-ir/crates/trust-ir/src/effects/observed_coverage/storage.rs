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
    pub(super) fn at<'a>(
        &mut self,
        rows: &'a [EffectPlace],
        index: usize,
    ) -> R<Option<&'a EffectPlace>> {
        self.admit(1, size_of::<Option<&EffectPlace>>())?;
        Ok(rows.get(index))
    }
    pub(super) fn next(&mut self, index: &mut usize) -> R {
        self.admit(1, size_of::<usize>())?;
        *index = index
            .checked_add(1)
            .ok_or(ObservedValueError::CapacityOverflow)?;
        Ok(())
    }
    pub(super) fn publish(&mut self, value: bool) -> R<bool> {
        self.session.admit(ExecutionProgress {
            phase: ExecutionPhase::Publication,
            site: self.site,
            work: 1,
            copy_bytes: size_of::<bool>(),
        })?;
        Ok(value)
    }
}
