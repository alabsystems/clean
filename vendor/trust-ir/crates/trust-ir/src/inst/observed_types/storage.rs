// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
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
    pub(super) fn push<'a>(&mut self, types: &mut Vec<&'a Ty>, ty: &'a Ty) -> R {
        self.admit(1, 0)?;
        if types.len() == types.capacity() {
            let requested = types
                .len()
                .checked_mul(2)
                .and_then(|n| n.checked_add(1))
                .ok_or(ObservedValueError::CapacityOverflow)?;
            let images = requested
                .checked_add(types.len())
                .ok_or(ObservedValueError::CapacityOverflow)?;
            self.admit(
                images,
                images
                    .checked_mul(size_of::<&Ty>())
                    .ok_or(ObservedValueError::CapacityOverflow)?,
            )?;
            types
                .try_reserve_exact(requested - types.len())
                .map_err(|_| ObservedValueError::AllocationFailed)?;
        }
        self.admit(1, size_of::<&Ty>())?;
        types.push(ty);
        Ok(())
    }
    pub(super) fn publication(&mut self) -> R {
        self.session
            .admit(ExecutionProgress {
                phase: ExecutionPhase::Publication,
                site: self.site,
                work: 1,
                copy_bytes: size_of::<Vec<&Ty>>(),
            })
            .map_err(Into::into)
    }
    pub(super) fn retire<T>(&mut self, value: T) {
        self.session.retirement_step(self.site, 1);
        drop(value);
        self.session.retirement_poll(self.site);
    }
    pub(super) fn retire_types(&mut self, types: &mut Vec<&Ty>) {
        while !types.is_empty() {
            self.session.retirement_step(self.site, 1);
            types.pop();
        }
        // The elements are borrowed headers: never drop or traverse a Ty.
        self.retire(core::mem::take(types));
    }
    pub(super) fn finish_types<'a>(&mut self, result: R, mut types: Vec<&'a Ty>) -> R<Vec<&'a Ty>> {
        let result = result.and_then(|()| self.publication());
        match result {
            Ok(()) => Ok(types),
            Err(error) => {
                self.retire_types(&mut types);
                Err(self.terminal(error))
            }
        }
    }
    pub(super) fn terminal(&self, error: ObservedValueError) -> ObservedValueError {
        // A local typed error precedes this consuming cleanup. Keep it even
        // when cleanup records a later original-session refusal.
        error
    }
}
