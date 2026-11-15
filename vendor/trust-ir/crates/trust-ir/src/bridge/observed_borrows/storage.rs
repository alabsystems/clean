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
    pub(super) fn reserve<T>(&mut self, rows: &mut Vec<T>) -> R {
        self.admit(1, 0)?;
        if rows.len() == rows.capacity() {
            let (requested, images, bytes) = growth_cost::<T>(rows.len())?;
            self.admit(images, bytes)?;
            rows.try_reserve_exact(requested - rows.len())
                .map_err(|_| ObservedValueError::AllocationFailed)?;
        }
        Ok(())
    }
    pub(super) fn make_type(&mut self, operand_ty: Option<&Ty>, pending: &mut Option<Ty>) -> R {
        self.admit(1, size_of::<Option<Ty>>())?;
        if pending.is_some() {
            return Err(ObservedValueError::InvalidRange);
        }
        // The only cloned roots are actual unrefined FatPtr leaves. All other
        // spellings normalize to Ptr without traversing or cloning payloads.
        *pending = Some(match operand_ty {
            Some(ty @ Ty::FatPtr(_)) => ty.clone_observed(self.session, self.site)?,
            _ => Ty::Ptr,
        });
        Ok(())
    }
    pub(super) fn push_row(
        &mut self,
        rows: &mut Vec<(ValueId, Ty)>,
        result: u32,
        pending: &mut Option<Ty>,
    ) -> R {
        self.reserve(rows)?;
        self.admit(1, size_of::<(ValueId, Ty)>() + size_of::<Option<Ty>>())?;
        let ty = pending.take().ok_or(ObservedValueError::InvalidRange)?;
        rows.push((ValueId::new(result), ty));
        Ok(())
    }
    pub(super) fn publication(&mut self, copy_bytes: usize) -> R {
        self.session
            .admit(ExecutionProgress {
                phase: ExecutionPhase::Publication,
                site: self.site,
                work: 1,
                copy_bytes,
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

pub(super) fn growth_cost<T>(len: usize) -> R<(usize, usize, usize)> {
    let requested = len
        .checked_mul(2)
        .and_then(|n| n.checked_add(1))
        .ok_or(ObservedValueError::CapacityOverflow)?;
    let images = requested
        .checked_add(len)
        .ok_or(ObservedValueError::CapacityOverflow)?;
    let bytes = images
        .checked_mul(size_of::<T>())
        .ok_or(ObservedValueError::CapacityOverflow)?;
    Ok((requested, images, bytes))
}
