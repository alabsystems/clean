// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Actual original one-refinement by-value aggregate-slot predicate.
use crate::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
use crate::{Module, Ty};
use core::mem::size_of;
#[cfg(test)]
mod tests;
impl Module {
    /// Exact observed counterpart of `is_by_value_aggregate_slot`: peel one
    /// Refine through the actual types table, classifying dangling/nested
    /// refinement as aggregate (fail closed), without walking wrapped payloads.
    /// This returns only the original classification, never layout/ABI/source
    /// or proof authority. The same supplied owner/site is used throughout.
    pub fn is_by_value_aggregate_slot_observed<O: ExecutionObserver>(
        &self,
        ty: &Ty,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> Result<bool, ObservedValueError> {
        let mut admit = |work, copy_bytes| {
            session
                .admit(ExecutionProgress {
                    phase: ExecutionPhase::Validation,
                    site,
                    work,
                    copy_bytes,
                })
                .map_err(ObservedValueError::from)
        };
        admit(1, size_of::<Option<&Ty>>())?;
        let base = match ty {
            Ty::Refine(base, _) => {
                admit(2, size_of::<usize>())?;
                match self.types.get(base.as_usize()) {
                    None | Some(Ty::Refine(..)) => None,
                    Some(base) => Some(base),
                }
            }
            other => Some(other),
        };
        admit(1, size_of::<bool>())?;
        let aggregate = match base {
            None => true,
            Some(base) => matches!(
                base,
                Ty::Struct(_)
                    | Ty::Tuple(_)
                    | Ty::Array(_, _)
                    | Ty::Enum(_)
                    | Ty::Record(_)
                    | Ty::Sequence(_)
                    | Ty::Set(_, _)
                    | Ty::Closure(_)
                    | Ty::Vector(_, _)
                    | Ty::Tensor(_, _)
            ),
        };
        session.admit(ExecutionProgress {
            phase: ExecutionPhase::Publication,
            site,
            work: 1,
            copy_bytes: size_of::<bool>(),
        })?;
        Ok(aggregate)
    }
}
// Borrowed input, fixed Copy scratch only; no new owner/grant/deadline/TLS/fuel.
// Full validation/caller disposal and physical std/hard-time remain OPEN.
