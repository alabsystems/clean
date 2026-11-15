// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Borrow the exact inline type surface without traversing type payloads.
use super::{BindingSlot, Inst, Ty};
use crate::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
use core::mem::size_of;
mod plan;
mod storage;
#[cfg(test)]
mod tests;
mod walk;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;

impl Inst {
    /// Every type spelled inline, in the original refinement visitor's order.
    /// Only borrowed type headers are copied; nested types, constant payloads,
    /// names, attributes and operand lists are not inspected. Actual slot and
    /// dialect result scans use the caller's original session/site. No partial
    /// Vec is returned on refusal. This confers no type/validation/source/proof
    /// authority; successful output/input disposal and physical allocator/time
    /// containment remain caller-owned.
    pub fn inline_types_observed<'a, O: ExecutionObserver>(
        &'a self,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<Vec<&'a Ty>> {
        session.admit(ExecutionProgress {
            phase: ExecutionPhase::Validation,
            site,
            work: 1,
            copy_bytes: size_of::<Vec<&Ty>>() + size_of::<Work<'_, '_, O>>(),
        })?;
        let mut types = Vec::new();
        let mut work = Work { session, site };
        let result: R = (|| {
            // Fixed borrowed descriptor construction, dispatch and retirement
            // images are priced before the exhaustive field projection.
            let bytes = size_of::<plan::Plan<'_>>()
                .checked_mul(4)
                .ok_or(ObservedValueError::CapacityOverflow)?;
            work.admit(67, bytes)?;
            let plan = plan::for_instruction(self);
            let result = walk::collect(plan, &mut types, &mut work);
            work.retire(plan);
            result
        })();
        work.finish_types(result, types)
    }
}

#[cfg(test)]
mod precedence_tests;
