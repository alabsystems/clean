// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The exhaustive original operand walk with actual inner observation.
//! Types, constants, names and definition IDs are borrowed or ignored exactly
//! as in the original visitor; they are never treated as SSA operands.

use super::{AssertKind, Inst, PanicLocation, PanicSite, SwitchCase, ValueId};
use crate::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
use core::mem::size_of;
mod contains;
mod plan;
mod storage;
#[cfg(test)]
mod tests;
mod walk;
type R<T = ()> = Result<T, ObservedValueError>;
use storage::Work;

impl Inst {
    /// Collect every original SSA operand in exact visitor order, including
    /// duplicates. Actual outer case scans and inner operand copies use the
    /// caller's original session/site. A refusal supplies no partial vector.
    /// This establishes no typing, CFG, source or proof authority. Successful
    /// output disposal and physical allocator/time bounds remain caller-owned.
    pub fn value_operands_observed<O: ExecutionObserver>(
        &self,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<Vec<ValueId>> {
        session.admit(ExecutionProgress {
            phase: ExecutionPhase::Validation,
            site,
            work: 1,
            copy_bytes: size_of::<Vec<ValueId>>() + size_of::<Work<'_, '_, O>>(),
        })?;
        let mut values = Vec::new();
        let mut work = Work { session, site };
        let result: R = (|| {
            // The descriptor has only fixed IDs and borrowed headers. Price
            // construction plus its fixed dispatch/retirement call copies
            // before selecting any fields; no variable payload is copied.
            let descriptor_bytes = size_of::<plan::Plan<'_>>()
                .checked_mul(4)
                .ok_or(ObservedValueError::CapacityOverflow)?;
            work.admit(64, descriptor_bytes)?;
            let plan = plan::for_instruction(self);
            let result = walk::collect(plan, &mut values, &mut work);
            work.retire(plan);
            result
        })();
        let result = result.and_then(|()| work.publication());
        match result {
            Ok(()) => Ok(values),
            Err(error) => {
                work.retire_values(&mut values);
                Err(work.terminal(error))
            }
        }
    }
}
