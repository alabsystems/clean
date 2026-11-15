// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Actual short-circuit operand membership for exact-use authentication.
use super::*;
mod find;
impl Inst {
    /// Exact first-match result of try_visit_value_operands, without constructing
    /// a full Vec or walking the unused tail after a match. Reuses the same
    /// exhaustive fixed-header Plan as the full collector; every actual list,
    /// case, assertion metadata and equality visit observes the original supplied
    /// session/site. Types/constants/names/definition IDs remain non-operands.
    /// Outer operational refusal is never semantic false or proof of a use.
    /// No source/type/CFG/module/proof authority or owner/grant/deadline/TLS/fuel
    /// renewal; input disposal and physical std/panic/hard bounds remain OPEN.
    pub fn uses_value_operand_observed<O: ExecutionObserver>(
        &self,
        value: ValueId,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<bool> {
        session.admit(ExecutionProgress {
            phase: ExecutionPhase::Validation,
            site,
            work: 1,
            copy_bytes: size_of::<bool>() + size_of::<Work<'_, '_, O>>(),
        })?;
        let mut work = Work { session, site };
        let result: R<bool> = (|| {
            let bytes = size_of::<plan::Plan<'_>>()
                .checked_mul(4)
                .ok_or(ObservedValueError::CapacityOverflow)?;
            work.admit(64, bytes)?;
            let plan = plan::for_instruction(self);
            let answer = find::in_plan(plan, value, &mut work);
            work.retire(plan);
            answer
        })();
        match result.and_then(|answer| {
            work.session.admit(ExecutionProgress {
                phase: ExecutionPhase::Publication,
                site: work.site,
                work: 1,
                copy_bytes: size_of::<bool>(),
            })?;
            Ok(answer)
        }) {
            Ok(answer) => Ok(answer),
            Err(error) => Err(work.terminal(error)),
        }
    }
}
