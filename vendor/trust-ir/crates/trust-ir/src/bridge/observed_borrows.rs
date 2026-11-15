// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Concrete original borrow-chain type resolution, without a lookup callback.
use super::{Function, Inst, Ty, ValueId};
use crate::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
use core::mem::{size_of, take};
mod index;
mod resolve;
mod retirement;
mod storage;
#[cfg(test)]
mod tests;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;
#[derive(Default)]
struct State {
    operands: Vec<(u32, u32)>,
    pending: Option<Ty>,
    resolved: Vec<(ValueId, Ty)>,
}

/// Exact original fat-only borrow result rule under the original session/site.
/// Fat input uses the actual observed type clone; thin, missing and refined-fat
/// input becomes Ptr. This returns plain data, not typing/source/proof authority.
pub fn borrow_result_ty_observed<O: ExecutionObserver>(
    operand_ty: Option<&Ty>,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<Ty> {
    session.admit(ExecutionProgress {
        phase: ExecutionPhase::Validation,
        site,
        work: 1,
        copy_bytes: size_of::<Option<Ty>>() + size_of::<Work<'_, '_, O>>(),
    })?;
    let mut work = Work { session, site };
    let mut pending = None;
    let result = work
        .make_type(operand_ty, &mut pending)
        .and_then(|()| work.publication(size_of::<Ty>()));
    match result {
        Ok(()) => pending.take().ok_or(ObservedValueError::InvalidRange),
        Err(error) => {
            work.retire_pending(&mut pending);
            Err(work.terminal(error))
        }
    }
}

/// Resolve every first Borrow/BorrowMut result in ascending ValueId order.
/// Last stored borrow definition wins, and chains ignore provisional known
/// types until reaching a non-borrow root. Concrete known rows are scanned in
/// reverse: their last matching key wins, as when collected into a BTreeMap.
/// Duplicate known rows need no separate authority or uniqueness assumption.
/// All actual scans/copies use the supplied original session/site; refusal
/// returns no partial output. Successful output/input disposal and physical
/// allocator/panic/time containment remain caller duties. No validation or
/// source/proof authority follows from these plain resolved pairs.
pub fn borrow_result_types_observed<O: ExecutionObserver>(
    function: &Function,
    known: &[(u32, Ty)],
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<Vec<(ValueId, Ty)>> {
    session.admit(ExecutionProgress {
        phase: ExecutionPhase::Validation,
        site,
        work: 1,
        copy_bytes: size_of::<State>() + size_of::<Work<'_, '_, O>>(),
    })?;
    let mut state = State::default();
    let mut work = Work { session, site };
    let result = state
        .collect(function, &mut work)
        .and_then(|()| state.resolve(known, &mut work));
    state.retire_scratch(&mut work);
    let result = result.and_then(|()| work.publication(size_of::<Vec<(ValueId, Ty)>>()));
    match result {
        Ok(()) => Ok(take(&mut state.resolved)),
        Err(error) => {
            state.retire_resolved(&mut work);
            Err(work.terminal(error))
        }
    }
}
