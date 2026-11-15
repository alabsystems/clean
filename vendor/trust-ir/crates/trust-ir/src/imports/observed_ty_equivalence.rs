// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Exact cross-module type identity with paid active-path continuations.
//! This is logical requested-data accounting, never allocator, stack, kernel,
//! callback, preemption, RSS or hard-time/proof/consumer authority.
use super::{TyEquivalence, TypeOriginConflict};
use crate::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
use crate::pred::{Pred, Universe};
use crate::ty::{EnumDef, EnumVariant, FieldDef, TypeOrigin};
use crate::value::{PredId, TyId};
use crate::{Constant, Module, Ty};
use core::mem::size_of;
mod constants;
mod engine;
mod nominal;
mod predicates;
mod state;
#[cfg(test)]
mod tests;
mod types;
mod work;
use state::{ConflictSource, Direction, Kind, State, Task, retire_conflict};
use work::Work;
type R<T = ()> = Result<T, ObservedValueError>;

/// Compare the actual ordinary cross-module relation using this SAME original
/// observer/site. No owned input is taken: modules and inline roots remain
/// borrowed and unchanged, and their eventual disposal stays caller-owned.
/// Active pairs are removed after each nested check; failed set candidates may
/// retain the first conflict, but an overall true relation still returns Equal.
/// Owned returned conflict DATA must be retired using `retire_observed`.
/// Operational refusal is an outer error, never inequality or a semantic cause.
/// There is no new owner, deadline, grant, instruction fuel or depth cutoff.
pub fn ty_equivalence_across_observed<O: ExecutionObserver>(
    a: &Module,
    ta: &Ty,
    b: &Module,
    tb: &Ty,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<TyEquivalence> {
    session.admit(ExecutionProgress {
        phase: ExecutionPhase::Validation,
        site,
        work: 1,
        copy_bytes: size_of::<State<'_>>() + size_of::<Work<'_, '_, O>>(),
    })?;
    let mut state = State::new();
    let mut work = Work { session, site };
    let result = engine::run(&mut state, a, ta, b, tb, &mut work);
    state.scratch(&mut work);
    if let Err(error) = result {
        state.owned(&mut work);
        return Err(work.terminal(error));
    }
    if state.last {
        state.owned(&mut work);
    }
    if let Err(error) = work.publication(size_of::<TyEquivalence>()) {
        state.owned(&mut work);
        return Err(work.terminal(error));
    }
    if state.last {
        Ok(TyEquivalence::Equal)
    } else if let Some(conflict) = state.conflict.take() {
        Ok(TyEquivalence::OriginConflict(conflict))
    } else {
        Ok(TyEquivalence::Unequal)
    }
}

/// Boolean projection of the SAME full relation, consuming diagnostic ownership
/// before its own publication. This does not drop a conflict outside observation.
pub fn ty_structurally_eq_across_observed<O: ExecutionObserver>(
    a: &Module,
    ta: &Ty,
    b: &Module,
    tb: &Ty,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<bool> {
    let verdict = ty_equivalence_across_observed(a, ta, b, tb, session, site)?;
    let mut work = Work { session, site };
    let equal = match verdict {
        TyEquivalence::Equal => true,
        TyEquivalence::Unequal => false,
        TyEquivalence::OriginConflict(conflict) => {
            retire_conflict(conflict, &mut work);
            false
        }
    };
    work.publication(size_of::<bool>())?;
    Ok(equal)
}
impl TypeOriginConflict {
    /// Consume the actual owned origin/name headers under the original session.
    /// Strings are freed, not byte-scanned: this is not a physical drop theorem.
    pub fn retire_observed<O: ExecutionObserver>(
        self,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R {
        let mut work = Work { session, site };
        retire_conflict(self, &mut work);
        if work.session.first_refusal().is_some() {
            Err(ObservedValueError::AdmissionRefused)
        } else {
            Ok(())
        }
    }
}
