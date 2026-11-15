// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Actual canonical place-list comparisons; borrowed input grants no authority.
use super::*;
use crate::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
use core::mem::size_of;
#[cfg(test)]
mod tests;

impl EffectSet {
    /// The same nonempty/strict-order predicate as is_canonical(), with every
    /// actual adjacent comparison under the supplied original session/site.
    /// The summary remains an unauthenticated claim; no body coverage is checked.
    pub fn is_canonical_observed<O: ExecutionObserver>(
        &self,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> Result<bool, ObservedValueError> {
        step(session, site, 1, size_of::<bool>())?;
        let result = match self {
            EffectSet::Nothing | EffectSet::Everything => true,
            EffectSet::Places(rows) => {
                if rows.is_empty() {
                    false
                } else {
                    step(session, site, 1, size_of::<usize>() + size_of::<bool>())?;
                    let mut index = 1;
                    let mut ordered = true;
                    loop {
                        step(session, site, 1, size_of::<Option<&EffectPlace>>())?;
                        let Some(right) = rows.get(index) else { break };
                        step(session, site, 1, size_of::<(EffectPlace, EffectPlace)>())?;
                        let left = &rows[index - 1];
                        ordered = match (left, right) {
                            (
                                EffectPlace::ParamPointee { index: a },
                                EffectPlace::ParamPointee { index: b },
                            ) => a < b,
                            (EffectPlace::ParamPointee { .. }, EffectPlace::Global(_)) => true,
                            (EffectPlace::Global(_), EffectPlace::ParamPointee { .. }) => false,
                            (EffectPlace::Global(a), EffectPlace::Global(b)) => {
                                a.index() < b.index()
                            }
                        };
                        if !ordered {
                            break;
                        }
                        step(session, site, 1, size_of::<usize>())?;
                        index = index
                            .checked_add(1)
                            .ok_or(ObservedValueError::CapacityOverflow)?;
                    }
                    ordered
                }
            }
        };
        session.admit(ExecutionProgress {
            phase: ExecutionPhase::Publication,
            site,
            work: 1,
            copy_bytes: size_of::<bool>(),
        })?;
        Ok(result)
    }
}
fn step<O: ExecutionObserver>(
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
    work: usize,
    copy_bytes: usize,
) -> Result<(), ObservedValueError> {
    session
        .admit(ExecutionProgress {
            phase: ExecutionPhase::Validation,
            site,
            work,
            copy_bytes,
        })
        .map_err(Into::into)
}
