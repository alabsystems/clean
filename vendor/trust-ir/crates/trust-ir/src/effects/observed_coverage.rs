// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Borrowed effect-set inclusion and explicit-global queries, not authority.
use super::{EffectPlace, EffectSet, EffectSummary};
use crate::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
use core::mem::size_of;
mod storage;
#[cfg(test)]
mod tests;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;

impl EffectSet {
    /// Exact ordinary set inclusion, including noncanonical empty/duplicate
    /// Places. Inputs remain borrowed. An operational stop is never a bool.
    pub fn covers_observed<O: ExecutionObserver>(
        &self,
        other: &Self,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<bool> {
        begin(session, site)?;
        let mut work = Work { session, site };
        let covered = work.covers(self, other)?;
        work.publish(covered)
    }
}
impl EffectSummary {
    /// The exact reads/writes/allocates/frees/may_unwind/io short-circuit order.
    /// This compares carried claims only; it authenticates no effects or body.
    pub fn covers_observed<O: ExecutionObserver>(
        &self,
        other: &Self,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<bool> {
        begin(session, site)?;
        let mut work = Work { session, site };
        work.admit(1, 2 * size_of::<&EffectSet>())?;
        if !work.covers(&self.reads, &other.reads)? {
            return work.publish(false);
        }
        work.admit(1, 2 * size_of::<&EffectSet>())?;
        if !work.covers(&self.writes, &other.writes)? {
            return work.publish(false);
        }
        // Each left flag is read first; a true left flag skips its right flag.
        work.admit(1, size_of::<bool>())?;
        if !self.allocates {
            work.admit(1, size_of::<bool>())?;
            if other.allocates {
                return work.publish(false);
            }
        }
        work.admit(1, size_of::<bool>())?;
        if !self.frees {
            work.admit(1, size_of::<bool>())?;
            if other.frees {
                return work.publish(false);
            }
        }
        work.admit(1, size_of::<bool>())?;
        if !self.may_unwind {
            work.admit(1, size_of::<bool>())?;
            if other.may_unwind {
                return work.publish(false);
            }
        }
        work.admit(1, size_of::<bool>())?;
        if !self.io {
            work.admit(1, size_of::<bool>())?;
            if other.io {
                return work.publish(false);
            }
        }
        work.publish(true)
    }
    /// Only explicitly named Global places count; Everything itself does not.
    /// Reads are scanned before writes, stopping at the first actual Global.
    pub fn names_a_global_observed<O: ExecutionObserver>(
        &self,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<bool> {
        begin(session, site)?;
        let mut work = Work { session, site };
        work.admit(1, size_of::<&EffectSet>())?;
        if work.names_global(&self.reads)? {
            return work.publish(true);
        }
        work.admit(1, size_of::<&EffectSet>())?;
        let named = work.names_global(&self.writes)?;
        work.publish(named)
    }
}
fn begin<O: ExecutionObserver>(session: &mut ObservedSession<'_, O>, site: ExecutionSite) -> R {
    session
        .admit(ExecutionProgress {
            phase: ExecutionPhase::Validation,
            site,
            work: 1,
            copy_bytes: size_of::<Work<'_, '_, O>>() + size_of::<bool>(),
        })
        .map_err(Into::into)
}
impl<O: ExecutionObserver> Work<'_, '_, O> {
    fn covers(&mut self, ours: &EffectSet, theirs: &EffectSet) -> R<bool> {
        self.admit(2, size_of::<bool>())?;
        match (ours, theirs) {
            (EffectSet::Everything, _) | (_, EffectSet::Nothing) => Ok(true),
            (_, EffectSet::Everything) => Ok(false),
            (EffectSet::Nothing, EffectSet::Places(rows)) => {
                self.admit(1, size_of::<bool>())?;
                Ok(rows.is_empty())
            }
            (EffectSet::Places(ours), EffectSet::Places(theirs)) => {
                self.admit(1, size_of::<usize>())?;
                let mut at = 0;
                while let Some(place) = self.at(theirs, at)? {
                    if !self.contains(ours, place)? {
                        return Ok(false);
                    }
                    self.next(&mut at)?;
                }
                Ok(true)
            }
        }
    }
    fn contains(&mut self, rows: &[EffectPlace], place: &EffectPlace) -> R<bool> {
        self.admit(1, size_of::<usize>())?;
        let mut index = 0;
        while let Some(candidate) = self.at(rows, index)? {
            if self.equal(candidate, place)? {
                return Ok(true);
            }
            self.next(&mut index)?;
        }
        Ok(false)
    }
    fn equal(&mut self, left: &EffectPlace, right: &EffectPlace) -> R<bool> {
        // Both tags/scalars are fixed; no derived variable equality hides work.
        self.admit(3, 2 * size_of::<EffectPlace>() + size_of::<bool>())?;
        Ok(match (left, right) {
            (EffectPlace::ParamPointee { index: a }, EffectPlace::ParamPointee { index: b }) => {
                a == b
            }
            (EffectPlace::Global(a), EffectPlace::Global(b)) => a.index() == b.index(),
            (EffectPlace::ParamPointee { .. }, EffectPlace::Global(_))
            | (EffectPlace::Global(_), EffectPlace::ParamPointee { .. }) => false,
        })
    }
    fn names_global(&mut self, set: &EffectSet) -> R<bool> {
        self.admit(1, size_of::<&[EffectPlace]>() + size_of::<usize>())?;
        let rows = match set {
            EffectSet::Nothing | EffectSet::Everything => return Ok(false),
            EffectSet::Places(rows) => rows,
        };
        let mut at = 0;
        while let Some(place) = self.at(rows, at)? {
            self.admit(1, size_of::<bool>())?;
            if matches!(place, EffectPlace::Global(_)) {
                return Ok(true);
            }
            self.next(&mut at)?;
        }
        Ok(false)
    }
}
// No owned scratch is allocated. Copy scalars and borrowed headers have no
// variable disposal path. Successful input ownership stays with the caller;
// no physical std/allocator/time, full validation or authority claim is made.
