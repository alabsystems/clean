// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Exact raw structural identity, never interpretation or proof authority.
use super::{ClauseBinding, ClausePlace, ClauseSort, ProofFormula};
use crate::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
use core::mem::{size_of, take};
mod sorts;
mod storage;
#[cfg(test)]
mod tests;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;
#[derive(Clone, Copy)]
enum Pair<'a> {
    Sort(&'a ClauseSort, &'a ClauseSort),
    Ctors(
        &'a [(String, Vec<(String, ClauseSort)>)],
        &'a [(String, Vec<(String, ClauseSort)>)],
        usize,
    ),
    Fields(
        &'a [(String, ClauseSort)],
        &'a [(String, ClauseSort)],
        usize,
    ),
}
#[derive(Default)]
struct State<'a> {
    tasks: Vec<Pair<'a>>,
}

impl ClauseSort {
    /// Exact derived structural equality with observations inside every
    /// recursive sort/string/list comparison. No sort is normalized or read
    /// as a proof, and no hash collision assumption replaces equality.
    pub fn structurally_eq_observed<O: ExecutionObserver>(
        &self,
        other: &Self,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<bool> {
        header(session, site, size_of::<State<'_>>())?;
        let mut work = Work { session, site };
        let mut state = State::default();
        let result = state.sorts(self, other, &mut work);
        state.retire(&mut work);
        work.finish(result)
    }
}
impl ProofFormula {
    /// Exact equality of every raw field, optional-string state and ordered
    /// binding/sort/place. Opaque schemas/payloads stay opaque: equality does
    /// not authenticate, parse, discharge or certify either formula.
    pub fn structurally_eq_observed<O: ExecutionObserver>(
        &self,
        other: &Self,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<bool> {
        header(session, site, 2 * size_of::<&Self>())?;
        let mut work = Work { session, site };
        let result = formulas(self, other, &mut work);
        work.finish(result)
    }
}
fn header<O: ExecutionObserver>(
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
    bytes: usize,
) -> R {
    session.admit(ExecutionProgress {
        phase: ExecutionPhase::Validation,
        site,
        work: 1,
        copy_bytes: bytes
            .checked_add(size_of::<Work<'_, '_, O>>())
            .ok_or(ObservedValueError::CapacityOverflow)?,
    })?;
    Ok(())
}
fn formulas<O: ExecutionObserver>(
    left: &ProofFormula,
    right: &ProofFormula,
    work: &mut Work<'_, '_, O>,
) -> R<bool> {
    work.admit(6, 12 * size_of::<usize>())?;
    // No ellipsis: a future formula field requires an explicit equality rule.
    let ProofFormula {
        schema: a,
        payload: b,
        smtlib: c,
        sort: d,
        bindings: e,
    } = left;
    let ProofFormula {
        schema: f,
        payload: g,
        smtlib: h,
        sort: i,
        bindings: j,
    } = right;
    if !work.text(a, f)?
        || !work.text(b, g)?
        || !work.optional_text(c, h)?
        || !work.optional_text(d, i)?
    {
        return Ok(false);
    }
    work.admit(1, 2 * size_of::<usize>())?;
    if e.len() != j.len() {
        return Ok(false);
    }
    let mut index = 0;
    while let Some((name, bind)) = work.at(e, index)? {
        let (other, other_bind) = work.at(j, index)?.ok_or(ObservedValueError::InvalidRange)?;
        if !work.text(name, other)? {
            return Ok(false);
        }
        work.admit(2, 4 * size_of::<usize>())?;
        let ClauseBinding { sort, place } = bind;
        let ClauseBinding {
            sort: other_sort,
            place: other_place,
        } = other_bind;
        // Binding derives equality in this declared field order: sort first.
        if !sort.structurally_eq_observed(other_sort, work.session, work.site)?
            || !places(place, other_place, work)?
        {
            return Ok(false);
        }
        work.next(&mut index)?;
    }
    Ok(true)
}
fn places<O: ExecutionObserver>(
    left: &ClausePlace,
    right: &ClausePlace,
    work: &mut Work<'_, '_, O>,
) -> R<bool> {
    work.admit(11, 2 * size_of::<ClausePlace>())?;
    Ok(match (left, right) {
        (ClausePlace::Param { index: a }, ClausePlace::Param { index: b })
        | (ClausePlace::ResultSlot { index: a }, ClausePlace::ResultSlot { index: b })
        | (ClausePlace::MutParamExit { index: a }, ClausePlace::MutParamExit { index: b })
        | (ClausePlace::SpecVar { index: a }, ClausePlace::SpecVar { index: b })
        | (ClausePlace::SpecVarNext { index: a }, ClausePlace::SpecVarNext { index: b })
        | (
            ClausePlace::ParamPointeeEntry { index: a },
            ClausePlace::ParamPointeeEntry { index: b },
        ) => a == b,
        (ClausePlace::World, ClausePlace::World)
        | (ClausePlace::Unwind, ClausePlace::Unwind)
        | (ClausePlace::WorldPre, ClausePlace::WorldPre)
        | (ClausePlace::WorldPost, ClausePlace::WorldPost) => true,
        (ClausePlace::Value(a), ClausePlace::Value(b)) => a.index() == b.index(),
        (
            ClausePlace::Param { .. }
            | ClausePlace::ResultSlot { .. }
            | ClausePlace::MutParamExit { .. }
            | ClausePlace::World
            | ClausePlace::Unwind
            | ClausePlace::Value(_)
            | ClausePlace::SpecVar { .. }
            | ClausePlace::SpecVarNext { .. }
            | ClausePlace::WorldPre
            | ClausePlace::WorldPost
            | ClausePlace::ParamPointeeEntry { .. },
            _,
        ) => false,
    })
}
impl State<'_> {
    fn retire<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        loop {
            work.step(size_of::<Option<Pair<'_>>>().saturating_add(1));
            let Some(pair) = self.tasks.pop() else { break };
            work.fixed(pair);
        }
        work.step(size_of::<Vec<Pair<'_>>>().saturating_add(1));
        drop(take(&mut self.tasks));
        work.poll();
    }
}
