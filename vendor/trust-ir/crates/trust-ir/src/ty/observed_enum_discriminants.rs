// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Actual enum assignment/tag traversal, not layout or producer authority.
use super::{EnumDef, EnumTagRepr};
use crate::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
use core::mem::{size_of, take};
mod storage;
#[cfg(test)]
mod tests;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;
#[derive(Default)]
struct State {
    values: Vec<i128>,
}
impl EnumDef {
    /// Exact original assignment: explicit values reset the next implicit
    /// value, first implicit is zero, duplicates and required implicit overflow
    /// return None. Every stored variant is visited; excess discriminant-tail
    /// entries and unrelated variant payloads retain their original opacity.
    /// No partial Some vector escapes an operational stop. Returned vector and
    /// borrowed input disposal remain caller-owned; this confers no authority.
    pub fn effective_discriminants_observed<O: ExecutionObserver>(
        &self,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<Option<Vec<i128>>> {
        session.admit(ExecutionProgress {
            phase: ExecutionPhase::Validation,
            site,
            work: 1,
            copy_bytes: size_of::<State>() + size_of::<Work<'_, '_, O>>(),
        })?;
        let mut state = State::default();
        let mut work = Work { session, site };
        match state.assign(self, &mut work) {
            Ok(true) => match work.publication(size_of::<Option<Vec<i128>>>()) {
                Ok(()) => Ok(Some(take(&mut state.values))),
                Err(error) => {
                    state.retire(&mut work);
                    Err(work.terminal(error))
                }
            },
            Ok(false) => {
                state.retire(&mut work);
                work.publication(size_of::<Option<Vec<i128>>>())?;
                Ok(None)
            }
            Err(error) => {
                state.retire(&mut work);
                Err(work.terminal(error))
            }
        }
    }
    /// Original canonical tag: empty/malformed assignment or inadequate hint
    /// is None; inferred tags retain the 64-bit cap while explicit 128-bit
    /// hints keep the original full signed/nonnegative representable ranges.
    /// All scratch is consumed before terminal publication under the same
    /// supplied original session/site, including after sticky refusal.
    /// Actual prior-value scans charge repeated work, without old hash-index
    /// complexity claims. No owner/grant/deadline/TLS/fuel/flag/fallback. Full
    /// enum/module/source/proof/native/MC qualification and physical std/
    /// allocator/deallocator/OOM/panic/unwind/RSS/hard100ms remain OPEN.
    pub fn canonical_tag_repr_observed<O: ExecutionObserver>(
        &self,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<Option<EnumTagRepr>> {
        session.admit(ExecutionProgress {
            phase: ExecutionPhase::Validation,
            site,
            work: 1,
            copy_bytes: size_of::<State>() + size_of::<Work<'_, '_, O>>(),
        })?;
        let mut state = State::default();
        let mut work = Work { session, site };
        let result = state.canonical(self, &mut work);
        state.retire(&mut work);
        match result.and_then(|answer| {
            work.publication(size_of::<Option<EnumTagRepr>>())?;
            Ok(answer)
        }) {
            Ok(answer) => Ok(answer),
            Err(error) => Err(work.terminal(error)),
        }
    }
}
impl State {
    fn assign<O: ExecutionObserver>(
        &mut self,
        definition: &EnumDef,
        work: &mut Work<'_, '_, O>,
    ) -> R<bool> {
        work.admit(1, 0)?;
        if self.values.capacity() != 0 {
            return Err(ObservedValueError::InvalidRange);
        }
        let mut next = Some(0i128);
        let mut index = 0;
        loop {
            work.admit(2, size_of::<usize>())?;
            if index >= definition.variants.len() {
                return Ok(true);
            }
            work.admit(3, size_of::<Option<i128>>())?;
            let value = match definition.discriminants.get(index).copied().flatten() {
                Some(value) => value,
                None => match next {
                    Some(value) => value,
                    None => return Ok(false),
                },
            };
            let mut seen = 0;
            loop {
                work.admit(1, size_of::<Option<&i128>>())?;
                let Some(prior) = self.values.get(seen) else {
                    break;
                };
                work.admit(1, size_of::<i128>())?;
                if *prior == value {
                    return Ok(false);
                }
                work.next(&mut seen)?;
            }
            work.reserve(&mut self.values)?;
            work.admit(2, size_of::<i128>() + size_of::<Option<i128>>())?;
            self.values.push(value);
            next = value.checked_add(1);
            work.next(&mut index)?;
        }
    }
    fn canonical<O: ExecutionObserver>(
        &mut self,
        definition: &EnumDef,
        work: &mut Work<'_, '_, O>,
    ) -> R<Option<EnumTagRepr>> {
        work.admit(1, 0)?;
        if definition.variants.is_empty() {
            return Ok(None);
        }
        if !self.assign(definition, work)? {
            return Ok(None);
        }
        work.admit(1, size_of::<Option<EnumTagRepr>>())?;
        if let Some(hint) = definition.repr {
            let mut i = 0;
            loop {
                work.admit(1, size_of::<Option<&i128>>())?;
                let Some(value) = self.values.get(i) else {
                    return Ok(Some(hint));
                };
                if !fits(hint, *value, work)? {
                    return Ok(None);
                }
                work.next(&mut i)?;
            }
        }
        let mut minimum = None;
        let mut maximum = None;
        let mut i = 0;
        loop {
            work.admit(1, size_of::<Option<&i128>>())?;
            let Some(value) = self.values.get(i) else {
                break;
            };
            work.admit(2, size_of::<Option<i128>>())?;
            minimum = Some(minimum.map_or(*value, |prior: i128| prior.min(*value)));
            work.next(&mut i)?;
        }
        let mut i = 0;
        loop {
            work.admit(1, size_of::<Option<&i128>>())?;
            let Some(value) = self.values.get(i) else {
                break;
            };
            work.admit(2, size_of::<Option<i128>>())?;
            maximum = Some(maximum.map_or(*value, |prior: i128| prior.max(*value)));
            work.next(&mut i)?;
        }
        work.admit(2, 0)?;
        let (Some(minimum), Some(maximum)) = (minimum, maximum) else {
            return Ok(None);
        };
        work.admit(4, 4 * size_of::<EnumTagRepr>())?;
        let candidates = if minimum >= 0 {
            [
                EnumTagRepr::U8,
                EnumTagRepr::U16,
                EnumTagRepr::U32,
                EnumTagRepr::U64,
            ]
        } else {
            [
                EnumTagRepr::I8,
                EnumTagRepr::I16,
                EnumTagRepr::I32,
                EnumTagRepr::I64,
            ]
        };
        let mut at = 0;
        loop {
            work.admit(1, size_of::<Option<&EnumTagRepr>>())?;
            let Some(candidate) = candidates.get(at) else {
                return Ok(None);
            };
            if fits(*candidate, minimum, work)? && fits(*candidate, maximum, work)? {
                return Ok(Some(*candidate));
            }
            work.next(&mut at)?;
        }
    }
    fn retire<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        loop {
            work.session
                .retirement_step(work.site, size_of::<Option<i128>>().saturating_add(1));
            let Some(value) = self.values.pop() else {
                break;
            };
            work.fixed(value);
        }
        work.session
            .retirement_step(work.site, size_of::<Vec<i128>>().saturating_add(1));
        drop(take(&mut self.values));
        work.session.retirement_poll(work.site);
    }
}
fn fits<O: ExecutionObserver>(
    repr: EnumTagRepr,
    value: i128,
    work: &mut Work<'_, '_, O>,
) -> R<bool> {
    work.admit(4, size_of::<EnumTagRepr>() + size_of::<i128>())?;
    // Exhaustive, fixed scalar predicates; no recursive/variable formatter or
    // payload traversal. New repr variants must acquire their own exact rule.
    Ok(match repr {
        EnumTagRepr::U8 => value >= 0 && value <= i128::from(u8::MAX),
        EnumTagRepr::U16 => value >= 0 && value <= i128::from(u16::MAX),
        EnumTagRepr::U32 => value >= 0 && value <= i128::from(u32::MAX),
        EnumTagRepr::U64 => value >= 0 && value <= i128::from(u64::MAX),
        EnumTagRepr::I8 => value >= i128::from(i8::MIN) && value <= i128::from(i8::MAX),
        EnumTagRepr::I16 => value >= i128::from(i16::MIN) && value <= i128::from(i16::MAX),
        EnumTagRepr::I32 => value >= i128::from(i32::MIN) && value <= i128::from(i32::MAX),
        EnumTagRepr::I64 => value >= i128::from(i64::MIN) && value <= i128::from(i64::MAX),
        EnumTagRepr::U128 => value >= 0,
        EnumTagRepr::I128 => true,
    })
}
