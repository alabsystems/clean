// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Actual inline predicates and inner-first width queries, never authority.
use super::*;
use crate::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
use core::mem::{size_of, take};
mod storage;
#[cfg(test)]
mod tests;
mod walk;
mod width;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;
#[derive(Clone, Copy)]
enum Frame<'a> {
    Visit(&'a Ty),
    Tail(&'a [Ty]),
}
#[derive(Default)]
struct State<'a> {
    frames: Vec<Frame<'a>>,
    lanes: Vec<u32>,
}
#[derive(Clone, Copy)]
enum Predicate {
    Handle,
    Dialect,
}
#[derive(Clone, Copy)]
enum Width {
    Unresolved,
    Pointer(u32),
}

impl Ty {
    /// Original complete inline visitor predicate: every inline node is read
    /// even after a Handle is found. Nominal IDs and payload strings remain
    /// opaque exactly as before. This is no full module/type/source authority.
    pub fn contains_handle_observed<O: ExecutionObserver>(
        &self,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<bool> {
        query_predicate(self, Predicate::Handle, session, site)
    }
    /// The same original complete inline traversal for Dialect discriminants.
    pub fn contains_dialect_observed<O: ExecutionObserver>(
        &self,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<bool> {
        query_predicate(self, Predicate::Dialect, session, site)
    }
    /// Original bool-lane rule follows ONLY nested Vector elements. Tuple,
    /// reference and nominal spellings are never broadened to their children.
    pub fn has_bool_lanes_observed<O: ExecutionObserver>(
        &self,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<bool> {
        header(session, site)?;
        let mut work = Work { session, site };
        let mut current = self;
        let result = loop {
            if let Err(error) = work.admit(3, size_of::<&Ty>()) {
                break Err(error);
            }
            match current {
                Ty::Bool => break Ok(true),
                Ty::Vector(inner, _) => current = inner,
                _ => break Ok(false),
            }
        };
        finish_copy(result, &mut State::default(), &mut work)
    }
    /// Preserve context-free scalar/inner-first Vector width and checked u32
    /// overflow as semantic None. Every actual layer uses this same owner.
    pub fn bit_width_observed<O: ExecutionObserver>(
        &self,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<Option<u32>> {
        query_width(self, Width::Unresolved, session, site)
    }
    /// Preserve exact target-width spelling, including Handle but NOT Func,
    /// fat checked multiplication, and inner-first nested-vector overflow.
    pub fn bit_width_with_observed<O: ExecutionObserver>(
        &self,
        pointer_bits: u32,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<Option<u32>> {
        query_width(self, Width::Pointer(pointer_bits), session, site)
    }
}
fn header<O: ExecutionObserver>(session: &mut ObservedSession<'_, O>, site: ExecutionSite) -> R {
    session
        .admit(ExecutionProgress {
            phase: ExecutionPhase::Validation,
            site,
            work: 1,
            copy_bytes: size_of::<State<'_>>() + size_of::<Work<'_, '_, O>>(),
        })
        .map_err(Into::into)
}
fn query_predicate<O: ExecutionObserver>(
    ty: &Ty,
    which: Predicate,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<bool> {
    header(session, site)?;
    let mut state = State::default();
    let mut work = Work { session, site };
    let result = state.predicate(ty, which, &mut work);
    finish_copy(result, &mut state, &mut work)
}
fn query_width<O: ExecutionObserver>(
    ty: &Ty,
    mode: Width,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<Option<u32>> {
    header(session, site)?;
    let mut state = State::default();
    let mut work = Work { session, site };
    let result = state.width(ty, mode, &mut work);
    finish_copy(result, &mut state, &mut work)
}
fn finish_copy<T: Copy, O: ExecutionObserver>(
    result: R<T>,
    state: &mut State<'_>,
    work: &mut Work<'_, '_, O>,
) -> R<T> {
    state.retire(work);
    match result.and_then(|answer| {
        work.publication::<T>()?;
        Ok(answer)
    }) {
        Ok(answer) => Ok(answer),
        Err(error) => Err(work.terminal(error)),
    }
}
impl State<'_> {
    fn retire<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        work.drain(&mut self.frames);
        work.drain(&mut self.lanes);
    }
}
