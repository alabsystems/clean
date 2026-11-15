// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored UNRUN controls. Ordinary structure is the exact semantic oracle.
use super::*;
use crate::interpret::InterpretOptions;
use crate::proof::ClauseBinding;
use crate::value::ValueId;
use std::{cell::Cell, rc::Rc};
mod custody;
mod fixtures;
mod helpers;
mod parity;
mod stops;
mod unicode_pricing;
mod witnesses;
use fixtures::{anchor, compact, deep_sort, formula, proof, valid, waiver};
#[derive(Default)]
struct Observer {
    events: Vec<ExecutionProgress>,
    stop: Option<usize>,
    work: usize,
    bytes: usize,
    work_cap: Option<usize>,
    byte_cap: Option<usize>,
    cleanup: Option<Rc<Cell<bool>>>,
}
impl ExecutionObserver for Observer {
    type Refusal = &'static str;
    fn admit(&mut self, event: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(event);
        if self.stop == Some(self.events.len()) {
            return Err("original spec stop");
        }
        if self.cleanup.as_ref().is_some_and(|arm| arm.get())
            && event.phase == ExecutionPhase::ScratchRetirement
        {
            return Err("cleanup");
        }
        self.work = self.work.checked_add(event.work).ok_or("work overflow")?;
        self.bytes = self
            .bytes
            .checked_add(event.copy_bytes)
            .ok_or("copy overflow")?;
        if self.work_cap.is_some_and(|cap| self.work > cap) {
            return Err("work");
        }
        if self.byte_cap.is_some_and(|cap| self.bytes > cap) {
            return Err("copy");
        }
        Ok(())
    }
}
fn site() -> ExecutionSite {
    ExecutionSite::Entry(FuncId::new(140))
}
fn run(specs: &[SpecModule]) -> (Vec<SpecLinkViolation>, Observer) {
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let out = validate_spec_structure_observed(specs, &mut session, site()).unwrap();
    assert_eq!(out, validate_spec_structure(specs));
    assert!(session.first_refusal().is_none());
    assert_eq!(session.remaining_fuel(), InterpretOptions::default().fuel);
    assert!(observer.events.iter().all(|event| event.site == site()));
    assert_eq!(
        observer.events.last().unwrap().phase,
        ExecutionPhase::Publication
    );
    (out, observer)
}
fn raw<'a, O: ExecutionObserver>(
    state: &mut State<'a>,
    specs: &'a [SpecModule],
    work: &mut Work<'_, '_, O>,
) -> R {
    state.declarations(specs, work)?;
    state.references(specs, work)?;
    state.normalize(work)
}
fn drain<O: ExecutionObserver>(state: &mut State<'_>, work: &mut Work<'_, '_, O>) {
    state.retire_scratch(work);
    retirement::consume_vec(take(&mut state.errors), work);
}
fn empty(state: &State<'_>) -> bool {
    state.fields.iter().all(|field| field.capacity() == 0)
        && state.detail.capacity() == 0
        && state.format.capacity() == 0
        && state.equality.capacity() == 0
        && state.pending.is_none()
        && state.errors.capacity() == 0
}
fn private_trace(specs: &[SpecModule]) -> Observer {
    // Baseline and every private replay use identical raw entry, without the
    // extra public wrapper header, followed by the same complete drain.
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut state = State::default();
    raw(&mut state, specs, &mut work).unwrap();
    assert_eq!(state.errors, validate_spec_structure(specs));
    drain(&mut state, &mut work);
    assert!(empty(&state));
    observer
}
