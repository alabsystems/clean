// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored UNRUN controls; ordinary executable links are the exact oracle.
use super::*;
use crate::Block;
use crate::FuncTy;
use crate::interpret::{InstructionSite, InterpretOptions};
use crate::value::{BlockId, ClosureTyId, EnumId, FuncTyId, PredId, RecordId, StructId, TyId};
use std::{cell::Cell, rc::Rc};
mod custody;
mod debug;
mod fixtures;
mod parity;
mod stops;
mod unicode_pricing;
use fixtures::{compact, fixture, types};
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
            return Err("original executable stop");
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
    ExecutionSite::Entry(FuncId::new(160))
}
fn run(module: &Module) -> (Vec<SpecLinkViolation>, Observer) {
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let errors = validate_spec_executable_links_observed(module, &mut s, site()).unwrap();
    assert_eq!(errors, validate_spec_executable_links(module));
    assert!(s.first_refusal().is_none());
    assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
    assert!(o.events.iter().all(|e| e.site == site()));
    assert_eq!(o.events.last().unwrap().phase, ExecutionPhase::Publication);
    (errors, o)
}
fn raw<'a, O: ExecutionObserver>(
    state: &mut State<'a>,
    module: &'a Module,
    work: &mut Work<'_, '_, O>,
) -> R {
    state.run(module, work)?;
    state.normalize(work)
}
fn drain<O: ExecutionObserver>(state: &mut State<'_>, work: &mut Work<'_, '_, O>) {
    state.retire_scratch(work);
    state.consume_errors(work);
}
fn empty(state: &State<'_>) -> bool {
    state.fields.iter().all(|s| s.capacity() == 0)
        && state.detail.capacity() == 0
        && state.tasks.capacity() == 0
        && state.pending.is_none()
        && state.errors.capacity() == 0
}
fn trace(module: &Module) -> Observer {
    // Exact same private raw entry path as custody/interior replays; no extra
    // public-wrapper initial header callback is present in either path.
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = State::default();
    raw(&mut state, module, &mut w).unwrap();
    assert_eq!(state.errors, validate_spec_executable_links(module));
    drain(&mut state, &mut w);
    assert!(empty(&state));
    o
}
fn detail(error: &SpecLinkViolation) -> &str {
    match error {
        SpecLinkViolation::ExecutableTargetInvalid { detail, .. } => detail,
        _ => panic!("variant"),
    }
}
