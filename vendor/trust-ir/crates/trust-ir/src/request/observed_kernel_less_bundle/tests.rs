// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Source-authored UNRUN; exact complete ordinary inner Result, not authority.
use super::*;
use crate::interpret::InterpretOptions;
use crate::request::*;
use crate::{FuncId, ModuleCompleteness, ProofDigest, ProofStatus, Ty};
use std::{cell::Cell, rc::Rc};
mod custody;
mod fixtures;
mod parity;
mod stops;
use fixtures::*;
#[derive(Default)]
struct Observer {
    events: Vec<ExecutionProgress>,
    calls: Rc<Cell<usize>>,
    stop: Option<usize>,
    arm: Option<Rc<Cell<bool>>>,
    retirement_stop: bool,
    work: usize,
    bytes: usize,
    work_cap: Option<usize>,
    byte_cap: Option<usize>,
}
impl ExecutionObserver for Observer {
    type Refusal = &'static str;
    fn admit(&mut self, p: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(p);
        self.calls.set(self.events.len());
        if self.stop == Some(self.events.len()) {
            return Err("interior");
        }
        if self.arm.as_ref().is_some_and(|a| a.get()) {
            return Err("interrupt");
        }
        if self.retirement_stop && p.phase == ExecutionPhase::ScratchRetirement {
            return Err("retirement");
        }
        self.work = self.work.checked_add(p.work).ok_or("overflow")?;
        self.bytes = self.bytes.checked_add(p.copy_bytes).ok_or("overflow")?;
        if self.work_cap.is_some_and(|n| self.work > n) {
            return Err("work");
        }
        if self.byte_cap.is_some_and(|n| self.bytes > n) {
            return Err("copy");
        }
        Ok(())
    }
}
fn site() -> ExecutionSite {
    ExecutionSite::Entry(FuncId::new(9819))
}
fn observed(b: &NativeVerificationBundle) -> (Validation, Observer, usize) {
    let mut o = Observer::default();
    let c = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let result = b.validate_kernel_less_observed(&mut s, site()).unwrap();
    assert_eq!(result, b.validate());
    let saved = result.clone();
    let end = c.get();
    NativeVerificationBundle::retire_kernel_less_validation_observed(result, &mut s, site())
        .unwrap();
    assert!(s.first_refusal().is_none());
    assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
    assert!(o.events.iter().all(|p| p.site == site()));
    (saved, o, end)
}
fn drain(st: &mut State, w: &mut Work<'_, '_, Observer>) {
    st.retire_scratch(w);
    st.retire_errors(w);
    st.retire_output(w);
}
fn empty(st: &State) {
    assert!(st.batch.is_none() && st.pending.is_none() && st.output.is_none());
    assert_eq!(st.errors.capacity(), 0);
    assert_eq!(st.batch_capacity, 0);
}
fn child_bound(b: &NativeVerificationBundle, group: super::children::Group) -> usize {
    let mut o = Observer::default();
    let c = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut st = State::default();
    st.child(b, group, &mut w).unwrap();
    let end = c.get();
    drain(&mut st, &mut w);
    end
}
