// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Source-authored UNRUN: actual existing sealed issuer, never fake currency.
use super::*;
use crate::interpret::InterpretOptions;
use crate::request::{NativeEvidenceBundle, NativeRequestId};
use crate::{FuncId, Inst, InstrNode, ValueId};
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
    ExecutionSite::Entry(FuncId::new(9827))
}
fn observed(
    a: &SourceGenerationAuthority,
    b: &NativeVerificationBundle,
) -> (bool, Observer, usize) {
    let mut o = Observer::default();
    let c = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let answer = a
        .authorizes_bundle_kernel_less_observed(b, &mut s, site())
        .unwrap();
    assert_eq!(answer, a.authorizes_bundle(b));
    let end = c.get();
    assert!(s.first_refusal().is_none());
    assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
    assert!(o.events.iter().all(|p| p.site == site()));
    (answer, o, end)
}
fn empty(st: &State) {
    assert!(st.digest.is_none() && st.validation.is_none() && st.answer.is_none());
}
