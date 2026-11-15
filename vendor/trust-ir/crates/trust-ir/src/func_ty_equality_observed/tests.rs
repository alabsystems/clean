// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::field_reassign_with_default,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use crate::interpret::InterpretOptions;
use crate::signature_abi::*;
mod fixtures;
mod parity;
mod stops;
use fixtures::*;

#[derive(Default)]
struct Observer {
    events: Vec<ExecutionProgress>,
    stop: Option<usize>,
    work: usize,
    bytes: usize,
    work_cap: Option<usize>,
    copy_cap: Option<usize>,
}
impl ExecutionObserver for Observer {
    type Refusal = &'static str;
    fn admit(&mut self, event: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(event);
        if self.stop == Some(self.events.len()) {
            return Err("original FuncTy stop");
        }
        self.work = self.work.checked_add(event.work).ok_or("work overflow")?;
        self.bytes = self
            .bytes
            .checked_add(event.copy_bytes)
            .ok_or("copy overflow")?;
        if self.work_cap.is_some_and(|cap| self.work > cap) {
            return Err("original work");
        }
        if self.copy_cap.is_some_and(|cap| self.bytes > cap) {
            return Err("original copy");
        }
        Ok(())
    }
}
fn site() -> ExecutionSite {
    ExecutionSite::Entry(crate::FuncId::new(1701))
}
fn run(a: &FuncTy, b: &FuncTy) -> (bool, Observer) {
    let mut observer = Observer::default();
    let result;
    {
        let mut options = InterpretOptions::default();
        options.fuel = 0;
        let mut session = ObservedSession::new(options, &mut observer);
        result = a.structural_eq_observed(b, &mut session, site()).unwrap();
        assert_eq!(session.remaining_fuel(), 0);
        assert!(session.first_refusal().is_none());
    }
    assert_eq!(result, a == b);
    assert!(observer.events.iter().all(|event| event.site == site()));
    assert_eq!(
        observer.events.last().unwrap().phase,
        ExecutionPhase::Publication
    );
    (result, observer)
}
fn mismatch(a: &FuncTy, b: &FuncTy) {
    assert_ne!(a, b);
    assert!(!run(a, b).0);
    assert!(!run(b, a).0);
}
fn abi_mut(sig: &mut FuncTy) -> &mut SignatureAbi {
    sig.abi.as_mut().unwrap()
}
