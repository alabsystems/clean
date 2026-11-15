// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored UNRUN. Actual ordinary methods are the semantic parity oracle.
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use crate::interpret::InterpretOptions;
use crate::{
    ArgExt, BlockId, CallingConv, Endianness, FuncId, FuncTyId, ParamAttrs, PassMode,
    StructPassingPolicy,
};
use std::{
    cell::{Cell, RefCell},
    rc::Rc,
};
mod custody;
mod descriptor;
mod fixtures;
mod parity;
mod reconciliation;
mod stops;
use fixtures::*;
#[derive(Default)]
struct Observer {
    events: Vec<ExecutionProgress>,
    trace: Rc<RefCell<Vec<ExecutionProgress>>>,
    interrupt: Option<Rc<Cell<bool>>>,
    calls: Rc<Cell<usize>>,
    stop: Option<usize>,
    work: usize,
    bytes: usize,
    work_cap: Option<usize>,
    byte_cap: Option<usize>,
    cleanup: Option<Rc<Cell<bool>>>,
}
impl ExecutionObserver for Observer {
    type Refusal = &'static str;
    fn admit(&mut self, e: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(e);
        self.trace.borrow_mut().push(e);
        self.calls.set(self.events.len());
        if self.stop == Some(self.events.len()) {
            return Err("original signature semantic stop");
        }
        if self.interrupt.as_ref().is_some_and(|a| a.get()) {
            return Err("interrupt");
        }
        if self.cleanup.as_ref().is_some_and(|a| a.get())
            && e.phase == ExecutionPhase::ScratchRetirement
        {
            return Err("cleanup");
        }
        self.work = self.work.checked_add(e.work).ok_or("overflow")?;
        self.bytes = self.bytes.checked_add(e.copy_bytes).ok_or("overflow")?;
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
    ExecutionSite::Entry(FuncId::new(6401))
}
fn ordinary(a: &SignatureAbi, request: &Request<'_>) -> Result<(), String> {
    match request {
        Request::Validate(sig) => a.validate(sig),
        Request::Target(target) => a.validate_target(*target),
        Request::Function(f) => a.reconcile_function(f),
    }
}
fn invoke<O: ExecutionObserver>(
    a: &SignatureAbi,
    request: &Request<'_>,
    s: &mut ObservedSession<'_, O>,
) -> R<Result<(), String>> {
    match request {
        Request::Validate(sig) => a.validate_observed(sig, s, site()),
        Request::Target(target) => a.validate_target_observed(*target, s, site()),
        Request::Function(f) => a.reconcile_function_observed(f, s, site()),
    }
}
fn retire<O: ExecutionObserver>(out: Result<(), String>, s: &mut ObservedSession<'_, O>) {
    if let Err(text) = out {
        Work {
            session: s,
            site: site(),
        }
        .flat(text);
    }
}
fn run(a: &SignatureAbi, request: Request<'_>) -> (Result<(), String>, Observer, usize) {
    let expected = ordinary(a, &request);
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let out = invoke(a, &request, &mut s).unwrap();
    let end = calls.get();
    assert_eq!(out, expected);
    retire(out, &mut s);
    assert!(s.first_refusal().is_none());
    assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
    drop(s);
    assert!(o.events.iter().all(|e| e.site == site()));
    (expected, o, end)
}
fn semantic_start(events: &[ExecutionProgress]) -> usize {
    events
        .iter()
        .rposition(|e| e.phase == ExecutionPhase::CanonicalSerialization)
        .map_or(0, |i| i + 1)
}
fn empty(s: &State) {
    assert_eq!(
        s.wire.capacity()
            + s.reason.capacity()
            + s.context.capacity()
            + s.ranges.capacity()
            + s.parameters.capacity()
            + s.results.capacity(),
        0
    );
}
fn drain<O: ExecutionObserver>(s: &mut State, w: &mut Work<'_, '_, O>) {
    s.retire_scratch(w);
    w.flat(take(&mut s.reason));
}
