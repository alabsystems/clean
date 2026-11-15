// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use crate::interpret::InterpretOptions;
use crate::{FuncId, ProofDigest, ProofId};
use std::{cell::Cell, rc::Rc};
mod custody;
mod fixtures;
mod parity;
mod stops;
use fixtures::*;
#[derive(Default)]
struct Observer {
    events: Vec<ExecutionProgress>,
    stop: Option<usize>,
    calls: Rc<Cell<usize>>,
    arm: Option<Rc<Cell<bool>>>,
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
        self.work = self.work.checked_add(p.work).ok_or("overflow")?;
        self.bytes = self.bytes.checked_add(p.copy_bytes).ok_or("overflow")?;
        if self.stop == Some(self.events.len()) {
            return Err("interior");
        }
        if self.arm.as_ref().is_some_and(|a| a.get()) {
            return Err("interrupt");
        }
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
    ExecutionSite::Entry(FuncId::new(9706))
}
#[derive(Clone, Copy)]
enum Case {
    Tool,
    Verifier,
    Replay,
    Certificate,
}
fn cases() -> [Case; 4] {
    [Case::Tool, Case::Verifier, Case::Replay, Case::Certificate]
}
fn request() -> NativeRequestId {
    NativeRequestId::new(39)
}
fn check<'a>(f: &'a Fixture, c: Case, suite: Suite) -> Check<'a> {
    match c {
        Case::Tool => Check::Tool("evidence.verifier", &f.tool),
        Case::Verifier => Check::Verifier(request(), suite, &f.tool),
        Case::Replay => Check::Replay(request(), suite, &f.replay),
        Case::Certificate => Check::Certificate(request(), suite, &f.cert),
    }
}
fn ordinary(f: &Fixture, c: Case, suite: Suite) -> Vec<E> {
    let mut out = Vec::new();
    match c {
        Case::Tool => {
            crate::request::validate_tool_identity("evidence.verifier", &f.tool, &mut out)
        }
        Case::Verifier => {
            crate::request::validate_expected_verifier_identity(request(), suite, &f.tool, &mut out)
        }
        Case::Replay => {
            crate::request::validate_replay_identity(request(), suite, &f.replay, &mut out)
        }
        Case::Certificate => {
            crate::request::validate_certificate_prover_suite(request(), suite, &f.cert, &mut out)
        }
    }
    out
}
fn observed(f: &Fixture, c: Case, suite: Suite) -> (Vec<E>, Observer, usize) {
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let rows = run(check(f, c, suite), &mut s, site()).unwrap();
    let end = calls.get();
    assert_eq!(rows, ordinary(f, c, suite));
    let copy = rows.clone();
    retire_native_bundle_errors_observed(rows, &mut s, site()).unwrap();
    assert!(s.first_refusal().is_none());
    assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
    drop(s);
    assert!(o.events.iter().all(|p| p.site == site()));
    (copy, o, end)
}
fn drain(st: &mut State, w: &mut Work<'_, '_, Observer>) {
    st.retire_scratch(w);
    w.record(1, size_of::<Vec<E>>());
    let _ = retire_native_bundle_errors_observed(take(&mut st.errors), w.session, w.site);
}
fn empty(st: &State) {
    assert!(st.pending.is_none());
    assert_eq!(
        st.canonical.capacity() + st.text.capacity() + st.errors.capacity(),
        0
    );
}
