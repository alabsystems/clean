// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use crate::interpret::InterpretOptions;
use crate::request::{NativeAssertionId, NativeReplayAtomId, NativeVerificationRequest};
use crate::{FuncId, ProofDigest, ProofFormula};
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
    ExecutionSite::Entry(FuncId::new(9710))
}
enum Input {
    Mc(TrustMcNativeRequest),
    Wp(TrustWpNativeRequest),
    Diagnostics(NativeRequestId, NativeDiagnosticsPolicy),
}
impl Input {
    fn check(&self) -> Check<'_> {
        match self {
            Self::Mc(r) => Check::Mc(r),
            Self::Wp(r) => Check::Wp(r),
            Self::Diagnostics(id, p) => Check::Diagnostics(*id, p),
        }
    }
    fn ordinary(&self) -> Vec<E> {
        let mut rows = Vec::new();
        match self {
            Self::Mc(r) => crate::request::validate_trust_mc_request(r, &mut rows),
            Self::Wp(r) => crate::request::validate_trust_wp_request(r, &mut rows),
            Self::Diagnostics(id, p) => crate::request::validate_diagnostics(*id, p, &mut rows),
        };
        rows
    }
    fn observed<O: ExecutionObserver>(&self, s: &mut ObservedSession<'_, O>) -> R<Vec<E>> {
        match self {
            Self::Mc(r) => r.mode_errors_observed(s, site()),
            Self::Wp(r) => r.mode_errors_observed(s, site()),
            Self::Diagnostics(id, p) => p.request_errors_observed(*id, s, site()),
        }
    }
}
fn observed(input: &Input) -> (Vec<E>, Observer, usize) {
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let rows = input.observed(&mut s).unwrap();
    let end = calls.get();
    assert_eq!(rows, input.ordinary());
    let copy = rows.clone();
    retire_native_bundle_errors_observed(rows, &mut s, site()).unwrap();
    assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
    assert!(s.first_refusal().is_none());
    drop(s);
    assert!(o.events.iter().all(|p| p.site == site()));
    (copy, o, end)
}
fn body(st: &mut State, input: &Input, w: &mut Work<'_, '_, Observer>) -> R {
    match input.check() {
        Check::Mc(r) => st.mc(r, w),
        Check::Wp(r) => st.wp(r, w),
        Check::Diagnostics(id, p) => st.diagnostics(id, p, w),
    }
}
fn drain(st: &mut State, w: &mut Work<'_, '_, Observer>) {
    st.retire_scratch(w);
    w.record(1, size_of::<Vec<E>>());
    let _ = retire_native_bundle_errors_observed(take(&mut st.errors), w.session, w.site);
}
fn empty(st: &State) {
    assert!(st.pending.is_none());
    assert_eq!(st.errors.capacity(), 0);
}
