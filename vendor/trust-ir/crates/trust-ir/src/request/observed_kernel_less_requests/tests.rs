// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Source-authored UNRUN; real original kernel-less whole-request oracle.
use super::*;
use crate::interpret::InterpretOptions;
use crate::request::{
    NativeRequestId, TrustMcVerificationMode as McMode, TrustVcVerificationMode as Mode,
    TrustWpVerificationMode as WpMode,
};
use crate::{FuncId, ProofDigest, ProofEvidence};
use std::{cell::Cell, rc::Rc};
mod custody;
mod fixtures;
mod parity;
mod source_binding;
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
    ExecutionSite::Entry(FuncId::new(9811))
}
fn ordinary(b: &NativeVerificationBundle) -> Vec<E> {
    b.request_errors_original_for_observed_tests()
}
fn observed(b: &NativeVerificationBundle) -> (Vec<E>, Observer, usize) {
    let mut o = Observer::default();
    let c = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let rows = b
        .request_errors_kernel_less_observed(&mut s, site())
        .unwrap();
    assert_eq!(rows, ordinary(b));
    let saved = rows.clone();
    let end = c.get();
    retire_native_bundle_errors_observed(rows, &mut s, site()).unwrap();
    assert!(s.first_refusal().is_none());
    assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
    assert!(o.events.iter().all(|p| p.site == site()));
    (saved, o, end)
}
fn drain(st: &mut State, w: &mut Work<'_, '_, Observer>) {
    st.retire_scratch(w);
    w.record(1, size_of::<Vec<E>>());
    let _ = retire_native_bundle_errors_observed(take(&mut st.errors), w.session, w.site);
}
fn empty(st: &State) {
    assert!(st.reference.is_none() && st.pending.is_none() && st.batch.is_none());
    assert_eq!(st.known.capacity(), 0);
    assert_eq!(st.text.capacity(), 0);
    assert_eq!(st.errors.capacity(), 0);
    assert_eq!(st.batch_capacity, 0);
}
fn private_vc_bound(b: &NativeVerificationBundle) -> (Vec<ExecutionProgress>, usize) {
    let mut o = Observer::default();
    let c = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut st = known(b);
    st.vc(b, vc_ref(b), &mut w).unwrap();
    let end = c.get();
    drain(&mut st, &mut w);
    (o.events, end)
}
