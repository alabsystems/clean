// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use crate::interpret::InterpretOptions;
use crate::request::{
    NativeAssertionId, NativeObligationCause, NativeReplayAtomId, NativeUnsupportedMode,
};
use crate::{FuncId, Module, ProofFormula, SourceSpan, pred::Pred};
use std::{cell::Cell, collections::BTreeSet, rc::Rc};
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
    ExecutionSite::Entry(FuncId::new(9711))
}
fn request() -> NativeRequestId {
    NativeRequestId::new(u32::MAX)
}
#[derive(Clone)]
struct Input {
    context: NativeReplayContext,
    obligations: Vec<ProofId>,
    facts: NativeCompilerFacts,
    module: Module,
}
impl Input {
    fn ordinary(&self) -> Vec<E> {
        let requested: BTreeSet<_> = self.obligations.iter().copied().collect();
        let mut out = Vec::new();
        crate::request::validate_replay_context(
            request(),
            &requested,
            &self.facts,
            &self.context,
            &self.module.pred_table(),
            &mut out,
        );
        out
    }
    fn observed<O: ExecutionObserver>(&self, s: &mut ObservedSession<'_, O>) -> R<Vec<E>> {
        self.context.validation_errors_observed(
            request(),
            &self.obligations,
            &self.facts,
            &self.module.pred_table(),
            s,
            site(),
        )
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
    st.run(
        &input.context,
        request(),
        &input.obligations,
        &input.facts,
        &input.module.pred_table(),
        w,
    )
}
fn drain(st: &mut State, w: &mut Work<'_, '_, Observer>) {
    st.retire_scratch(w);
    w.record(1, size_of::<Vec<E>>());
    let _ = retire_native_bundle_errors_observed(take(&mut st.errors), w.session, w.site);
}
fn empty(st: &State) {
    assert_eq!(st.text.capacity(), 0);
    assert!(st.pending.is_none());
    assert_eq!(st.errors.capacity(), 0);
}
