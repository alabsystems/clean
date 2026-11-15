// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use crate::interpret::InterpretOptions;
use crate::request::{NativeAdapterInput, NativeBundleProducer};
use crate::{
    BlockId, FuncId, FuncTyId, Inst, InstrNode, Module, ProofLineageId, ProofLineageManifest,
    ProofLineageNode, ProofTransform, ProofTransformStage, ValueId,
};
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
    ExecutionSite::Entry(FuncId::new(9702))
}
fn rules() -> [Rule; 2] {
    [Rule::Reference, Rule::Lineage]
}
fn ordinary(bundle: &NativeVerificationBundle, rule: Rule) -> Vec<E> {
    // Whole actual unchanged validator is the oracle; these variants are
    // exclusive to the two complete leaves. No copied scan computes expected.
    bundle
        .validate()
        .err()
        .unwrap_or_default()
        .into_iter()
        .filter(|e| match rule {
            Rule::Reference => matches!(e, E::RustReferenceAsPermissionBorrow { .. }),
            Rule::Lineage => matches!(
                e,
                E::SourceDigestNotInLineage(_) | E::TrustIrDigestNotInLineage(_)
            ),
        })
        .collect()
}
fn observed(bundle: &NativeVerificationBundle, rule: Rule) -> (Vec<E>, Observer, usize) {
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let actual = run(bundle, rule, &mut s, site()).unwrap();
    let end = calls.get();
    assert_eq!(actual, ordinary(bundle, rule));
    let copy = actual.clone();
    retire_native_bundle_errors_observed(actual, &mut s, site()).unwrap();
    assert!(s.first_refusal().is_none());
    assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
    drop(s);
    assert!(o.events.iter().all(|p| p.site == site()));
    (copy, o, end)
}
fn drain(state: &mut State, w: &mut Work<'_, '_, Observer>) {
    state.retire_scratch(w);
    w.record(1, size_of::<Vec<E>>());
    let _ = retire_native_bundle_errors_observed(take(&mut state.errors), w.session, w.site);
}
fn empty(state: &State) {
    assert!(state.pending.is_none());
    assert_eq!(state.text.capacity() + state.errors.capacity(), 0);
}
