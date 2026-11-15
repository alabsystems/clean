// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use crate::interpret::InterpretOptions;
use crate::{FuncId, ProofDigestAlgorithm, ProofTransform, ProofTransformStage};
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
    ExecutionSite::Entry(FuncId::new(9712))
}
#[derive(Clone)]
struct Input {
    manifest: ProofLineageManifest,
    roots: Vec<ProofLineageId>,
    source: Option<ProofDigest>,
}
type Census = (
    BTreeSet<ProofId>,
    BTreeSet<ProofCertificateRef>,
    BTreeSet<ProofDigest>,
);
fn census(m: &Members<'_>) -> Census {
    (
        m.obligations.iter().copied().collect(),
        m.certificates.iter().map(|r| (*r).clone()).collect(),
        m.sources.iter().copied().collect(),
    )
}
fn expected(input: &Input) -> (Census, (BTreeSet<ProofId>, BTreeSet<ProofCertificateRef>)) {
    (
        crate::request::lineage_closure(&input.manifest, &input.roots),
        crate::request::source_bound_lineage_membership(
            &input.manifest,
            &input.roots,
            input.source,
        ),
    )
}
fn observed(input: &Input) -> (Observer, usize) {
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let out = input
        .manifest
        .request_lineage_observed(&input.roots, input.source, &mut s, site())
        .unwrap();
    let end = calls.get();
    let old = expected(input);
    assert_eq!(census(&out.reachable), old.0);
    let bound = census(&out.bound);
    assert_eq!((bound.0, bound.1), old.1);
    assert!(bound.2.is_empty());
    out.retire_observed(&mut s, site()).unwrap();
    assert!(s.first_refusal().is_none());
    assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
    drop(s);
    assert!(o.events.iter().all(|p| p.site == site()));
    (o, end)
}
fn body<'m>(st: &mut State<'m>, i: &'m Input, w: &mut Work<'_, '_, Observer>) -> R {
    st.run(&i.manifest, &i.roots, i.source, w)
}
fn drain(st: &mut State<'_>, w: &mut Work<'_, '_, Observer>) {
    st.scratch(w);
    st.out.retire(w);
}
fn empty(st: &State<'_>) {
    for m in [&st.current, &st.out.reachable, &st.out.bound] {
        assert_eq!(m.obligations.capacity(), 0);
        assert_eq!(m.certificates.capacity(), 0);
        assert_eq!(m.sources.capacity(), 0);
    }
    assert_eq!(st.stack.capacity(), 0);
    assert_eq!(st.seen.capacity(), 0);
}
