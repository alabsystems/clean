// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored UNRUN; actual exact catalog data, no candidate/authority factory.
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use crate::interpret::InterpretOptions;
use crate::{BlockId, FuncTyId, Module};
use std::{cell::Cell, rc::Rc};
mod custody;
mod error_precedence;
mod parity;
mod stops;
#[derive(Default)]
pub(super) struct Observer {
    pub(super) events: Vec<ExecutionProgress>,
    pub(super) calls: Rc<Cell<usize>>,
    pub(super) work: Rc<Cell<usize>>,
    pub(super) bytes: Rc<Cell<usize>>,
    pub(super) stop: Option<usize>,
    pub(super) cleanup_after: Option<usize>,
    pub(super) work_cap: Option<usize>,
    pub(super) byte_cap: Option<usize>,
}
impl ExecutionObserver for Observer {
    type Refusal = &'static str;
    fn admit(&mut self, e: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(e);
        self.calls.set(self.events.len());
        if self.stop == Some(self.events.len()) {
            return Err("original catalog query stop");
        }
        if e.phase == ExecutionPhase::ScratchRetirement
            && self.cleanup_after.is_some_and(|n| self.events.len() > n)
        {
            return Err("cleanup");
        }
        self.work
            .set(self.work.get().checked_add(e.work).ok_or("overflow")?);
        self.bytes.set(
            self.bytes
                .get()
                .checked_add(e.copy_bytes)
                .ok_or("overflow")?,
        );
        if self.work_cap.is_some_and(|n| self.work.get() > n) {
            return Err("work");
        }
        if self.byte_cap.is_some_and(|n| self.bytes.get() > n) {
            return Err("copy");
        }
        Ok(())
    }
}

fn site() -> ExecutionSite {
    ExecutionSite::Entry(FuncId::new(1105))
}
fn fixture() -> Module {
    let mut m = Module::new("catalog");
    for (id, name) in [
        (u32::MAX, "max"),
        (3, "first"),
        (8, "only"),
        (3, "last"),
        (19, "one"),
        (19, "two"),
        (1, "small"),
    ] {
        m.functions.push(Function::new(
            FuncId::new(id),
            name,
            FuncTyId::new(0),
            BlockId::new(1),
        ));
    }
    m
}
fn setup<'m, O: ExecutionObserver>(
    m: &'m Module,
    s: &mut ObservedSession<'_, O>,
) -> ModuleFunctionCatalog<'m> {
    ModuleFunctionCatalog::new_observed(m, s, site()).unwrap()
}
fn run(m: &Module) -> (Observer, usize, usize) {
    let plain = ModuleFunctionCatalog::new(m);
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let a = setup(m, &mut s);
    let begin = calls.get();
    let out = a.ambiguous_ids_observed(&mut s, site()).unwrap();
    let end = calls.get();
    assert_eq!(out, plain.ambiguous_ids().collect::<Vec<_>>());
    Work {
        session: &mut s,
        site: site(),
    }
    .rows(out);
    a.retire_observed(&mut s, site()).unwrap();
    assert!(s.first_refusal().is_none());
    drop(s);
    (o, begin, end)
}
