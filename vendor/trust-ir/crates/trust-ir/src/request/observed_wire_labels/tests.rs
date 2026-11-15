// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Source-authored UNRUN: actual original raw location oracle and ownership.
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use crate::interpret::InterpretOptions;
use crate::value::FuncTyId;
use crate::{BlockId, ModuleCompleteness, Ty};
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
    ExecutionSite::Entry(FuncId::new(9761))
}
fn ordinary(m: &Module, row: &BinaryProjectionError) -> E {
    let (location, construct) =
        super::super::bundle::wire_identity_site_original_for_observed_tests(m, row);
    E::TrustIrModuleHasNoWireIdentity {
        location,
        construct,
    }
}
fn drain(r: &mut Render, w: &mut Work<'_, '_, Observer>) {
    r.retire_scratch(w);
    w.record(1, size_of::<Vec<E>>());
    let _ = retire_native_bundle_errors_observed(take(&mut r.errors), w.session, w.site);
}
fn empty(r: &Render) {
    assert_eq!(r.text.capacity(), 0);
    assert!(r.pending.is_none());
    assert_eq!(r.errors.capacity(), 0);
}
fn mapped(m: &Module, row: &BinaryProjectionError) -> (E, Observer, usize) {
    let mut o = Observer::default();
    let c = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut r = Render::default();
    r.map(m, row, &mut w).unwrap();
    assert_eq!(r.errors, vec![ordinary(m, row)]);
    let saved = r.errors[0].clone();
    let end = c.get();
    drain(&mut r, &mut w);
    empty(&r);
    drop(w);
    assert!(s.first_refusal().is_none());
    drop(s);
    (saved, o, end)
}
fn observed(b: &NativeVerificationBundle) -> (Vec<E>, Observer, usize) {
    let mut o = Observer::default();
    let c = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let rows = b.wire_identity_errors_observed(&mut s, site()).unwrap();
    let expected: Vec<_> = b
        .module
        .wire_image_refusals()
        .iter()
        .map(|row| ordinary(&b.module, row))
        .collect();
    assert_eq!(rows, expected);
    let saved = rows.clone();
    let end = c.get();
    retire_native_bundle_errors_observed(rows, &mut s, site()).unwrap();
    assert!(s.first_refusal().is_none());
    assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
    drop(s);
    assert!(o.events.iter().all(|p| p.site == site()));
    (saved, o, end)
}
