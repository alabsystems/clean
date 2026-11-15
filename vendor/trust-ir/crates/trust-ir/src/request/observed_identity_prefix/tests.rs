// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Source-authored UNRUN: actual original whole validation prefix projection.
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use crate::interpret::InterpretOptions;
use crate::{Module, ModuleCompleteness, Ty};
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
    ExecutionSite::Entry(crate::FuncId::new(9771))
}
fn selected(e: &E) -> bool {
    matches!(
        e,
        E::UnsupportedSchemaVersion(_)
            | E::EmptyDigest {
                field: "trust_ir_module_digest"
            }
            | E::NonCryptographicDigest {
                field: "trust_ir_module_digest"
            }
            | E::TrustIrModuleHasNoWireIdentity { .. }
            | E::TrustIrModuleDigestMismatch { .. }
    )
}
fn ordinary(b: &NativeVerificationBundle) -> Vec<E> {
    b.validate()
        .err()
        .unwrap_or_default()
        .into_iter()
        .filter(selected)
        .collect()
}
fn observed(b: &NativeVerificationBundle) -> (Vec<E>, Observer, usize) {
    let mut o = Observer::default();
    let c = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let rows = b.identity_prefix_errors_observed(&mut s, site()).unwrap();
    assert_eq!(rows, ordinary(b));
    let saved = rows.clone();
    let end = c.get();
    retire_native_bundle_errors_observed(rows, &mut s, site()).unwrap();
    assert!(s.first_refusal().is_none());
    assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
    drop(s);
    assert!(o.events.iter().all(|p| p.site == site()));
    (saved, o, end)
}
fn empty(st: &State) {
    assert_eq!(st.batch.capacity(), 0);
    assert!(st.pending.is_none() && st.actual.is_none());
    assert_eq!(st.errors.capacity(), 0);
}
fn drain(st: &mut State, w: &mut Work<'_, '_, Observer>) {
    st.retire_scratch(w);
    w.record(1, size_of::<Vec<E>>());
    let _ = retire_native_bundle_errors_observed(take(&mut st.errors), w.session, w.site);
}
