// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Source-authored UNRUN controls; ordinary encoding-result oracle, no authority.
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use crate::{FuncId, interpret::InterpretOptions};
use std::{cell::Cell, rc::Rc};
mod custody;
mod fixtures;
mod parity;
mod stops;
use fixtures::{fixture, minimal};
#[derive(Default)]
struct Observer {
    events: Vec<ExecutionProgress>,
    record: bool,
    calls: Rc<Cell<usize>>,
    stop: Option<usize>,
    arm: Option<Rc<Cell<bool>>>,
    stop_retirement: bool,
    work: usize,
    bytes: usize,
    work_cap: Option<usize>,
    byte_cap: Option<usize>,
}
impl ExecutionObserver for Observer {
    type Refusal = &'static str;
    fn admit(&mut self, p: ExecutionProgress) -> Result<(), Self::Refusal> {
        let n = self.calls.get() + 1;
        self.calls.set(n);
        if self.record {
            self.events.push(p);
        }
        if self.stop == Some(n) {
            return Err("interior");
        }
        if self.arm.as_ref().is_some_and(|a| a.get()) {
            return Err("interrupt");
        }
        if self.stop_retirement && p.phase == ExecutionPhase::ScratchRetirement {
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
    ExecutionSite::Entry(FuncId::new(9741))
}
fn ordinary(a: &SignatureAbi) -> Reply {
    a.validate_encoding_limits().map(|()| a.to_canonical_text())
}
fn run(a: &SignatureAbi, record: bool) -> (Reply, Observer, usize) {
    let mut o = Observer {
        record,
        ..Observer::default()
    };
    let c = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let reply = a
        .canonical_text_encoding_result_observed(&mut s, site())
        .unwrap();
    assert_eq!(reply, ordinary(a));
    let saved = reply.clone();
    let end = c.get();
    SignatureAbi::retire_encoding_result_observed(reply, &mut s, site()).unwrap();
    assert!(s.first_refusal().is_none());
    assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
    drop(s);
    assert!(o.events.iter().all(|p| p.site == site()));
    (saved, o, end)
}
fn too_many_bytes() -> SignatureAbi {
    let mut a = minimal();
    a.frontend.name = "x".repeat(MAX_ABI_TEXT_BYTES + 1);
    a
}
fn too_many_nodes() -> SignatureAbi {
    let mut a = minimal();
    a.target.features = vec![String::new(); MAX_NODES];
    a
}
fn escaped_limit() -> SignatureAbi {
    let mut a = minimal();
    a.frontend.name = "\0".repeat(MAX_ABI_TEXT_BYTES / 2);
    a
}
fn drain(pending: &mut Option<Reply>, out: &mut Writer<'_, '_, Observer>) {
    retire_text(take(&mut out.text), out);
    retire_pending(pending, out);
}
