// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use crate::FuncId;
use crate::interpret::InterpretOptions;
use std::{cell::Cell, rc::Rc};
mod custody;
mod parity;
mod stops;
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
    ExecutionSite::Entry(FuncId::new(9705))
}
fn observed(name: &str) -> (String, Observer, usize) {
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let out = canonical_tool_name_observed(name, &mut s, site()).unwrap();
    let end = calls.get();
    assert_eq!(out, crate::request::canonical_tool_name(name));
    let copy = out.clone();
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    w.record(1, size_of::<String>());
    w.text_drop(out);
    drop(w);
    assert!(s.first_refusal().is_none());
    assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
    drop(s);
    assert!(o.events.iter().all(|p| p.site == site()));
    (copy, o, end)
}
fn names() -> [String; 4] {
    [
        " !TRUST---MC..NATIVE_".to_owned() + &"A".repeat(2700),
        "[Other]-".to_owned() + &"B".repeat(2100),
        " \u{2003}---🦀".into(),
        "trust-ir".into(),
    ]
}
fn drain(st: &mut State, w: &mut Work<'_, '_, Observer>) {
    st.retire_scratch(w);
    w.record(1, size_of::<String>());
    w.text_drop(take(&mut st.canonical));
}
fn empty(st: &State) {
    assert_eq!(st.normalized.capacity() + st.canonical.capacity(), 0);
}
