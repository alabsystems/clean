// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored UNRUN; actual ordinary table-free value and shape text oracles.
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use crate::interpret::InterpretOptions;
use crate::value::{FuncId, FuncTyId};
use std::{cell::Cell, rc::Rc};
mod custody;
mod parity;
mod stops;
#[derive(Default)]
struct Observer {
    events: Vec<ExecutionProgress>,
    calls: Rc<Cell<usize>>,
    work: Rc<Cell<usize>>,
    bytes: Rc<Cell<usize>>,
    stop: Option<usize>,
    work_cap: Option<usize>,
    byte_cap: Option<usize>,
}
impl ExecutionObserver for Observer {
    type Refusal = &'static str;
    fn admit(&mut self, e: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(e);
        self.calls.set(self.events.len());
        if self.stop == Some(self.events.len()) {
            return Err("original constant-value stop");
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
    ExecutionSite::Entry(FuncId::new(1471))
}
fn predicate(value: &Constant, ty: &Ty, bits: u32) -> (bool, Observer, usize) {
    let expected = value.value_matches_ty(ty, bits);
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let result = value
        .value_matches_ty_observed(ty, bits, &mut s, site())
        .unwrap();
    let end = calls.get();
    assert_eq!(result, expected);
    assert!(s.first_refusal().is_none());
    assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
    drop(s);
    (expected, o, end)
}
fn label(value: &Constant) -> (String, Observer, usize) {
    let expected = value.shape_label();
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let result = value.shape_label_observed(&mut s, site()).unwrap();
    let end = calls.get();
    assert_eq!(result, expected);
    Work {
        session: &mut s,
        site: site(),
    }
    .flat(result);
    assert!(s.first_refusal().is_none());
    drop(s);
    (expected, o, end)
}
fn branching() -> (Constant, Ty) {
    (
        Constant::Vector(vec![
            Constant::Vector(vec![Constant::Int(1), Constant::Int(2)]),
            Constant::Vector(vec![Constant::Int(3), Constant::Int(255)]),
        ]),
        Ty::Vector(Box::new(Ty::Vector(Box::new(Ty::U8), 2)), 2),
    )
}
fn symbol() -> Constant {
    Constant::SymbolAddr {
        symbol: "é🦀symbol中".repeat(400),
        addend: i64::MIN,
    }
}
fn empty(s: &State<'_>) {
    assert_eq!(s.pending.capacity() + s.label.capacity(), 0);
}
