// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored UNRUN; actual original full uniform set and source-address oracles.
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use crate::interpret::InterpretOptions;
use crate::value::FuncId;
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
            return Err("original uniform-class stop");
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
    ExecutionSite::Entry(FuncId::new(1511))
}
fn array(values: Vec<Constant>) -> Constant {
    Constant::Array(values)
}
fn bytes(values: &[u8]) -> Constant {
    Constant::Bytes {
        data: values.to_vec(),
        utf8: false,
    }
}
fn all(root: &Constant) -> Vec<&Constant> {
    let mut nodes = Vec::new();
    root.visit_constants(|n| nodes.push(n));
    nodes
}
fn run(root: &Constant) -> (usize, Observer, usize, usize) {
    let expected = root.uniform_element_lists();
    let nodes = all(root);
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let table = root.uniform_element_lists_observed(&mut s, site()).unwrap();
    let build = calls.get();
    assert!(core::ptr::eq(table._root, root));
    let count = table.rows.len();
    let expected_count = nodes.iter().filter(|n| expected.contains(n)).count();
    assert_eq!(count, expected_count);
    for node in nodes {
        assert_eq!(
            table.contains_observed(node, &mut s, site()).unwrap(),
            expected.contains(node)
        );
    }
    let queried = calls.get();
    table.retire_observed(&mut s, site()).unwrap();
    assert!(s.first_refusal().is_none());
    assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
    drop(s);
    assert!(o.events.iter().all(|e| e.site == site()));
    (count, o, build, queried)
}
fn sample() -> Constant {
    array(vec![
        Constant::Record(vec![(
            "é🦀label中".repeat(3),
            array(vec![Constant::Int(1), Constant::Int(1)]),
        )]),
        Constant::Record(vec![("é🦀label中".repeat(3), bytes(&[1, 1]))]),
    ])
}
fn empty(s: &State<'_>) {
    assert!(
        s.current.is_none()
            && s.building.is_none()
            && s.pending_key.is_none()
            && s.buckets.is_empty()
    );
    assert_eq!(
        s.stack.capacity()
            + s.results.capacity()
            + s.classes.capacity()
            + s.pending_bucket.capacity()
            + s.uniform.capacity(),
        0
    );
}
fn drain<O: ExecutionObserver>(s: &mut State<'_>, w: &mut Work<'_, '_, O>) {
    s.retire_scratch(w);
    w.rows(take(&mut s.uniform));
}
