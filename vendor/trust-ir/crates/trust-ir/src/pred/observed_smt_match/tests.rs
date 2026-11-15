// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored UNRUN: exact ordinary text equality, original stops and custody.
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use crate::{FuncId, interpret::InterpretOptions};
mod custody;
mod error_precedence;
mod parity;
mod stops;
#[derive(Default)]
struct Observer {
    events: Vec<ExecutionProgress>,
    stop: Option<usize>,
    cleanup_after: Option<usize>,
    work: usize,
    bytes: usize,
    work_cap: Option<usize>,
    byte_cap: Option<usize>,
}
impl ExecutionObserver for Observer {
    type Refusal = &'static str;
    fn admit(&mut self, e: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(e);
        if self.stop == Some(self.events.len()) {
            return Err("original predicate stop");
        }
        if e.phase == ExecutionPhase::ScratchRetirement
            && self.cleanup_after.is_some_and(|n| self.events.len() > n)
        {
            return Err("original cleanup stop");
        }
        self.work = self.work.checked_add(e.work).ok_or("overflow")?;
        self.bytes = self.bytes.checked_add(e.copy_bytes).ok_or("overflow")?;
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
    ExecutionSite::Entry(FuncId::new(461))
}
fn run(preds: &[Pred], universes: &[Universe], id: u32, text: &str) -> (bool, Observer) {
    let table = PredTable::new(preds, universes);
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let answer = table
        .smtlib_matches_observed(PredId::new(id), text, &mut s, site())
        .unwrap();
    assert_eq!(
        answer,
        table
            .smtlib_of_within(PredId::new(id), text.len())
            .as_deref()
            == Some(text)
    );
    assert!(s.first_refusal().is_none());
    assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
    drop(s);
    assert!(o.events.iter().all(|e| e.site == site()));
    assert_eq!(o.events.last().unwrap().phase, ExecutionPhase::Publication);
    (answer, o)
}
fn mixed() -> Vec<Pred> {
    vec![
        Pred::Top,
        Pred::Interval {
            lo: i128::MIN,
            hi: i128::MAX,
        },
        Pred::FiniteSet(vec![
            Constant::Bool(false),
            Constant::Int(-8),
            Constant::SymbolAddr {
                symbol: "raw λ\0尾".repeat(400),
                addend: -7,
            },
        ]),
        Pred::Conj(vec![PredId::new(1), PredId::new(2), PredId::new(0)]),
    ]
}
fn empty(state: &State<'_>) -> bool {
    state.tasks.capacity() == 0 && state.pending.is_none()
}
