// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored UNRUN: exact ordinary borrowed predicates are the parity oracle.
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use crate::interpret::{InstructionSite, InterpretOptions};
use crate::value::{BlockId, FuncId, GlobalId};
mod parity;
mod stops;
#[derive(Default)]
struct Observer {
    events: Vec<ExecutionProgress>,
    stop: Option<usize>,
    work: usize,
    bytes: usize,
    work_cap: Option<usize>,
    byte_cap: Option<usize>,
}
impl ExecutionObserver for Observer {
    type Refusal = &'static str;
    fn admit(&mut self, event: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(event);
        if self.stop == Some(self.events.len()) {
            return Err("original coverage stop");
        }
        self.work = self.work.checked_add(event.work).ok_or("work overflow")?;
        self.bytes = self
            .bytes
            .checked_add(event.copy_bytes)
            .ok_or("copy overflow")?;
        if self.work_cap.is_some_and(|cap| self.work > cap) {
            return Err("work");
        }
        if self.byte_cap.is_some_and(|cap| self.bytes > cap) {
            return Err("copy");
        }
        Ok(())
    }
}
#[derive(Clone, Copy)]
enum Query<'a> {
    Set(&'a EffectSet, &'a EffectSet),
    Summary(&'a EffectSummary, &'a EffectSummary),
    Names(&'a EffectSummary),
}
impl Query<'_> {
    fn expected(self) -> bool {
        match self {
            Self::Set(a, b) => a.covers(b),
            Self::Summary(a, b) => a.covers(b),
            Self::Names(summary) => summary.names_a_global(),
        }
    }
    fn call<O: ExecutionObserver>(
        self,
        original: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<bool> {
        match self {
            Self::Set(a, b) => a.covers_observed(b, original, site),
            Self::Summary(a, b) => a.covers_observed(b, original, site),
            Self::Names(summary) => summary.names_a_global_observed(original, site),
        }
    }
}
fn site() -> ExecutionSite {
    ExecutionSite::Entry(FuncId::new(247))
}
fn p(index: u32) -> EffectPlace {
    EffectPlace::ParamPointee { index }
}
fn g(index: u32) -> EffectPlace {
    EffectPlace::Global(GlobalId::new(index))
}
fn sets() -> Vec<EffectSet> {
    vec![
        EffectSet::Nothing,
        EffectSet::Everything,
        EffectSet::Places(Vec::new()),
        EffectSet::Places(vec![p(0)]),
        EffectSet::Places(vec![g(0)]),
        EffectSet::Places(vec![g(9), p(0), p(0), g(9)]),
        EffectSet::Places(vec![p(u32::MAX), g(u32::MAX)]),
    ]
}
fn summary(bits: u8) -> EffectSummary {
    EffectSummary {
        reads: EffectSet::Nothing,
        writes: EffectSet::Nothing,
        allocates: bits & 1 != 0,
        frees: bits & 2 != 0,
        may_unwind: bits & 4 != 0,
        io: bits & 8 != 0,
    }
}
fn trace(query: Query<'_>) -> Observer {
    let mut observer = Observer::default();
    let mut original = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(query.call(&mut original, site()), Ok(query.expected()));
    assert!(original.first_refusal().is_none());
    assert_eq!(original.remaining_fuel(), InterpretOptions::default().fuel);
    drop(original);
    assert!(observer.events.iter().all(|event| event.site == site()));
    assert_eq!(
        observer.events.last().unwrap().phase,
        ExecutionPhase::Publication
    );
    observer
}
fn samples<'a>(
    ours: &'a EffectSet,
    theirs: &'a EffectSet,
    top: &'a EffectSummary,
    pure: &'a EffectSummary,
    global: &'a EffectSummary,
) -> [Query<'a>; 7] {
    [
        Query::Set(ours, theirs),
        Query::Set(theirs, ours),
        Query::Summary(top, pure),
        Query::Summary(pure, top),
        Query::Summary(pure, pure),
        Query::Names(global),
        Query::Names(pure),
    ]
}
