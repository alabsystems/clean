// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored UNRUN controls: logical cleanup, not allocator/concurrency evidence.
use super::*;
use crate::interpret::InterpretOptions;
use crate::shape::{PointerMetadataShape, TyShape};
use crate::ty::EnumTagRepr;
use crate::value::{ClosureTyId, EnumId, FuncId, StructId, TyId};
mod exact;
mod fixtures;
mod ownership;
mod stops;
use fixtures::{encodings, enum_shape, expected_enum_work, field, ty_shape, ty_shapes};

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
            return Err("original retirement stop");
        }
        self.work = self.work.checked_add(event.work).ok_or("work overflow")?;
        self.bytes = self
            .bytes
            .checked_add(event.copy_bytes)
            .ok_or("byte overflow")?;
        if self.work_cap.is_some_and(|cap| self.work > cap) {
            return Err("original work cap");
        }
        if self.byte_cap.is_some_and(|cap| self.bytes > cap) {
            return Err("original byte cap");
        }
        Ok(())
    }
}
fn site() -> ExecutionSite {
    ExecutionSite::Entry(FuncId::new(131))
}
#[derive(Clone)]
enum Sample {
    Ty(TyLayoutShape),
    Enum(EnumLayoutShape),
}
impl Sample {
    fn retire<O: ExecutionObserver>(self, arc: bool, session: &mut ObservedSession<'_, O>) -> R {
        match (self, arc) {
            (Self::Ty(value), false) => value.retire_observed(session, site()),
            (Self::Enum(value), false) => value.retire_observed(session, site()),
            (Self::Ty(value), true) => Arc::new(value).retire_arc_observed(session, site()),
            (Self::Enum(value), true) => Arc::new(value).retire_arc_observed(session, site()),
        }
    }
}
fn execute(sample: Sample, arc: bool, mut observer: Observer) -> (R, Observer) {
    let stop = observer.stop;
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let result = sample.retire(arc, &mut session);
    assert_eq!(session.remaining_fuel(), InterpretOptions::default().fuel);
    if result.is_err() {
        assert!(session.first_refusal().is_some());
    } else {
        assert!(session.first_refusal().is_none());
    }
    let refusal = session
        .first_refusal()
        .map(|refusal| (refusal.progress, refusal.cause));
    if let Some(stop) = stop {
        let (progress, cause) = refusal.unwrap();
        assert_eq!(cause, "original retirement stop");
        assert_eq!(progress, observer.events[stop - 1]);
    }
    assert!(observer.events.iter().all(|event| event.site == site()));
    (result, observer)
}
fn trace(sample: Sample, arc: bool) -> Observer {
    let (result, observer) = execute(sample, arc, Observer::default());
    assert_eq!(result, Ok(()));
    assert_eq!(
        observer.events.last(),
        Some(&ExecutionProgress {
            phase: ExecutionPhase::Publication,
            site: site(),
            work: 0,
            copy_bytes: 0,
        })
    );
    assert!(
        observer.events[..observer.events.len() - 1]
            .iter()
            .all(|event| event.phase == ExecutionPhase::ScratchRetirement && event.copy_bytes == 0)
    );
    observer
}
fn count_work(observer: &Observer, work: usize) -> usize {
    observer
        .events
        .iter()
        .filter(|event| event.phase == ExecutionPhase::ScratchRetirement && event.work == work)
        .count()
}
