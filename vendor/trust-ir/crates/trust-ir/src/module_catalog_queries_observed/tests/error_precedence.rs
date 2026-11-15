// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[derive(Default)]
struct CutObserver {
    events: Vec<ExecutionProgress>,
    cursor: Rc<Cell<usize>>,
    stop: Rc<Cell<Option<usize>>>,
}
impl ExecutionObserver for CutObserver {
    type Refusal = &'static str;
    fn admit(&mut self, event: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(event);
        self.cursor.set(self.events.len());
        if self.stop.get() == Some(self.events.len()) {
            Err("catalog cut")
        } else {
            Ok(())
        }
    }
}
fn real_rows<O: ExecutionObserver>(
    catalog: &ModuleFunctionCatalog<'_>,
    w: &mut Work<'_, '_, O>,
) -> Vec<u32> {
    let mut rows = Vec::new();
    catalog.ambiguous(&mut rows, w).unwrap();
    assert_eq!(rows, vec![3, 19]);
    rows
}
#[test]
fn actual_query_finish_preserves_held_local_errors_across_every_nonempty_cleanup_cut() {
    let m = fixture();
    let catalog = ModuleFunctionCatalog::new(&m);
    for error in [
        ObservedValueError::CapacityOverflow,
        ObservedValueError::AllocationFailed,
        ObservedValueError::InvalidRange,
        ObservedValueError::UnsupportedValue,
    ] {
        for offset in 1..=5 {
            let mut o = CutObserver::default();
            let cursor = o.cursor.clone();
            let stop = o.stop.clone();
            let mut s = ObservedSession::new(
                InterpretOptions {
                    fuel: 0,
                    ..InterpretOptions::default()
                },
                &mut o,
            );
            let mut w = Work {
                session: &mut s,
                site: site(),
            };
            let rows = real_rows(&catalog, &mut w);
            let before = cursor.get();
            stop.set(Some(before + offset));
            // Exact consuming production seam with actual complete query output.
            // Explicit held typed errors do not force or claim allocator failures.
            assert_eq!(w.finish_roster(Err(error), rows), Err(error));
            assert_eq!(s.first_refusal().unwrap().cause, "catalog cut");
            let first = s.first_refusal().unwrap().progress;
            assert_eq!(first.phase, ExecutionPhase::ScratchRetirement);
            assert_eq!(s.remaining_fuel(), 0);
            drop(s);
            assert_eq!(o.events.len(), before + 5);
            assert_eq!(first, o.events[before + offset - 1]);
            assert!(
                o.events[before..]
                    .iter()
                    .all(|e| e.phase == ExecutionPhase::ScratchRetirement && e.site == site())
            );
        }
    }
}
#[test]
fn actual_query_publication_refusal_consumes_all_healthy_roster_storage() {
    let m = fixture();
    let catalog = ModuleFunctionCatalog::new(&m);
    let mut o = CutObserver::default();
    let cursor = o.cursor.clone();
    let stop = o.stop.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let rows = real_rows(&catalog, &mut w);
    let before = cursor.get();
    stop.set(Some(before + 1));
    assert_eq!(
        w.finish_roster(Ok(()), rows),
        Err(ObservedValueError::AdmissionRefused)
    );
    let first = s.first_refusal().unwrap().progress;
    assert_eq!(first.phase, ExecutionPhase::Publication);
    drop(s);
    assert_eq!(o.events.len(), before + 6);
    assert_eq!(first, o.events[before]);
    assert!(
        o.events[before + 1..]
            .iter()
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
}
#[test]
fn earlier_original_query_cause_remains_immutable_while_held_error_and_full_roster_drain() {
    let m = fixture();
    let catalog = ModuleFunctionCatalog::new(&m);
    let mut o = CutObserver::default();
    let cursor = o.cursor.clone();
    let stop = o.stop.clone();
    let mut s = ObservedSession::new(
        InterpretOptions {
            fuel: 0,
            ..InterpretOptions::default()
        },
        &mut o,
    );
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let rows = real_rows(&catalog, &mut w);
    let at = cursor.get();
    stop.set(Some(at + 1));
    assert_eq!(w.admit(1, 0), Err(ObservedValueError::AdmissionRefused));
    let first = w.session.first_refusal().unwrap().progress;
    assert_eq!(
        w.finish_roster(Err(ObservedValueError::InvalidRange), rows),
        Err(ObservedValueError::InvalidRange)
    );
    assert_eq!(s.first_refusal().unwrap().progress, first);
    assert_eq!(s.first_refusal().unwrap().cause, "catalog cut");
    assert_eq!(s.remaining_fuel(), 0);
    drop(s);
    assert_eq!(first, o.events[at]);
    assert!(
        o.events[at + 1..]
            .iter()
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
}
#[test]
fn healthy_actual_query_finish_transfers_the_same_complete_buffer_until_caller_retirement() {
    let m = fixture();
    let catalog = ModuleFunctionCatalog::new(&m);
    let mut o = CutObserver::default();
    let cursor = o.cursor.clone();
    let stop = o.stop.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let rows = real_rows(&catalog, &mut w);
    let pointer = rows.as_ptr();
    let capacity = rows.capacity();
    let rows = w.finish_roster(Ok(()), rows).unwrap();
    assert_eq!(rows, vec![3, 19]);
    assert_eq!(rows.as_ptr(), pointer);
    assert_eq!(rows.capacity(), capacity);
    stop.set(Some(cursor.get() + 1));
    w.rows(rows);
    assert_eq!(w.publication(0), Err(ObservedValueError::AdmissionRefused));
    assert_eq!(s.first_refusal().unwrap().cause, "catalog cut");
    assert_eq!(
        s.first_refusal().unwrap().progress.phase,
        ExecutionPhase::ScratchRetirement
    );
    assert_eq!(m.functions.len(), 7);
}
