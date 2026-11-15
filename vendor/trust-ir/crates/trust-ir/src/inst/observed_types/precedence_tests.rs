// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use crate::interpret::InterpretOptions;
use crate::{FuncId, ValueId};
use std::cell::Cell;
use std::rc::Rc;
#[derive(Default)]
struct Observer {
    events: Vec<ExecutionProgress>,
    marker: Rc<Cell<usize>>,
    stop: Rc<Cell<Option<usize>>>,
}
impl ExecutionObserver for Observer {
    type Refusal = &'static str;
    fn admit(&mut self, e: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(e);
        self.marker.set(self.events.len());
        if self.stop.get() == Some(self.events.len()) {
            Err("inline stop")
        } else {
            Ok(())
        }
    }
}
fn site() -> ExecutionSite {
    ExecutionSite::Entry(FuncId::new(904))
}
#[test]
fn actual_finish_types_holds_each_local_error_and_drains_every_borrowed_header_at_each_cleanup_cut()
{
    let source = [Ty::I8, Ty::Tuple(vec![Ty::I64, Ty::Ref(Box::new(Ty::U8))])];
    for error in [
        ObservedValueError::InvalidRange,
        ObservedValueError::UnsupportedValue,
        ObservedValueError::CapacityOverflow,
        ObservedValueError::AllocationFailed,
    ] {
        for offset in 1..=4 {
            let mut o = Observer::default();
            let marker = Rc::clone(&o.marker);
            let stop = Rc::clone(&o.stop);
            let mut s = ObservedSession::new(
                InterpretOptions {
                    fuel: 0,
                    ..InterpretOptions::default()
                },
                &mut o,
            );
            let mut work = Work {
                session: &mut s,
                site: site(),
            };
            let mut types = Vec::new();
            for ty in &source {
                work.push(&mut types, ty).unwrap();
            }
            let before = marker.get();
            stop.set(Some(before + offset));
            // Exact consuming production helper, holding an explicit typed
            // child result; no pretend allocator failure or ordinary replay.
            assert_eq!(work.finish_types(Err(error), types), Err(error));
            assert_eq!(s.first_refusal().unwrap().cause, "inline stop");
            assert_eq!(s.remaining_fuel(), 0);
            drop(s);
            let tail = &o.events[before..];
            assert_eq!(tail.len(), 4);
            assert!(
                tail.iter()
                    .all(|e| e.phase == ExecutionPhase::ScratchRetirement && e.site == site())
            );
            assert_eq!(
                tail.iter().map(|e| e.work).collect::<Vec<_>>(),
                vec![1, 1, 1, 0]
            );
        }
    }
    assert_eq!(
        source[1],
        Ty::Tuple(vec![Ty::I64, Ty::Ref(Box::new(Ty::U8))])
    );
}
#[test]
fn actual_finish_types_withholds_healthy_headers_on_real_publication_refusal_and_cleans_them_all() {
    let source = [Ty::I8, Ty::I64];
    let mut o = Observer::default();
    let marker = Rc::clone(&o.marker);
    let stop = Rc::clone(&o.stop);
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    let mut types = Vec::new();
    for ty in &source {
        work.push(&mut types, ty).unwrap();
    }
    let before = marker.get();
    stop.set(Some(before + 1));
    assert_eq!(
        work.finish_types(Ok(()), types),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        s.first_refusal().unwrap().progress.phase,
        ExecutionPhase::Publication
    );
    drop(s);
    assert_eq!(o.events.len(), before + 5);
    assert!(
        o.events[before + 1..]
            .iter()
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
}
#[test]
fn actual_inline_public_path_cleanup_stop_keeps_original_site_cause_and_zero_fuel() {
    let inst = Inst::Copy {
        ty: Ty::Tuple(vec![Ty::I64, Ty::I8]),
        operand: ValueId::new(9),
    };
    let mut baseline = Observer::default();
    let mut s = ObservedSession::new(
        InterpretOptions {
            fuel: 0,
            ..InterpretOptions::default()
        },
        &mut baseline,
    );
    let mut types = inst.inline_types_observed(&mut s, site()).unwrap();
    assert_eq!(types, vec![&Ty::Tuple(vec![Ty::I64, Ty::I8])]);
    Work {
        session: &mut s,
        site: site(),
    }
    .retire_types(&mut types);
    assert!(types.is_empty());
    drop(s);
    let at = baseline
        .events
        .iter()
        .position(|e| e.phase == ExecutionPhase::ScratchRetirement)
        .unwrap();
    let mut o = Observer::default();
    o.stop.set(Some(at + 1));
    let mut s = ObservedSession::new(
        InterpretOptions {
            fuel: 0,
            ..InterpretOptions::default()
        },
        &mut o,
    );
    assert_eq!(
        inst.inline_types_observed(&mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    let first = s.first_refusal().unwrap().progress;
    assert_eq!(first, baseline.events[at]);
    assert_eq!(s.first_refusal().unwrap().cause, "inline stop");
    assert_eq!(s.remaining_fuel(), 0);
    assert!(
        s.admit(ExecutionProgress {
            phase: ExecutionPhase::Publication,
            site: site(),
            work: 0,
            copy_bytes: 0
        })
        .is_err()
    );
    drop(s);
    assert_eq!(&o.events[..=at], &baseline.events[..=at]);
    assert!(
        o.events[at + 1..]
            .iter()
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
}
