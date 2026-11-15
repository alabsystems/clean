// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Real child helpers and their shared consuming seam; compiler/native UNRUN.
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use crate::interpret::InterpretOptions;
use std::cell::Cell;
use std::rc::Rc;
#[derive(Default)]
struct Observer {
    events: Vec<ExecutionProgress>,
    cut: Option<usize>,
    limit: Option<usize>,
    work: usize,
    marker: Rc<Cell<usize>>,
    dynamic: Rc<Cell<Option<usize>>>,
    drops: Rc<Cell<usize>>,
    seen_drops: Vec<usize>,
}
impl ExecutionObserver for Observer {
    type Refusal = &'static str;
    fn admit(&mut self, e: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(e);
        self.seen_drops.push(self.drops.get());
        self.marker.set(self.events.len());
        if self.cut.or(self.dynamic.get()) == Some(self.events.len()) {
            return Err("cut");
        }
        self.work = self.work.checked_add(e.work).ok_or("overflow")?;
        if self.limit.is_some_and(|cap| self.work > cap) {
            return Err("work");
        }
        Ok(())
    }
}
fn site() -> ExecutionSite {
    ExecutionSite::Entry(FuncId::new(903))
}
struct Pending(Rc<Cell<usize>>);
impl Drop for Pending {
    fn drop(&mut self) {
        self.0.set(self.0.get() + 1);
    }
}
#[derive(Clone, Copy, Debug)]
enum Route {
    Type,
    Constant,
    Sort,
    TypeStrings,
    ConstantStrings,
    SortStrings,
    Intern,
}
const ROUTES: [Route; 7] = [
    Route::Type,
    Route::Constant,
    Route::Sort,
    Route::TypeStrings,
    Route::ConstantStrings,
    Route::SortStrings,
    Route::Intern,
];
fn route<O: ExecutionObserver>(
    r: Route,
    out: &mut Output<'_, '_, O>,
    builder: &mut Builder,
    pool: &SealedPool,
) -> R<u64> {
    match r {
        Route::Type => observed_write_ty(
            out,
            pool,
            &Ty::Tuple(vec![Ty::I8, Ty::Ref(Box::new(Ty::I64))]),
        )
        .map(|()| 71),
        Route::Constant => observed_write_constant(
            out,
            pool,
            &crate::Constant::Aggregate(vec![
                crate::Constant::Int(17),
                crate::Constant::Bool(true),
            ]),
        )
        .map(|()| 71),
        Route::Sort => observed_write_clause_sort(
            out,
            pool,
            &ClauseSort::Array(Box::new(ClauseSort::Int), Box::new(ClauseSort::BitVec(8))),
        )
        .map(|()| 71),
        Route::TypeStrings => {
            observed_collect_type_strings(&Ty::handle("child_λ", "runtime::Child"), builder, out)
                .map(|()| 71)
        }
        Route::ConstantStrings => observed_collect_constant_strings(
            &crate::Constant::SymbolAddr {
                symbol: "child_λ".into(),
                addend: 7,
            },
            builder,
            out,
        )
        .map(|()| 71),
        Route::SortStrings => observed_collect_clause_sort_strings(
            &ClauseSort::Datatype {
                name: "child_λ".into(),
                constructors: vec![("C".into(), vec![("f".into(), ClauseSort::Int)])],
            },
            builder,
            out,
        )
        .map(|()| 71),
        Route::Intern => builder.intern("child_λ", out),
    }
}
fn run_route(
    r: Route,
    cut: Option<usize>,
    limit: Option<usize>,
) -> (R<u64>, Observer, Option<ExecutionProgress>) {
    let mut o = Observer {
        cut,
        limit,
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut out = Output::counter(&mut s, site()).unwrap();
    out.admit(1, 3 * core::mem::size_of::<Builder>()).unwrap();
    let mut builder = Builder::new(false);
    let pool = Builder::new(false).seal();
    let result = route(r, &mut out, &mut builder, &pool);
    builder.retire(&mut out);
    pool.retire(&mut out);
    drop(out);
    assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
    let cause = s.first_refusal().map(|e| e.progress);
    drop(s);
    (result, o, cause)
}
#[test]
fn all_seven_real_helpers_withhold_healthy_results_at_every_actual_cleanup_cut() {
    for r in ROUTES {
        let (healthy, base, _) = run_route(r, None, None);
        assert!(healthy.is_ok(), "{r:?}");
        // Exclude fixture pool destruction; only cuts preceding the child's
        // actual final poll are inside the child return boundary.
        let end = base
            .events
            .iter()
            .rposition(|e| e.phase == ExecutionPhase::CanonicalSerialization)
            .unwrap();
        let cuts: Vec<_> = base.events[..end]
            .iter()
            .enumerate()
            .filter(|(_, e)| e.phase == ExecutionPhase::ScratchRetirement)
            .map(|(i, _)| i + 1)
            .collect();
        assert!(!cuts.is_empty(), "{r:?}");
        for cut in cuts {
            let (actual, o, cause) = run_route(r, Some(cut), None);
            assert_eq!(
                actual,
                Err(ObservedValueError::AdmissionRefused),
                "{r:?} {cut}"
            );
            assert_eq!(cause, Some(base.events[cut - 1]));
            assert_eq!(&o.events[..cut], &base.events[..cut]);
            assert!(
                o.events[cut..]
                    .iter()
                    .all(|e| e.phase == ExecutionPhase::ScratchRetirement && e.site == site())
            );
        }
    }
}
#[test]
fn all_seven_real_helpers_use_the_same_cumulative_original_work_budget() {
    for r in ROUTES {
        let (expected, base, _) = run_route(r, None, None);
        let last = base
            .events
            .iter()
            .rposition(|e| e.phase == ExecutionPhase::CanonicalSerialization)
            .unwrap();
        let charge: usize = base.events[..=last].iter().map(|e| e.work).sum();
        let (actual, o, cause) = run_route(r, None, Some(charge - 1));
        assert_eq!(actual, Err(ObservedValueError::AdmissionRefused), "{r:?}");
        assert_eq!(cause, Some(base.events[last]));
        assert_eq!(&o.events[..=last], &base.events[..=last]);
        assert_eq!(run_route(r, None, Some(base.work)).0, expected);
    }
}
fn missing_pool(kind: usize, cut: Option<usize>) -> (R, Observer, Option<ExecutionProgress>) {
    let mut o = Observer {
        cut,
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut out = Output::counter(&mut s, site()).unwrap();
    out.admit(1, 2 * core::mem::size_of::<Builder>()).unwrap();
    let pool = Builder::new(false).seal();
    let result = match kind {
        0 => observed_write_ty(&mut out, &pool, &Ty::Error),
        1 => observed_write_constant(
            &mut out,
            &pool,
            &crate::Constant::SymbolAddr {
                symbol: "absent_λ".into(),
                addend: 17,
            },
        ),
        _ => observed_write_clause_sort(
            &mut out,
            &pool,
            &ClauseSort::Datatype {
                name: "absent_λ".into(),
                constructors: vec![],
            },
        ),
    };
    // Observe the child boundary before consuming the independent pool.
    pool.retire(&mut out);
    drop(out);
    let cause = s.first_refusal().map(|e| e.progress);
    drop(s);
    (result, o, cause)
}
#[test]
fn actual_type_constant_and_sort_local_errors_survive_each_later_cleanup_cut() {
    for kind in 0..3 {
        let (result, base, _) = missing_pool(kind, None);
        assert_eq!(result, Err(ObservedValueError::UnsupportedValue));
        let last = base
            .events
            .iter()
            .rposition(|e| e.phase == ExecutionPhase::CanonicalSerialization)
            .unwrap();
        let mut start = last;
        while start > 0 && base.events[start - 1].phase == ExecutionPhase::ScratchRetirement {
            start -= 1;
        }
        assert_eq!(last - start, 2);
        for cut in start + 1..=last {
            let (result, o, cause) = missing_pool(kind, Some(cut));
            assert_eq!(result, Err(ObservedValueError::UnsupportedValue));
            assert_eq!(cause, Some(base.events[cut - 1]));
            assert_eq!(&o.events[..cut], &base.events[..cut]);
            assert!(
                o.events[cut..]
                    .iter()
                    .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
            );
        }
    }
}
#[test]
fn actual_shared_finish_keeps_local_errors_and_consumes_all_pending_on_both_cleanup_cuts() {
    for error in [
        ObservedValueError::UnsupportedValue,
        ObservedValueError::CapacityOverflow,
        ObservedValueError::AllocationFailed,
        ObservedValueError::InvalidRange,
    ] {
        for offset in 1..=3 {
            let mut o = Observer::default();
            let marker = Rc::clone(&o.marker);
            let dynamic = Rc::clone(&o.dynamic);
            let drops = Rc::clone(&o.drops);
            let mut s = ObservedSession::new(
                InterpretOptions {
                    fuel: 0,
                    ..InterpretOptions::default()
                },
                &mut o,
            );
            let mut out = Output::counter(&mut s, site()).unwrap();
            let mut pending = Vec::new();
            for _ in 0..3 {
                out.push_value(&mut pending, Pending(Rc::clone(&drops)))
                    .unwrap();
            }
            let before = marker.get();
            dynamic.set(Some(before + offset));
            // This is the production finish called by all seven helpers. The
            // held typed error is explicit, never a forged allocator failure.
            assert_eq!(out.finish_child::<u64, _>(Err(error), pending), Err(error));
            assert_eq!(drops.get(), 3);
            drop(out);
            assert_eq!(s.first_refusal().unwrap().cause, "cut");
            assert_eq!(s.remaining_fuel(), 0);
            drop(s);
            assert_eq!(o.seen_drops[before], 0);
            assert_eq!(o.seen_drops[before + 1], 3);
            let count = if offset < 3 { 2 } else { 3 };
            assert_eq!(o.events.len(), before + count);
            assert!(
                o.events[before..before + 2]
                    .iter()
                    .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
            );
        }
    }
}
#[test]
fn actual_shared_finish_withholds_a_healthy_nonunit_value_at_cleanup_or_final_poll() {
    for offset in 1..=3 {
        let mut o = Observer::default();
        let dynamic = Rc::clone(&o.dynamic);
        let marker = Rc::clone(&o.marker);
        let drops = Rc::clone(&o.drops);
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut out = Output::counter(&mut s, site()).unwrap();
        let mut pending = Vec::new();
        out.push_value(&mut pending, Pending(Rc::clone(&drops)))
            .unwrap();
        dynamic.set(Some(marker.get() + offset));
        assert_eq!(
            out.finish_child(Ok(73u64), pending),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(drops.get(), 1);
    }
}
#[test]
fn actual_shared_finish_keeps_preexisting_original_cause_and_never_resumes() {
    let mut o = Observer::default();
    let dynamic = Rc::clone(&o.dynamic);
    let marker = Rc::clone(&o.marker);
    let drops = Rc::clone(&o.drops);
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut out = Output::counter(&mut s, site()).unwrap();
    let mut pending = Vec::new();
    out.push_value(&mut pending, Pending(Rc::clone(&drops)))
        .unwrap();
    dynamic.set(Some(marker.get() + 1));
    assert_eq!(out.poll(), Err(ObservedValueError::AdmissionRefused));
    assert_eq!(
        out.finish_child::<u64, _>(Err(ObservedValueError::InvalidRange), pending),
        Err(ObservedValueError::InvalidRange)
    );
    assert_eq!(drops.get(), 1);
    drop(out);
    assert_eq!(s.first_refusal().unwrap().cause, "cut");
    let first = s.first_refusal().unwrap().progress;
    assert_eq!(
        s.admit(ExecutionProgress {
            phase: ExecutionPhase::Publication,
            site: site(),
            work: 0,
            copy_bytes: 0
        }),
        Err(crate::interpret::ObservationStopped)
    );
    assert_eq!(s.first_refusal().unwrap().progress, first);
    drop(s);
    assert!(
        o.events[o.events.len() - 2..]
            .iter()
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
}
