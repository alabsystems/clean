// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored UNRUN parity and original-context controls.
use super::*;
use crate::interpret::InterpretOptions;
use crate::value::{ClosureTyId, EnumId, FuncId, PredId, RecordId, StructId, TyId};
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
    fn admit(&mut self, e: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(e);
        if self.stop == Some(self.events.len()) {
            return Err("original slot stop");
        }
        self.work += e.work;
        self.bytes += e.copy_bytes;
        if self.work_cap.is_some_and(|n| self.work > n) {
            return Err("work");
        }
        if self.byte_cap.is_some_and(|n| self.bytes > n) {
            return Err("bytes");
        }
        Ok(())
    }
}
fn site() -> ExecutionSite {
    ExecutionSite::Entry(FuncId::new(138))
}
fn run(m: &Module, t: &Ty) -> (bool, Observer) {
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let out = m
        .is_by_value_aggregate_slot_observed(t, &mut s, site())
        .unwrap();
    assert_eq!(out, m.is_by_value_aggregate_slot(t));
    assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
    assert!(o.events.iter().all(|e| e.site == site()));
    (out, o)
}
#[test]
fn every_original_aggregate_spelling_and_scalar_boundary_matches_one_predicate() {
    let m = Module::new("slots");
    for t in [
        Ty::Struct(StructId::new(0)),
        Ty::Tuple(vec![]),
        Ty::Array(TyId::new(0), 0),
        Ty::Enum(EnumId::new(0)),
        Ty::Record(RecordId::new(0)),
        Ty::Sequence(TyId::new(0)),
        Ty::Set(TyId::new(0), crate::ty::SetRepr::Boxed),
        Ty::Closure(ClosureTyId::new(0)),
        Ty::Vector(Box::new(Ty::U8), 0),
        Ty::Tensor(Box::new(Ty::U8), 0),
    ] {
        assert!(run(&m, &t).0);
    }
    for t in [
        Ty::U8,
        Ty::Ptr,
        Ty::Unit,
        Ty::Never,
        Ty::Error,
        Ty::Ref(Box::new(Ty::Unit)),
        Ty::FatPtr(crate::ty::FatPtrKind::Str),
    ] {
        assert!(!run(&m, &t).0);
    }
}
#[test]
fn exactly_one_refinement_lookup_keeps_dangling_nested_and_self_cycles_aggregate() {
    let mut m = Module::new("refine");
    m.types = vec![
        Ty::U8,
        Ty::Tuple(vec![]),
        Ty::Refine(TyId::new(2), PredId::new(0)),
    ];
    for (id, expected) in [(0, false), (1, true), (2, true), (u32::MAX, true)] {
        assert_eq!(
            run(&m, &Ty::Refine(TyId::new(id), PredId::new(u32::MAX))).0,
            expected
        );
    }
}
#[test]
fn wrapped_payloads_and_registered_aggregate_payloads_remain_opaque() {
    let m = Module::new("opaque");
    let (_, before) = run(&m, &Ty::PtrConst(Box::new(Ty::Unit)));
    let (_, after) = run(
        &m,
        &Ty::PtrConst(Box::new(Ty::Tuple(vec![Ty::Error; 10000]))),
    );
    assert_eq!(before.events, after.events);
    let (_, before) = run(&m, &Ty::Tuple(vec![]));
    let (_, after) = run(&m, &Ty::Tuple(vec![Ty::Error; 10000]));
    assert_eq!(before.events, after.events);
}
#[test]
fn every_real_callback_is_original_context_refusal_not_a_classification() {
    let mut m = Module::new("stop");
    m.types = vec![Ty::Tuple(vec![])];
    let t = Ty::Refine(TyId::new(0), PredId::new(0));
    let (_, base) = run(&m, &t);
    for stop in 1..=base.events.len() {
        let mut o = Observer {
            stop: Some(stop),
            ..Default::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert_eq!(
            m.is_by_value_aggregate_slot_observed(&t, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(s.first_refusal().unwrap().progress, base.events[stop - 1]);
    }
}
#[test]
fn cumulative_work_and_copy_are_shared_without_resetting_the_original_session() {
    let m = Module::new("limits");
    let (_, base) = run(&m, &Ty::Unit);
    for bytes in [false, true] {
        let mut o = Observer {
            work_cap: (!bytes).then_some(base.work),
            byte_cap: bytes.then_some(base.bytes),
            ..Default::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert!(
            !m.is_by_value_aggregate_slot_observed(&Ty::Unit, &mut s, site())
                .unwrap()
        );
        assert_eq!(
            m.is_by_value_aggregate_slot_observed(&Ty::Unit, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
    }
}
#[test]
fn preexisting_stop_and_zero_fuel_do_not_create_a_new_grant() {
    let m = Module::new("owner");
    let mut o = Observer {
        stop: Some(1),
        ..Default::default()
    };
    let mut s = ObservedSession::new(
        InterpretOptions {
            fuel: 0,
            ..Default::default()
        },
        &mut o,
    );
    assert_eq!(
        m.is_by_value_aggregate_slot_observed(&Ty::Unit, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    let first = s.first_refusal().unwrap().progress;
    assert_eq!(
        m.is_by_value_aggregate_slot_observed(&Ty::Tuple(vec![]), &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(s.first_refusal().unwrap().progress, first);
    assert_eq!(s.remaining_fuel(), 0);
    assert_eq!(o.events.len(), 1);
}
