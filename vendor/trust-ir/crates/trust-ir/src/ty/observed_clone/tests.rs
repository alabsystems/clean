// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
use crate::interpret::InterpretOptions;
#[derive(Default)]
struct Observer {
    events: Vec<ExecutionProgress>,
    stop_at: Option<usize>,
    stop_phase: Option<ExecutionPhase>,
    cap: Option<usize>,
    bytes_cap: Option<usize>,
    work: usize,
    bytes: usize,
}
impl ExecutionObserver for Observer {
    type Refusal = &'static str;
    fn admit(&mut self, event: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(event);
        if self.stop_at == Some(self.events.len()) || self.stop_phase == Some(event.phase) {
            return Err("interior");
        }
        self.work = self.work.checked_add(event.work).ok_or("overflow")?;
        self.bytes = self.bytes.checked_add(event.copy_bytes).ok_or("overflow")?;
        if self.cap.is_some_and(|cap| self.work > cap) {
            return Err("work");
        }
        if self.bytes_cap.is_some_and(|cap| self.bytes > cap) {
            return Err("bytes");
        }
        Ok(())
    }
}
fn site() -> ExecutionSite {
    ExecutionSite::Entry(crate::FuncId::new(61))
}
fn mixed() -> Ty {
    Ty::Tuple(vec![
        Ty::Ref(Box::new(Ty::Tuple(vec![Ty::U8, Ty::Bool]))),
        Ty::Tuple(vec![]),
        Ty::Vector(Box::new(Ty::RefMut(Box::new(Ty::Char))), 19),
        Ty::PtrMut(Box::new(Ty::PtrConst(Box::new(Ty::Rc(Box::new(
            Ty::Never,
        )))))),
        Ty::Dialect(Box::new(DialectTy::new("namespace", "name", 7))),
        Ty::Handle(Box::new(HandleTy::new("name-λ", "runtime::X"))),
    ])
}
fn clone(ty: &Ty) -> (Ty, Observer) {
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let output = ty.clone_observed(&mut session, site()).unwrap();
    assert!(session.first_refusal().is_none());
    assert_eq!(session.remaining_fuel(), InterpretOptions::default().fuel);
    (output, observer)
}
#[test]
fn exact_small_clone_preserves_all_leaf_fields_and_owned_child_order() {
    let ty = mixed();
    let (output, observed) = clone(&ty);
    assert_eq!(output, ty.clone());
    assert!(observed.events.iter().all(|e| e.site == site()));
    assert_eq!(
        observed.events.last().unwrap().phase,
        ExecutionPhase::Publication
    );
    assert_eq!(
        observed
            .events
            .iter()
            .filter(|e| e.phase == ExecutionPhase::Publication)
            .count(),
        1
    );
    let leaves = [
        Ty::I8,
        Ty::I16,
        Ty::I32,
        Ty::I64,
        Ty::I128,
        Ty::U8,
        Ty::U16,
        Ty::U32,
        Ty::U64,
        Ty::U128,
        Ty::Isize,
        Ty::Usize,
        Ty::Char,
        Ty::Error,
        Ty::F16,
        Ty::F32,
        Ty::F64,
        Ty::Bool,
        Ty::Ptr,
        Ty::Unit,
        Ty::Never,
        Ty::FatPtr(FatPtrKind::Slice(TyId::new(5))),
        Ty::FatPtr(FatPtrKind::Str),
        Ty::FatPtr(FatPtrKind::TraitObject { trait_id: 6 }),
        Ty::FatPtr(FatPtrKind::ContainerLen),
        Ty::FatPtr(FatPtrKind::ContainerVtable),
        Ty::Struct(StructId::new(17)),
        Ty::Array(TyId::new(18), u64::MAX),
        Ty::Enum(EnumId::new(19)),
        Ty::Func(FuncTyId::new(20)),
        Ty::Set(TyId::new(21), SetRepr::Bitset),
        Ty::Set(TyId::new(22), SetRepr::Boxed),
        Ty::Sequence(TyId::new(23)),
        Ty::Record(RecordId::new(24)),
        Ty::Closure(ClosureTyId::new(25)),
        Ty::Refine(TyId::new(26), PredId::new(27)),
    ];
    for leaf in leaves {
        assert_eq!(clone(&leaf).0, leaf);
    }
}
#[test]
fn wide_lazy_tuples_reconstruct_in_original_order_without_bulk_owned_moves() {
    let ty = Ty::Tuple(
        (0..2048)
            .map(|n| Ty::Array(TyId::new(n), u64::from(n)))
            .collect(),
    );
    let (output, observed) = clone(&ty);
    assert_eq!(output, ty);
    assert!(observed.work >= 2048);
    assert!(observed.bytes >= 2048 * size_of::<Ty>());
}
#[test]
fn deep_inline_clone_and_explicit_retirement_do_not_reenter_recursive_type_drop() {
    let mut ty = Ty::Bool;
    for n in 0..20_000 {
        ty = if n % 2 == 0 {
            Ty::Ref(Box::new(ty))
        } else {
            Ty::Tuple(vec![ty])
        };
    }
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let output = ty.clone_observed(&mut session, site()).unwrap();
    assert!(
        ty.structural_eq_observed(&output, &mut session, site())
            .unwrap()
    );
    output.retire_observed(&mut session, site()).unwrap();
    ty.retire_observed(&mut session, site()).unwrap();
    assert!(session.first_refusal().is_none());
}
#[test]
fn every_actual_small_event_refuses_without_publishing_or_mutating_the_input() {
    let input = mixed();
    let expected = input.clone();
    let (_, measured) = clone(&input);
    for stop in 1..=measured.events.len() {
        let mut observer = Observer {
            stop_at: Some(stop),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        assert_eq!(
            input.clone_observed(&mut session, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(session.first_refusal().unwrap().cause, "interior");
        assert_eq!(input, expected);
        assert!(
            observer
                .events
                .iter()
                .skip(stop)
                .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
        );
    }
}
#[test]
fn original_work_is_cumulative_across_two_clones_without_new_fuel_or_grant() {
    let input = mixed();
    let (_, measured) = clone(&input);
    let mut observer = Observer {
        cap: Some(measured.work),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let first = input.clone_observed(&mut session, site()).unwrap();
    assert_eq!(
        input.clone_observed(&mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(session.first_refusal().unwrap().cause, "work");
    assert_eq!(session.remaining_fuel(), InterpretOptions::default().fuel);
    assert_eq!(
        first.retire_observed(&mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
}
#[test]
fn nominal_utf8_copy_has_real_bounded_interiors_and_second_string_pending_ownership() {
    let input = Ty::Dialect(Box::new(DialectTy::new(
        "λ".repeat(3000),
        "界".repeat(3000),
        0,
    )));
    // Measure the SAME direct state entry point that is replayed below. The
    // public wrapper has an additional header admission before State::run.
    let mut measured = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut measured);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut state = State::default();
    state.run(&input, &mut work).unwrap();
    assert_eq!(state.output.as_ref().unwrap(), &input);
    state.retire_scratch(&mut work);
    observed_retirement::retire_type(state.output.take().unwrap(), work.session, site());
    let stop = measured
        .events
        .iter()
        .enumerate()
        .filter(|(_, e)| e.copy_bytes == 1023 && e.work == 1023)
        .nth(2)
        .unwrap()
        .0
        + 1;
    let mut observer = Observer {
        stop_at: Some(stop),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut state = State::default();
    assert_eq!(
        state.run(&input, &mut work),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(state.first.len(), 6000);
    assert_eq!(state.second.len(), 1023);
    assert!(state.output.is_none());
    state.retire_scratch(&mut work);
    assert!(state.first.is_empty() && state.second.is_empty());
    assert_eq!(work.session.first_refusal().unwrap().cause, "interior");
}
#[test]
fn requested_storage_refusal_occurs_before_growing_the_owned_tuple_workspace() {
    let input = Ty::Tuple(vec![Ty::Bool; 64]);
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut state = State::default();
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    state.run(&input, &mut work).unwrap();
    assert!(state.output.is_some());
    state.retire_scratch(&mut work);
    let output = state.output.take().unwrap();
    output.retire_observed(work.session, site()).unwrap();
    // Directly target the actual tuple-storage admission while retaining all
    // completed children; no allocator-failure flag can grant a smaller output.
    let baseline = observer.events;
    let stop = baseline
        .iter()
        .position(|e| e.copy_bytes == 64 * size_of::<Ty>() && e.work == 64)
        .unwrap()
        + 1;
    let mut observer = Observer {
        stop_at: Some(stop),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut state = State::default();
    assert_eq!(
        state.run(&input, &mut work),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(state.values.len(), 64);
    assert_eq!(state.tuple.capacity(), 0);
    state.retire_scratch(&mut work);
}

#[test]
fn deep_owned_result_is_explicitly_retired_when_final_publication_refuses() {
    let mut input = Ty::Bool;
    for _ in 0..20_000 {
        input = Ty::Ref(Box::new(input));
    }
    let mut observer = Observer {
        stop_phase: Some(ExecutionPhase::Publication),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert!(matches!(
        input.clone_observed(&mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    ));
    assert_eq!(
        session.first_refusal().unwrap().progress.phase,
        ExecutionPhase::Publication
    );
    assert_eq!(
        input.retire_observed(&mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert!(
        observer
            .events
            .iter()
            .rev()
            .take(100)
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
}

#[test]
fn requested_bytes_are_cumulative_across_calls_without_replacement_allowance() {
    let input = mixed();
    let (_, measured) = clone(&input);
    let mut observer = Observer {
        bytes_cap: Some(measured.bytes),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let first = input.clone_observed(&mut session, site()).unwrap();
    assert_eq!(
        input.clone_observed(&mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(session.first_refusal().unwrap().cause, "bytes");
    assert_eq!(
        first.retire_observed(&mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(session.remaining_fuel(), InterpretOptions::default().fuel);
}
#[test]
fn tensor_clone_preserves_its_rank_and_inline_element() {
    let ty = Ty::Tuple(vec![
        Ty::Tensor(Box::new(Ty::U8), 0),
        Ty::Tensor(Box::new(Ty::I64), 3),
    ]);
    assert_eq!(clone(&ty).0, ty);
}
