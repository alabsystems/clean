// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
use super::*;

#[test]
fn every_actual_collection_event_refuses_without_smaller_output_and_keeps_first_cause() {
    for f in [
        chain(4),
        function(vec![borrow(1, 1, false)]),
        function(vec![]),
    ] {
        let known = known();
        let (_, baseline) = observed(&f, &known);
        for stop_at in 1..=baseline.events.len() {
            let mut observer = Observer {
                stop_at: Some(stop_at),
                ..Observer::default()
            };
            let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
            assert!(matches!(
                borrow_result_types_observed(&f, &known, &mut session, site()),
                Err(ObservedValueError::AdmissionRefused)
            ));
            assert_eq!(
                session.first_refusal().unwrap().cause,
                "original borrow stop"
            );
            assert_eq!(session.remaining_fuel(), InterpretOptions::default().fuel);
            assert!(
                observer
                    .events
                    .iter()
                    .skip(stop_at)
                    .all(|event| event.phase == ExecutionPhase::ScratchRetirement)
            );
        }
    }
}
#[test]
fn every_single_rule_event_including_actual_fat_clone_and_publication_is_fallible() {
    for input in [None, Some(Ty::Ptr), Some(fat())] {
        let mut baseline = Observer::default();
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut baseline);
        borrow_result_ty_observed(input.as_ref(), &mut session, site()).unwrap();
        for stop_at in 1..=baseline.events.len() {
            let mut observer = Observer {
                stop_at: Some(stop_at),
                ..Observer::default()
            };
            let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
            assert_eq!(
                borrow_result_ty_observed(input.as_ref(), &mut session, site()),
                Err(ObservedValueError::AdmissionRefused)
            );
            assert_eq!(
                session.first_refusal().unwrap().cause,
                "original borrow stop"
            );
            assert!(
                observer
                    .events
                    .iter()
                    .skip(stop_at)
                    .all(|event| event.phase == ExecutionPhase::ScratchRetirement)
            );
        }
    }
}
#[test]
fn single_rule_and_chain_calls_share_original_cumulative_work_and_byte_caps() {
    let f = chain(3);
    let known = known();
    let mut baseline = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    borrow_result_ty_observed(None, &mut session, site()).unwrap();
    borrow_result_types_observed(&f, &known, &mut session, site()).unwrap();
    for bytes in [false, true] {
        let mut observer = Observer {
            work_cap: (!bytes).then_some(baseline.work - 1),
            byte_cap: bytes.then_some(baseline.bytes - 1),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        borrow_result_ty_observed(None, &mut session, site()).unwrap();
        assert!(matches!(
            borrow_result_types_observed(&f, &known, &mut session, site()),
            Err(ObservedValueError::AdmissionRefused)
        ));
        assert_eq!(
            session.first_refusal().unwrap().cause,
            if bytes { "bytes" } else { "work" }
        );
        assert_eq!(
            borrow_result_ty_observed(None, &mut session, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(
            session.first_refusal().unwrap().cause,
            if bytes { "bytes" } else { "work" }
        );
    }
}
#[test]
fn first_index_storage_refusal_precedes_allocation_and_output_storage_keeps_pending_type() {
    let mut observer = Observer {
        byte_cap: Some(0),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut state = State::default();
    assert_eq!(
        work.reserve(&mut state.operands),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!((state.operands.len(), state.operands.capacity()), (0, 0));
    state.retire_scratch(&mut work);
    let mut observer = Observer {
        byte_cap: Some(0),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut state = State {
        pending: Some(fat()),
        ..State::default()
    };
    assert_eq!(
        work.push_row(&mut state.resolved, 1, &mut state.pending),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert!(matches!(state.pending, Some(Ty::FatPtr(_))));
    assert_eq!((state.resolved.len(), state.resolved.capacity()), (0, 0));
    state.retire_scratch(&mut work);
    assert!(state.pending.is_none());
    assert_eq!(work.session.first_refusal().unwrap().cause, "bytes");
}
#[test]
fn growth_refusal_keeps_the_existing_concrete_index_allocation_and_rows() {
    let mut rows = Vec::<(u32, u32)>::with_capacity(2);
    let capacity = rows.capacity();
    rows.resize(capacity, (7, 0));
    let expected = rows.clone();
    let original = rows.as_ptr();
    let mut observer = Observer {
        byte_cap: Some(0),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    assert_eq!(
        work.reserve(&mut rows),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(rows.as_ptr(), original);
    assert_eq!(rows, expected);
    let mut state = State {
        operands: rows,
        ..State::default()
    };
    state.retire_scratch(&mut work);
}

#[test]
fn actual_growth_cost_checks_count_and_byte_overflows_before_any_allocation() {
    assert_eq!(
        storage::growth_cost::<(u32, u32)>(usize::MAX),
        Err(ObservedValueError::CapacityOverflow)
    );
    assert_eq!(
        storage::growth_cost::<(u32, u32)>(usize::MAX / 2),
        Err(ObservedValueError::CapacityOverflow)
    );
    assert_eq!(
        storage::growth_cost::<(ValueId, Ty)>(usize::MAX / 4),
        Err(ObservedValueError::CapacityOverflow)
    );
    assert_eq!(
        storage::growth_cost::<(u32, u32)>(0),
        Ok((1, 1, size_of::<(u32, u32)>()))
    );
}
#[test]
fn actual_owned_pending_clone_and_prior_rows_remain_in_state_at_every_later_stop() {
    let f = chain(3);
    let known = known();
    let mut baseline = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut state = State::default();
    state.collect(&f, &mut work).unwrap();
    state.resolve(&known, &mut work).unwrap();
    state.retire_scratch(&mut work);
    state.retire_resolved(&mut work);
    let (mut pending, mut partial) = (false, false);
    for stop_at in 1..=baseline.events.len() {
        let mut observer = Observer {
            stop_at: Some(stop_at),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        let mut work = Work {
            session: &mut session,
            site: site(),
        };
        let mut state = State::default();
        let result = state
            .collect(&f, &mut work)
            .and_then(|()| state.resolve(&known, &mut work));
        if result.is_err() {
            pending |= matches!(state.pending, Some(Ty::FatPtr(_)));
            partial |= !state.resolved.is_empty() && state.resolved.len() < 3;
        }
        state.retire_scratch(&mut work);
        state.retire_resolved(&mut work);
        assert!(state.pending.is_none() && state.operands.is_empty() && state.resolved.is_empty());
    }
    assert!(pending && partial);
}
#[test]
fn final_outer_publication_stop_retires_actual_completed_types_and_output_buffer() {
    let f = chain(4);
    let known = known();
    let (_, baseline) = observed(&f, &known);
    let mut observer = Observer {
        stop_at: Some(baseline.events.len()),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert!(matches!(
        borrow_result_types_observed(&f, &known, &mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    ));
    assert_eq!(
        session.first_refusal().unwrap().progress.phase,
        ExecutionPhase::Publication
    );
    let cleanup = &observer.events[baseline.events.len()..];
    assert!(cleanup.len() > 4);
    assert!(
        cleanup
            .iter()
            .all(|event| event.phase == ExecutionPhase::ScratchRetirement)
    );
}
#[test]
fn scratch_retirement_refusal_cannot_publish_a_complete_or_default_result() {
    let f = function(vec![borrow(1, 1, false)]);
    let (_, baseline) = observed(&f, &[]);
    let stop_at = baseline
        .events
        .iter()
        .position(|event| event.phase == ExecutionPhase::ScratchRetirement)
        .unwrap()
        + 1;
    let mut observer = Observer {
        stop_at: Some(stop_at),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert!(matches!(
        borrow_result_types_observed(&f, &[], &mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    ));
    assert_eq!(
        session.first_refusal().unwrap().progress.phase,
        ExecutionPhase::ScratchRetirement
    );
    assert!(
        observer
            .events
            .iter()
            .all(|event| event.phase != ExecutionPhase::Publication)
    );
}
#[test]
fn actual_reverse_known_scan_stops_interiorly_before_reaching_a_fat_root() {
    let f = chain(1);
    let mut known = vec![(0, fat())];
    known.extend((1..5000).map(|id| (id, Ty::Ref(Box::new(Ty::I32)))));
    let mut observer = Observer {
        work_cap: Some(300),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert!(matches!(
        borrow_result_types_observed(&f, &known, &mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    ));
    assert_eq!(session.first_refusal().unwrap().cause, "work");
    assert!(observer.events.len() < 400);
    assert!(
        observer
            .events
            .iter()
            .all(|event| event.phase != ExecutionPhase::Publication)
    );
}
#[test]
fn actual_chain_hops_stop_interiorly_under_one_original_session() {
    // Prebuilt private index fixture; this claims no index-construction work.
    // One original session observes the actual long chain and its cleanup.
    let operands = (1..=40).map(|id| (id, id - 1)).collect();
    let mut observer = Observer {
        work_cap: Some(100),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut state = State {
        operands,
        ..State::default()
    };
    assert_eq!(
        resolve::chain_root(&state.operands, 40, &mut work),
        Err(ObservedValueError::AdmissionRefused)
    );
    state.retire_scratch(&mut work);
    state.retire_resolved(&mut work);
    assert_eq!(work.session.first_refusal().unwrap().cause, "work");
}
#[test]
fn an_existing_pending_type_is_never_implicitly_overwritten_or_dropped() {
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut pending = Some(fat());
    assert_eq!(
        work.make_type(None, &mut pending),
        Err(ObservedValueError::InvalidRange)
    );
    assert!(matches!(pending, Some(Ty::FatPtr(_))));
    work.retire_pending(&mut pending);
    assert!(pending.is_none());
}
