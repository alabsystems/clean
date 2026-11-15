// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn every_actual_query_callback_refuses_without_partial_bool_width_or_new_owner() {
    for ty in [
        fixture(),
        vectors(Ty::Bool, 8, 2),
        vectors(Ty::FatPtr(FatPtrKind::Str), 8, 3),
    ] {
        for query in ALL {
            let (_, baseline) = run(&ty, query);
            for stop in 1..=baseline.events.len() {
                let mut observer = Observer {
                    stop: Some(stop),
                    ..Observer::default()
                };
                let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
                assert_eq!(
                    invoke(&ty, query, &mut session),
                    Err(ObservedValueError::AdmissionRefused)
                );
                assert_eq!(
                    session.first_refusal().unwrap().cause,
                    "original type-query stop"
                );
                assert_eq!(session.remaining_fuel(), InterpretOptions::default().fuel);
                assert!(
                    observer
                        .events
                        .iter()
                        .skip(stop)
                        .all(|event| event.phase == ExecutionPhase::ScratchRetirement)
                );
            }
        }
    }
}
#[test]
fn all_five_queries_share_the_same_cumulative_work_copy_caps_and_sticky_stop() {
    let ty = fixture();
    let mut baseline = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    for query in ALL {
        invoke(&ty, query, &mut session).unwrap();
    }
    for bytes in [false, true] {
        let mut observer = Observer {
            work_cap: (!bytes).then_some(baseline.work - 1),
            byte_cap: bytes.then_some(baseline.bytes - 1),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        for query in ALL.into_iter().take(4) {
            invoke(&ty, query, &mut session).unwrap();
        }
        assert_eq!(
            invoke(&ty, ALL[4], &mut session),
            Err(ObservedValueError::AdmissionRefused)
        );
        let first = session.first_refusal().unwrap().progress;
        assert_eq!(
            session.first_refusal().unwrap().cause,
            if bytes { "bytes" } else { "work" }
        );
        assert_eq!(
            invoke(&ty, Query::Width, &mut session),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(session.first_refusal().unwrap().progress, first);
    }
}
#[test]
fn a_found_handle_or_dialect_does_not_skip_the_original_remaining_visitor_work() {
    for (first, query) in [
        (
            Ty::Handle(Box::new(HandleTy::new("Nat", "runtime"))),
            Query::Handle,
        ),
        (
            Ty::Dialect(Box::new(DialectTy::new("vector", "lanes", 1))),
            Query::Dialect,
        ),
    ] {
        let ty = Ty::Tuple(vec![first, Ty::Tuple(vec![Ty::U32; 5000])]);
        let mut observer = Observer {
            work_cap: Some(500),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        assert_eq!(
            invoke(&ty, query, &mut session),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(session.first_refusal().unwrap().cause, "work");
        assert!(observer.events.len() < 500);
    }
}
#[test]
fn first_frame_and_width_stack_growth_are_admitted_before_allocation() {
    let leaf = Ty::Bool;
    for frames in [false, true] {
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
        let result = if frames {
            work.push(&mut state.frames, Frame::Visit(&leaf))
        } else {
            work.push(&mut state.lanes, 2)
        };
        assert_eq!(result, Err(ObservedValueError::AdmissionRefused));
        assert_eq!(state.frames.capacity() + state.lanes.capacity(), 0);
        state.retire(&mut work);
    }
}
#[test]
fn actual_nested_width_scan_stops_with_owned_partial_lanes_then_retires_them() {
    let ty = vectors(Ty::U32, 3000, 2);
    let mut observer = Observer {
        work_cap: Some(100),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut state = State::default();
    assert_eq!(
        state.width(&ty, Width::Unresolved, &mut work),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert!(!state.lanes.is_empty() && state.lanes.len() < 3000);
    state.retire(&mut work);
    assert_eq!(state.frames.capacity() + state.lanes.capacity(), 0);
    assert_eq!(work.session.first_refusal().unwrap().cause, "work");
    // Input destruction is a distinct caller action, explicitly using the
    // same stopped session instead of a recursive unobserved deep Drop.
    assert_eq!(
        ty.retire_observed(work.session, work.site),
        Err(ObservedValueError::AdmissionRefused)
    );
}
#[test]
fn actual_bool_lane_descent_stops_interiorly_and_caller_retires_the_deep_input() {
    let ty = vectors(Ty::Bool, 3000, 1);
    let mut observer = Observer {
        work_cap: Some(100),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        ty.has_bool_lanes_observed(&mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(session.first_refusal().unwrap().cause, "work");
    assert_eq!(
        ty.retire_observed(&mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
}
#[test]
fn retained_borrowed_tail_and_original_cleanup_refusal_cannot_publish_a_partial_predicate() {
    let ty = fixture();
    let arm = Rc::new(Cell::new(false));
    let mut observer = Observer {
        cleanup_stop: Some(arm.clone()),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut state = State::default();
    work.push(&mut state.frames, Frame::Visit(&ty)).unwrap();
    work.push(&mut state.lanes, 2).unwrap();
    arm.set(true);
    assert_eq!(
        finish_copy(Ok(true), &mut state, &mut work),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(state.frames.capacity() + state.lanes.capacity(), 0);
    assert_eq!(
        work.session.first_refusal().unwrap().cause,
        "original type-query cleanup"
    );
}
#[test]
fn final_publication_refuses_each_completed_copy_answer_after_full_scratch_retirement() {
    let ty = fixture();
    for query in ALL {
        let (_, baseline) = run(&ty, query);
        let stop = baseline.events.len();
        let mut observer = Observer {
            stop: Some(stop),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        assert_eq!(
            invoke(&ty, query, &mut session),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(
            session.first_refusal().unwrap().progress.phase,
            ExecutionPhase::Publication
        );
        assert!(
            observer
                .events
                .iter()
                .skip(stop)
                .all(|event| event.phase == ExecutionPhase::ScratchRetirement)
        );
    }
}
