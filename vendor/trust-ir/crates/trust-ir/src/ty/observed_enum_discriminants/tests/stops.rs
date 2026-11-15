// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn every_actual_assignment_and_tag_callback_refuses_without_partial_some() {
    for e in [
        definition(4, vec![Some(-2), None, None, Some(8)], None),
        definition(3, vec![Some(7), Some(7)], None),
        definition(4, vec![], Some(EnumTagRepr::U8)),
        definition(0, vec![], None),
    ] {
        for tag in [false, true] {
            let base = if tag {
                canonical(&e).1
            } else {
                assignment(&e).1
            };
            for stop in 1..=base.events.len() {
                let mut o = Observer {
                    stop: Some(stop),
                    ..Observer::default()
                };
                let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
                if tag {
                    assert_eq!(
                        e.canonical_tag_repr_observed(&mut s, site()),
                        Err(ObservedValueError::AdmissionRefused)
                    );
                } else {
                    assert_eq!(
                        e.effective_discriminants_observed(&mut s, site()),
                        Err(ObservedValueError::AdmissionRefused)
                    );
                }
                assert_eq!(
                    s.first_refusal().unwrap().cause,
                    "original discriminant stop"
                );
                assert_eq!(s.first_refusal().unwrap().progress, base.events[stop - 1]);
                assert!(
                    o.events
                        .iter()
                        .skip(stop)
                        .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
                );
            }
        }
    }
}
#[test]
fn original_work_and_copy_cumulate_across_calls_with_no_fresh_fuel() {
    let e = definition(8, vec![], None);
    for tag in [false, true] {
        let base = if tag {
            canonical(&e).1
        } else {
            assignment(&e).1
        };
        for bytes in [false, true] {
            let mut o = Observer {
                work_cap: (!bytes).then_some(base.work),
                byte_cap: bytes.then_some(base.bytes),
                ..Observer::default()
            };
            let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
            if tag {
                e.canonical_tag_repr_observed(&mut s, site()).unwrap();
                assert_eq!(
                    e.canonical_tag_repr_observed(&mut s, site()),
                    Err(ObservedValueError::AdmissionRefused)
                );
            } else {
                e.effective_discriminants_observed(&mut s, site()).unwrap();
                assert_eq!(
                    e.effective_discriminants_observed(&mut s, site()),
                    Err(ObservedValueError::AdmissionRefused)
                );
            }
            assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
            let first = s.first_refusal().unwrap().progress;
            assert_eq!(
                e.canonical_tag_repr_observed(&mut s, site()),
                Err(ObservedValueError::AdmissionRefused)
            );
            assert_eq!(s.first_refusal().unwrap().progress, first);
        }
    }
}
#[test]
fn real_duplicate_scan_can_stop_interior_with_only_prior_values_owned() {
    let e = definition(100, vec![], None);
    let mut o = Observer {
        work_cap: Some(300),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = State::default();
    assert_eq!(
        state.assign(&e, &mut work),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert!(!state.values.is_empty());
    assert!(state.values.len() < 100);
    state.retire(&mut work);
    assert_eq!(state.values.capacity(), 0);
    assert_eq!(work.session.first_refusal().unwrap().cause, "work");
}
#[test]
fn actual_pre_push_stop_retains_previous_values_and_allocated_output_capacity() {
    let e = definition(3, vec![], None);
    let mut base = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut base);
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = State::default();
    state.assign(&e, &mut work).unwrap();
    state.retire(&mut work);
    let positions = base
        .events
        .iter()
        .enumerate()
        .filter(|(_, e)| {
            e.phase == ExecutionPhase::Validation
                && e.work == 2
                && e.copy_bytes == size_of::<i128>() + size_of::<Option<i128>>()
        })
        .map(|(i, _)| i + 1)
        .collect::<Vec<_>>();
    assert_eq!(positions.len(), 3);
    let stop = positions[1];
    let mut o = Observer {
        stop: Some(stop),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = State::default();
    assert_eq!(
        state.assign(&e, &mut work),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(state.values, vec![0]);
    assert!(state.values.capacity() >= 2);
    state.retire(&mut work);
    assert_eq!(state.values.capacity(), 0);
}
#[test]
fn actual_hint_check_can_stop_after_assignment_while_all_values_stay_owned() {
    let e = definition(20, vec![], Some(EnumTagRepr::I128));
    let mut base = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut base);
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = State::default();
    state.canonical(&e, &mut work).unwrap();
    state.retire(&mut work);
    let stops = base
        .events
        .iter()
        .enumerate()
        .filter(|(_, e)| {
            e.work == 4 && e.copy_bytes == size_of::<EnumTagRepr>() + size_of::<i128>()
        })
        .map(|(i, _)| i + 1)
        .collect::<Vec<_>>();
    assert_eq!(stops.len(), 20);
    let mut o = Observer {
        stop: Some(stops[7]),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = State::default();
    assert_eq!(
        state.canonical(&e, &mut work),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(state.values, (0..20).map(i128::from).collect::<Vec<_>>());
    state.retire(&mut work);
    assert_eq!(state.values.capacity(), 0);
}
#[test]
fn cleanup_refusal_consumes_all_actual_values_under_the_same_original_session() {
    let e = definition(20, vec![], None);
    let arm = Rc::new(Cell::new(false));
    let mut o = Observer {
        cleanup: Some(arm.clone()),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = State::default();
    assert!(state.assign(&e, &mut work).unwrap());
    arm.set(true);
    state.retire(&mut work);
    assert_eq!(state.values.capacity(), 0);
    assert_eq!(work.session.first_refusal().unwrap().cause, "cleanup");
    assert_eq!(
        work.publication(size_of::<Option<EnumTagRepr>>()),
        Err(ObservedValueError::AdmissionRefused)
    );
}
#[test]
fn initial_header_and_completed_vector_publication_refuse_without_escape() {
    let e = definition(4, vec![], None);
    for tag in [false, true] {
        let mut o = Observer {
            byte_cap: Some(0),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        if tag {
            assert_eq!(
                e.canonical_tag_repr_observed(&mut s, site()),
                Err(ObservedValueError::AdmissionRefused)
            );
        } else {
            assert_eq!(
                e.effective_discriminants_observed(&mut s, site()),
                Err(ObservedValueError::AdmissionRefused)
            );
        }
        assert_eq!(o.events.len(), 1);
    }
    let (_, base) = assignment(&e);
    let stop = base.events.len();
    let mut o = Observer {
        stop: Some(stop),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(
        e.effective_discriminants_observed(&mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        s.first_refusal().unwrap().progress.phase,
        ExecutionPhase::Publication
    );
    assert!(o.events.len() > stop);
    assert!(
        o.events
            .iter()
            .skip(stop)
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
}
