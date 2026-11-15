// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn every_closure_and_retirement_boundary_is_terminal_under_original_session() {
    let universe = fixture();
    let mut measured = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut measured);
    universe
        .close_observed(false, &mut session, site())
        .unwrap();
    for stop_at in 1..=measured.events.len() {
        let mut observer = Observer {
            stop_at: Some(stop_at),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        assert_eq!(
            universe
                .close_observed(false, &mut session, site())
                .unwrap_err(),
            ObservedValueError::AdmissionRefused,
            "event {stop_at}"
        );
        assert_eq!(session.first_refusal().unwrap().cause, "interior");
        assert_eq!(
            universe
                .close_observed(false, &mut session, site())
                .unwrap_err(),
            ObservedValueError::AdmissionRefused
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

#[test]
fn original_work_and_requested_copy_allowances_accumulate_across_closures() {
    let universe = fixture();
    let mut measured = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut measured);
    universe
        .close_observed(false, &mut session, site())
        .unwrap();
    for copying in [false, true] {
        let mut observer = if copying {
            Observer {
                byte_limit: Some(measured.bytes),
                ..Observer::default()
            }
        } else {
            Observer {
                work_limit: Some(measured.work),
                ..Observer::default()
            }
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        let first = universe
            .close_observed(false, &mut session, site())
            .unwrap();
        equal(&first, &universe.close(false));
        assert_eq!(
            universe
                .close_observed(false, &mut session, site())
                .unwrap_err(),
            ObservedValueError::AdmissionRefused
        );
        assert_eq!(
            session.first_refusal().unwrap().cause,
            if copying { "bytes" } else { "work" }
        );
        assert_eq!(session.remaining_fuel(), InterpretOptions::default().fuel);
    }
}

#[test]
fn vector_and_btree_storage_are_refused_before_first_allocation() {
    let mut observer = Observer {
        byte_limit: Some(0),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut values: Vec<PrincipalKey> = Vec::new();
    assert_eq!(
        push(&mut values, PrincipalKey(1), &mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(values.len(), 0);
    assert_eq!(values.capacity(), 0);
    let mut observer = Observer {
        byte_limit: Some(0),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut values = BTreeSet::new();
    assert_eq!(
        insert(&mut values, PrincipalKey(1), &mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert!(values.is_empty());
    let mut observer = Observer {
        byte_limit: Some(0),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        fixture()
            .close_observed(false, &mut session, site())
            .unwrap_err(),
        ObservedValueError::AdmissionRefused
    );
    assert_eq!(observer.events.len(), 1);
}

#[test]
fn actual_parameter_comparison_and_copy_loops_poll_interior_work() {
    let left = FnShape {
        abi: None,
        variadic: None,
        params: Some(vec![ArgClass::Int(8); 257]),
    };
    let mut right = left.clone();
    right.params.as_mut().unwrap()[256] = ArgClass::Int(32);
    let mut observer = Observer {
        stop_at: Some(8),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        keys::compare(Key::Fn(&left), Key::Fn(&right), &mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(observer.events.len(), 8);
    let mut observer = Observer {
        stop_at: Some(18),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        keys::copy_key(Key::Fn(&left), &mut session, site()).unwrap_err(),
        ObservedValueError::AdmissionRefused
    );
    assert_eq!(session.first_refusal().unwrap().cause, "interior");
    assert!(
        observer
            .events
            .iter()
            .skip(18)
            .all(|event| event.phase == ExecutionPhase::ScratchRetirement)
    );
}

#[test]
fn post_drop_retirement_can_refuse_an_already_computed_pool_result() {
    let universe = fixture();
    let mut measured = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut measured);
    universe
        .close_observed(false, &mut session, site())
        .unwrap();
    let last_retirement = measured
        .events
        .iter()
        .rposition(|event| event.phase == ExecutionPhase::ScratchRetirement)
        .unwrap();
    let mut observer = Observer {
        stop_at: Some(last_retirement + 1),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        universe
            .close_observed(false, &mut session, site())
            .unwrap_err(),
        ObservedValueError::AdmissionRefused
    );
    assert_eq!(session.first_refusal().unwrap().cause, "interior");
    assert!(
        observer
            .events
            .iter()
            .skip(last_retirement + 1)
            .all(|event| event.phase == ExecutionPhase::ScratchRetirement)
    );
}
