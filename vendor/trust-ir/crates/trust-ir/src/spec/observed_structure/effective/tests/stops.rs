// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn every_public_callback_refuses_without_returning_equal_unknown_or_partial_mismatch() {
    for (variable, binding) in [
        (SpecVar::new("x", "opaque"), ClauseSort::Bool),
        (SpecVar::new("x", "Int"), ClauseSort::Int),
        (
            SpecVar::new("x", "opaque").with_sort(datatype("λ\n")),
            ClauseSort::Bool,
        ),
    ] {
        let (_, base, bound) = run(&variable, &binding);
        for stop in 1..=bound {
            let mut observer = Observer {
                stop: Some(stop),
                ..Observer::default()
            };
            let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
            assert_eq!(
                variable.effective_sort_mismatch_observed(&binding, &mut session, site()),
                Err(ObservedValueError::AdmissionRefused)
            );
            assert_eq!(
                session.first_refusal().unwrap().cause,
                "original effective-sort stop"
            );
            assert_eq!(
                session.first_refusal().unwrap().progress,
                base.events[stop - 1]
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
}
#[test]
fn original_work_and_copy_limits_cumulate_with_caller_disposal_and_second_call() {
    let variable = SpecVar::new("x", "opaque").with_sort(datatype("Dλ"));
    let (_, base, _) = run(&variable, &ClauseSort::Bool);
    for bytes in [false, true] {
        let mut observer = Observer {
            work_cap: (!bytes).then_some(base.work),
            byte_cap: bytes.then_some(base.bytes),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        let output = variable
            .effective_sort_mismatch_observed(&ClauseSort::Bool, &mut session, site())
            .unwrap();
        dispose(output, &mut session);
        assert!(session.first_refusal().is_none());
        assert_eq!(
            variable.effective_sort_mismatch_observed(&ClauseSort::Bool, &mut session, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        let cause = session.first_refusal().unwrap().progress;
        assert_eq!(
            variable.effective_sort_mismatch_observed(&ClauseSort::Bool, &mut session, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(session.first_refusal().unwrap().progress, cause);
        assert_eq!(session.remaining_fuel(), InterpretOptions::default().fuel);
    }
}
#[test]
fn original_instruction_coordinates_and_zero_execution_fuel_survive_all_phases() {
    let variable = SpecVar::new("x", "opaque").with_sort(nested(16, datatype("D")));
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(
        InterpretOptions {
            fuel: 0,
            ..InterpretOptions::default()
        },
        &mut observer,
    );
    let output = variable
        .effective_sort_mismatch_observed(&ClauseSort::Bool, &mut session, site())
        .unwrap();
    assert_eq!(output, oracle(&variable, &ClauseSort::Bool));
    dispose(output, &mut session);
    assert_eq!(session.remaining_fuel(), 0);
    assert!(session.first_refusal().is_none());
    assert!(observer.events.iter().all(|event| event.site == site()));
}
#[test]
fn final_publication_refuses_after_actual_retirement_for_all_three_results() {
    for (variable, binding) in [
        (SpecVar::new("x", "opaque"), ClauseSort::Bool),
        (SpecVar::new("x", "Int"), ClauseSort::Int),
        (SpecVar::new("x", "Int"), ClauseSort::Bool),
    ] {
        let (_, base, bound) = run(&variable, &binding);
        assert!(
            base.events[..bound - 1]
                .iter()
                .any(|event| event.phase == ExecutionPhase::ScratchRetirement)
        );
        let mut observer = Observer {
            stop: Some(bound),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        assert_eq!(
            variable.effective_sort_mismatch_observed(&binding, &mut session, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(
            session.first_refusal().unwrap().progress.phase,
            ExecutionPhase::Publication
        );
        assert!(
            observer.events[bound..]
                .iter()
                .all(|event| event.phase == ExecutionPhase::ScratchRetirement)
        );
    }
}
#[test]
fn actual_legacy_decimal_interior_stop_is_not_converted_into_unknown_sort() {
    let variable = SpecVar::new("x", "1".repeat(2000) + ".." + &"2".repeat(2000));
    let (_, base, bound) = run(&variable, &ClauseSort::Bool);
    let stop = base.events[..bound]
        .iter()
        .enumerate()
        .filter(|(_, event)| {
            event.phase == ExecutionPhase::Validation
                && event.work == 1
                && event.copy_bytes == size_of::<Option<&u8>>()
        })
        .nth(100)
        .unwrap()
        .0
        + 1;
    let mut observer = Observer {
        stop: Some(stop),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        variable.effective_sort_mismatch_observed(&ClauseSort::Bool, &mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        session.first_refusal().unwrap().progress,
        base.events[stop - 1]
    );
    assert!(
        !observer.events[..stop]
            .iter()
            .any(|event| event.phase == ExecutionPhase::Publication)
    );
}
#[test]
fn actual_long_datatype_equality_refuses_inside_a_name_before_diagnostic_formatting() {
    let sort = datatype(&"λ".repeat(3000));
    let variable = SpecVar::new("x", "opaque").with_sort(sort.clone());
    let (_, base, bound) = run(&variable, &sort);
    let stop = base.events[..bound]
        .iter()
        .enumerate()
        .filter(|(_, event)| {
            event.phase == ExecutionPhase::Validation && event.work == 1024 && event.copy_bytes == 0
        })
        .nth(2)
        .unwrap()
        .0
        + 1;
    let mut observer = Observer {
        stop: Some(stop),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        variable.effective_sort_mismatch_observed(&sort, &mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        session.first_refusal().unwrap().progress,
        base.events[stop - 1]
    );
    assert!(
        !observer.events[..stop]
            .iter()
            .any(|event| event.phase == ExecutionPhase::Publication)
    );
}
#[test]
fn initial_copy_refusal_and_existing_sticky_cause_do_not_enter_the_legacy_parser() {
    let variable = SpecVar::new("x", "1".repeat(100_000));
    let mut observer = Observer {
        byte_cap: Some(0),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        variable.effective_sort_mismatch_observed(&ClauseSort::Bool, &mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    let first = session.first_refusal().unwrap().progress;
    assert_eq!(
        variable.effective_sort_mismatch_observed(&ClauseSort::Bool, &mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(session.first_refusal().unwrap().progress, first);
    assert_eq!(observer.events.len(), 1);
}
