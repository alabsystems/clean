// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn every_actual_event_refuses_without_publication_or_input_mutation() {
    let value = mixed();
    let expected = value.to_string();
    let (_, measured) = text(&value);
    for stop in 1..=measured.events.len() {
        let mut observer = Observer {
            stop_at: Some(stop),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        assert_eq!(
            value.display_observed(&mut session, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(session.first_refusal().unwrap().cause, "original stop");
        assert_eq!(value.to_string(), expected);
        assert!(
            observer
                .events
                .iter()
                .skip(stop)
                .all(|event| event.phase == ExecutionPhase::ScratchRetirement)
        );
    }
}
#[test]
fn work_and_requested_bytes_are_cumulative_across_two_calls() {
    let value = mixed();
    let (_, measured) = text(&value);
    for bytes in [false, true] {
        let mut observer = Observer {
            work_cap: (!bytes).then_some(measured.work),
            byte_cap: bytes.then_some(measured.bytes),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        assert_eq!(
            value.display_observed(&mut session, site()).unwrap(),
            value.to_string()
        );
        assert_eq!(
            value.display_observed(&mut session, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(
            session.first_refusal().unwrap().cause,
            if bytes { "bytes" } else { "work" }
        );
        assert_eq!(session.remaining_fuel(), InterpretOptions::default().fuel);
    }
}
#[test]
fn task_growth_refusal_precedes_the_first_allocation() {
    let mut observer = Observer {
        stop_at: Some(2),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut state = State::default();
    assert_eq!(
        state.push(Task::Text("tail"), &mut work),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(state.tasks.capacity(), 0);
    assert!(state.output.is_empty());
    state.retire_tasks(&mut work);
}
#[test]
fn interior_unicode_stop_retains_then_retires_the_exact_partial_output() {
    let value = Constant::SymbolAddr {
        symbol: "λ".repeat(3000),
        addend: 0,
    };
    // Both measurement and replay use the same direct State::run entry point.
    let mut measured = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut measured);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut state = State::default();
    state.run(&value, &mut work).unwrap();
    state.retire_tasks(&mut work);
    work.retire(take(&mut state.output));
    let stop = measured
        .events
        .iter()
        .enumerate()
        .filter(|(_, event)| event.work == 1024 && event.copy_bytes == 1024)
        .nth(1)
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
        state.run(&value, &mut work),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(state.output, format!("symaddr<{}", "λ".repeat(512)));
    state.retire_tasks(&mut work);
    work.retire(take(&mut state.output));
    assert!(state.output.is_empty());
    assert_eq!(work.session.first_refusal().unwrap().cause, "original stop");
}
#[test]
fn scratch_deallocation_and_final_publication_stops_both_refuse_the_string() {
    let value = Constant::Int(2);
    let (_, measured) = text(&value);
    for stop in [
        measured
            .events
            .iter()
            .position(|event| event.phase == ExecutionPhase::ScratchRetirement)
            .unwrap()
            + 1,
        measured.events.len(),
    ] {
        let mut observer = Observer {
            stop_at: Some(stop),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        assert_eq!(
            value.display_observed(&mut session, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(session.first_refusal().unwrap().cause, "original stop");
        assert_eq!(
            observer.events.last().unwrap().phase,
            ExecutionPhase::ScratchRetirement
        );
    }
}
