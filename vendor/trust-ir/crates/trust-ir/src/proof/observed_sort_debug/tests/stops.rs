// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn every_actual_callback_of_all_tags_and_nested_rows_can_refuse_without_partial_text() {
    let mut values = examples();
    values.push(mixed());
    for value in &values {
        let (_, baseline) = execute(value);
        for at in 1..=baseline.events.len() {
            let mut observer = Observer {
                at: Some(at),
                ..Default::default()
            };
            let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
            assert_eq!(
                value.debug_observed(&mut session, site()),
                Err(ObservedValueError::AdmissionRefused)
            );
            assert_eq!(session.first_refusal().unwrap().cause, "original interior");
        }
    }
}
#[test]
fn initial_public_header_admission_stops_before_any_state_or_task_allocation() {
    let mut observer = Observer {
        at: Some(1),
        ..Default::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        ClauseSort::Bool.debug_observed(&mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    drop(session);
    assert_eq!(observer.events.len(), 1);
    assert_eq!(
        observer.events[0].copy_bytes,
        size_of::<State<'_>>() + size_of::<Work<'_, '_, Observer>>()
    );
}
#[test]
fn repeated_complete_calls_use_the_original_cumulative_work_budget() {
    let value = mixed();
    let (_, baseline) = execute(&value);
    let mut observer = Observer {
        cap: Some(baseline.work),
        ..Default::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        value.debug_observed(&mut session, site()).unwrap(),
        format!("{value:?}")
    );
    assert_eq!(
        value.debug_observed(&mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(session.first_refusal().unwrap().cause, "work");
}
#[test]
fn repeated_complete_calls_use_the_original_cumulative_copy_budget() {
    let value = mixed();
    let (_, baseline) = execute(&value);
    let mut observer = Observer {
        byte_cap: Some(baseline.bytes),
        ..Default::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        value.debug_observed(&mut session, site()).unwrap(),
        format!("{value:?}")
    );
    assert_eq!(
        value.debug_observed(&mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(session.first_refusal().unwrap().cause, "bytes");
}
#[test]
fn actual_scalar_debug_work_can_refuse_in_the_interior_of_a_unicode_name() {
    let value = ClauseSort::Datatype {
        name: "λ\u{301}".repeat(3000),
        constructors: Vec::new(),
    };
    let (_, baseline) = execute(&value);
    let at = baseline
        .events
        .iter()
        .enumerate()
        .filter(|(_, event)| {
            event.phase == ExecutionPhase::Validation
                && event.work >= 8 * u32::BITS as usize
                && event.copy_bytes == size_of::<core::char::EscapeDebug>()
        })
        .nth(100)
        .unwrap()
        .0
        + 1;
    let mut observer = Observer {
        at: Some(at),
        ..Default::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        value.debug_observed(&mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(session.first_refusal().unwrap().cause, "original interior");
    drop(session);
    assert!(
        observer
            .events
            .iter()
            .any(|event| event.phase == ExecutionPhase::ScratchRetirement
                && event.work > size_of::<String>() + 1)
    );
}
fn task_pop_ordinal(trace: &Observer, index: usize) -> usize {
    trace
        .events
        .windows(2)
        .enumerate()
        .filter(|(_, pair)| {
            pair[0].phase == ExecutionPhase::Validation
                && pair[0].work == 1
                && pair[0].copy_bytes == size_of::<Option<Task<'_>>>()
                && pair[1].phase == ExecutionPhase::Validation
                && pair[1].work == 4
                && pair[1].copy_bytes == size_of::<Task<'_>>()
        })
        .nth(index)
        .unwrap()
        .0
        + 1
}
#[test]
fn wide_empty_constructor_task_walk_can_stop_after_many_actual_rows() {
    let value = ClauseSort::Datatype {
        name: "D".into(),
        constructors: (0..100).map(|i| (format!("C{i}"), Vec::new())).collect(),
    };
    let (_, baseline) = execute(&value);
    let at = task_pop_ordinal(&baseline, 150);
    let mut observer = Observer {
        at: Some(at),
        ..Default::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        value.debug_observed(&mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(session.first_refusal().unwrap().cause, "original interior");
}
#[test]
fn wide_field_task_walk_can_stop_inside_actual_nested_field_rows() {
    let value = ClauseSort::Datatype {
        name: "D".into(),
        constructors: vec![(
            "C".into(),
            (0..100)
                .map(|i| (format!("f{i}"), ClauseSort::BitVec(i)))
                .collect(),
        )],
    };
    let (_, baseline) = execute(&value);
    let at = task_pop_ordinal(&baseline, 150);
    let mut observer = Observer {
        at: Some(at),
        ..Default::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        value.debug_observed(&mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(session.first_refusal().unwrap().cause, "original interior");
}
#[test]
fn stopped_original_owner_cannot_resume_a_later_formatting_attempt() {
    let value = mixed();
    let trigger = Rc::new(Cell::new(false));
    let mut observer = Observer {
        next: Some(trigger.clone()),
        cleanup: true,
        ..Default::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    // The observer cannot issue a new grant once the original cause is latched.
    trigger.set(true);
    assert_eq!(
        value.debug_observed(&mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    trigger.set(false);
    assert_eq!(
        value.debug_observed(&mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(session.first_refusal().unwrap().cause, "original interior");
}
