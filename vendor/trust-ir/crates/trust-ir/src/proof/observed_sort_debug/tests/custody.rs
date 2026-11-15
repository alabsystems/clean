// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn descriptor_header_refusal_occurs_before_pending_construction_or_queue_allocation() {
    let value = ClauseSort::Bool;
    let mut state = State::default();
    let mut observer = Observer {
        byte_cap: Some(0),
        ..Default::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let result = state.sort(&value, &mut work);
    assert_eq!(result, Err(ObservedValueError::AdmissionRefused));
    assert!(state.pending.is_none());
    assert_eq!((state.tasks.len(), state.tasks.capacity()), (0, 0));
    assert_eq!(
        state.finish(result, &mut work),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert!(state.pending.is_none() && state.tasks.is_empty() && state.output.is_empty());
}
#[test]
fn queue_growth_refusal_keeps_the_new_pending_descriptor_before_allocating() {
    let value = ClauseSort::Int;
    let mut state = State::default();
    // Descriptor header, reserve probe, then requested first queue allocation.
    let mut observer = Observer {
        at: Some(3),
        ..Default::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let result = state.sort(&value, &mut work);
    assert_eq!(result, Err(ObservedValueError::AdmissionRefused));
    assert!(matches!(state.pending, Some(Task::Sort(sort)) if core::ptr::eq(sort, &value)));
    assert_eq!((state.tasks.len(), state.tasks.capacity()), (0, 0));
    assert_eq!(
        state.finish(result, &mut work),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert!(state.pending.is_none() && state.tasks.is_empty() && state.output.is_empty());
}
#[test]
fn final_queue_move_header_refusal_keeps_pending_after_capacity_has_been_admitted() {
    let value = ClauseSort::RoundingMode;
    let mut state = State::default();
    let mut observer = Observer {
        at: Some(4),
        ..Default::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let result = state.sort(&value, &mut work);
    assert_eq!(result, Err(ObservedValueError::AdmissionRefused));
    assert!(state.tasks.is_empty() && state.tasks.capacity() >= 1);
    assert!(matches!(state.pending, Some(Task::Sort(sort)) if core::ptr::eq(sort, &value)));
    assert_eq!(
        state.finish(result, &mut work),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(state.tasks.capacity(), 0);
    assert!(state.pending.is_none() && state.output.is_empty());
}
#[test]
fn text_growth_admission_precedes_the_actual_output_allocation_and_copy() {
    let source = "λ文".repeat(5000);
    let mut state = State::default();
    let mut observer = Observer {
        byte_cap: Some(0),
        ..Default::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let result = work.text(&source, &mut state.output);
    assert_eq!(result, Err(ObservedValueError::AdmissionRefused));
    assert_eq!((state.output.len(), state.output.capacity()), (0, 0));
    assert_eq!(
        state.finish(result, &mut work),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert!(state.pending.is_none() && state.tasks.is_empty() && state.output.is_empty());
}
#[test]
fn pending_queued_headers_and_partial_output_remain_owned_until_complete_sticky_cleanup() {
    let value = mixed();
    let text = "partial λ文".repeat(5000);
    let trigger = Rc::new(Cell::new(true));
    let mut state = State {
        tasks: vec![Task::Text(")"), Task::Sort(&value)],
        pending: Some(Task::Sort(&value)),
        output: text.clone(),
    };
    let mut observer = Observer {
        next: Some(trigger),
        cleanup: true,
        ..Default::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let result = state.enqueue(&mut work);
    assert_eq!(result, Err(ObservedValueError::AdmissionRefused));
    assert_eq!(state.output, text);
    assert_eq!(state.tasks.len(), 2);
    assert!(matches!(state.pending, Some(Task::Sort(sort)) if core::ptr::eq(sort, &value)));
    assert_eq!(
        state.finish(result, &mut work),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert!(state.pending.is_none() && state.tasks.is_empty() && state.output.is_empty());
    assert_eq!((state.tasks.capacity(), state.output.capacity()), (0, 0));
    drop(work);
    assert_eq!(session.first_refusal().unwrap().cause, "original interior");
    drop(session);
    assert!(
        observer.events[1..]
            .iter()
            .all(|event| event.phase == ExecutionPhase::ScratchRetirement)
    );
    let expected = 5 * (size_of::<Option<Task<'_>>>() + 1)
        + 2 * (size_of::<Task<'_>>() + 1)
        + size_of::<Vec<Task<'_>>>()
        + 1
        + text.len()
        + size_of::<String>()
        + 1;
    assert_eq!(
        observer
            .events
            .iter()
            .filter(|e| e.phase == ExecutionPhase::ScratchRetirement)
            .map(|e| e.work)
            .sum::<usize>(),
        expected
    );
}
#[test]
fn a_first_refusal_during_scratch_retirement_still_consumes_the_completed_output() {
    let value = mixed();
    let mut observer = Observer {
        cleanup: true,
        ..Default::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        value.debug_observed(&mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(session.first_refusal().unwrap().cause, "cleanup");
    drop(session);
    let output = format!("{value:?}");
    assert!(
        observer
            .events
            .iter()
            .any(|event| event.phase == ExecutionPhase::ScratchRetirement
                && event.work == output.len() + size_of::<String>() + 1)
    );
}
#[test]
fn rejected_outer_publication_consumes_the_full_result_after_all_task_scratch() {
    let value = mixed();
    let (output, baseline) = execute(&value);
    let mut observer = Observer {
        at: Some(baseline.events.len()),
        ..Default::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        value.debug_observed(&mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(session.first_refusal().unwrap().cause, "original interior");
    drop(session);
    let tail = &observer.events[baseline.events.len()..];
    assert!(
        tail.iter()
            .all(|event| event.phase == ExecutionPhase::ScratchRetirement)
    );
    assert_eq!(
        tail.iter().map(|event| event.work).sum::<usize>(),
        output.len() + size_of::<String>() + 1
    );
}
#[test]
fn typed_representation_failure_retires_held_text_and_all_borrowed_scratch() {
    let value = ClauseSort::Bool;
    let mut state = State {
        tasks: vec![Task::Sort(&value)],
        pending: Some(Task::Text("suffix")),
        output: "owned λ".repeat(1000),
    };
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    // An already-held descriptor is an internal invariant refusal, not a
    // semantic sort error or a permissive partial formatting success.
    let result = state.sort(&value, &mut work);
    assert_eq!(result, Err(ObservedValueError::InvalidRange));
    assert_eq!(state.tasks.len(), 1);
    assert!(matches!(state.pending, Some(Task::Text("suffix"))));
    assert!(!state.output.is_empty());
    assert_eq!(
        state.finish(result, &mut work),
        Err(ObservedValueError::InvalidRange)
    );
    assert!(state.pending.is_none() && state.tasks.is_empty() && state.output.is_empty());
    drop(work);
    assert!(session.first_refusal().is_none());
}
