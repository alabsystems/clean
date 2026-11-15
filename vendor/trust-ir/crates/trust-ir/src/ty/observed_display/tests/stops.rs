// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;

#[test]
fn every_actual_callback_refuses_without_partial_text_and_keeps_original_owner_cause() {
    let ty = fixture();
    let (_, baseline) = run(&ty);
    for stop in 1..=baseline.events.len() {
        let mut observer = Observer {
            stop: Some(stop),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        assert_eq!(
            ty.display_observed(&mut session, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(
            session.first_refusal().unwrap().cause,
            "original type text stop"
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

#[test]
fn cumulative_work_and_copy_caps_apply_across_distinct_types_in_one_session() {
    let a = fixture();
    let b = Ty::Tuple(vec![Ty::U32; 32]);
    let mut baseline = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    a.display_observed(&mut session, site()).unwrap();
    b.display_observed(&mut session, site()).unwrap();
    for bytes in [false, true] {
        let mut observer = Observer {
            work_cap: (!bytes).then_some(baseline.work - 1),
            byte_cap: bytes.then_some(baseline.bytes - 1),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        a.display_observed(&mut session, site()).unwrap();
        assert_eq!(
            b.display_observed(&mut session, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(
            session.first_refusal().unwrap().cause,
            if bytes { "bytes" } else { "work" }
        );
        assert_eq!(
            a.display_observed(&mut session, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
    }
}

#[test]
fn first_frame_and_text_storage_are_admitted_before_any_allocation() {
    let ty = Ty::U32;
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
        state.push(Task::Type(&ty), &mut work),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!((state.tasks.len(), state.tasks.capacity()), (0, 0));
    state.retire_tasks(&mut work);
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
        work.text("λ", &mut state.output),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!((state.output.len(), state.output.capacity()), (0, 0));
}

#[test]
fn later_raw_utf8_chunk_refusal_keeps_exact_partial_output_until_retirement() {
    let ty = Ty::Dialect(Box::new(DialectTy::new("λ".repeat(3000), "name", 1)));
    let mut baseline = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let mut state = State::default();
    state
        .walk(
            &ty,
            &mut Work {
                session: &mut session,
                site: site(),
            },
        )
        .unwrap();
    let stop = baseline
        .events
        .iter()
        .enumerate()
        .filter(|(_, e)| e.work == 1024 && e.copy_bytes == 1024)
        .nth(1)
        .unwrap()
        .0
        + 1;
    let mut observer = Observer {
        stop: Some(stop),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut state = State::default();
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    assert_eq!(
        state.walk(&ty, &mut work),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(state.output, "dialect<".to_owned() + &"λ".repeat(512));
    state.retire_tasks(&mut work);
    work.retire(take(&mut state.output));
    assert_eq!(state.output.capacity(), 0);
}

#[test]
fn actual_scalar_escape_refusal_keeps_the_owned_prefix_instead_of_accepting_partial_debug() {
    let mut baseline = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let mut text = String::new();
    Work {
        session: &mut session,
        site: site(),
    }
    .quoted("beforeλafter", &mut text)
    .unwrap();
    let stop = baseline
        .events
        .iter()
        .enumerate()
        .filter(|(_, e)| {
            e.phase == ExecutionPhase::Validation
                && e.work >= 8 * u32::BITS as usize
                && e.copy_bytes == size_of::<core::char::EscapeDebug>()
        })
        .nth(3)
        .unwrap()
        .0
        + 1;
    let mut observer = Observer {
        stop: Some(stop),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut text = String::new();
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    assert_eq!(
        work.quoted("beforeλafter", &mut text),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(text, "\"bef");
    work.retire(text);
    assert_eq!(
        work.session.first_refusal().unwrap().cause,
        "original type text stop"
    );
}

#[test]
fn final_publication_refusal_retires_completed_string_after_all_borrowed_tasks() {
    let ty = fixture();
    let (_, baseline) = run(&ty);
    let stop = baseline.events.len();
    let mut observer = Observer {
        stop: Some(stop),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        ty.display_observed(&mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        session.first_refusal().unwrap().progress.phase,
        ExecutionPhase::Publication
    );
    assert_eq!(observer.events.len(), stop + 2);
    assert!(
        observer
            .events
            .iter()
            .skip(stop)
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
}

#[test]
fn first_task_buffer_retirement_refusal_cannot_publish_even_completed_text() {
    let ty = fixture();
    let (_, baseline) = run(&ty);
    let stop = baseline
        .events
        .iter()
        .position(|e| e.phase == ExecutionPhase::ScratchRetirement)
        .unwrap()
        + 1;
    let mut observer = Observer {
        stop: Some(stop),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        ty.display_observed(&mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        session.first_refusal().unwrap().progress.phase,
        ExecutionPhase::ScratchRetirement
    );
    assert!(
        observer
            .events
            .iter()
            .all(|e| e.phase != ExecutionPhase::Publication)
    );
    assert_eq!(observer.events.len(), stop + 3);
}

#[test]
fn wide_tuple_interior_stop_retires_pending_borrowed_continuations_and_buffer() {
    let ty = Ty::Tuple(vec![Ty::U32; 4096]);
    let mut observer = Observer {
        work_cap: Some(1000),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut state = State::default();
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    assert_eq!(
        state.walk(&ty, &mut work),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert!(!state.tasks.is_empty() && !state.output.is_empty());
    state.retire_tasks(&mut work);
    work.retire(take(&mut state.output));
    assert_eq!((state.tasks.len(), state.tasks.capacity()), (0, 0));
    assert_eq!(state.output.capacity(), 0);
    assert_eq!(work.session.first_refusal().unwrap().cause, "work");
}
