// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;

#[test]
fn each_display_callback_in_every_variant_refuses_without_partial_publication_or_new_owner() {
    for error in fixtures::errors(u32::MAX) {
        let (_, baseline) = run(&error);
        for stop in 1..=baseline.events.len() {
            let mut observer = Observer {
                stop: Some(stop),
                ..Observer::default()
            };
            let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
            assert_eq!(
                error.display_observed(&mut session, site()),
                Err(ObservedValueError::AdmissionRefused)
            );
            assert_eq!(
                session.first_refusal().unwrap().cause,
                "original layout text stop"
            );
            assert_eq!(
                session.first_refusal().unwrap().progress,
                baseline.events[stop - 1]
            );
            assert_eq!(session.remaining_fuel(), InterpretOptions::default().fuel);
            // A retry uses the same stopped owner; it cannot reacquire admission.
            assert_eq!(
                LayoutError::SizeOverflow.display_observed(&mut session, site()),
                Err(ObservedValueError::AdmissionRefused)
            );
            assert!(
                observer
                    .events
                    .iter()
                    .skip(stop)
                    .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
            );
            assert!(observer.events.iter().all(|e| e.site == site()));
        }
    }
}

#[test]
fn each_retirement_callback_in_every_variant_still_consumes_all_original_fields() {
    for error in fixtures::errors(u32::MAX) {
        let baseline = retirement(error.clone());
        let expected: Vec<_> = baseline
            .events
            .iter()
            .copied()
            .filter(|e| e.phase == ExecutionPhase::ScratchRetirement)
            .collect();
        for stop in 1..=baseline.events.len() {
            let mut observer = Observer {
                stop: Some(stop),
                ..Observer::default()
            };
            let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
            assert_eq!(
                error.clone().retire_observed(&mut session, site()),
                Err(ObservedValueError::AdmissionRefused)
            );
            assert_eq!(
                session.first_refusal().unwrap().cause,
                "original layout text stop"
            );
            assert_eq!(
                session.first_refusal().unwrap().progress,
                baseline.events[stop - 1]
            );
            assert_eq!(session.remaining_fuel(), InterpretOptions::default().fuel);
            assert_eq!(
                observer
                    .events
                    .iter()
                    .copied()
                    .filter(|e| e.phase == ExecutionPhase::ScratchRetirement)
                    .collect::<Vec<_>>(),
                expected
            );
            assert!(
                observer
                    .events
                    .iter()
                    .skip(stop)
                    .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
            );
        }
    }
}

#[test]
fn work_and_copy_caps_accumulate_across_distinct_errors_without_replenishment() {
    let a = LayoutError::MissingFieldOffset {
        struct_id: StructId::new(u32::MAX),
        field: 29,
    };
    let b = triple("λ\n'\"next");
    let mut baseline = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    a.display_observed(&mut session, site()).unwrap();
    b.display_observed(&mut session, site()).unwrap();
    for copy in [false, true] {
        let mut observer = Observer {
            work_cap: (!copy).then_some(baseline.work - 1),
            byte_cap: copy.then_some(baseline.bytes - 1),
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
            if copy { "copy cap" } else { "work cap" }
        );
        assert_eq!(
            a.display_observed(&mut session, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
    }
}

#[test]
fn first_output_header_refusal_has_no_owned_partial_text_to_retire() {
    let mut observer = Observer {
        byte_cap: Some(0),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        triple("must remain borrowed").display_observed(&mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(session.first_refusal().unwrap().cause, "copy cap");
    assert_eq!(observer.events.len(), 1);
    assert_eq!(
        (
            observer.events[0].phase,
            observer.events[0].work,
            observer.events[0].copy_bytes
        ),
        (ExecutionPhase::Validation, 1, size_of::<String>())
    );
}

#[test]
fn first_utf8_growth_and_actual_copy_have_distinct_preoperation_admissions() {
    let mut baseline = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let mut text = String::new();
    Work {
        session: &mut session,
        site: site(),
    }
    .text("λ", &mut text)
    .unwrap();
    let ordinals: Vec<_> = baseline
        .events
        .iter()
        .enumerate()
        .filter(|(_, e)| e.work == 2 && e.copy_bytes == 2)
        .map(|(i, _)| i + 1)
        .collect();
    assert_eq!(ordinals, vec![3, 4]);
    for (stop, allocated) in [(ordinals[0], false), (ordinals[1], true)] {
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
            work.text("λ", &mut text),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(text.len(), 0);
        assert_eq!(text.capacity() >= 2, allocated);
        work.retire_text(text);
        assert_eq!(
            work.session.first_refusal().unwrap().cause,
            "original layout text stop"
        );
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
fn final_display_publication_refusal_consumes_the_entire_completed_text() {
    let error = triple("λ'\n\"complete");
    let (text, baseline) = run(&error);
    let stop = baseline.events.len();
    let mut observer = Observer {
        stop: Some(stop),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        error.display_observed(&mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        session.first_refusal().unwrap().progress.phase,
        ExecutionPhase::Publication
    );
    assert_eq!(observer.events.len(), stop + 2);
    assert_eq!(
        (
            observer.events[stop].phase,
            observer.events[stop].work,
            observer.events[stop].copy_bytes
        ),
        (
            ExecutionPhase::ScratchRetirement,
            text.len() + size_of::<String>() + 1,
            0
        )
    );
    assert_eq!(
        (
            observer.events[stop + 1].phase,
            observer.events[stop + 1].work
        ),
        (ExecutionPhase::ScratchRetirement, 0)
    );
}
