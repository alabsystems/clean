// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;

#[test]
fn actual_scalar_classification_stop_retains_the_exact_owned_quoted_prefix() {
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
    let bytes = text.len();
    work.retire_text(text);
    assert_eq!(
        work.session.first_refusal().unwrap().cause,
        "original layout text stop"
    );
    assert_eq!(observer.events[stop].work, bytes + size_of::<String>() + 1);
    assert!(
        observer
            .events
            .iter()
            .skip(stop)
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
}

#[test]
fn interior_long_triple_stop_cannot_skip_to_the_closing_quote_or_accept_prefix() {
    let source = "λ".repeat(1500);
    let mut baseline = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let mut output = String::new();
    display::write(
        &triple(&source),
        &mut Work {
            session: &mut session,
            site: site(),
        },
        &mut output,
    )
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
        .nth(512)
        .unwrap()
        .0
        + 1;
    let mut observer = Observer {
        stop: Some(stop),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut output = String::new();
    assert_eq!(
        display::write(&triple(&source), &mut work, &mut output),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(output, "target \"".to_owned() + &"λ".repeat(512));
    let bytes = output.len();
    work.retire_text(output);
    assert_eq!(observer.events[stop].work, bytes + size_of::<String>() + 1);
    assert!(
        observer
            .events
            .iter()
            .skip(stop)
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
}

#[test]
fn existing_sticky_refusal_cannot_bypass_owned_text_or_any_fixed_variant_retirement() {
    let mut observer = Observer {
        stop: Some(1),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let first = ExecutionProgress {
        phase: ExecutionPhase::ModuleLookup,
        site: site(),
        work: 17,
        copy_bytes: 0,
    };
    assert!(session.admit(first).is_err());
    let mut expected = Vec::new();
    for error in fixtures::errors(u32::MAX) {
        expected.extend(
            retirement(error.clone())
                .events
                .into_iter()
                .filter(|e| e.phase == ExecutionPhase::ScratchRetirement),
        );
        assert_eq!(
            error.retire_observed(&mut session, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(session.first_refusal().unwrap().progress, first);
        assert_eq!(
            session.first_refusal().unwrap().cause,
            "original layout text stop"
        );
    }
    assert_eq!(observer.events[1..], expected);
    assert!(
        observer.events[1..]
            .iter()
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
}

#[test]
fn refusal_during_owned_text_retirement_still_reaches_all_cleanup_and_keeps_first_cause() {
    let mut observer = Observer {
        stop: Some(2),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        triple(&"λ".repeat(5000)).retire_observed(&mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    let first = session.first_refusal().unwrap().progress;
    assert_eq!(first.work, 10000 + size_of::<String>() + 1);
    assert_eq!(first.phase, ExecutionPhase::ScratchRetirement);
    assert_eq!(
        triple("second").retire_observed(&mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(session.first_refusal().unwrap().progress, first);
    assert_eq!(
        session.first_refusal().unwrap().cause,
        "original layout text stop"
    );
    assert_eq!(observer.events.len(), 8);
    assert!(
        observer
            .events
            .iter()
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
    assert_eq!(
        observer.events[5].work,
        "second".len() + size_of::<String>() + 1
    );
}

#[test]
fn cumulative_retirement_work_uses_the_same_original_cap_and_consumes_second_error() {
    let a = triple("first");
    let b = triple("λsecond");
    let mut baseline = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    a.clone().retire_observed(&mut session, site()).unwrap();
    b.clone().retire_observed(&mut session, site()).unwrap();
    let mut observer = Observer {
        work_cap: Some(baseline.work - 1),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    a.retire_observed(&mut session, site()).unwrap();
    assert_eq!(
        b.retire_observed(&mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(session.first_refusal().unwrap().cause, "work cap");
    assert_eq!(session.remaining_fuel(), InterpretOptions::default().fuel);
    // First error has terminal Publication; stopped second still has every
    // retirement event, including its text poll and outer header poll.
    assert_eq!(observer.events.len(), 9);
    assert_eq!(
        observer
            .events
            .iter()
            .filter(|e| e.phase == ExecutionPhase::Publication)
            .count(),
        1
    );
    assert_eq!(
        observer.events.last().unwrap().phase,
        ExecutionPhase::ScratchRetirement
    );
    assert_eq!(observer.events.last().unwrap().work, 0);
}

#[test]
fn zero_work_cleanup_publication_can_itself_refuse_after_complete_consumption() {
    let error = triple("already consumed before finish");
    let baseline = retirement(error.clone());
    let stop = baseline.events.len();
    let mut observer = Observer {
        stop: Some(stop),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        error.retire_observed(&mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        (
            session.first_refusal().unwrap().progress.phase,
            session.first_refusal().unwrap().progress.work
        ),
        (ExecutionPhase::Publication, 0)
    );
    assert_eq!(observer.events, baseline.events);
}

#[test]
fn secondary_cleanup_refusals_cannot_replace_the_original_typed_cause() {
    #[derive(Default)]
    struct RejectEvery {
        events: Vec<ExecutionProgress>,
    }
    impl ExecutionObserver for RejectEvery {
        type Refusal = &'static str;
        fn admit(&mut self, event: ExecutionProgress) -> Result<(), Self::Refusal> {
            self.events.push(event);
            Err(if event.phase == ExecutionPhase::ScratchRetirement {
                "secondary cleanup refusal"
            } else {
                "original caller refusal"
            })
        }
    }
    let mut observer = RejectEvery::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let first = ExecutionProgress {
        phase: ExecutionPhase::ModuleLookup,
        site: site(),
        work: 19,
        copy_bytes: 0,
    };
    assert!(session.admit(first).is_err());
    assert_eq!(
        triple("fully consumed after every refusal").retire_observed(&mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        session.first_refusal().unwrap().cause,
        "original caller refusal"
    );
    assert_eq!(session.first_refusal().unwrap().progress, first);
    assert_eq!(observer.events.len(), 5);
    assert!(
        observer.events[1..]
            .iter()
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
    assert_eq!(
        observer.events[2].work,
        "fully consumed after every refusal".len() + size_of::<String>() + 1
    );
    assert_eq!(observer.events.last().unwrap().work, 0);
}
