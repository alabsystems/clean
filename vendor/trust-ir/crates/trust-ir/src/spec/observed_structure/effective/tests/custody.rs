// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn failed_final_publication_consumes_the_complete_pending_text_and_preserves_first_cause() {
    let variable = SpecVar::new("x", "opaque").with_sort(datatype(&"longλ\n".repeat(600)));
    let (expected, base, bound) = run(&variable, &ClauseSort::Bool);
    let expected = expected.unwrap();
    let mut observer = Observer {
        stop: Some(bound),
        refuse_cleanup: true,
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        variable.effective_sort_mismatch_observed(&ClauseSort::Bool, &mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        session.first_refusal().unwrap().cause,
        "original effective-sort stop"
    );
    assert_eq!(
        session.first_refusal().unwrap().progress,
        base.events[bound - 1]
    );
    let full_text_fee = expected.len() + size_of::<String>() + 1;
    assert!(observer.events[bound..].iter().any(|event| event.phase
        == ExecutionPhase::ScratchRetirement
        && event.work == full_text_fee));
    assert_eq!(
        observer.events.last().unwrap().phase,
        ExecutionPhase::ScratchRetirement
    );
}
#[test]
fn actual_formatting_cut_retains_its_owned_prefix_until_same_owner_complete_drain() {
    let sort = datatype(&"longλ\n".repeat(100));
    let expected = format!("{sort:?}");
    let mut base = Observer::default();
    let bound;
    {
        let count = base.count.clone();
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut base);
        let mut work = Work {
            session: &mut session,
            site: site(),
        };
        let mut state = State::default();
        state
            .sort_text(sorts::Sort::Borrowed(&sort), &mut work)
            .unwrap();
        assert_eq!(state.detail, expected);
        bound = count.get();
        state.retire_scratch(&mut work);
        retirement::consume_vec(take(&mut state.errors), &mut work);
        assert!(empty(&state));
    }
    let stop = base.events[..bound]
        .iter()
        .enumerate()
        .filter(|(_, event)| event.phase == ExecutionPhase::Validation)
        .nth(100)
        .unwrap()
        .0
        + 1;
    let mut observer = Observer {
        stop: Some(stop),
        refuse_cleanup: true,
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut state = State::default();
    assert_eq!(
        state.sort_text(sorts::Sort::Borrowed(&sort), &mut work),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert!(!state.detail.is_empty());
    assert!(state.detail.len() < expected.len());
    assert!(expected.starts_with(&state.detail));
    let retained = state.detail.clone();
    assert_eq!(state.detail, retained);
    state.retire_scratch(&mut work);
    retirement::consume_vec(take(&mut state.errors), &mut work);
    assert!(empty(&state));
    assert_eq!(
        work.session.first_refusal().unwrap().cause,
        "original effective-sort stop"
    );
    assert_eq!(
        work.session.first_refusal().unwrap().progress,
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
#[test]
fn the_actual_text_storage_copy_cap_refuses_before_growing_a_diagnostic_buffer() {
    let mut observer = Observer {
        byte_cap: Some(3),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut text = String::new();
    assert_eq!(
        work.text("Bool", &mut text),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(text.capacity(), 0);
    assert!(text.is_empty());
    let first = work.session.first_refusal().unwrap().progress;
    assert_eq!(first.work, 4);
    assert_eq!(first.copy_bytes, 4);
    work.retire_text(&mut text);
    assert_eq!(text.capacity(), 0);
    assert_eq!(work.session.first_refusal().unwrap().progress, first);
}
