// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;

#[test]
fn actual_encoder_reader_shape_rerender_and_retirement_keep_one_original_session() {
    let a = minimal();
    let mut measured = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut measured);
    a.canonical_text_for_wire_observed(&mut session, site())
        .unwrap();
    // Cover ordered stages of the actual round-trip, not an artificial prewalk.
    let count = measured.events.len();
    let mut selected = vec![1, 2, 3, count];
    for numerator in 1..32 {
        selected.push(count * numerator / 32 + 1);
    }
    for (index, event) in measured.events.iter().enumerate() {
        if event.phase == ExecutionPhase::ScratchRetirement
            || event.phase == ExecutionPhase::Publication
        {
            selected.push(index + 1);
        }
    }
    selected.sort_unstable();
    selected.dedup();
    for stop in selected {
        let mut observer = Observer {
            stop_at: Some(stop),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        assert_eq!(
            a.canonical_text_for_wire_observed(&mut session, site()),
            Err(ObservedValueError::AdmissionRefused),
            "event {stop}"
        );
        assert_eq!(session.first_refusal().unwrap().cause, "interior");
        assert_eq!(
            a.canonical_text_for_wire_observed(&mut session, site()),
            Err(ObservedValueError::AdmissionRefused)
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
fn work_and_requested_storage_accumulate_across_complete_abi_round_trips() {
    let a = fixture();
    let mut measured = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut measured);
    a.canonical_text_for_wire_observed(&mut session, site())
        .unwrap();
    for memory in [false, true] {
        let mut observer = if memory {
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
        assert_eq!(
            a.canonical_text_for_wire_observed(&mut session, site())
                .unwrap(),
            a.to_canonical_text()
        );
        assert_eq!(
            a.canonical_text_for_wire_observed(&mut session, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(
            session.first_refusal().unwrap().cause,
            if memory { "bytes" } else { "work" }
        );
        assert_eq!(session.remaining_fuel(), InterpretOptions::default().fuel);
    }
}

#[test]
fn a_refusal_during_flat_owned_retirement_prevents_text_publication() {
    let mut observer = Observer {
        stop_retirement: true,
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        fixture().canonical_text_for_wire_observed(&mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(session.first_refusal().unwrap().cause, "retirement");
    assert_eq!(
        session.first_refusal().unwrap().progress.phase,
        ExecutionPhase::ScratchRetirement
    );
}

#[test]
fn long_quoted_and_numeric_work_is_observed_inside_the_actual_loop() {
    let mut observer = Observer {
        stop_at: Some(20),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut out = Writer::new(&mut session, site()).unwrap();
    assert_eq!(
        out.quoted(&"λ\\\0".repeat(2049)),
        Err(ObservedValueError::AdmissionRefused)
    );
    let residue = core::mem::take(&mut out.text);
    out.retire(residue);
    assert_eq!(session.first_refusal().unwrap().cause, "interior");
    let mut observer = Observer {
        stop_at: Some(5),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut out = Writer::new(&mut session, site()).unwrap();
    assert_eq!(
        out.number(u64::MAX),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert!(out.text.is_empty());
}
