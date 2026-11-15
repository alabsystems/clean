// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn every_actual_construction_hash_compare_and_publication_callback_refuses() {
    let source = fixture();
    let (_, baseline) = run(&source);
    for stop in 1..=baseline.events.len() {
        let mut observer = Observer {
            stop: Some(stop),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        assert_eq!(
            source.binding_digest_is_valid_observed(&mut session, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(
            session.first_refusal().unwrap().cause,
            "original source binding stop"
        );
        assert_eq!(session.remaining_fuel(), InterpretOptions::default().fuel);
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
fn original_cumulative_work_and_copy_caps_are_not_renewed_between_bindings() {
    let source = fixture();
    let mut baseline = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    for _ in 0..2 {
        assert!(
            source
                .binding_digest_is_valid_observed(&mut session, site())
                .unwrap()
        );
    }
    for bytes in [false, true] {
        let mut observer = Observer {
            work_cap: (!bytes).then_some(baseline.work - 1),
            byte_cap: bytes.then_some(baseline.bytes - 1),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        assert!(
            source
                .binding_digest_is_valid_observed(&mut session, site())
                .unwrap()
        );
        assert_eq!(
            source.binding_digest_is_valid_observed(&mut session, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        let first = session.first_refusal().unwrap().progress;
        assert_eq!(
            source.binding_digest_is_valid_observed(&mut session, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(session.first_refusal().unwrap().progress, first);
    }
}
#[test]
fn actual_partial_name_chunk_and_preimage_buffer_remain_owned_on_interior_stop() {
    let mut source = fixture();
    source.loops[0].bindings[0].name = "λ".repeat(4000);
    let mut baseline = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let mut writer = Writer {
        session: &mut session,
        site: site(),
        bytes: Vec::new(),
    };
    writer.preimage(&source).unwrap();
    writer.retire();
    let chunks = baseline
        .events
        .iter()
        .enumerate()
        .filter(|(_, e)| {
            e.phase == ExecutionPhase::CanonicalSerialization
                && e.work == 1024
                && e.copy_bytes == 1024
        })
        .map(|(index, _)| index + 1)
        .collect::<Vec<_>>();
    assert!(chunks.len() > 2);
    let stop = chunks[1];
    let mut observer = Observer {
        stop: Some(stop),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut writer = Writer {
        session: &mut session,
        site: site(),
        bytes: Vec::new(),
    };
    assert_eq!(
        writer.preimage(&source),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert!(writer.bytes.len() > 1024 && writer.bytes.len() < 2000);
    let first = writer.session.first_refusal().unwrap().progress;
    writer.retire();
    assert_eq!(writer.bytes.capacity(), 0);
    assert_eq!(writer.session.first_refusal().unwrap().progress, first);
}
#[test]
fn raw_buffer_growth_is_admitted_before_allocation_or_input_copy() {
    let mut observer = Observer {
        byte_cap: Some(0),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut writer = Writer {
        session: &mut session,
        site: site(),
        bytes: Vec::new(),
    };
    assert_eq!(
        writer.append(b"retained input"),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(writer.bytes.capacity(), 0);
    assert!(writer.bytes.is_empty());
    writer.retire();
    assert_eq!(writer.session.first_refusal().unwrap().cause, "bytes");
}
#[test]
fn cleanup_refusal_consumes_even_allocated_empty_buffer_and_denies_publication() {
    let arm = Rc::new(Cell::new(false));
    let mut observer = Observer {
        cleanup: Some(arm.clone()),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut writer = Writer {
        session: &mut session,
        site: site(),
        bytes: Vec::with_capacity(128),
    };
    arm.set(true);
    writer.retire();
    assert_eq!(writer.bytes.capacity(), 0);
    assert_eq!(
        writer.publication(),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        writer.session.first_refusal().unwrap().cause,
        "original source binding cleanup"
    );
}
#[test]
fn initial_header_and_final_bool_publication_stops_return_no_binding_verdict() {
    let source = fixture();
    let mut observer = Observer {
        byte_cap: Some(0),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        source.binding_digest_is_valid_observed(&mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(observer.events.len(), 1);
    let (_, baseline) = run(&source);
    let stop = baseline.events.len();
    let mut observer = Observer {
        stop: Some(stop),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        source.binding_digest_is_valid_observed(&mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        session.first_refusal().unwrap().progress.phase,
        ExecutionPhase::Publication
    );
    assert_eq!(observer.events.len(), stop);
}
