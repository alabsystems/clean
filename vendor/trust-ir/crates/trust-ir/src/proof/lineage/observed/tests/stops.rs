// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;

#[test]
fn every_actual_small_shape_and_retirement_boundary_is_terminal() {
    let manifest = ProofLineageManifest {
        schema_version: 2,
        nodes: vec![node(7, 1, 2)],
        roots: vec![ProofLineageId::new(7)],
    };
    let mut measured = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut measured);
    manifest
        .shape_errors_observed(&mut session, site())
        .unwrap();
    for stop in 1..=measured.events.len() {
        let mut observer = Observer {
            stop_at: Some(stop),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        assert_eq!(
            manifest.shape_errors_observed(&mut session, site()),
            Err(ObservedValueError::AdmissionRefused),
            "event {stop}"
        );
        assert_eq!(session.first_refusal().unwrap().cause, "interior");
        assert_eq!(
            manifest.shape_errors_observed(&mut session, site()),
            Err(ObservedValueError::AdmissionRefused)
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

#[test]
fn cumulative_work_and_requested_storage_are_not_renewed_between_manifest_checks() {
    let manifest = fixture();
    let mut measured = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut measured);
    manifest
        .shape_errors_observed(&mut session, site())
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
        assert!(
            manifest
                .shape_errors_observed(&mut session, site())
                .unwrap()
                .is_empty()
        );
        assert_eq!(
            manifest.shape_errors_observed(&mut session, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(
            session.first_refusal().unwrap().cause,
            if memory { "bytes" } else { "work" }
        );
    }
}

#[test]
fn refused_error_storage_keeps_owned_pending_diagnostic_until_explicit_retirement() {
    let mut state = Checking::default();
    let mut observer = Observer {
        byte_limit: Some(0),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let error = ProofLineageError::MissingCertificate {
        node: ProofLineageId::new(1),
        obligation: ProofId::new(1),
        prover: "owned fixture".into(),
    };
    assert_eq!(
        state.error(error, &mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert!(state.pending_error.is_some());
    assert!(state.errors.is_empty());
    assert_eq!(state.errors.capacity(), 0);
    state.retire_errors(&mut session, site());
    assert!(state.pending_error.is_none());
    assert_eq!(session.first_refusal().unwrap().cause, "bytes");
}

#[test]
fn retirement_refusal_prevents_an_otherwise_valid_structural_result() {
    let mut observer = Observer {
        stop_retirement: true,
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        fixture().shape_errors_observed(&mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(session.first_refusal().unwrap().cause, "retirement");
    assert_eq!(
        session.first_refusal().unwrap().progress.phase,
        ExecutionPhase::ScratchRetirement
    );
}
