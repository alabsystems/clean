// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
#[test]
fn every_actual_nested_callback_and_terminal_publication_can_refuse() {
    let baseline = capture(all());
    for (i, expected) in baseline.events.iter().enumerate() {
        let mut observer = Observer {
            stop_at: Some(i + 1),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(
            InterpretOptions {
                fuel: 0,
                ..InterpretOptions::default()
            },
            &mut observer,
        );
        assert_eq!(
            retire_native_bundle_errors_observed(all(), &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(s.first_refusal().unwrap().progress, *expected);
        assert_eq!(s.first_refusal().unwrap().cause, "interior");
        assert_eq!(s.remaining_fuel(), 0);
        assert_eq!(&observer.events[..=i], &baseline.events[..=i]);
        assert!(
            observer.events[i + 1..]
                .iter()
                .all(|p| p.phase == ExecutionPhase::ScratchRetirement)
        );
    }
}
#[test]
fn cancellation_before_entry_cannot_abandon_any_payload() {
    let baseline = capture(all());
    let mut observer = Observer {
        stop_at: Some(1),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let marker = ExecutionProgress {
        phase: ExecutionPhase::Validation,
        site: site(),
        work: 1,
        copy_bytes: 0,
    };
    assert!(s.admit(marker).is_err());
    assert_eq!(
        retire_native_bundle_errors_observed(all(), &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(s.first_refusal().unwrap().progress, marker);
    assert_eq!(
        &observer.events[1..],
        &baseline.events[..baseline.events.len() - 1]
    );
}
#[test]
fn original_cumulative_work_cannot_renew_across_disposals() {
    let baseline = capture(all());
    let mut observer = Observer {
        work_limit: Some(baseline.work),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut observer);
    retire_native_bundle_errors_observed(all(), &mut s, site()).unwrap();
    assert_eq!(
        retire_native_bundle_errors_observed(all(), &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(s.first_refusal().unwrap().cause, "work");
    assert_eq!(
        retire_native_bundle_errors_observed(Vec::new(), &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
}
#[test]
fn original_cumulative_copy_cannot_renew_across_disposals() {
    let baseline = capture(all());
    let mut observer = Observer {
        byte_limit: Some(baseline.bytes),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut observer);
    retire_native_bundle_errors_observed(all(), &mut s, site()).unwrap();
    assert_eq!(
        retire_native_bundle_errors_observed(all(), &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(s.first_refusal().unwrap().cause, "copy");
}
#[test]
fn nonzero_retirement_copy_refusal_still_consumes_every_later_store() {
    let baseline = capture(all());
    let mut observer = Observer {
        byte_limit: Some(0),
        ..Observer::default()
    };
    assert_eq!(
        run(all(), &mut observer),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        &observer.events[..],
        &baseline.events[..baseline.events.len() - 1]
    );
}
#[test]
fn terminal_refusal_does_not_resume_or_replace_its_first_cause() {
    let baseline = capture(all());
    let mut observer = Observer {
        stop_at: Some(baseline.events.len()),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        retire_native_bundle_errors_observed(all(), &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    let first = s.first_refusal().unwrap().progress;
    assert_eq!(
        retire_native_bundle_errors_observed(all(), &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(s.first_refusal().unwrap().progress, first);
    assert_eq!(s.first_refusal().unwrap().cause, "interior");
}
