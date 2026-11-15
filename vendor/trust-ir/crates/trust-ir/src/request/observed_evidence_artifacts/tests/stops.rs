// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
#[test]
fn every_source_text_growth_duplicate_and_publication_callback_is_cancellable() {
    let e = fixture();
    let (_, baseline, end) = observed(&e);
    for (i, expected) in baseline.events[..end].iter().enumerate() {
        let mut o = Observer {
            stop: Some(i + 1),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert_eq!(
            e.artifact_errors_observed(&mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(s.first_refusal().unwrap().progress, *expected);
        assert_eq!(s.first_refusal().unwrap().cause, "interior");
        assert_eq!(&o.events[..=i], &baseline.events[..=i]);
        assert!(
            o.events[i + 1..]
                .iter()
                .all(|p| p.phase == ExecutionPhase::ScratchRetirement)
        );
    }
}
#[test]
fn cumulative_work_budget_cannot_be_renewed_between_artifact_batches() {
    let e = fixture();
    let (_, base, _) = observed(&e);
    let mut o = Observer {
        work_cap: Some(base.work),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let rows = e.artifact_errors_observed(&mut s, site()).unwrap();
    retire_native_bundle_errors_observed(rows, &mut s, site()).unwrap();
    assert_eq!(
        e.artifact_errors_observed(&mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(s.first_refusal().unwrap().cause, "work");
}
#[test]
fn cumulative_copy_budget_cannot_be_renewed_between_artifact_batches() {
    let e = fixture();
    let (_, base, _) = observed(&e);
    let mut o = Observer {
        byte_cap: Some(base.bytes),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let rows = e.artifact_errors_observed(&mut s, site()).unwrap();
    retire_native_bundle_errors_observed(rows, &mut s, site()).unwrap();
    assert_eq!(
        e.artifact_errors_observed(&mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(s.first_refusal().unwrap().cause, "copy");
}
#[test]
fn original_interrupt_cannot_clear_after_first_callback() {
    let e = fixture();
    let arm = Rc::new(Cell::new(true));
    let mut o = Observer {
        arm: Some(arm.clone()),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(
        e.artifact_errors_observed(&mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    arm.set(false);
    assert_eq!(
        e.artifact_errors_observed(&mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(s.first_refusal().unwrap().cause, "interrupt");
}
#[test]
fn zero_instruction_fuel_is_unchanged_by_metadata_validation_and_disposal() {
    let e = fixture();
    let mut o = Observer::default();
    let mut s = ObservedSession::new(
        InterpretOptions {
            fuel: 0,
            ..InterpretOptions::default()
        },
        &mut o,
    );
    let rows = e.artifact_errors_observed(&mut s, site()).unwrap();
    retire_native_bundle_errors_observed(rows, &mut s, site()).unwrap();
    assert_eq!(s.remaining_fuel(), 0);
}
#[test]
fn final_publication_refusal_discards_the_complete_list_without_a_prefix() {
    let e = fixture();
    let (_, base, end) = observed(&e);
    let mut o = Observer {
        stop: Some(end),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(base.events[end - 1].phase, ExecutionPhase::Publication);
    assert_eq!(
        e.artifact_errors_observed(&mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(s.first_refusal().unwrap().progress, base.events[end - 1]);
    assert!(
        o.events[end..]
            .iter()
            .all(|p| p.phase == ExecutionPhase::ScratchRetirement)
    );
}
