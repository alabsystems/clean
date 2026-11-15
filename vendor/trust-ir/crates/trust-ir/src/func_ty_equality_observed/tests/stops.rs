// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;

#[test]
fn every_real_type_string_feature_mode_binding_and_publication_callback_can_refuse() {
    let a = fixture();
    let before = a.clone();
    let (_, baseline) = run(&a, &a);
    for cut in 1..=baseline.events.len() {
        let mut observer = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        {
            let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
            assert_eq!(
                a.structural_eq_observed(&a, &mut session, site()),
                Err(ObservedValueError::AdmissionRefused)
            );
            assert_eq!(
                session.first_refusal().unwrap().cause,
                "original FuncTy stop"
            );
        }
        assert_eq!(&observer.events[..cut], &baseline.events[..cut]);
        assert!(
            observer.events[cut..]
                .iter()
                .all(|event| event.phase == ExecutionPhase::ScratchRetirement)
        );
        assert_eq!(a, before);
    }
}

#[test]
fn repeated_comparisons_spend_original_cumulative_work_and_copy_without_regrant() {
    let a = fixture();
    let (_, baseline) = run(&a, &a);
    for copy in [false, true] {
        let mut observer = Observer::default();
        if copy {
            observer.copy_cap = Some(baseline.bytes);
        } else {
            observer.work_cap = Some(baseline.work);
        }
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        assert!(a.structural_eq_observed(&a, &mut session, site()).unwrap());
        assert_eq!(
            a.structural_eq_observed(&a, &mut session, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert!(session.first_refusal().is_some());
    }
}

#[test]
fn zero_instruction_fuel_site_and_preexisting_original_cause_are_preserved() {
    let a = fixture();
    let (_, observer) = run(&a, &a);
    assert!(observer.events.iter().all(|event| event.site == site()));
    let mut observer = Observer {
        stop: Some(1),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert!(
        session
            .admit(ExecutionProgress {
                phase: ExecutionPhase::Validation,
                site: site(),
                work: 1,
                copy_bytes: 0
            })
            .is_err()
    );
    assert_eq!(
        a.structural_eq_observed(&a, &mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        session.first_refusal().unwrap().cause,
        "original FuncTy stop"
    );
}

#[test]
fn refusal_at_final_whole_boolean_publication_cannot_return_equal_or_false() {
    let a = fixture();
    let mut different = a.clone();
    different.is_vararg = !a.is_vararg;
    for b in [a.clone(), different] {
        let (_, baseline) = run(&a, &b);
        let mut observer = Observer {
            stop: Some(baseline.events.len()),
            ..Observer::default()
        };
        {
            let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
            assert_eq!(
                a.structural_eq_observed(&b, &mut session, site()),
                Err(ObservedValueError::AdmissionRefused)
            );
        }
        assert_eq!(observer.events, baseline.events);
        assert_eq!(
            observer.events.last().unwrap().phase,
            ExecutionPhase::Publication
        );
    }
}
