// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    clippy::field_reassign_with_default,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn every_actual_nested_value_iterator_reserve_retirement_and_boolean_publication_refuses() {
    let (v, t) = branching();
    let (_, baseline, end) = predicate(&v, &t, 64);
    for cut in 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert_eq!(
            v.value_matches_ty_observed(&t, 64, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(
            s.first_refusal().unwrap().cause,
            "original constant-value stop"
        );
        drop(s);
        assert_eq!(&o.events[..cut], &baseline.events[..cut]);
        assert!(
            o.events[cut..]
                .iter()
                .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
        );
    }
}
#[test]
fn every_actual_unicode_boundary_growth_decimal_copy_and_label_publication_refuses() {
    let v = symbol();
    let (_, baseline, end) = label(&v);
    for cut in 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert_eq!(
            v.shape_label_observed(&mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(
            s.first_refusal().unwrap().cause,
            "original constant-value stop"
        );
        drop(s);
        assert_eq!(&o.events[..cut], &baseline.events[..cut]);
        assert!(
            o.events[cut..]
                .iter()
                .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
        );
    }
}
#[test]
fn both_original_cumulative_work_and_copy_caps_span_repeated_predicate_and_label_calls() {
    for label_case in [false, true] {
        let (v, t) = branching();
        let v = if label_case { symbol() } else { v };
        let baseline = if label_case {
            let (_, o, e) = label(&v);
            (o, e)
        } else {
            let (_, o, e) = predicate(&v, &t, 64);
            (o, e)
        };
        for copy in [false, true] {
            let cap = baseline.0.events[..baseline.1]
                .iter()
                .map(|e| if copy { e.copy_bytes } else { e.work })
                .sum();
            let mut o = Observer::default();
            if copy {
                o.byte_cap = Some(cap)
            } else {
                o.work_cap = Some(cap)
            }
            let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
            if label_case {
                let held = v.shape_label_observed(&mut s, site()).unwrap();
                assert_eq!(
                    v.shape_label_observed(&mut s, site()),
                    Err(ObservedValueError::AdmissionRefused)
                );
                Work {
                    session: &mut s,
                    site: site(),
                }
                .flat(held);
            } else {
                assert!(v.value_matches_ty_observed(&t, 64, &mut s, site()).unwrap());
                assert_eq!(
                    v.value_matches_ty_observed(&t, 64, &mut s, site()),
                    Err(ObservedValueError::AdmissionRefused)
                );
            }
            assert_eq!(
                s.first_refusal().unwrap().cause,
                if copy { "copy" } else { "work" }
            );
        }
    }
}
#[test]
fn zero_instruction_fuel_and_preexisting_stop_preserve_original_site_and_cause() {
    let (v, t) = branching();
    let mut o = Observer::default();
    let mut options = InterpretOptions::default();
    options.fuel = 0;
    let mut s = ObservedSession::new(options, &mut o);
    assert!(v.value_matches_ty_observed(&t, 64, &mut s, site()).unwrap());
    let text = symbol().shape_label_observed(&mut s, site()).unwrap();
    Work {
        session: &mut s,
        site: site(),
    }
    .flat(text);
    assert_eq!(s.remaining_fuel(), 0);
    drop(s);
    let mut o = Observer {
        stop: Some(1),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert!(
        s.admit(ExecutionProgress {
            phase: ExecutionPhase::Validation,
            site: site(),
            work: 1,
            copy_bytes: 0
        })
        .is_err()
    );
    assert_eq!(
        v.value_matches_ty_observed(&t, 64, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        symbol().shape_label_observed(&mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        s.first_refusal().unwrap().cause,
        "original constant-value stop"
    );
}
