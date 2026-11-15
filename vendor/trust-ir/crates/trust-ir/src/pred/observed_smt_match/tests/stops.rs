// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    clippy::field_reassign_with_default,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn every_actual_success_callback_refuses_without_a_boolean_fallback() {
    let preds = vec![Pred::Interval { lo: -97, hi: 123 }];
    let text = PredTable::new(&preds, &[])
        .smtlib_of(PredId::new(0))
        .unwrap();
    let (_, baseline) = run(&preds, &[], 0, &text);
    for stop in 1..=baseline.events.len() {
        let mut o = Observer {
            stop: Some(stop),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert_eq!(
            PredTable::new(&preds, &[]).smtlib_matches_observed(
                PredId::new(0),
                &text,
                &mut s,
                site()
            ),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert!(s.first_refusal().is_some());
        drop(s);
        assert_eq!(&o.events[..stop], &baseline.events[..stop]);
        assert!(
            o.events[stop..]
                .iter()
                .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
        );
    }
}
#[test]
fn every_false_or_dangling_callback_remains_a_typed_stop() {
    for (preds, expected) in [
        (vec![Pred::NonZero], "false"),
        (vec![Pred::Conj(vec![PredId::new(8)])], "(and true)"),
    ] {
        let (answer, baseline) = run(&preds, &[], 0, expected);
        assert!(!answer);
        for stop in 1..=baseline.events.len() {
            let mut o = Observer {
                stop: Some(stop),
                ..Observer::default()
            };
            let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
            assert_eq!(
                PredTable::new(&preds, &[]).smtlib_matches_observed(
                    PredId::new(0),
                    expected,
                    &mut s,
                    site()
                ),
                Err(ObservedValueError::AdmissionRefused)
            );
            assert!(s.first_refusal().is_some());
        }
    }
}
#[test]
fn two_real_calls_share_cumulative_work_and_copy_admission() {
    let preds = vec![Pred::Interval { lo: -3, hi: 8 }];
    let text = PredTable::new(&preds, &[])
        .smtlib_of(PredId::new(0))
        .unwrap();
    let (_, baseline) = run(&preds, &[], 0, &text);
    for copy in [false, true] {
        let mut o = Observer::default();
        if copy {
            o.byte_cap = Some(baseline.bytes + 1);
        } else {
            o.work_cap = Some(baseline.work + 1);
        }
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let table = PredTable::new(&preds, &[]);
        assert_eq!(
            table.smtlib_matches_observed(PredId::new(0), &text, &mut s, site()),
            Ok(true)
        );
        assert_eq!(
            table.smtlib_matches_observed(PredId::new(0), &text, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert!(s.first_refusal().is_some());
    }
}
#[test]
fn original_site_zero_fuel_and_already_latched_stop_are_preserved() {
    let mut o = Observer::default();
    let mut options = InterpretOptions::default();
    options.fuel = 0;
    let mut s = ObservedSession::new(options, &mut o);
    assert_eq!(
        PredTable::new(&[Pred::Top], &[]).smtlib_matches_observed(
            PredId::new(0),
            "true",
            &mut s,
            site()
        ),
        Ok(true)
    );
    assert_eq!(s.remaining_fuel(), 0);
    drop(s);
    assert!(o.events.iter().all(|e| e.site == site()));
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
        PredTable::new(&[Pred::Top], &[]).smtlib_matches_observed(
            PredId::new(0),
            "true",
            &mut s,
            site()
        ),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(s.first_refusal().unwrap().cause, "original predicate stop");
}
#[test]
fn final_outer_publication_refusal_cannot_return_an_answer() {
    for expected in ["true", "false"] {
        let (_, baseline) = run(&[Pred::Top], &[], 0, expected);
        assert_eq!(
            baseline.events.last().unwrap().copy_bytes,
            size_of::<bool>()
        );
        let mut o = Observer {
            stop: Some(baseline.events.len()),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert_eq!(
            PredTable::new(&[Pred::Top], &[]).smtlib_matches_observed(
                PredId::new(0),
                expected,
                &mut s,
                site()
            ),
            Err(ObservedValueError::AdmissionRefused)
        );
    }
}
#[test]
fn actual_long_constant_comparison_chunk_is_interruptible() {
    let preds = mixed();
    let text = PredTable::new(&preds, &[])
        .smtlib_of(PredId::new(3))
        .unwrap();
    let (_, baseline) = run(&preds, &[], 3, &text);
    let cut = baseline
        .events
        .iter()
        .position(|e| e.phase == ExecutionPhase::Validation && e.work == 1024 && e.copy_bytes == 0)
        .unwrap()
        + 1;
    let mut o = Observer {
        stop: Some(cut),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(
        PredTable::new(&preds, &[]).smtlib_matches_observed(PredId::new(3), &text, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert!(s.first_refusal().is_some());
    drop(s);
    assert_eq!(&o.events[..cut], &baseline.events[..cut]);
    assert!(o.events.len() > cut);
    assert!(
        o.events[cut..]
            .iter()
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
}
#[test]
fn scratch_retirement_refusal_prevents_both_true_and_false_publication() {
    for expected in ["true", "false"] {
        let (_, baseline) = run(&[Pred::Top], &[], 0, expected);
        let cut = baseline
            .events
            .iter()
            .position(|e| e.phase == ExecutionPhase::ScratchRetirement)
            .unwrap();
        let mut o = Observer {
            cleanup_after: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert_eq!(
            PredTable::new(&[Pred::Top], &[]).smtlib_matches_observed(
                PredId::new(0),
                expected,
                &mut s,
                site()
            ),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert!(s.first_refusal().is_some());
        drop(s);
        assert!(
            !o.events
                .iter()
                .any(|e| e.phase == ExecutionPhase::Publication)
        );
    }
}
