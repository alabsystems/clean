// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    clippy::field_reassign_with_default,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn every_dialect_callback_preserves_typed_nonsemantic_refusal() {
    let value = DialectTy::new("namespace_9", "value_8", 1);
    let (_, baseline) = dialect(&value);
    for cut in 1..=baseline.events.len() {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert_eq!(
            value.validate_observed(&mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert!(s.first_refusal().is_some());
        drop(s);
        assert_eq!(o.events, baseline.events[..cut]);
    }
}
#[test]
fn every_runtime_segment_delimiter_callback_preserves_typed_refusal() {
    let value = HandleTy::new("Name_9", "first::second_9::Third");
    let (_, baseline) = handle(&value);
    for cut in 1..=baseline.events.len() {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert_eq!(
            value.validate_observed(&mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        drop(s);
        assert_eq!(o.events, baseline.events[..cut]);
    }
}
#[test]
fn semantic_error_routes_never_substitute_a_validation_error_for_a_stop() {
    for value in [
        DialectTy::new("!", "bad", 0),
        DialectTy::new("ns", "!", 0),
        DialectTy::new("ns", "name", 0),
    ] {
        let (_, baseline) = dialect(&value);
        for cut in 1..=baseline.events.len() {
            let mut o = Observer {
                stop: Some(cut),
                ..Observer::default()
            };
            let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
            assert_eq!(
                value.validate_observed(&mut s, site()),
                Err(ObservedValueError::AdmissionRefused)
            );
        }
    }
    for value in [HandleTy::new("!", ""), HandleTy::new("Name", "first:::bad")] {
        let (_, baseline) = handle(&value);
        for cut in 1..=baseline.events.len() {
            let mut o = Observer {
                stop: Some(cut),
                ..Observer::default()
            };
            let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
            assert_eq!(
                value.validate_observed(&mut s, site()),
                Err(ObservedValueError::AdmissionRefused)
            );
        }
    }
}
#[test]
fn dialect_and_handle_calls_share_one_original_cumulative_account() {
    let d = DialectTy::new("ns", "name", 1);
    let h = HandleTy::new("Name", "first::second");
    let (_, do_) = dialect(&d);
    let (_, ho) = handle(&h);
    for copy in [false, true] {
        let mut o = Observer::default();
        if copy {
            o.byte_cap = Some(do_.bytes + ho.bytes + 1)
        } else {
            o.work_cap = Some(do_.work + ho.work + 1)
        }
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert_eq!(d.validate_observed(&mut s, site()), Ok(Ok(())));
        assert_eq!(h.validate_observed(&mut s, site()), Ok(Ok(())));
        assert_eq!(
            d.validate_observed(&mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert!(s.first_refusal().is_some());
    }
}
#[test]
fn a_late_runtime_byte_classification_remains_interruptible() {
    let value = HandleTy::new("Name", format!("{}::tail", "a".repeat(2000)));
    let (_, baseline) = handle(&value);
    let cut = baseline
        .events
        .iter()
        .enumerate()
        .filter(|(_, e)| {
            e.phase == ExecutionPhase::Validation
                && e.work == 4
                && e.copy_bytes == size_of::<bool>()
        })
        .nth(1000)
        .unwrap()
        .0
        + 1;
    let mut o = Observer {
        stop: Some(cut),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(
        value.validate_observed(&mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    drop(s);
    assert_eq!(o.events, baseline.events[..cut]);
}
#[test]
fn final_semantic_result_publication_must_be_admitted() {
    for value in [
        DialectTy::new("ns", "name", 1),
        DialectTy::new("ns", "name", 0),
    ] {
        let (_, baseline) = dialect(&value);
        assert_eq!(
            baseline.events.last().unwrap().phase,
            ExecutionPhase::Publication
        );
        let mut o = Observer {
            stop: Some(baseline.events.len()),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert_eq!(
            value.validate_observed(&mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
    }
}
#[test]
fn exact_original_site_and_zero_fuel_are_preserved_for_both_types() {
    let mut options = InterpretOptions::default();
    options.fuel = 0;
    let mut o = Observer::default();
    let mut s = ObservedSession::new(options, &mut o);
    assert_eq!(
        DialectTy::new("ns", "name", 1).validate_observed(&mut s, site()),
        Ok(Ok(()))
    );
    assert_eq!(
        HandleTy::new("Name", "first::second").validate_observed(&mut s, site()),
        Ok(Ok(()))
    );
    assert_eq!(s.remaining_fuel(), 0);
    drop(s);
    assert!(o.events.iter().all(|e| e.site == site()));
}
#[test]
fn a_latched_first_cause_is_not_replaced_by_later_semantic_failure() {
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
        DialectTy::new("!", "!", 0).validate_observed(&mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        HandleTy::new("!", "").validate_observed(&mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(s.first_refusal().unwrap().cause, "original nominal stop");
    drop(s);
    assert_eq!(o.events.len(), 1);
}
