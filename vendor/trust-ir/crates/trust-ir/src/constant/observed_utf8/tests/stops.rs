// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    clippy::field_reassign_with_default,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn every_actual_entry_byte_and_final_publication_cut_returns_original_stop() {
    for bytes in [
        &[][..],
        b"ascii",
        "a¢€😀".as_bytes(),
        &[0xff, b'a'],
        &[0xe2, 0x82],
    ] {
        let (_, baseline) = run(bytes);
        for cut in 1..=baseline.calls {
            let mut o = Meter {
                stop: Some(cut),
                ..Meter::default()
            };
            let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
            assert_eq!(
                utf8_is_valid_observed(bytes, &mut s, site()),
                Err(ObservedValueError::AdmissionRefused)
            );
            assert_eq!(s.first_refusal().unwrap().cause, "original utf8 refusal");
            assert_eq!(
                utf8_is_valid_observed(b"later", &mut s, site()),
                Err(ObservedValueError::AdmissionRefused)
            );
            drop(s);
            assert_eq!(o.calls, cut);
        }
    }
}
#[test]
fn both_original_cumulative_work_and_copy_caps_apply_without_regrant() {
    let bytes = "a¢€😀".as_bytes();
    let (_, baseline) = run(bytes);
    for mut o in [
        Meter {
            work_cap: Some(baseline.work),
            ..Meter::default()
        },
        Meter {
            copy_cap: Some(baseline.copy),
            ..Meter::default()
        },
    ] {
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert!(utf8_is_valid_observed(bytes, &mut s, site()).unwrap());
        assert_eq!(
            utf8_is_valid_observed(bytes, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(s.first_refusal().unwrap().cause, "original utf8 refusal");
    }
}
#[test]
fn zero_instruction_fuel_is_preserved_and_existing_cause_never_replaced() {
    let mut o = Meter::default();
    let mut options = InterpretOptions::default();
    options.fuel = 0;
    let mut s = ObservedSession::new(options, &mut o);
    assert!(utf8_is_valid_observed(b"valid", &mut s, site()).unwrap());
    assert_eq!(s.remaining_fuel(), 0);
    drop(s);
    let mut o = Meter {
        stop: Some(1),
        ..Meter::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert!(
        s.admit(ExecutionProgress {
            phase: ExecutionPhase::Validation,
            site: site(),
            work: 0,
            copy_bytes: 0
        })
        .is_err()
    );
    assert_eq!(
        utf8_is_valid_observed(b"valid", &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(s.first_refusal().unwrap().cause, "original utf8 refusal");
}
#[test]
fn borrowed_complete_source_survives_success_and_all_refusals_unchanged() {
    let bytes = "a¢€😀".repeat(1024).into_bytes();
    let original = bytes.clone();
    let pointer = bytes.as_ptr();
    assert!(run(&bytes).0);
    for cut in [1, 2, 40, bytes.len() + 2] {
        let mut o = Meter {
            stop: Some(cut),
            ..Meter::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert!(utf8_is_valid_observed(&bytes, &mut s, site()).is_err());
        assert_eq!(bytes, original);
        assert_eq!(bytes.as_ptr(), pointer);
    }
}
