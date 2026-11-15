// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    clippy::field_reassign_with_default,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn every_actual_schema_citation_predicate_and_publication_callback_is_refusable() {
    let preds = [Pred::Interval { lo: -7, hi: 13 }];
    let table = PredTable::new(&preds, &[]);
    let f = formula(
        OwnedFormulaSchema::Pred.name(),
        "pred.0",
        Some("(and (<= -7 self) (<= self 13))"),
    );
    let (_, baseline) = run(&f, &table);
    for cut in 1..=baseline.events.len() {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert_eq!(
            f.states_two_texts_observed(&table, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert!(s.first_refusal().is_some());
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
fn malformed_and_opaque_short_paths_do_not_turn_refusal_into_a_boolean() {
    let table = PredTable::new(&[], &[]);
    for f in [
        formula("opaque", "raw", Some("tail")),
        formula(OwnedFormulaSchema::Pred.name(), "pred.01", Some("true")),
        formula(OwnedFormulaSchema::Smtlib2.name(), "false", None),
    ] {
        let (_, baseline) = run(&f, &table);
        for cut in 1..=baseline.events.len() {
            let mut o = Observer {
                stop: Some(cut),
                ..Observer::default()
            };
            let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
            assert_eq!(
                f.states_two_texts_observed(&table, &mut s, site()),
                Err(ObservedValueError::AdmissionRefused)
            );
        }
    }
}
#[test]
fn actual_long_smtlib_comparison_can_stop_in_a_middle_byte_chunk() {
    let table = PredTable::new(&[], &[]);
    let text = "λ\0尾".repeat(1000);
    let f = formula(OwnedFormulaSchema::Smtlib2.name(), &text, Some(&text));
    let (_, baseline) = run(&f, &table);
    let cut = baseline
        .events
        .iter()
        .enumerate()
        .filter(|(_, e)| e.work == 1024 && e.copy_bytes == 0)
        .nth(1)
        .unwrap()
        .0
        + 1;
    let mut o = Observer {
        stop: Some(cut),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(
        f.states_two_texts_observed(&table, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    drop(s);
    assert_eq!(o.events, baseline.events[..cut]);
}
#[test]
fn two_formula_calls_share_the_original_cumulative_work_and_copy_caps() {
    let table = PredTable::new(&[], &[]);
    let f = formula(OwnedFormulaSchema::Smtlib2.name(), "same", Some("same"));
    let (_, baseline) = run(&f, &table);
    for copy in [false, true] {
        let mut o = Observer::default();
        if copy {
            o.byte_cap = Some(baseline.bytes + 1)
        } else {
            o.work_cap = Some(baseline.work + 1)
        }
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert_eq!(
            f.states_two_texts_observed(&table, &mut s, site()),
            Ok(false)
        );
        assert_eq!(
            f.states_two_texts_observed(&table, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert!(s.first_refusal().is_some());
    }
}
#[test]
fn outer_publication_refusal_is_distinct_from_completed_predicate_child() {
    let preds = [Pred::Top];
    let table = PredTable::new(&preds, &[]);
    let f = formula(OwnedFormulaSchema::Pred.name(), "pred.0", Some("true"));
    let (_, baseline) = run(&f, &table);
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
        f.states_two_texts_observed(&table, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    drop(s);
    assert_eq!(
        o.events
            .iter()
            .filter(|e| e.phase == ExecutionPhase::Publication)
            .count(),
        2
    );
}
#[test]
fn original_site_zero_fuel_and_first_cause_are_never_replaced() {
    let table = PredTable::new(&[], &[]);
    let f = formula("opaque", "", Some(""));
    let mut options = InterpretOptions::default();
    options.fuel = 0;
    let mut o = Observer::default();
    let mut s = ObservedSession::new(options, &mut o);
    assert_eq!(
        f.states_two_texts_observed(&table, &mut s, site()),
        Ok(false)
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
        f.states_two_texts_observed(&table, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(s.first_refusal().unwrap().cause, "original formula stop");
    drop(s);
    assert_eq!(o.events.len(), 1);
}
#[test]
fn citation_parser_admits_actual_digits_and_refuses_before_later_digits() {
    let table = PredTable::new(&[], &[]);
    let f = formula(
        OwnedFormulaSchema::Pred.name(),
        "pred.4294967295",
        Some("true"),
    );
    let (_, baseline) = run(&f, &table);
    let cut = baseline
        .events
        .iter()
        .enumerate()
        .filter(|(_, e)| e.work == 5 && e.copy_bytes == size_of::<u32>() + size_of::<Option<u32>>())
        .nth(4)
        .unwrap()
        .0
        + 1;
    let mut o = Observer {
        stop: Some(cut),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(
        f.states_two_texts_observed(&table, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    drop(s);
    assert_eq!(o.events, baseline.events[..cut]);
}
