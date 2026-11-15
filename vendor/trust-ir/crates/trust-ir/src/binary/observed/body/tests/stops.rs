// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    clippy::field_reassign_with_default,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn every_actual_success_callback_is_terminal_with_the_exact_original_prefix_and_site() {
    let m = module();
    let base = run(&m, f());
    for cut in 1..=base.split {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert_eq!(
            call(&m, f(), &mut s),
            Err(ObservedValueError::AdmissionRefused),
            "cut{cut}"
        );
        assert_eq!(s.first_refusal().unwrap().cause, "body stop");
        assert_eq!(s.first_refusal().unwrap().progress, base.events()[cut - 1]);
        drop(s);
        assert_eq!(&o.events[..cut], &base.events()[..cut]);
        assert!(
            o.events[cut..]
                .iter()
                .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
        );
    }
}
#[test]
fn every_actual_semantic_reason_callback_withholds_the_whole_reason_and_no_prefix_escapes() {
    let m = ambiguous();
    let base = run(&m, f());
    for cut in 1..=base.split {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert_eq!(
            call(&m, f(), &mut s),
            Err(ObservedValueError::AdmissionRefused),
            "cut{cut}"
        );
        assert_eq!(s.first_refusal().unwrap().cause, "body stop");
        drop(s);
        assert_eq!(&o.events[..cut], &base.events()[..cut]);
        assert!(
            o.events[cut..]
                .iter()
                .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
        );
    }
}
#[test]
fn repeated_whole_digest_calls_share_both_original_cumulative_ledgers() {
    for m in [module(), ambiguous()] {
        let base = run(&m, f());
        for copy in [false, true] {
            let cap = total(base.events(), copy);
            let mut o = Observer {
                work_cap: (!copy).then_some(cap),
                copy_cap: copy.then_some(cap),
                ..Observer::default()
            };
            let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
            let actual = call(&m, f(), &mut s).unwrap();
            assert_eq!(actual, m.function_body_digest(f()));
            assert_eq!(
                call(&m, f(), &mut s),
                Err(ObservedValueError::AdmissionRefused)
            );
            assert_eq!(
                s.first_refusal().unwrap().cause,
                if copy { "copy" } else { "work" }
            );
            assert!(
                Module::retire_function_body_digest_result_observed(actual, &mut s, site())
                    .is_err()
            );
        }
    }
}
#[test]
fn a_prior_partial_original_debit_cannot_be_discarded_by_any_plan_or_hash_child() {
    let m = drops();
    let base = run(&m, f());
    for copy in [false, true] {
        let cap = total(base.events(), copy);
        let mut o = Observer {
            work_cap: (!copy).then_some(cap),
            copy_cap: copy.then_some(cap),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        s.admit(ExecutionProgress {
            phase: ExecutionPhase::Validation,
            site: site(),
            work: usize::from(!copy),
            copy_bytes: usize::from(copy),
        })
        .unwrap();
        assert_eq!(
            call(&m, f(), &mut s),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(
            s.first_refusal().unwrap().cause,
            if copy { "copy" } else { "work" }
        );
    }
}
#[test]
fn zero_fuel_is_unchanged_and_an_earlier_original_first_cause_remains_sticky() {
    let m = module();
    let mut o = Observer::default();
    let mut opts = InterpretOptions::default();
    opts.fuel = 0;
    let mut s = ObservedSession::new(opts, &mut o);
    let actual = call(&m, f(), &mut s).unwrap();
    assert_eq!(actual, m.function_body_digest(f()));
    assert_eq!(s.remaining_fuel(), 0);
    Module::retire_function_body_digest_result_observed(actual, &mut s, site()).unwrap();
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
        call(&m, f(), &mut s),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(s.first_refusal().unwrap().cause, "body stop");
    drop(s);
    assert_eq!(o.events.len(), 1);
}
#[test]
fn one_below_the_full_success_or_reason_bill_refuses_without_weakening_the_inner_relation() {
    for m in [module(), same_glue()] {
        let base = run(&m, f());
        for copy in [false, true] {
            let cap = total(base.events(), copy) - 1;
            let mut o = Observer {
                work_cap: (!copy).then_some(cap),
                copy_cap: copy.then_some(cap),
                ..Observer::default()
            };
            let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
            assert_eq!(
                call(&m, f(), &mut s),
                Err(ObservedValueError::AdmissionRefused)
            );
            assert_eq!(
                s.first_refusal().unwrap().cause,
                if copy { "copy" } else { "work" }
            );
        }
    }
}
