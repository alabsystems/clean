// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn every_actual_raw_equality_multiplicity_counter_error_and_publication_can_stop() {
    let (r, e) = bad();
    let (_, base, end) = observed(&r, &e);
    for (i, expected) in base.events[..end].iter().enumerate() {
        let mut o = Observer {
            stop: Some(i + 1),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert_eq!(
            e.provenance_binding_errors_observed(&r, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(s.first_refusal().unwrap().progress, *expected);
        assert_eq!(s.first_refusal().unwrap().cause, "interior");
        assert_eq!(&o.events[..=i], &base.events[..=i]);
        assert!(
            o.events[i + 1..]
                .iter()
                .all(|p| p.phase == ExecutionPhase::ScratchRetirement)
        );
    }
}
#[test]
fn original_work_and_copy_budgets_do_not_renew_between_bound_records() {
    let (r, e) = bad();
    let (_, base, _) = observed(&r, &e);
    for copy in [false, true] {
        let mut o = if copy {
            Observer {
                byte_cap: Some(base.bytes),
                ..Observer::default()
            }
        } else {
            Observer {
                work_cap: Some(base.work),
                ..Observer::default()
            }
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let rows = e
            .provenance_binding_errors_observed(&r, &mut s, site())
            .unwrap();
        retire_native_bundle_errors_observed(rows, &mut s, site()).unwrap();
        assert_eq!(
            e.provenance_binding_errors_observed(&r, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(
            s.first_refusal().unwrap().cause,
            if copy { "copy" } else { "work" }
        );
    }
}
#[test]
fn original_interrupt_is_sticky_across_verifier_solver_and_replay_work() {
    let (r, e) = bad();
    let arm = Rc::new(Cell::new(true));
    let mut o = Observer {
        arm: Some(arm.clone()),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert!(
        e.provenance_binding_errors_observed(&r, &mut s, site())
            .is_err()
    );
    arm.set(false);
    assert!(
        e.provenance_binding_errors_observed(&r, &mut s, site())
            .is_err()
    );
    assert_eq!(s.first_refusal().unwrap().cause, "interrupt");
}
#[test]
fn zero_instruction_fuel_does_not_disable_full_raw_metadata_checks() {
    let (r, e) = bad();
    let mut o = Observer::default();
    let mut s = ObservedSession::new(
        InterpretOptions {
            fuel: 0,
            ..InterpretOptions::default()
        },
        &mut o,
    );
    let rows = e
        .provenance_binding_errors_observed(&r, &mut s, site())
        .unwrap();
    assert_eq!(rows, ordinary(&r, &e));
    retire_native_bundle_errors_observed(rows, &mut s, site()).unwrap();
    assert_eq!(s.remaining_fuel(), 0);
}
#[test]
fn full_output_publication_refusal_never_publishes_a_shorter_mismatch_list() {
    let (r, e) = bad();
    let (_, base, end) = observed(&r, &e);
    let mut o = Observer {
        stop: Some(end),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(base.events[end - 1].phase, ExecutionPhase::Publication);
    assert!(
        e.provenance_binding_errors_observed(&r, &mut s, site())
            .is_err()
    );
    assert_eq!(s.first_refusal().unwrap().progress, base.events[end - 1]);
    assert!(
        o.events[end..]
            .iter()
            .all(|p| p.phase == ExecutionPhase::ScratchRetirement)
    );
}
#[test]
fn even_empty_equal_multisets_remain_observed_and_can_refuse() {
    let mut base = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut base);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    assert!(w.multiset(&[], &[]).unwrap());
    drop(w);
    drop(s);
    for (i, expected) in base.events.iter().enumerate() {
        let mut o = Observer {
            stop: Some(i + 1),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut w = Work {
            session: &mut s,
            site: site(),
        };
        assert!(w.multiset(&[], &[]).is_err());
        assert_eq!(w.session.first_refusal().unwrap().progress, *expected);
    }
}
