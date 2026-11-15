// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn every_actual_id_compare_shift_reserve_retirement_and_publication_can_stop() {
    let (r, e) = fixture();
    let (_, base, end) = observed(&r, &e);
    for (i, expected) in base.events[..end].iter().enumerate() {
        let mut o = Observer {
            stop: Some(i + 1),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert_eq!(
            e.obligation_errors_observed(&r, &mut s, site()),
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
fn cumulative_original_work_and_copy_caps_do_not_renew() {
    let (r, e) = fixture();
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
        let rows = e.obligation_errors_observed(&r, &mut s, site()).unwrap();
        retire_native_bundle_errors_observed(rows, &mut s, site()).unwrap();
        assert_eq!(
            e.obligation_errors_observed(&r, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(
            s.first_refusal().unwrap().cause,
            if copy { "copy" } else { "work" }
        );
    }
}
#[test]
fn an_original_armed_interrupt_remains_sticky_after_it_is_disarmed() {
    let (r, e) = fixture();
    let arm = Rc::new(Cell::new(true));
    let mut o = Observer {
        arm: Some(arm.clone()),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(
        e.obligation_errors_observed(&r, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    arm.set(false);
    assert_eq!(
        e.obligation_errors_observed(&r, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(s.first_refusal().unwrap().cause, "interrupt");
}
#[test]
fn zero_instruction_fuel_is_not_spent_for_either_set_or_diagnostic_pass() {
    let (r, e) = fixture();
    let mut o = Observer::default();
    let mut s = ObservedSession::new(
        InterpretOptions {
            fuel: 0,
            ..InterpretOptions::default()
        },
        &mut o,
    );
    let rows = e.obligation_errors_observed(&r, &mut s, site()).unwrap();
    retire_native_bundle_errors_observed(rows, &mut s, site()).unwrap();
    assert_eq!(s.remaining_fuel(), 0);
}
#[test]
fn first_copy_vector_growth_is_refused_before_allocation() {
    let mut baseline = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut rows = Vec::new();
    w.insert_id(&mut rows, ProofId::new(1)).unwrap();
    w.copy_rows(rows);
    drop(w);
    drop(s);
    // In an empty ID vector the first one-ID image is the actual reserve
    // admission; the preceding get/empty and reserve polls allocate nothing.
    let growth = baseline
        .events
        .iter()
        .position(|p| p.work == 1 && p.copy_bytes == size_of::<ProofId>())
        .unwrap()
        + 1;
    let mut o = Observer {
        stop: Some(growth),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut rows = Vec::new();
    assert_eq!(
        w.insert_id(&mut rows, ProofId::new(1)),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(rows.capacity(), 0);
    assert_eq!(
        w.session.first_refusal().unwrap().progress,
        baseline.events[growth - 1]
    );
    w.copy_rows(rows);
}
#[test]
fn final_publication_refusal_never_returns_a_smaller_set_difference() {
    let (r, e) = fixture();
    let (_, base, end) = observed(&r, &e);
    let mut o = Observer {
        stop: Some(end),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(base.events[end - 1].phase, ExecutionPhase::Publication);
    assert_eq!(
        e.obligation_errors_observed(&r, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(s.first_refusal().unwrap().progress, base.events[end - 1]);
    assert!(
        o.events[end..]
            .iter()
            .all(|p| p.phase == ExecutionPhase::ScratchRetirement)
    );
}
