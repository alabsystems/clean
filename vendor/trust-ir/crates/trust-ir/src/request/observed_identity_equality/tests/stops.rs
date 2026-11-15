// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
#[test]
fn every_actual_tool_field_read_and_true_or_false_publication_can_stop() {
    let a = tool();
    let mut b = a.clone();
    b.name.push('x');
    for pair in [(&a, &a), (&a, &b)] {
        let (_, base) = tool_run(pair.0, pair.1);
        for (i, expected) in base.events.iter().enumerate() {
            let mut o = Observer {
                stop: Some(i + 1),
                ..Observer::default()
            };
            let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
            assert_eq!(
                pair.0.structural_eq_observed(pair.1, &mut s, site()),
                Err(ObservedValueError::AdmissionRefused)
            );
            assert_eq!(s.first_refusal().unwrap().progress, *expected);
            assert_eq!(s.first_refusal().unwrap().cause, "interior");
            assert_eq!(&o.events[..], &base.events[..=i]);
        }
    }
}
#[test]
fn every_actual_replay_field_read_and_true_or_false_publication_can_stop() {
    let a = replay();
    let mut b = a.clone();
    b.invocation.push('x');
    for b in [&a, &b] {
        let (_, base) = replay_run(&a, b);
        for (i, expected) in base.events.iter().enumerate() {
            let mut o = Observer {
                stop: Some(i + 1),
                ..Observer::default()
            };
            let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
            assert_eq!(
                a.structural_eq_observed(b, &mut s, site()),
                Err(ObservedValueError::AdmissionRefused)
            );
            assert_eq!(s.first_refusal().unwrap().progress, *expected);
            assert_eq!(&o.events[..], &base.events[..=i]);
        }
    }
}
#[test]
fn original_cumulative_work_and_copy_cannot_renew_after_equality() {
    let a = tool();
    let (_, base) = tool_run(&a, &a);
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
        assert!(a.structural_eq_observed(&a, &mut s, site()).unwrap());
        assert_eq!(
            a.structural_eq_observed(&a, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(
            s.first_refusal().unwrap().cause,
            if copy { "copy" } else { "work" }
        );
    }
}
#[test]
fn original_interrupt_cannot_be_cleared_by_another_identity_kind() {
    let a = tool();
    let p = replay();
    let arm = Rc::new(Cell::new(true));
    let mut o = Observer {
        arm: Some(arm.clone()),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert!(a.structural_eq_observed(&a, &mut s, site()).is_err());
    arm.set(false);
    assert!(p.structural_eq_observed(&p, &mut s, site()).is_err());
    assert_eq!(s.first_refusal().unwrap().cause, "interrupt");
}
#[test]
fn zero_instruction_fuel_does_not_disable_raw_structural_work() {
    let a = tool();
    let p = replay();
    let mut o = Observer::default();
    let mut s = ObservedSession::new(
        InterpretOptions {
            fuel: 0,
            ..InterpretOptions::default()
        },
        &mut o,
    );
    assert!(a.structural_eq_observed(&a, &mut s, site()).unwrap());
    assert!(p.structural_eq_observed(&p, &mut s, site()).unwrap());
    assert_eq!(s.remaining_fuel(), 0);
}
#[test]
fn a_late_window_stop_is_before_the_actual_last_byte_comparison() {
    let mut a = tool();
    a.name = "x".repeat(4096) + "a";
    let mut b = a.clone();
    b.name.pop();
    b.name.push('b');
    let (_, base) = tool_run(&a, &b);
    let cut = base
        .events
        .iter()
        .rposition(|p| p.phase == ExecutionPhase::Validation && p.work == 2 && p.copy_bytes == 0)
        .unwrap()
        + 1;
    let mut o = Observer {
        stop: Some(cut),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(
        a.structural_eq_observed(&b, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(s.first_refusal().unwrap().progress, base.events[cut - 1]);
}
