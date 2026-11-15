// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
#[test]
fn every_original_source_allocation_retirement_and_publication_callback_can_stop() {
    let b = fixture();
    for rule in rules() {
        let (_, baseline, end) = observed(&b, rule);
        for (i, expected) in baseline.events[..end].iter().enumerate() {
            let mut o = Observer {
                stop: Some(i + 1),
                ..Observer::default()
            };
            let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
            assert_eq!(
                run(&b, rule, &mut s, site()),
                Err(ObservedValueError::AdmissionRefused)
            );
            assert_eq!(s.first_refusal().unwrap().progress, *expected);
            assert_eq!(s.first_refusal().unwrap().cause, "interior");
            assert_eq!(&o.events[..=i], &baseline.events[..=i]);
            assert!(
                o.events[i + 1..]
                    .iter()
                    .all(|p| p.phase == ExecutionPhase::ScratchRetirement)
            );
        }
    }
}
#[test]
fn original_work_and_copy_budgets_are_cumulative_across_both_leaves() {
    let b = fixture();
    let mut base = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut base);
    for rule in rules() {
        let rows = run(&b, rule, &mut s, site()).unwrap();
        retire_native_bundle_errors_observed(rows, &mut s, site()).unwrap();
    }
    for copy in [false, true] {
        let mut o = if copy {
            Observer {
                byte_cap: Some(base.bytes - 1),
                ..Observer::default()
            }
        } else {
            Observer {
                work_cap: Some(base.work - 1),
                ..Observer::default()
            }
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut stopped = false;
        for rule in rules() {
            match run(&b, rule, &mut s, site()) {
                Ok(rows) => {
                    if retire_native_bundle_errors_observed(rows, &mut s, site()).is_err() {
                        stopped = true;
                    }
                }
                Err(_) => stopped = true,
            }
        }
        assert!(stopped);
        assert_eq!(
            s.first_refusal().unwrap().cause,
            if copy { "copy" } else { "work" }
        );
        assert_eq!(
            run(&b, Rule::Reference, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
    }
}
#[test]
fn armed_original_interrupt_cannot_be_recaptured_or_cleared() {
    let b = fixture();
    let arm = Rc::new(Cell::new(true));
    let mut o = Observer {
        arm: Some(arm.clone()),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(
        run(&b, Rule::Reference, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    arm.set(false);
    assert_eq!(
        run(&b, Rule::Lineage, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(s.first_refusal().unwrap().cause, "interrupt");
}
#[test]
fn zero_instruction_fuel_is_not_spent_by_either_structural_leaf() {
    let b = fixture();
    let mut o = Observer::default();
    let mut s = ObservedSession::new(
        InterpretOptions {
            fuel: 0,
            ..InterpretOptions::default()
        },
        &mut o,
    );
    for rule in rules() {
        let rows = run(&b, rule, &mut s, site()).unwrap();
        retire_native_bundle_errors_observed(rows, &mut s, site()).unwrap();
    }
    assert_eq!(s.remaining_fuel(), 0);
    assert!(s.first_refusal().is_none());
}
#[test]
fn decimal_helper_preserves_full_u128_and_never_truncates_u32_block_ids() {
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    for n in [
        0,
        9,
        10,
        u128::from(u32::MAX),
        usize::MAX as u128,
        u128::MAX,
    ] {
        let mut out = String::new();
        w.decimal(n, &mut out).unwrap();
        assert_eq!(out, n.to_string());
        w.text_drop(out);
    }
}
#[test]
fn final_full_diagnostic_publication_can_be_refused_without_a_prefix() {
    let b = fixture();
    for rule in rules() {
        let (_, base, end) = observed(&b, rule);
        assert_eq!(base.events[end - 1].phase, ExecutionPhase::Publication);
        let mut o = Observer {
            stop: Some(end),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert_eq!(
            run(&b, rule, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(s.first_refusal().unwrap().progress, base.events[end - 1]);
        assert!(
            o.events[end..]
                .iter()
                .all(|p| p.phase == ExecutionPhase::ScratchRetirement)
        );
    }
}
