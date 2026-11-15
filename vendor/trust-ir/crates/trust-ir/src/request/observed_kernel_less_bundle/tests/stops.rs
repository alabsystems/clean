// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
#[test]
fn every_outer_group_publication_and_stratified_inner_callback_can_stop_the_whole_result() {
    let b = bad();
    let (_, base, end) = observed(&b);
    let mut cuts = vec![1, end];
    for n in 1..65 {
        cuts.push(n * end / 65 + 1);
    }
    for (at, p) in base.events[..end].iter().enumerate() {
        if p.phase == ExecutionPhase::Publication {
            cuts.push(at + 1);
        }
    }
    cuts.sort_unstable();
    cuts.dedup();
    for cut in cuts {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert!(b.validate_kernel_less_observed(&mut s, site()).is_err());
        assert_eq!(s.first_refusal().unwrap().progress, base.events[cut - 1]);
    }
}
#[test]
fn every_actual_ready_mapping_empty_backing_and_outer_publication_fee_is_refusable() {
    for invalid in [false, true] {
        let setup = || {
            if invalid {
                State {
                    errors: vec![E::EmptyRequests],
                    ..State::default()
                }
            } else {
                State {
                    errors: Vec::with_capacity(19),
                    ..State::default()
                }
            }
        };
        let mut base = Observer::default();
        let c = base.calls.clone();
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut base);
        let mut w = Work {
            session: &mut s,
            site: site(),
        };
        let mut st = setup();
        st.ready(&mut w).unwrap();
        let end = c.get();
        drain(&mut st, &mut w);
        for cut in 1..=end {
            let mut o = Observer {
                stop: Some(cut),
                ..Observer::default()
            };
            let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
            let mut w = Work {
                session: &mut s,
                site: site(),
            };
            let mut st = setup();
            let result = st.ready(&mut w);
            assert!(result.is_err());
            drain(&mut st, &mut w);
            empty(&st);
        }
    }
}
#[test]
fn original_work_and_copy_budgets_cover_all_three_groups_and_caller_retirement() {
    let b = good();
    let (_, base, _) = observed(&b);
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
        let result = b.validate_kernel_less_observed(&mut s, site()).unwrap();
        NativeVerificationBundle::retire_kernel_less_validation_observed(result, &mut s, site())
            .unwrap();
        assert!(b.validate_kernel_less_observed(&mut s, site()).is_err());
        assert_eq!(
            s.first_refusal().unwrap().cause,
            if copy { "copy" } else { "work" }
        );
    }
}
#[test]
fn original_interrupt_is_sticky_and_zero_instruction_fuel_is_never_replenished() {
    let b = good();
    let arm = Rc::new(Cell::new(true));
    let mut o = Observer {
        arm: Some(arm.clone()),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(
        InterpretOptions {
            fuel: 0,
            ..InterpretOptions::default()
        },
        &mut o,
    );
    assert!(b.validate_kernel_less_observed(&mut s, site()).is_err());
    arm.set(false);
    assert!(b.validate_kernel_less_observed(&mut s, site()).is_err());
    assert_eq!(s.remaining_fuel(), 0);
    assert_eq!(s.first_refusal().unwrap().cause, "interrupt");
}
#[test]
fn both_inner_success_and_inner_failure_remain_owned_until_final_outer_publication() {
    for b in [good(), bad()] {
        let (_, base, end) = observed(&b);
        assert_eq!(base.events[end - 1].phase, ExecutionPhase::Publication);
        let mut o = Observer {
            stop: Some(end),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert_eq!(
            b.validate_kernel_less_observed(&mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(s.first_refusal().unwrap().progress, base.events[end - 1]);
    }
}
#[test]
fn cleanup_only_refusal_never_turns_complete_inner_result_into_healthy_outer_success() {
    let mut o = Observer {
        retirement_stop: true,
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut st = State::default();
    assert_eq!(
        st.finish(Ok(()), &mut w),
        Err(ObservedValueError::AdmissionRefused)
    );
    empty(&st);
}
