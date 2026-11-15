// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
#[test]
fn every_actual_sorted_shift_first_pair_pending_and_publication_callback_can_stop() {
    let i = fixture();
    let (_, base, end) = observed(&i);
    for (at, p) in base.events[..end].iter().enumerate() {
        let mut o = Observer {
            stop: Some(at + 1),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert_eq!(
            i.trust_vc_mode_collision_errors_observed(&mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(s.first_refusal().unwrap().progress, *p);
        assert_eq!(&o.events[..=at], &base.events[..=at]);
        assert!(
            o.events[at + 1..]
                .iter()
                .all(|p| p.phase == ExecutionPhase::ScratchRetirement)
        );
    }
}
#[test]
fn cumulative_original_work_and_copy_never_reset_between_whole_calls() {
    let i = fixture();
    let (_, base, _) = observed(&i);
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
        let rows = i
            .trust_vc_mode_collision_errors_observed(&mut s, site())
            .unwrap();
        retire_native_bundle_errors_observed(rows, &mut s, site()).unwrap();
        assert!(
            i.trust_vc_mode_collision_errors_observed(&mut s, site())
                .is_err()
        );
        assert_eq!(
            s.first_refusal().unwrap().cause,
            if copy { "copy" } else { "work" }
        );
    }
}
#[test]
fn interrupt_stays_sticky_after_the_external_flag_clears() {
    let i = fixture();
    let arm = Rc::new(Cell::new(true));
    let mut o = Observer {
        arm: Some(arm.clone()),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert!(
        i.trust_vc_mode_collision_errors_observed(&mut s, site())
            .is_err()
    );
    arm.set(false);
    assert!(
        i.trust_vc_mode_collision_errors_observed(&mut s, site())
            .is_err()
    );
    assert_eq!(s.first_refusal().unwrap().cause, "interrupt");
}
#[test]
fn zero_instruction_fuel_still_checks_all_collisions() {
    let i = fixture();
    let mut o = Observer::default();
    let mut s = ObservedSession::new(
        InterpretOptions {
            fuel: 0,
            ..InterpretOptions::default()
        },
        &mut o,
    );
    let rows = i
        .trust_vc_mode_collision_errors_observed(&mut s, site())
        .unwrap();
    assert_eq!(rows, ordinary(&i));
    retire_native_bundle_errors_observed(rows, &mut s, site()).unwrap();
    assert_eq!(s.remaining_fuel(), 0);
}
#[test]
fn final_whole_result_publication_refusal_never_exposes_sorted_prefix() {
    let i = fixture();
    let (_, base, end) = observed(&i);
    assert_eq!(base.events[end - 1].phase, ExecutionPhase::Publication);
    let mut o = Observer {
        stop: Some(end),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert!(
        i.trust_vc_mode_collision_errors_observed(&mut s, site())
            .is_err()
    );
    assert_eq!(s.first_refusal().unwrap().progress, base.events[end - 1]);
}
#[test]
fn refusal_mid_actual_backward_shift_keeps_private_copy_slots_until_drain() {
    let i = fixture();
    let (_, _, end) = observed(&i);
    let mut found = false;
    for cut in 1..end {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut w = Work {
            session: &mut s,
            site: site(),
        };
        let mut st = State::default();
        let result = st.run(&i.requests, &mut w);
        if result.is_err() && st.ids.len() >= 2 && st.ids.windows(2).any(|p| p[0] == p[1]) {
            found = true;
            assert!(st.errors.is_empty());
            assert!(st.finish(result, &mut w).is_err());
            empty(&st);
            break;
        }
        drain(&mut st, &mut w);
    }
    assert!(found);
}
#[test]
fn actual_interior_first_pair_search_refuses_with_complete_ids_retained() {
    let i = fixture();
    let (_, _, end) = observed(&i);
    let mut found = false;
    for cut in 1..end {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut w = Work {
            session: &mut s,
            site: site(),
        };
        let mut st = State::default();
        let result = st.run(&i.requests, &mut w);
        if result.is_err()
            && st.ids == vec![ProofId::new(1), ProofId::new(3), ProofId::new(9)]
            && st.errors.len() == 1
            && st.pending.is_none()
        {
            found = true;
            assert!(st.finish(result, &mut w).is_err());
            empty(&st);
            break;
        }
        drain(&mut st, &mut w);
    }
    assert!(found);
}
#[test]
fn cleanup_only_copy_refusal_is_checked_before_empty_success() {
    let mut o = Observer {
        byte_cap: Some(0),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut st = State::default();
    assert!(st.finish(Ok(()), &mut w).is_err());
    empty(&st);
}
