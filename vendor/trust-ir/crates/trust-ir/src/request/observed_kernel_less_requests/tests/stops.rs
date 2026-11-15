// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
#[test]
fn every_actual_vc_lookup_name_copy_pending_and_emit_callback_can_refuse() {
    let b = trusted();
    let (events, end) = private_vc_bound(&b);
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
        let mut st = known(&b);
        let result = st.vc(&b, vc_ref(&b), &mut w);
        assert_eq!(result, Err(ObservedValueError::AdmissionRefused));
        assert_eq!(w.session.first_refusal().unwrap().progress, events[cut - 1]);
        assert!(st.finish(result, &mut w).is_err());
        empty(&st);
        assert_eq!(&o.events[..cut], &events[..cut]);
        assert!(
            o.events[cut..]
                .iter()
                .all(|p| p.phase == ExecutionPhase::ScratchRetirement)
        );
    }
}
#[test]
fn actual_whole_request_children_and_final_collision_are_refusable_under_one_session() {
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
        assert!(
            b.request_errors_kernel_less_observed(&mut s, site())
                .is_err()
        );
        assert_eq!(s.first_refusal().unwrap().progress, base.events[cut - 1]);
    }
}
#[test]
fn one_original_cumulative_work_and_copy_limit_covers_repeated_complete_calls() {
    let b = trusted();
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
        let rows = b
            .request_errors_kernel_less_observed(&mut s, site())
            .unwrap();
        retire_native_bundle_errors_observed(rows, &mut s, site()).unwrap();
        assert!(
            b.request_errors_kernel_less_observed(&mut s, site())
                .is_err()
        );
        assert_eq!(
            s.first_refusal().unwrap().cause,
            if copy { "copy" } else { "work" }
        );
    }
}
#[test]
fn original_interrupt_remains_sticky_after_live_interrupt_is_cleared() {
    let b = fixture();
    let arm = Rc::new(Cell::new(true));
    let mut o = Observer {
        arm: Some(arm.clone()),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert!(
        b.request_errors_kernel_less_observed(&mut s, site())
            .is_err()
    );
    arm.set(false);
    assert!(
        b.request_errors_kernel_less_observed(&mut s, site())
            .is_err()
    );
    assert_eq!(s.first_refusal().unwrap().cause, "interrupt");
}
#[test]
fn zero_instruction_fuel_is_preserved_while_all_request_checks_still_run() {
    let b = bad();
    let mut o = Observer::default();
    let mut s = ObservedSession::new(
        InterpretOptions {
            fuel: 0,
            ..InterpretOptions::default()
        },
        &mut o,
    );
    let rows = b
        .request_errors_kernel_less_observed(&mut s, site())
        .unwrap();
    assert_eq!(rows, ordinary(&b));
    retire_native_bundle_errors_observed(rows, &mut s, site()).unwrap();
    assert_eq!(s.remaining_fuel(), 0);
}
#[test]
fn final_complete_result_publication_cannot_return_a_shorter_list_after_refusal() {
    let b = bad();
    let (_, base, end) = observed(&b);
    assert_eq!(base.events[end - 1].phase, ExecutionPhase::Publication);
    let mut o = Observer {
        stop: Some(end),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert!(
        b.request_errors_kernel_less_observed(&mut s, site())
            .is_err()
    );
    assert_eq!(s.first_refusal().unwrap().progress, base.events[end - 1]);
}
#[test]
fn interior_last_status_scan_late_match_and_absence_are_both_refusable() {
    let mut b = fixture();
    let target = b.module.proof_obligations[0].clone();
    let mut other = target.clone();
    other.id = ProofId::new(45);
    b.module.proof_obligations = vec![target];
    b.module.proof_obligations.extend(vec![other; 31]);
    for id in [ProofId::new(0), ProofId::new(99)] {
        let mut base = Observer::default();
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut base);
        let mut w = Work {
            session: &mut s,
            site: site(),
        };
        let answer = State::last_status(&b, id, &mut w).unwrap();
        assert_eq!(answer.is_some(), id == ProofId::new(0));
        let cuts: Vec<_> = base
            .events
            .iter()
            .enumerate()
            .filter(|(_, p)| p.copy_bytes == 2 * size_of::<ProofId>() + size_of::<bool>())
            .map(|(at, _)| at + 1)
            .collect();
        assert_eq!(cuts.len(), 32);
        let cut = cuts[20];
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut w = Work {
            session: &mut s,
            site: site(),
        };
        assert_eq!(
            State::last_status(&b, id, &mut w),
            Err(ObservedValueError::AdmissionRefused)
        );
    }
}
#[test]
fn cleanup_only_stop_cannot_publish_a_healthy_empty_result() {
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
