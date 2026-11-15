// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
#[test]
fn every_actual_child_batch_prefix_lookup_and_publication_callback_can_stop() {
    let b = bad();
    let (_, base, end) = observed(&b, 1);
    for (at, p) in base.events[..end].iter().enumerate() {
        let mut o = Observer {
            stop: Some(at + 1),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert_eq!(
            b.request_metadata_errors_observed(1, &mut s, site()),
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
fn one_original_cumulative_work_and_copy_budget_covers_all_metadata_children() {
    let b = bad();
    let (_, base, _) = observed(&b, 1);
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
            .request_metadata_errors_observed(1, &mut s, site())
            .unwrap();
        retire_native_bundle_errors_observed(rows, &mut s, site()).unwrap();
        assert!(
            b.request_metadata_errors_observed(1, &mut s, site())
                .is_err()
        );
        assert_eq!(
            s.first_refusal().unwrap().cause,
            if copy { "copy" } else { "work" }
        );
    }
}
#[test]
fn original_interrupt_is_sticky_across_indexed_metadata_invocations() {
    let b = bad();
    let arm = Rc::new(Cell::new(true));
    let mut o = Observer {
        arm: Some(arm.clone()),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert!(
        b.request_metadata_errors_observed(1, &mut s, site())
            .is_err()
    );
    arm.set(false);
    assert!(
        b.request_metadata_errors_observed(0, &mut s, site())
            .is_err()
    );
    assert_eq!(s.first_refusal().unwrap().cause, "interrupt");
}
#[test]
fn zero_instruction_fuel_does_not_bypass_actual_prefix_or_replay_context() {
    let b = bad();
    let (expected, _, _) = observed(&b, 1);
    let mut o = Observer::default();
    let mut s = ObservedSession::new(
        InterpretOptions {
            fuel: 0,
            ..InterpretOptions::default()
        },
        &mut o,
    );
    let rows = b
        .request_metadata_errors_observed(1, &mut s, site())
        .unwrap();
    assert_eq!(rows, expected);
    retire_native_bundle_errors_observed(rows, &mut s, site()).unwrap();
    assert_eq!(s.remaining_fuel(), 0);
}
#[test]
fn final_whole_prefix_publication_refusal_returns_no_shorter_error_list() {
    let b = bad();
    let (_, base, end) = observed(&b, 1);
    let mut o = Observer {
        stop: Some(end),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(base.events[end - 1].phase, ExecutionPhase::Publication);
    assert!(
        b.request_metadata_errors_observed(1, &mut s, site())
            .is_err()
    );
    assert_eq!(s.first_refusal().unwrap().progress, base.events[end - 1]);
}
#[test]
fn real_known_module_obligation_scan_refuses_inside_a_late_match() {
    let mut b = fixture();
    let target = b.module.proof_obligations[1].clone();
    let mut prior = b.module.proof_obligations[0].clone();
    prior.id = ProofId::new(33);
    b.module.proof_obligations = vec![prior; 31];
    b.module.proof_obligations.push(target);
    let (_, base, end) = observed(&b, 1);
    let hits: Vec<_> = base.events[..end]
        .iter()
        .enumerate()
        .filter(|(_, p)| {
            p.phase == ExecutionPhase::Validation
                && p.work == 1
                && p.copy_bytes == 2 * size_of::<ProofId>() + size_of::<bool>()
        })
        .map(|(at, _)| at + 1)
        .collect();
    assert!(hits.len() >= 32);
    let cut = hits[20];
    let mut o = Observer {
        stop: Some(cut),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert!(
        b.request_metadata_errors_observed(1, &mut s, site())
            .is_err()
    );
    assert_eq!(s.first_refusal().unwrap().progress, base.events[cut - 1]);
}
#[test]
fn empty_success_still_has_a_refusable_actual_final_publication() {
    let b = fixture();
    let (rows, base, end) = observed(&b, 1);
    assert!(rows.is_empty());
    let mut o = Observer {
        stop: Some(end),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert!(
        b.request_metadata_errors_observed(1, &mut s, site())
            .is_err()
    );
    assert_eq!(s.first_refusal().unwrap().progress, base.events[end - 1]);
}
#[test]
fn cleanup_only_refusal_is_checked_before_healthy_empty_output() {
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
