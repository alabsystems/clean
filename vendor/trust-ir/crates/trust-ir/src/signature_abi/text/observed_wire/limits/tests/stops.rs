// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn every_actual_identity_diagnostic_and_publication_callback_can_refuse_operationally() {
    let a = too_many_bytes();
    let (_, base, end) = run(&a, true);
    for cut in 1..=end {
        let mut o = Observer {
            record: true,
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert_eq!(
            a.canonical_text_encoding_result_observed(&mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(s.first_refusal().unwrap().progress, base.events[cut - 1]);
        drop(s);
        assert_eq!(&o.events[..cut], &base.events[..cut]);
        assert!(
            o.events[cut..]
                .iter()
                .all(|p| p.phase == ExecutionPhase::ScratchRetirement)
        );
    }
}
#[test]
fn all_changed_stages_and_inherited_real_roundtrip_cuts_remain_typed_outer_refusals() {
    let a = minimal();
    let (_, base, end) = run(&a, true);
    let mut cuts = vec![1, 2, 3, end];
    for n in 1..48 {
        cuts.push(end * n / 48 + 1);
    }
    for (at, p) in base.events[..end].iter().enumerate() {
        if matches!(
            p.phase,
            ExecutionPhase::Publication | ExecutionPhase::ScratchRetirement
        ) {
            cuts.push(at + 1);
        }
    }
    cuts.sort_unstable();
    cuts.dedup();
    for cut in cuts {
        let mut o = Observer {
            record: true,
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert_eq!(
            a.canonical_text_encoding_result_observed(&mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(s.first_refusal().unwrap().progress, base.events[cut - 1]);
        drop(s);
        assert!(
            o.events[cut..]
                .iter()
                .all(|p| p.phase == ExecutionPhase::ScratchRetirement)
        );
    }
}
#[test]
fn late_actual_feature_traversal_interrupt_does_not_become_node_limit_diagnostic() {
    let a = too_many_nodes();
    let (_, base, end) = run(&a, true);
    let cut = end / 2;
    assert!(cut > MAX_NODES / 2);
    let mut o = Observer {
        record: true,
        stop: Some(cut),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(
        a.canonical_text_encoding_result_observed(&mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(s.first_refusal().unwrap().progress, base.events[cut - 1]);
}
#[test]
fn complete_success_and_original_caller_retirement_share_one_work_and_copy_budget() {
    let a = minimal();
    let (_, base, _) = run(&a, false);
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
        let result = a
            .canonical_text_encoding_result_observed(&mut s, site())
            .unwrap();
        SignatureAbi::retire_encoding_result_observed(result, &mut s, site()).unwrap();
        assert_eq!(
            a.canonical_text_encoding_result_observed(&mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(
            s.first_refusal().unwrap().cause,
            if copy { "copy" } else { "work" }
        );
    }
}
#[test]
fn cleared_interrupt_never_renews_the_original_session_for_a_different_result() {
    let arm = Rc::new(Cell::new(true));
    let mut o = Observer {
        arm: Some(arm.clone()),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert!(
        minimal()
            .canonical_text_encoding_result_observed(&mut s, site())
            .is_err()
    );
    arm.set(false);
    assert!(
        too_many_bytes()
            .canonical_text_encoding_result_observed(&mut s, site())
            .is_err()
    );
    assert_eq!(s.first_refusal().unwrap().cause, "interrupt");
}
#[test]
fn zero_instruction_fuel_retains_real_success_and_diagnostic_checks() {
    for a in [minimal(), too_many_bytes()] {
        let mut o = Observer::default();
        let mut s = ObservedSession::new(
            InterpretOptions {
                fuel: 0,
                ..InterpretOptions::default()
            },
            &mut o,
        );
        let result = a
            .canonical_text_encoding_result_observed(&mut s, site())
            .unwrap();
        assert_eq!(result, ordinary(&a));
        SignatureAbi::retire_encoding_result_observed(result, &mut s, site()).unwrap();
        assert_eq!(s.remaining_fuel(), 0);
    }
}
#[test]
fn either_full_result_is_withheld_when_its_final_publication_refuses() {
    for a in [minimal(), too_many_bytes()] {
        let (_, base, end) = run(&a, true);
        assert_eq!(base.events[end - 1].phase, ExecutionPhase::Publication);
        let mut o = Observer {
            record: true,
            stop: Some(end),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert!(
            a.canonical_text_encoding_result_observed(&mut s, site())
                .is_err()
        );
        drop(s);
        assert!(
            o.events[end..]
                .iter()
                .all(|p| p.phase == ExecutionPhase::ScratchRetirement)
        );
    }
}
#[test]
fn cleanup_only_stop_never_returns_canonical_text_or_inner_limit_diagnostic() {
    for a in [minimal(), too_many_bytes(), escaped_limit()] {
        let mut o = Observer {
            record: true,
            stop_retirement: true,
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert_eq!(
            a.canonical_text_encoding_result_observed(&mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(s.first_refusal().unwrap().cause, "retirement");
    }
}
