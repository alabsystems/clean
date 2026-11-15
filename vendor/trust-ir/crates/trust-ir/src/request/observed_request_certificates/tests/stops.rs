// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn every_actual_selector_build_raw_match_lineage_child_batch_and_publication_can_stop() {
    let b = bad();
    let (_, base, end) = observed(&b, 0);
    for (at, p) in base.events[..end].iter().enumerate() {
        let mut o = Observer {
            stop: Some(at + 1),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert_eq!(
            b.request_certificate_errors_observed(0, &mut s, site()),
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
fn one_original_work_and_copy_budget_covers_all_selector_and_request_children() {
    let b = bad();
    let (_, base, _) = observed(&b, 0);
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
            .request_certificate_errors_observed(0, &mut s, site())
            .unwrap();
        retire_native_bundle_errors_observed(rows, &mut s, site()).unwrap();
        assert!(
            b.request_certificate_errors_observed(0, &mut s, site())
                .is_err()
        );
        assert_eq!(
            s.first_refusal().unwrap().cause,
            if copy { "copy" } else { "work" }
        );
    }
}
#[test]
fn original_interrupt_stays_sticky_across_actual_indexed_calls() {
    let b = bad();
    let arm = Rc::new(Cell::new(true));
    let mut o = Observer {
        arm: Some(arm.clone()),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert!(
        b.request_certificate_errors_observed(0, &mut s, site())
            .is_err()
    );
    arm.set(false);
    assert!(
        b.request_certificate_errors_observed(1, &mut s, site())
            .is_err()
    );
    assert_eq!(s.first_refusal().unwrap().cause, "interrupt");
}
#[test]
fn zero_instruction_fuel_never_bypasses_full_certificate_data_checks() {
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
        .request_certificate_errors_observed(0, &mut s, site())
        .unwrap();
    assert_eq!(rows, ordinary(&b, 0));
    retire_native_bundle_errors_observed(rows, &mut s, site()).unwrap();
    assert_eq!(s.remaining_fuel(), 0);
}
#[test]
fn final_whole_output_publication_refusal_never_exposes_an_error_prefix() {
    let b = bad();
    let (_, base, end) = observed(&b, 0);
    assert_eq!(base.events[end - 1].phase, ExecutionPhase::Publication);
    let mut o = Observer {
        stop: Some(end),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert!(
        b.request_certificate_errors_observed(0, &mut s, site())
            .is_err()
    );
    assert_eq!(s.first_refusal().unwrap().progress, base.events[end - 1]);
}
#[test]
fn actual_whole_owned_module_selector_publication_can_refuse_before_parent_capture() {
    let b = fixture();
    let (_, base, end) = observed(&b, 0);
    let cut = base.events[..end]
        .iter()
        .position(|p| {
            p.phase == ExecutionPhase::Publication
                && p.copy_bytes == size_of::<Option<ProofCertificateRef>>()
        })
        .unwrap()
        + 1;
    let mut o = Observer {
        stop: Some(cut),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert!(
        b.request_certificate_errors_observed(0, &mut s, site())
            .is_err()
    );
    assert_eq!(s.first_refusal().unwrap().progress, base.events[cut - 1]);
    assert!(
        o.events[cut..]
            .iter()
            .all(|p| p.phase == ExecutionPhase::ScratchRetirement)
    );
}
#[test]
fn actual_late_raw_pair_comparison_can_refuse_without_false_missing_answer() {
    let a = ProofCertificateRef {
        obligation: ProofId::new(0),
        prover: "a".repeat(2048) + "x",
        evidence_digest: ProofDigest::sha256([1; 32]),
    };
    let mut b = a.clone();
    b.prover = "a".repeat(2048) + "y";
    let mut base = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut base);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    assert!(!w.pair_equal(&a, &b).unwrap());
    drop(w);
    drop(s);
    let hits: Vec<_> = base
        .events
        .iter()
        .enumerate()
        .filter(|(_, p)| p.work == 2048 && p.copy_bytes == 0)
        .map(|(at, _)| at + 1)
        .collect();
    assert_eq!(hits.len(), 2);
    let mut o = Observer {
        stop: Some(hits[1]),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    assert_eq!(
        w.pair_equal(&a, &b),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        w.session.first_refusal().unwrap().progress,
        base.events[hits[1] - 1]
    );
}
#[test]
fn cleanup_only_refusal_is_checked_before_empty_healthy_result() {
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
