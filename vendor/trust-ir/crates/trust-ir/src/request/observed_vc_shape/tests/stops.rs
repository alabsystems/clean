// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn every_actual_site_sort_scan_mode_name_error_and_publication_callback_can_refuse() {
    for b in [bad(), importing()] {
        let (_, base, end) = observed(&b, 0);
        for (at, p) in base.events[..end].iter().enumerate() {
            let mut o = Observer {
                stop: Some(at + 1),
                ..Observer::default()
            };
            let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
            assert_eq!(
                b.request_vc_shape_errors_observed(0, &mut s, site()),
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
}
#[test]
fn same_original_cumulative_work_and_copy_budget_covers_both_shape_groups() {
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
            .request_vc_shape_errors_observed(0, &mut s, site())
            .unwrap();
        retire_native_bundle_errors_observed(rows, &mut s, site()).unwrap();
        assert!(
            b.request_vc_shape_errors_observed(0, &mut s, site())
                .is_err()
        );
        assert_eq!(
            s.first_refusal().unwrap().cause,
            if copy { "copy" } else { "work" }
        );
    }
}
#[test]
fn original_interrupt_cannot_be_reset_for_a_later_mode_or_index() {
    let b = bad();
    let arm = Rc::new(Cell::new(true));
    let mut o = Observer {
        arm: Some(arm.clone()),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert!(
        b.request_vc_shape_errors_observed(0, &mut s, site())
            .is_err()
    );
    arm.set(false);
    assert!(
        b.request_vc_shape_errors_observed(1, &mut s, site())
            .is_err()
    );
    assert_eq!(s.first_refusal().unwrap().cause, "interrupt");
}
#[test]
fn zero_instruction_fuel_does_not_disable_actual_mode_shape_checks() {
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
        .request_vc_shape_errors_observed(0, &mut s, site())
        .unwrap();
    assert_eq!(rows, ordinary(&b, 0));
    retire_native_bundle_errors_observed(rows, &mut s, site()).unwrap();
    assert_eq!(s.remaining_fuel(), 0);
}
#[test]
fn full_final_publication_refusal_never_exposes_site_or_shape_prefix() {
    let b = bad();
    let (_, base, end) = observed(&b, 0);
    assert_eq!(base.events[end - 1].phase, ExecutionPhase::Publication);
    let mut o = Observer {
        stop: Some(end),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert!(
        b.request_vc_shape_errors_observed(0, &mut s, site())
            .is_err()
    );
    assert_eq!(s.first_refusal().unwrap().progress, base.events[end - 1]);
}
#[test]
fn actual_late_ir_declaration_scan_refuses_before_claiming_its_site() {
    let mut b = bad();
    let target = b.module.proof_obligations[0].clone();
    let mut other = target.clone();
    other.id = ProofId::new(33);
    b.module.proof_obligations = vec![other; 31];
    b.module.proof_obligations.push(target);
    let r = vc(&mut b);
    r.obligations = vec![ProofId::new(0)];
    r.certificates.clear();
    let NativeVerificationRequest::TrustVc(request) = &b.requests[0] else {
        panic!("VC fixture");
    };
    // Isolate the actual site child: the later mode-shape check has an
    // unrelated callback with the same copy size as a declaration comparison.
    let mut base = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut base);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut st = State::default();
    st.sites(&b, request, &mut w).unwrap();
    drain(&mut st, &mut w);
    drop(w);
    drop(s);
    let hits: Vec<_> = base
        .events
        .iter()
        .enumerate()
        .filter(|(_, p)| {
            p.phase == ExecutionPhase::Validation
                && p.work == 1
                && p.copy_bytes == 2 * size_of::<ProofId>() + size_of::<bool>()
        })
        .map(|(at, _)| at + 1)
        .collect();
    assert_eq!(hits.len(), 32);
    let mut o = Observer {
        stop: Some(hits[20]),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut st = State::default();
    let result = st.sites(&b, request, &mut w);
    assert_eq!(result, Err(ObservedValueError::AdmissionRefused));
    assert_eq!(
        w.session.first_refusal().unwrap().progress,
        base.events[hits[20] - 1]
    );
    assert!(st.errors.is_empty());
    assert_eq!(
        st.finish(result, &mut w),
        Err(ObservedValueError::AdmissionRefused)
    );
    empty(&st);
}
#[test]
fn skipped_other_family_still_has_refusable_whole_empty_publication() {
    let b = fixture();
    let (rows, base, end) = observed(&b, 1);
    assert!(rows.is_empty());
    let mut o = Observer {
        stop: Some(end),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert!(
        b.request_vc_shape_errors_observed(1, &mut s, site())
            .is_err()
    );
    assert_eq!(s.first_refusal().unwrap().progress, base.events[end - 1]);
}
#[test]
fn cleanup_only_refusal_is_checked_before_any_healthy_empty_result() {
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
