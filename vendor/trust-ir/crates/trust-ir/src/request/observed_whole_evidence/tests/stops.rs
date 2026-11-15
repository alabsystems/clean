// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn every_actual_selection_digest_child_batch_retirement_and_publication_can_stop() {
    let b = minimal();
    let (_, base, end) = observed(&b);
    for (i, expected) in base.events[..end].iter().enumerate() {
        let mut o = Observer {
            stop: Some(i + 1),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert_eq!(
            b.evidence_errors_observed(&mut s, site()),
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
fn original_work_and_copy_caps_do_not_renew_between_evidence_attempts() {
    let b = minimal();
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
        let rows = b.evidence_errors_observed(&mut s, site()).unwrap();
        retire_native_bundle_errors_observed(rows, &mut s, site()).unwrap();
        assert!(b.evidence_errors_observed(&mut s, site()).is_err());
        assert_eq!(
            s.first_refusal().unwrap().cause,
            if copy { "copy" } else { "work" }
        );
    }
}
#[test]
fn original_interrupt_cannot_be_cleared_by_another_evidence_attempt() {
    let b = minimal();
    let arm = Rc::new(Cell::new(true));
    let mut o = Observer {
        arm: Some(arm.clone()),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert!(b.evidence_errors_observed(&mut s, site()).is_err());
    arm.set(false);
    assert!(b.evidence_errors_observed(&mut s, site()).is_err());
    assert_eq!(s.first_refusal().unwrap().cause, "interrupt");
}
#[test]
fn zero_instruction_fuel_remains_unchanged_across_real_request_digest_and_children() {
    let b = minimal();
    let mut o = Observer::default();
    let mut s = ObservedSession::new(
        InterpretOptions {
            fuel: 0,
            ..InterpretOptions::default()
        },
        &mut o,
    );
    let rows = b.evidence_errors_observed(&mut s, site()).unwrap();
    assert_eq!(rows, ordinary(&b));
    retire_native_bundle_errors_observed(rows, &mut s, site()).unwrap();
    assert_eq!(s.remaining_fuel(), 0);
}
#[test]
fn final_publication_refusal_never_publishes_completed_child_prefixes() {
    let b = minimal();
    let (_, base, end) = observed(&b);
    assert_eq!(base.events[end - 1].phase, ExecutionPhase::Publication);
    let mut o = Observer {
        stop: Some(end),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert!(b.evidence_errors_observed(&mut s, site()).is_err());
    assert_eq!(s.first_refusal().unwrap().progress, base.events[end - 1]);
    assert!(
        o.events[end..]
            .iter()
            .all(|p| p.phase == ExecutionPhase::ScratchRetirement)
    );
}
#[test]
fn late_request_lookup_is_actually_observed_inside_reverse_search() {
    let mut b = minimal();
    let correct = b.requests[0].clone();
    for _ in 0..40 {
        let mut r = correct.clone();
        if let NativeVerificationRequest::TrustMc(r) = &mut r {
            r.id = NativeRequestId::new(999);
        }
        b.requests.push(r);
    }
    let (_, base, end) = observed(&b);
    let cut = base.events[..end]
        .iter()
        .enumerate()
        .filter(|(_, p)| {
            p.work == 8 && p.copy_bytes == size_of::<NativeRequestId>() + size_of::<bool>()
        })
        .nth(23)
        .unwrap()
        .0
        + 1;
    let mut o = Observer {
        stop: Some(cut),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert!(b.evidence_errors_observed(&mut s, site()).is_err());
    assert_eq!(s.first_refusal().unwrap().progress, base.events[cut - 1]);
}
#[test]
fn late_duplicate_prefix_is_observed_before_whole_metadata_children() {
    let mut b = minimal();
    let current = b.evidence_bundles[0].clone();
    let mut prefix = Vec::new();
    for i in 0..30 {
        let mut e = current.clone();
        mc(&mut e).request = NativeRequestId::new(999 + i);
        prefix.push(e);
    }
    prefix.push(current);
    b.evidence_bundles = prefix;
    let mut base = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut base);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut st = State::default();
    st.run(&b, &mut w).unwrap();
    drain(&mut st, &mut w);
    drop(w);
    drop(s);
    let cut = base
        .events
        .iter()
        .rposition(|p| {
            p.phase == ExecutionPhase::Validation
                && p.work == 64
                && p.copy_bytes
                    == size_of::<NativeRequestId>() + 2 * size_of::<u8>() + size_of::<bool>()
        })
        .unwrap()
        + 1;
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
    let result = st.run(&b, &mut w);
    assert_eq!(result, Err(ObservedValueError::AdmissionRefused));
    assert_eq!(st.errors.len(), 30);
    assert!(
        st.errors
            .iter()
            .all(|e| matches!(e, E::EvidenceRequestUnknown { .. }))
    );
    assert!(st.batch.is_none() && st.pending.is_none());
    assert_eq!(
        w.session.first_refusal().unwrap().progress,
        base.events[cut - 1]
    );
    assert!(st.finish(result, &mut w).is_err());
    empty(&st);
}
#[test]
fn cleanup_only_copy_refusal_cannot_allow_a_completed_batch_to_publish() {
    let mut o = Observer {
        byte_cap: Some(0),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut st = State {
        pending: Some(E::EmptyRequests),
        errors: vec![E::EmptyRequests],
        batch: Some(vec![E::EmptyRequests].into_iter()),
        batch_capacity: 1,
    };
    assert!(st.finish(Ok(()), &mut w).is_err());
    empty(&st);
    assert_eq!(w.session.first_refusal().unwrap().cause, "copy");
}
