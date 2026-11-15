// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn actual_whole_owned_module_selector_is_held_before_first_parent_reserve() {
    let b = fixture();
    let expected = b.module.proof_certificates[0].lineage_ref();
    let mut base = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut base);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut st = State::default();
    st.setup(&b, &b.requests[0], &mut w).unwrap();
    drain(&mut st, &mut w);
    drop(w);
    drop(s);
    let cut = base
        .events
        .iter()
        .position(|p| {
            p.phase == ExecutionPhase::Publication
                && p.copy_bytes == size_of::<Option<ProofCertificateRef>>()
        })
        .unwrap()
        + 2;
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
    let result = st.setup(&b, &b.requests[0], &mut w);
    assert!(result.is_err());
    assert_eq!(st.reference.as_ref(), Some(&expected));
    assert!(st.known.is_empty());
    assert!(st.lineage.is_none());
    assert!(st.finish(result, &mut w).is_err());
    empty(&st);
}
#[test]
fn complete_prior_selectors_stay_owned_while_next_selector_child_refuses() {
    let mut b = fixture();
    let extra = b.module.proof_certificates[0].clone();
    b.module.proof_certificates.push(extra);
    let (_, _, end) = observed(&b, 0);
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
        let result = st.run(&b, 0, &mut w);
        if result.is_err() && st.known.len() == 1 && st.lineage.is_none() {
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
fn full_prover_pending_error_precedes_output_reserve_and_transport() {
    let b = bad();
    let (_, _, end) = observed(&b, 0);
    let mut found = 0;
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
        let result = st.run(&b, 0, &mut w);
        if result.is_err()
            && st.errors.is_empty()
            && matches!(&st.pending,Some(E::CertificateDigestMismatch{prover,..})if prover=="trust_vc")
        {
            found += 1;
            assert!(st.text.is_empty());
            assert!(st.finish(result, &mut w).is_err());
            empty(&st);
        } else {
            drain(&mut st, &mut w);
        }
    }
    assert!(found >= 2);
}
#[test]
fn held_local_error_survives_complete_selector_lineage_batch_and_prior_retirement() {
    let b = fixture();
    let mut o = Observer::default();
    let arm = Rc::new(Cell::new(false));
    o.arm = Some(arm.clone());
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut st = State::default();
    st.setup(&b, &b.requests[0], &mut w).unwrap();
    st.text = "full partial".into();
    st.pending = Some(E::EmptyRequests);
    st.errors = vec![E::EmptyRequests];
    st.batch = Some(vec![E::EmptyRequests].into_iter());
    st.batch_capacity = 1;
    arm.set(true);
    assert_eq!(
        st.finish(Err(ObservedValueError::InvalidRange), &mut w),
        Err(ObservedValueError::InvalidRange)
    );
    empty(&st);
    assert_eq!(w.session.first_refusal().unwrap().cause, "interrupt");
}
#[test]
fn full_selector_text_output_and_batch_spare_capacity_consume_after_stop() {
    let b = fixture();
    let reference = b.module.proof_certificates[0].lineage_ref();
    let mut known = Vec::with_capacity(37);
    known.push(reference.clone());
    let known_capacity = known.capacity();
    let mut text = String::with_capacity(2048);
    text.push_str("prefix");
    let text_capacity = text.capacity();
    let mut st = State {
        known,
        reference: Some(reference),
        text,
        pending: Some(E::EmptyRequests),
        errors: Vec::with_capacity(31),
        ..State::default()
    };
    st.errors.push(E::EmptyRequests);
    let errors = st.errors.capacity();
    let mut o = Observer {
        stop: Some(1),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    assert!(st.finish(Ok(()), &mut w).is_err());
    empty(&st);
    drop(w);
    drop(s);
    for capacity in [
        known_capacity * size_of::<ProofCertificateRef>(),
        text_capacity,
        errors * size_of::<E>(),
    ] {
        assert!(
            o.events
                .iter()
                .any(|p| p.phase == ExecutionPhase::ScratchRetirement && p.copy_bytes == capacity)
        );
    }
}
#[test]
fn borrowed_whole_module_manifest_and_requests_remain_exact_after_stop() {
    let b = bad();
    let before = b.stable_digest();
    let requests = b.requests.clone();
    let manifest = b.lineage.clone();
    let mut o = Observer {
        stop: Some(31),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert!(
        b.request_certificate_errors_observed(0, &mut s, site())
            .is_err()
    );
    assert_eq!(b.stable_digest(), before);
    assert_eq!(b.requests, requests);
    assert_eq!(b.lineage, manifest);
}
#[test]
fn healthy_original_caller_result_retirement_ends_scratch_then_zero_publication() {
    let b = bad();
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let rows = b
        .request_certificate_errors_observed(0, &mut s, site())
        .unwrap();
    let end = calls.get();
    retire_native_bundle_errors_observed(rows, &mut s, site()).unwrap();
    drop(s);
    assert!(
        o.events[end..o.events.len() - 1]
            .iter()
            .all(|p| p.phase == ExecutionPhase::ScratchRetirement)
    );
    let last = o.events.last().unwrap();
    assert_eq!(last.phase, ExecutionPhase::Publication);
    assert_eq!((last.work, last.copy_bytes), (0, 0));
}
#[test]
fn stopped_original_caller_result_retirement_drains_without_new_publication() {
    let b = bad();
    let arm = Rc::new(Cell::new(false));
    let mut o = Observer {
        arm: Some(arm.clone()),
        ..Observer::default()
    };
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let rows = b
        .request_certificate_errors_observed(0, &mut s, site())
        .unwrap();
    let end = calls.get();
    arm.set(true);
    assert!(retire_native_bundle_errors_observed(rows, &mut s, site()).is_err());
    arm.set(false);
    assert!(
        b.request_certificate_errors_observed(1, &mut s, site())
            .is_err()
    );
    assert_eq!(s.first_refusal().unwrap().cause, "interrupt");
    drop(s);
    assert!(
        o.events[end..]
            .iter()
            .all(|p| p.phase == ExecutionPhase::ScratchRetirement)
    );
}
