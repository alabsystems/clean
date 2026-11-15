// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
#[test]
fn complete_real_reference_is_held_before_known_table_allocation_or_transport() {
    let b = trusted();
    let expected = b.module.proof_certificates[0].lineage_ref();
    let mut base = Observer::default();
    let c = base.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut base);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut st = State::default();
    st.setup(&b, &mut w).unwrap();
    let end = c.get();
    drain(&mut st, &mut w);
    let mut found = false;
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
        let mut st = State::default();
        let result = st.setup(&b, &mut w);
        if result.is_err() && st.reference.as_ref() == Some(&expected) {
            found = true;
            assert!(st.known.is_empty());
            assert!(st.finish(result, &mut w).is_err());
            empty(&st);
            break;
        }
        drain(&mut st, &mut w);
    }
    assert!(found);
}
#[test]
fn actual_child_batch_is_captured_whole_before_first_outer_flush_callback() {
    let b = bad();
    let mut base = Observer::default();
    let c = base.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut base);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut st = State::default();
    st.child(&b, 0, super::super::scan::Group::Metadata, &mut w)
        .unwrap();
    let end = c.get();
    drain(&mut st, &mut w);
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
        let result = st.child(&b, 0, super::super::scan::Group::Metadata, &mut w);
        if result.is_err()
            && st.batch.as_ref().is_some_and(|r| !r.as_slice().is_empty())
            && st.pending.is_none()
        {
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
fn full_raw_prover_is_pending_before_error_output_reserve() {
    let mut b = trusted();
    let raw = "λ\0尾".repeat(400);
    b.module.proof_certificates[0].prover = raw.clone();
    vc(&mut b).certificates = vec![b.module.proof_certificates[0].lineage_ref()];
    let (_, end) = private_vc_bound(&b);
    let mut found = false;
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
        if result.is_err()
            && matches!(&st.pending,Some(E::TrustVcCertificateNotDischarged{prover,..})if prover==&raw)
        {
            found = true;
            assert!(st.text.is_empty());
            assert!(st.finish(result, &mut w).is_err());
            empty(&st);
            break;
        }
        drain(&mut st, &mut w);
    }
    assert!(found);
}
#[test]
fn partial_unicode_copy_stays_owned_with_known_references_and_prior_errors() {
    let mut b = trusted();
    let raw = "λ\0尾".repeat(600);
    b.module.proof_certificates[0].prover = raw.clone();
    let reference = b.module.proof_certificates[0].lineage_ref();
    vc(&mut b).certificates = vec![reference];
    let (_, end) = private_vc_bound(&b);
    let mut found = false;
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
        st.errors.push(E::EmptyRequests);
        let result = st.vc(&b, vc_ref(&b), &mut w);
        if result.is_err() && !st.text.is_empty() && st.text.len() < raw.len() {
            found = true;
            assert!(raw.starts_with(&st.text));
            assert_eq!(st.known.len(), 1);
            assert_eq!(st.errors, vec![E::EmptyRequests]);
            assert!(st.finish(result, &mut w).is_err());
            empty(&st);
            break;
        }
        drain(&mut st, &mut w);
    }
    assert!(found);
}
#[test]
fn already_held_local_error_wins_while_every_tail_capacity_is_consumed() {
    let b = trusted();
    let mut st = known(&b);
    st.reference = Some(vc_ref(&b).certificates[0].clone());
    let mut rows = Vec::with_capacity(29);
    rows.push(E::EmptyRequests);
    rows.push(E::MissingReplayIdentity(NativeRequestId::new(7)));
    let cap = rows.capacity();
    st.batch = Some(rows.into_iter());
    st.batch_capacity = cap;
    st.text = "whole λ\0".into();
    st.pending = Some(E::EmptyRequests);
    st.errors.push(E::EmptyRequests);
    let mut o = Observer {
        retirement_stop: true,
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    assert_eq!(
        st.finish(Err(ObservedValueError::InvalidRange), &mut w),
        Err(ObservedValueError::InvalidRange)
    );
    empty(&st);
    assert!(
        o.events
            .iter()
            .any(|p| p.phase == ExecutionPhase::ScratchRetirement
                && p.copy_bytes == cap * size_of::<E>())
    );
}
#[test]
fn healthy_and_stopped_caller_retirement_keep_original_terminal_receipt_semantics() {
    for stop in [false, true] {
        let b = trusted();
        let arm = Rc::new(Cell::new(false));
        let mut o = Observer {
            arm: Some(arm.clone()),
            ..Observer::default()
        };
        let c = o.calls.clone();
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let rows = b
            .request_errors_kernel_less_observed(&mut s, site())
            .unwrap();
        let end = c.get();
        arm.set(stop);
        assert_eq!(
            retire_native_bundle_errors_observed(rows, &mut s, site()).is_err(),
            stop
        );
        if stop {
            assert!(
                o.events[end..]
                    .iter()
                    .all(|p| p.phase == ExecutionPhase::ScratchRetirement)
            );
        } else {
            let last = o.events.last().unwrap();
            assert_eq!(
                (last.phase, last.work, last.copy_bytes),
                (ExecutionPhase::Publication, 0, 0)
            );
            assert!(
                o.events[end..o.events.len() - 1]
                    .iter()
                    .all(|p| p.phase == ExecutionPhase::ScratchRetirement)
            );
        }
    }
}
#[test]
fn stale_known_backing_or_reference_refuses_before_any_child_can_replace_it() {
    let b = trusted();
    for reference in [false, true] {
        let mut st = State::default();
        if reference {
            st.reference = Some(vc_ref(&b).certificates[0].clone());
        } else {
            st.known = Vec::with_capacity(13);
        }
        let capacity = st.known.capacity();
        let mut o = Observer::default();
        let c = o.calls.clone();
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut w = Work {
            session: &mut s,
            site: site(),
        };
        let result = st.setup(&b, &mut w);
        assert_eq!(result, Err(ObservedValueError::InvalidRange));
        assert_eq!(c.get(), 1);
        assert_eq!(st.known.capacity(), capacity);
        assert_eq!(
            st.finish(result, &mut w),
            Err(ObservedValueError::InvalidRange)
        );
        empty(&st);
    }
}
#[test]
fn all_source_bytes_are_unchanged_after_whole_child_or_authority_refusal() {
    let b = bad();
    let before = b.clone();
    let (_, _, end) = observed(&b);
    for cut in [1, end / 2, end] {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert!(
            b.request_errors_kernel_less_observed(&mut s, site())
                .is_err()
        );
        assert_eq!(b, before);
    }
}
