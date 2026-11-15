// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored UNRUN: the whole-request source child binds an ACTUAL physical row.
use super::super::scan::Group;
use super::*;

#[test]
fn source_child_uses_the_selected_physical_row_even_when_ids_repeat() {
    let mut b = fixture();
    let mut different = b.requests[0].clone();
    if let NativeVerificationRequest::TrustVc(r) = &mut different {
        r.lineage_roots.clear();
        r.function = Some(FuncId::new(u32::MAX));
    } else {
        panic!("VC fixture");
    }
    b.requests.push(different);
    let mut expected = Vec::new();
    for index in [0, b.requests.len() - 1] {
        let mut o = Observer::default();
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let rows = b
            .request_source_errors_observed(&b.requests[index], &mut s, site())
            .unwrap();
        expected.push(rows.clone());
        retire_native_bundle_errors_observed(rows, &mut s, site()).unwrap();
        let mut w = Work {
            session: &mut s,
            site: site(),
        };
        let mut st = State::default();
        st.child(&b, index, Group::Source, &mut w).unwrap();
        assert_eq!(st.errors, *expected.last().unwrap());
        drain(&mut st, &mut w);
        empty(&st);
        assert!(w.session.first_refusal().is_none());
    }
    assert_ne!(expected[0], expected[1]);
    assert_eq!(b.requests[0].id(), b.requests.last().unwrap().id());
}

#[test]
fn source_child_refuses_missing_actual_rows_without_empty_success() {
    let b = fixture();
    for index in [b.requests.len(), usize::MAX] {
        let mut o = Observer::default();
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut w = Work {
            session: &mut s,
            site: site(),
        };
        let mut st = State::default();
        let result = st.child(&b, index, Group::Source, &mut w);
        assert_eq!(result, Err(ObservedValueError::InvalidRange));
        assert!(st.errors.is_empty() && st.batch.is_none() && st.pending.is_none());
        assert_eq!(
            st.finish(result, &mut w),
            Err(ObservedValueError::InvalidRange)
        );
        empty(&st);
        assert!(w.session.first_refusal().is_none());
    }
}

#[test]
fn every_actual_source_row_child_and_parent_transfer_fee_uses_the_original_stop() {
    let b = bad();
    let mut base = Observer::default();
    let calls = base.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut base);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut st = State::default();
    st.child(&b, 0, Group::Source, &mut w).unwrap();
    let end = calls.get();
    drain(&mut st, &mut w);
    assert!(end > 3);
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
        let result = st.child(&b, 0, Group::Source, &mut w);
        assert_eq!(result, Err(ObservedValueError::AdmissionRefused));
        assert_eq!(
            w.session.first_refusal().unwrap().progress,
            base.events[cut - 1]
        );
        assert!(st.finish(result, &mut w).is_err());
        empty(&st);
        assert_eq!(&o.events[..cut], &base.events[..cut]);
        assert!(
            o.events[cut..]
                .iter()
                .all(|p| p.phase == ExecutionPhase::ScratchRetirement)
        );
    }
}
