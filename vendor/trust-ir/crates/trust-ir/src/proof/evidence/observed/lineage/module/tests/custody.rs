// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn whole_actual_content_preimage_remains_owned_before_binding_and_hash() {
    let (m, row, _) = fixture();
    let expected = content(&m, &row).unwrap();
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut st = State::default();
    assert!(st.module_content(&row, &m, &mut w).unwrap());
    assert_eq!(st.bytes, expected);
    st.retire(&mut w);
    empty(&st);
}
#[test]
fn partial_raw_link_name_and_prior_content_remain_owned_after_interruption() {
    let (mut m, row, _) = fixture();
    m.functions[0].name = "λ\0尾".repeat(600);
    let expected = content(&m, &row).unwrap();
    let mut base = Observer::default();
    let c = base.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut base);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut st = State::default();
    st.module_content(&row, &m, &mut w).unwrap();
    let end = c.get();
    st.retire(&mut w);
    drop(w);
    drop(s);
    let mut seen = false;
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
        let r = st.module_content(&row, &m, &mut w);
        assert!(r.is_err());
        assert!(expected.starts_with(&st.bytes));
        if !st.bytes.is_empty() && st.bytes.len() < expected.len() {
            seen = true;
        }
        st.retire(&mut w);
        empty(&st);
    }
    assert!(seen);
}
#[test]
fn unresolved_function_still_holds_prior_complete_fields_until_consuming_cleanup() {
    let (mut m, row, _) = fixture();
    m.functions.clear();
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut st = State::default();
    assert!(!st.module_content(&row, &m, &mut w).unwrap());
    assert!(!st.bytes.is_empty());
    assert!(st.finish_module_digest(Ok(None), &mut w).unwrap().is_none());
    empty(&st);
}
#[test]
fn held_local_error_wins_later_cleanup_stop_with_full_preimage_and_spare_backing() {
    let (m, row, _) = fixture();
    let arm = Rc::new(Cell::new(false));
    let mut o = Observer {
        arm: Some(arm.clone()),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut st = State::default();
    st.module_content(&row, &m, &mut w).unwrap();
    assert!(!st.bytes.is_empty());
    arm.set(true);
    assert_eq!(
        st.finish_module_digest(Err(ObservedValueError::CapacityOverflow), &mut w),
        Err(ObservedValueError::CapacityOverflow)
    );
    empty(&st);
}
#[test]
fn original_module_and_all_raw_obligation_binding_fields_remain_unchanged_on_stop() {
    let (m, row, b) = fixture();
    let before = (m.clone(), row.clone(), b.clone());
    let (_, _, end) = observed(&m, &row, Some(&b));
    for cut in [1, end / 2, end] {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert!(
            row.clean_cic_lineage_digest_v8_in_module_observed(&m, Some(&b), &mut s, site())
                .is_err()
        );
        assert_eq!((&m, &row, &b), (&before.0, &before.1, &before.2));
    }
}
#[test]
fn nonmatching_duplicate_catalog_is_not_required_or_constructed_by_actual_module_api() {
    let (mut m, row, b) = fixture();
    m.functions.push(function(77, "duplicate"));
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let d = row
        .clean_cic_lineage_digest_v8_in_module_observed(&m, Some(&b), &mut s, site())
        .unwrap();
    assert_eq!(d, original(&m, &row, Some(&b)));
    let e = evidence(d.unwrap(), Some(b));
    assert!(
        e.clean_cic_lineage_binds_in_module_observed(&row, &m, &mut s, site())
            .unwrap()
    );
    assert!(m.functions.len() == 2);
}
