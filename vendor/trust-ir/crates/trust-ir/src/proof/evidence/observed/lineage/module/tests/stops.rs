// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn every_actual_late_fallback_row_and_name_copy_callback_is_refusable() {
    let (mut m, _) = plain();
    m.functions = vec![function(33, "skip"); 24];
    m.functions.push(function(77, "late λ"));
    let mut base = Observer::default();
    let c = base.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut base);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut st = State::default();
    assert!(st.module_symbol(FuncId::new(77), &m, &mut w).unwrap());
    let end = c.get();
    st.retire(&mut w);
    drop(w);
    drop(s);
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
        assert_eq!(
            st.module_symbol(FuncId::new(77), &m, &mut w),
            Err(ObservedValueError::AdmissionRefused)
        );
        st.retire(&mut w);
        empty(&st);
    }
}
#[test]
fn every_actual_small_content_field_callback_can_refuse_without_partial_success() {
    let (m, row) = plain();
    let expected = content(&m, &row).unwrap();
    let mut base = Observer::default();
    let c = base.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut base);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut st = State::default();
    assert!(st.module_content(&row, &m, &mut w).unwrap());
    let end = c.get();
    st.retire(&mut w);
    drop(w);
    drop(s);
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
        assert_eq!(
            st.module_content(&row, &m, &mut w),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert!(expected.starts_with(&st.bytes));
        st.retire(&mut w);
        empty(&st);
    }
}
#[test]
fn real_complete_hash_and_final_publication_are_refusable_under_original_site() {
    let (m, row, b) = fixture();
    let (_, base, end) = observed(&m, &row, Some(&b));
    let mut cuts = vec![1, end];
    for n in 1..65 {
        cuts.push(n * end / 65 + 1);
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
            row.clean_cic_lineage_digest_v8_in_module_observed(&m, Some(&b), &mut s, site())
                .is_err()
        );
        assert_eq!(s.first_refusal().unwrap().progress, base.events[cut - 1]);
    }
}
#[test]
fn both_boolean_predicates_require_their_own_final_publication() {
    let (m, row, b) = fixture();
    let d = original(&m, &row, Some(&b)).unwrap();
    for v8 in [false, true] {
        let e = evidence(d, Some(b.clone()));
        let mut base = Observer::default();
        let c = base.calls.clone();
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut base);
        if v8 {
            e.clean_cic_lineage_is_v8_in_module_observed(&row, &m, &mut s, site())
                .unwrap();
        } else {
            e.clean_cic_lineage_binds_in_module_observed(&row, &m, &mut s, site())
                .unwrap();
        }
        let end = c.get();
        drop(s);
        let mut o = Observer {
            stop: Some(end),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let r = if v8 {
            e.clean_cic_lineage_is_v8_in_module_observed(&row, &m, &mut s, site())
        } else {
            e.clean_cic_lineage_binds_in_module_observed(&row, &m, &mut s, site())
        };
        assert!(r.is_err());
        assert_eq!(s.first_refusal().unwrap().progress, base.events[end - 1]);
    }
}
#[test]
fn one_original_cumulative_work_and_copy_budget_covers_two_full_module_queries() {
    let (m, row, b) = fixture();
    let (_, base, _) = observed(&m, &row, Some(&b));
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
        row.clean_cic_lineage_digest_v8_in_module_observed(&m, Some(&b), &mut s, site())
            .unwrap();
        assert!(
            row.clean_cic_lineage_digest_v8_in_module_observed(&m, Some(&b), &mut s, site())
                .is_err()
        );
        assert_eq!(
            s.first_refusal().unwrap().cause,
            if copy { "copy" } else { "work" }
        );
    }
}
#[test]
fn original_interrupt_remains_sticky_instead_of_semantic_none_or_false() {
    let (m, row, b) = fixture();
    let arm = Rc::new(Cell::new(true));
    let mut o = Observer {
        arm: Some(arm.clone()),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert!(
        row.clean_cic_lineage_digest_v8_in_module_observed(&m, Some(&b), &mut s, site())
            .is_err()
    );
    arm.set(false);
    assert!(
        row.clean_cic_lineage_digest_v8_in_module_observed(&m, Some(&b), &mut s, site())
            .is_err()
    );
    assert_eq!(s.first_refusal().unwrap().cause, "interrupt");
}
#[test]
fn zero_instruction_fuel_is_preserved_through_module_resolution_and_hash() {
    let (m, row, b) = fixture();
    let mut o = Observer::default();
    let mut s = ObservedSession::new(
        InterpretOptions {
            fuel: 0,
            ..InterpretOptions::default()
        },
        &mut o,
    );
    assert_eq!(
        row.clean_cic_lineage_digest_v8_in_module_observed(&m, Some(&b), &mut s, site())
            .unwrap(),
        original(&m, &row, Some(&b))
    );
    assert_eq!(s.remaining_fuel(), 0);
}
#[test]
fn cleanup_only_stop_cannot_publish_either_some_digest_or_unknown_none() {
    for digest in [None, Some(ProofDigest::sha256([1; 32]))] {
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
            st.finish_module_digest(Ok(digest), &mut w),
            Err(ObservedValueError::AdmissionRefused)
        );
        empty(&st);
    }
}
