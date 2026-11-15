// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    clippy::field_reassign_with_default,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn every_unique_lookup_and_borrowed_publication_callback_refuses_without_semantic_none() {
    let m = fixture();
    for id in [0, 3, 8] {
        let mut baseline = Observer::default();
        let calls = baseline.calls.clone();
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut baseline);
        let a = setup(&m, &mut s);
        let begin = calls.get();
        let _ = a.unique_observed(FuncId::new(id), &mut s, site()).unwrap();
        let end = calls.get();
        a.retire_observed(&mut s, site()).unwrap();
        drop(s);
        for cut in begin + 1..=end {
            let mut o = Observer {
                stop: Some(cut),
                ..Observer::default()
            };
            let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
            let a = setup(&m, &mut s);
            assert_eq!(
                a.unique_observed(FuncId::new(id), &mut s, site()),
                Err(ObservedValueError::AdmissionRefused)
            );
            let _ = a.retire_observed(&mut s, site());
            drop(s);
            assert_eq!(&o.events[..cut], &baseline.events[..cut]);
            assert!(
                o.events[cut..]
                    .iter()
                    .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
            );
        }
    }
}
#[test]
fn every_cursor_reserve_copy_and_full_roster_publication_callback_refuses() {
    let m = fixture();
    let (baseline, begin, end) = run(&m);
    for cut in begin + 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let a = setup(&m, &mut s);
        assert_eq!(
            a.ambiguous_ids_observed(&mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        let _ = a.retire_observed(&mut s, site());
        drop(s);
        assert_eq!(&o.events[..cut], &baseline.events[..cut]);
        assert!(
            o.events[cut..]
                .iter()
                .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
        );
    }
}
#[test]
fn repeated_queries_share_original_cumulative_work_and_copy_without_regrant() {
    let m = fixture();
    let (baseline, _, end) = run(&m);
    for copy in [false, true] {
        let cap = baseline.events[..end]
            .iter()
            .map(|e| if copy { e.copy_bytes } else { e.work })
            .sum();
        let mut o = Observer::default();
        if copy {
            o.byte_cap = Some(cap)
        } else {
            o.work_cap = Some(cap)
        }
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let a = setup(&m, &mut s);
        let first = a.ambiguous_ids_observed(&mut s, site()).unwrap();
        assert_eq!(
            a.ambiguous_ids_observed(&mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        Work {
            session: &mut s,
            site: site(),
        }
        .rows(first);
        let _ = a.retire_observed(&mut s, site());
    }
}
#[test]
fn zero_fuel_preexisting_stop_and_query_site_remain_original() {
    let m = fixture();
    let mut options = InterpretOptions::default();
    options.fuel = 0;
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(options, &mut o);
    let a = setup(&m, &mut s);
    let begin = calls.get();
    a.unique_observed(FuncId::new(8), &mut s, site()).unwrap();
    a.retire_observed(&mut s, site()).unwrap();
    assert_eq!(s.remaining_fuel(), 0);
    drop(s);
    assert!(o.events[begin..].iter().all(|e| e.site == site()));
    let (_, begin, _) = run(&m);
    let mut o = Observer {
        stop: Some(begin + 1),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let a = setup(&m, &mut s);
    assert!(
        s.admit(ExecutionProgress {
            phase: ExecutionPhase::ModuleLookup,
            site: site(),
            work: 1,
            copy_bytes: 0
        })
        .is_err()
    );
    assert_eq!(
        a.unique_observed(FuncId::new(8), &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        a.ambiguous_ids_observed(&mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        s.first_refusal().unwrap().cause,
        "original catalog query stop"
    );
    let _ = a.retire_observed(&mut s, site());
}
#[test]
fn final_roster_publication_stop_keeps_first_cause_through_all_cleanup_refusals() {
    let m = fixture();
    let (_, _, end) = run(&m);
    let mut o = Observer {
        stop: Some(end),
        cleanup_after: Some(end),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let a = setup(&m, &mut s);
    assert_eq!(
        a.ambiguous_ids_observed(&mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    let _ = a.retire_observed(&mut s, site());
    assert_eq!(
        s.first_refusal().unwrap().cause,
        "original catalog query stop"
    );
    drop(s);
    assert!(
        o.events[end..]
            .iter()
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
}
#[test]
fn every_consuming_catalog_retirement_callback_refuses_only_after_complete_drain() {
    let m = fixture();
    let mut baseline = Observer::default();
    let calls = baseline.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let a = setup(&m, &mut s);
    let begin = calls.get();
    a.retire_observed(&mut s, site()).unwrap();
    let end = calls.get();
    drop(s);
    for cut in begin + 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let a = setup(&m, &mut s);
        assert_eq!(
            a.retire_observed(&mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        drop(s);
        assert_eq!(&o.events[..cut], &baseline.events[..cut]);
        assert!(
            o.events[cut..]
                .iter()
                .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
        );
    }
}
