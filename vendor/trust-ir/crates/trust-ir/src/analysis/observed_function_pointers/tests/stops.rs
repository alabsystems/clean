// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    clippy::field_reassign_with_default,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn every_actual_query_callback_refuses_without_partial_cache_or_smaller_answer() {
    for (f, value, index) in [
        (chain(), 2, 3),
        (
            function(vec![copy(0, 1, ft(0)), copy(1, 0, ft(0)), call(0), ret()]),
            0,
            2,
        ),
    ] {
        let baseline = run_query_only(&f, value, index);
        for cut in 3..=baseline.events.len() {
            let mut o = Observer {
                stop_at: Some(cut),
                ..Observer::default()
            };
            let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
            let mut a =
                ObservedStaticFunctionPointerAnalysis::new_observed(&f, &mut s, site()).unwrap();
            assert_eq!(
                a.resolve_typed_at_observed(v(value), BlockId::new(0), index, &mut s, site()),
                Err(ObservedValueError::AdmissionRefused)
            );
            empty(&a.state);
            assert_eq!(s.first_refusal().unwrap().cause, "original stop");
            drop(a);
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
fn repeated_cached_queries_share_cumulative_work_and_copy_limits() {
    let f = chain();
    let baseline = run_query_only(&f, 2, 3);
    for copy in [false, true] {
        let mut o = Observer::default();
        if copy {
            o.byte_cap = Some(baseline.bytes)
        } else {
            o.work_cap = Some(baseline.work)
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut a =
            ObservedStaticFunctionPointerAnalysis::new_observed(&f, &mut s, site()).unwrap();
        assert!(
            a.resolve_typed_at_observed(v(2), BlockId::new(0), 3, &mut s, site())
                .unwrap()
                .is_some()
        );
        assert_eq!(
            a.resolve_typed_at_observed(v(2), BlockId::new(0), 3, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        empty(&a.state);
        assert_eq!(
            s.first_refusal().unwrap().cause,
            if copy { "bytes" } else { "work" }
        );
    }
}
#[test]
fn zero_instruction_fuel_original_site_and_session_remain_unchanged() {
    let f = chain();
    let mut o = Observer::default();
    let mut options = InterpretOptions::default();
    options.fuel = 0;
    let mut s = ObservedSession::new(options, &mut o);
    let mut a = ObservedStaticFunctionPointerAnalysis::new_observed(&f, &mut s, site()).unwrap();
    assert!(
        a.resolve_typed_at_observed(v(2), BlockId::new(0), 3, &mut s, site())
            .unwrap()
            .is_some()
    );
    assert_eq!(s.remaining_fuel(), 0);
    a.retire_observed(&mut s, site()).unwrap();
    drop(s);
    assert!(o.events.iter().all(|e| e.site == site()));
}
#[test]
fn preexisting_original_stop_drains_successful_caches_and_never_regrants() {
    let f = chain();
    let baseline = run_query_only(&f, 2, 3);
    let mut o = Observer {
        stop_at: Some(baseline.events.len() + 1),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut a = ObservedStaticFunctionPointerAnalysis::new_observed(&f, &mut s, site()).unwrap();
    a.resolve_typed_at_observed(v(2), BlockId::new(0), 3, &mut s, site())
        .unwrap();
    assert!(
        s.admit(ExecutionProgress {
            phase: ExecutionPhase::Validation,
            site: site(),
            work: 1,
            copy_bytes: 0
        })
        .is_err()
    );
    assert_eq!(
        a.resolve_typed_at_observed(v(2), BlockId::new(0), 3, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    empty(&a.state);
    assert_eq!(s.first_refusal().unwrap().cause, "original stop");
}
#[test]
fn constructor_publication_refusal_does_not_return_even_empty_analysis() {
    let f = chain();
    for cut in [1, 2] {
        let mut o = Observer {
            stop_at: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert!(matches!(
            ObservedStaticFunctionPointerAnalysis::new_observed(&f, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        ));
    }
}
#[test]
fn fixed_key_population_overflow_is_typed_without_unpriced_map_access() {
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    assert_eq!(
        work.lookup(usize::MAX),
        Err(ObservedValueError::CapacityOverflow)
    );
    assert!(s.first_refusal().is_none());
}
