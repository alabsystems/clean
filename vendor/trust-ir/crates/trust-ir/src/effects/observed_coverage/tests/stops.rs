// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn every_callback_of_all_three_public_predicates_can_refuse_without_a_semantic_bool() {
    let ours = EffectSet::Places(vec![p(0), p(1), g(3)]);
    let theirs = EffectSet::Places(vec![g(3), p(1)]);
    let top = EffectSummary::top();
    let pure = EffectSummary::pure();
    let global = pure.clone().reading(EffectSet::Places(vec![p(0), g(1)]));
    for query in samples(&ours, &theirs, &top, &pure, &global) {
        let base = trace(query);
        for stop in 1..=base.events.len() {
            let mut observer = Observer {
                stop: Some(stop),
                ..Observer::default()
            };
            let mut original = ObservedSession::new(InterpretOptions::default(), &mut observer);
            assert_eq!(
                query.call(&mut original, site()),
                Err(ObservedValueError::AdmissionRefused)
            );
            assert_eq!(
                original.first_refusal().unwrap().cause,
                "original coverage stop"
            );
            assert_eq!(
                original.first_refusal().unwrap().progress,
                base.events[stop - 1]
            );
            drop(original);
            // No owned scratch or input is consumed by these borrowed queries.
            assert_eq!(observer.events.len(), stop);
        }
    }
}
#[test]
fn a_real_inner_membership_comparison_can_refuse_before_the_long_scan_finishes() {
    let ours = EffectSet::Places((0..100).map(p).collect());
    let theirs = EffectSet::Places(vec![g(u32::MAX)]);
    let query = Query::Set(&ours, &theirs);
    let base = trace(query);
    let matches = base
        .events
        .iter()
        .enumerate()
        .filter(|(_, e)| {
            e.phase == ExecutionPhase::Validation
                && e.work == 3
                && e.copy_bytes == 2 * size_of::<EffectPlace>() + size_of::<bool>()
        })
        .map(|(index, _)| index + 1)
        .collect::<Vec<_>>();
    assert_eq!(matches.len(), 100);
    let stop = matches[50];
    let mut o = Observer {
        stop: Some(stop),
        ..Observer::default()
    };
    let mut original = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(
        query.call(&mut original, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        original.first_refusal().unwrap().progress,
        base.events[stop - 1]
    );
}
#[test]
fn every_duplicate_required_row_is_really_checked_and_can_stop_the_outer_loop() {
    let ours = EffectSet::Places(vec![p(7)]);
    let theirs = EffectSet::Places(vec![p(7); 100]);
    let query = Query::Set(&ours, &theirs);
    let base = trace(query);
    let visits = base
        .events
        .iter()
        .enumerate()
        .filter(|(_, e)| {
            e.phase == ExecutionPhase::Validation
                && e.work == 3
                && e.copy_bytes == 2 * size_of::<EffectPlace>() + size_of::<bool>()
        })
        .map(|(index, _)| index + 1)
        .collect::<Vec<_>>();
    assert_eq!(visits.len(), 100);
    let stop = visits[50];
    let mut o = Observer {
        stop: Some(stop),
        ..Observer::default()
    };
    let mut original = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(
        query.call(&mut original, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        original.first_refusal().unwrap().progress,
        base.events[stop - 1]
    );
}
#[test]
fn global_query_can_refuse_inside_the_actual_long_place_scan() {
    let mut rows = vec![p(1); 100];
    rows.push(g(9));
    let summary = EffectSummary::pure().writing(EffectSet::Places(rows));
    let query = Query::Names(&summary);
    let base = trace(query);
    let reads = base
        .events
        .iter()
        .enumerate()
        .filter(|(_, e)| {
            e.phase == ExecutionPhase::Validation
                && e.work == 1
                && e.copy_bytes == size_of::<bool>()
        })
        .map(|(index, _)| index + 1)
        .collect::<Vec<_>>();
    assert_eq!(reads.len(), 101);
    let stop = reads[50];
    let mut o = Observer {
        stop: Some(stop),
        ..Observer::default()
    };
    let mut original = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(
        query.call(&mut original, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        original.first_refusal().unwrap().progress,
        base.events[stop - 1]
    );
}
#[test]
fn cumulative_work_and_copy_limits_cover_repeated_calls_of_every_public_api() {
    let ours = EffectSet::Places(vec![p(0), p(1), g(3)]);
    let theirs = EffectSet::Places(vec![g(3), p(1)]);
    let top = EffectSummary::top();
    let pure = EffectSummary::pure();
    let global = pure.clone().writing(EffectSet::Places(vec![p(0), g(1)]));
    for query in samples(&ours, &theirs, &top, &pure, &global) {
        let base = trace(query);
        for copy in [false, true] {
            let mut o = Observer {
                work_cap: (!copy).then_some(base.work),
                byte_cap: copy.then_some(base.bytes),
                ..Observer::default()
            };
            let mut original = ObservedSession::new(InterpretOptions::default(), &mut o);
            assert_eq!(query.call(&mut original, site()), Ok(query.expected()));
            assert_eq!(
                query.call(&mut original, site()),
                Err(ObservedValueError::AdmissionRefused)
            );
            assert_eq!(
                original.first_refusal().unwrap().cause,
                if copy { "copy" } else { "work" }
            );
            let first = original.first_refusal().unwrap().progress;
            assert_eq!(
                query.call(&mut original, site()),
                Err(ObservedValueError::AdmissionRefused)
            );
            assert_eq!(original.first_refusal().unwrap().progress, first);
        }
    }
}
#[test]
fn first_header_refusal_is_sticky_across_all_three_different_predicates() {
    let set = EffectSet::Nothing;
    let pure = EffectSummary::pure();
    let mut o = Observer {
        byte_cap: Some(0),
        ..Observer::default()
    };
    let mut original = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(
        set.covers_observed(&set, &mut original, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    let first = original.first_refusal().unwrap().progress;
    assert_eq!(
        pure.covers_observed(&pure, &mut original, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        pure.names_a_global_observed(&mut original, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(original.first_refusal().unwrap().progress, first);
    drop(original);
    assert_eq!(o.events.len(), 1);
}
#[test]
fn final_publication_refusal_never_returns_a_computed_true_or_false() {
    let ours = EffectSet::Places(vec![p(0), g(3)]);
    let theirs = EffectSet::Places(vec![g(3)]);
    let top = EffectSummary::top();
    let pure = EffectSummary::pure();
    let global = pure.clone().reading(EffectSet::Places(vec![g(1)]));
    for query in samples(&ours, &theirs, &top, &pure, &global) {
        let base = trace(query);
        let stop = base.events.len();
        assert_eq!(base.events[stop - 1].phase, ExecutionPhase::Publication);
        let mut o = Observer {
            stop: Some(stop),
            ..Observer::default()
        };
        let mut original = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert_eq!(
            query.call(&mut original, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(
            original.first_refusal().unwrap().progress,
            base.events[stop - 1]
        );
    }
}
#[test]
fn exact_original_instruction_site_and_zero_fuel_survive_all_predicates() {
    let exact = ExecutionSite::Instruction(InstructionSite {
        function: FuncId::new(247),
        block: BlockId::new(8),
        instruction_index: usize::MAX,
    });
    let set = EffectSet::Places(vec![p(0), g(3)]);
    let summary = EffectSummary::pure().reading(set.clone());
    let mut o = Observer::default();
    let mut original = ObservedSession::new(
        InterpretOptions {
            fuel: 0,
            ..InterpretOptions::default()
        },
        &mut o,
    );
    assert_eq!(set.covers_observed(&set, &mut original, exact), Ok(true));
    assert_eq!(
        summary.covers_observed(&summary, &mut original, exact),
        Ok(true)
    );
    assert_eq!(
        summary.names_a_global_observed(&mut original, exact),
        Ok(true)
    );
    assert_eq!(original.remaining_fuel(), 0);
    assert!(original.first_refusal().is_none());
    drop(original);
    assert!(o.events.iter().all(|event| event.site == exact));
}
#[test]
fn borrowed_input_rows_and_capacities_are_preserved_after_interior_and_publication_stops() {
    let a = vec![g(9), p(7), p(7), p(8)];
    let b = vec![p(8), g(9)];
    let pa = a.as_ptr();
    let pb = b.as_ptr();
    let ca = a.capacity();
    let cb = b.capacity();
    let ours = EffectSet::Places(a);
    let theirs = EffectSet::Places(b);
    let query = Query::Set(&ours, &theirs);
    let base = trace(query);
    for stop in [base.events.len() / 2, base.events.len()] {
        let mut o = Observer {
            stop: Some(stop),
            ..Observer::default()
        };
        let mut original = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert_eq!(
            query.call(&mut original, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        let EffectSet::Places(a) = &ours else {
            unreachable!()
        };
        let EffectSet::Places(b) = &theirs else {
            unreachable!()
        };
        assert_eq!((a.as_ptr(), a.capacity()), (pa, ca));
        assert_eq!((b.as_ptr(), b.capacity()), (pb, cb));
        assert_eq!(a, &[g(9), p(7), p(7), p(8)]);
        assert_eq!(b, &[p(8), g(9)]);
        drop(original);
        assert!(
            o.events
                .iter()
                .all(|event| event.phase != ExecutionPhase::ScratchRetirement)
        );
    }
}
