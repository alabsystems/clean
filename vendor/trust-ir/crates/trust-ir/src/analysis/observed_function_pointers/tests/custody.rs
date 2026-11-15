// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn complete_successful_analysis_stays_owned_until_original_caller_retirement() {
    let f = chain();
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut a = ObservedStaticFunctionPointerAnalysis::new_observed(&f, &mut s, site()).unwrap();
    a.resolve_typed_at_observed(v(2), BlockId::new(0), 3, &mut s, site())
        .unwrap();
    assert!(
        !a.state.uses.is_empty()
            && !a.state.definitions.is_empty()
            && !a.state.provenances.is_empty()
    );
    assert!(a.state.dominators.is_some());
    a.state.retire(&mut Work {
        session: &mut s,
        site: site(),
    });
    empty(&a.state);
    a.retire_observed(&mut s, site()).unwrap();
    drop(s);
    assert_eq!(
        *o.events.last().unwrap(),
        ExecutionProgress {
            phase: ExecutionPhase::Publication,
            site: site(),
            work: 0,
            copy_bytes: 0
        }
    );
}
#[test]
fn full_pending_duplicate_parameter_sets_remain_owned_at_preallocation_refusal() {
    let mut f = chain();
    f.blocks[0].params = (100..104).map(|n| (v(n), ft(0))).collect();
    f.blocks.push(f.blocks[0].clone());
    let mut baseline = Observer::default();
    let mut bs = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let mut state = State::default();
    state
        .build_uses(
            &f,
            &mut Work {
                session: &mut bs,
                site: site(),
            },
        )
        .unwrap();
    drop(bs);
    let mut saw_full_pending = false;
    for cut in 1..=baseline.events.len() {
        let mut o = Observer {
            stop_at: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut state = State::default();
        let mut work = Work {
            session: &mut s,
            site: site(),
        };
        assert_eq!(
            state.build_uses(&f, &mut work),
            Err(ObservedValueError::AdmissionRefused)
        );
        if let Some(UseBlockState::Unique { parameters, .. }) = &state.pending_use {
            saw_full_pending |= parameters.len() == 4 && !state.uses.is_empty();
        }
        state.retire(&mut work);
        empty(&state);
    }
    assert!(saw_full_pending);
}
#[test]
fn active_path_and_completed_memo_survive_interior_stop_until_explicit_drain() {
    let f = function(vec![
        seed(9, 7),
        copy(0, 9, ft(0)),
        copy(1, 0, ft(0)),
        call(1),
        ret(),
    ]);
    let definitions = build_definition_index(&f, None);
    let tree = DominatorTree::new(&f);
    let mut baseline = Observer::default();
    let mut bs = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let mut state = State::default();
    provenance::build(
        &definitions.entries,
        &tree,
        &mut state.provenances,
        &mut state.active,
        &mut state.path,
        &mut Work {
            session: &mut bs,
            site: site(),
        },
    )
    .unwrap();
    drop(bs);
    let mut saw_path = false;
    let mut saw_memo = false;
    for cut in 1..=baseline.events.len() {
        let mut o = Observer {
            stop_at: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut state = State::default();
        let mut work = Work {
            session: &mut s,
            site: site(),
        };
        assert_eq!(
            provenance::build(
                &definitions.entries,
                &tree,
                &mut state.provenances,
                &mut state.active,
                &mut state.path,
                &mut work
            ),
            Err(ObservedValueError::AdmissionRefused)
        );
        saw_path |= !state.active.is_empty() && !state.path.is_empty();
        saw_memo |= !state.provenances.is_empty();
        state.retire(&mut work);
        empty(&state);
    }
    assert!(saw_path && saw_memo);
}
#[test]
fn true_and_false_final_query_publications_cannot_escape_after_refusal() {
    let f = chain();
    for (value, index) in [(2, 3), (99, 3)] {
        let baseline = run_query_only(&f, value, index);
        let mut o = Observer {
            stop_at: Some(baseline.events.len()),
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
    }
}
#[test]
fn every_full_cache_retirement_callback_drains_all_buffers_even_when_cancelled() {
    let f = chain();
    let base = run_query_only(&f, 2, 3);
    let mut baseline = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let mut a = ObservedStaticFunctionPointerAnalysis::new_observed(&f, &mut s, site()).unwrap();
    a.resolve_typed_at_observed(v(2), BlockId::new(0), 3, &mut s, site())
        .unwrap();
    a.state.retire(&mut Work {
        session: &mut s,
        site: site(),
    });
    drop(s);
    for cut in base.events.len() + 1..=baseline.events.len() {
        let mut o = Observer {
            stop_at: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut a =
            ObservedStaticFunctionPointerAnalysis::new_observed(&f, &mut s, site()).unwrap();
        a.resolve_typed_at_observed(v(2), BlockId::new(0), 3, &mut s, site())
            .unwrap();
        a.state.retire(&mut Work {
            session: &mut s,
            site: site(),
        });
        empty(&a.state);
        assert_eq!(
            a.retire_observed(&mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(s.first_refusal().unwrap().cause, "original stop");
    }
}
#[test]
fn stopped_retirement_suppresses_healthy_child_and_outer_publications() {
    let f = chain();
    let base = run_query_only(&f, 2, 3);
    let mut o = Observer {
        stop_at: Some(base.events.len() + 1),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut a = ObservedStaticFunctionPointerAnalysis::new_observed(&f, &mut s, site()).unwrap();
    a.resolve_typed_at_observed(v(2), BlockId::new(0), 3, &mut s, site())
        .unwrap();
    assert_eq!(
        a.retire_observed(&mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    drop(s);
    assert!(
        o.events[base.events.len()..]
            .iter()
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
}
