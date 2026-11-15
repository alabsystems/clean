// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

#![allow(
    clippy::drop_non_drop,
    clippy::field_reassign_with_default,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn actual_owned_stack_and_seen_are_drained_after_interior_stop() {
    let i = fixture();
    let (base, end) = observed(&i);
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
        let result = body(&mut st, &i, &mut w);
        if result.is_err() && !st.stack.is_empty() && !st.seen.is_empty() {
            found = true;
            assert!(st.finish(result, &mut w).is_err());
            empty(&st);
            break;
        }
        drain(&mut st, &mut w);
    }
    assert!(found);
    assert!(!base.events.is_empty());
}
#[test]
fn complete_reachable_result_stays_held_when_per_root_rebuild_refuses() {
    let i = fixture();
    let (_, end) = observed(&i);
    let want = expected(&i).0;
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
        let result = body(&mut st, &i, &mut w);
        if result.is_err()
            && census(&st.out.reachable) == want
            && !st.current.obligations.is_empty()
        {
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
fn complete_selected_root_members_stay_owned_before_union_transfer() {
    let i = fixture();
    let (_, end) = observed(&i);
    let expected_root = crate::request::lineage_closure(&i.manifest, &i.roots[..1]);
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
        let result = body(&mut st, &i, &mut w);
        if result.is_err()
            && census(&st.current) == expected_root
            && st.out.bound.obligations.is_empty()
        {
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
fn all_actual_scratch_and_output_spare_capacities_retire_after_stop() {
    let mut st = State::default();
    st.stack = Vec::with_capacity(73);
    st.stack.push(ProofLineageId::new(1));
    let capacity = st.stack.capacity();
    st.out.reachable.obligations = Vec::with_capacity(91);
    st.out.reachable.obligations.push(ProofId::new(1));
    let out_capacity = st.out.reachable.obligations.capacity();
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
    assert!(
        o.events
            .iter()
            .any(|p| p.phase == ExecutionPhase::ScratchRetirement
                && p.copy_bytes == capacity * size_of::<ProofLineageId>())
    );
    assert!(
        o.events
            .iter()
            .any(|p| p.phase == ExecutionPhase::ScratchRetirement
                && p.copy_bytes == out_capacity * size_of::<ProofId>())
    );
}
#[test]
fn held_local_error_retains_precedence_while_all_owned_sets_consume() {
    let mut st = State::default();
    st.out.reachable.obligations = vec![ProofId::new(1)];
    st.current.sources = vec![digest(1)];
    st.stack = vec![ProofLineageId::new(1)];
    let mut o = Observer {
        stop: Some(1),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    assert!(matches!(
        st.finish(Err(ObservedValueError::InvalidRange), &mut w),
        Err(ObservedValueError::InvalidRange)
    ));
    empty(&st);
    assert_eq!(w.session.first_refusal().unwrap().cause, "interior");
}
#[test]
fn borrowed_manifest_and_roots_remain_exact_after_interior_stop() {
    let i = fixture();
    let before = i.clone();
    let mut o = Observer {
        stop: Some(10),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert!(
        i.manifest
            .request_lineage_observed(&i.roots, i.source, &mut s, site())
            .is_err()
    );
    assert_eq!(i.manifest, before.manifest);
    assert_eq!(i.roots, before.roots);
    assert_eq!(i.source, before.source);
}
#[test]
fn successful_caller_retirement_has_full_scratch_tail_then_zero_publication() {
    let i = fixture();
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let out = i
        .manifest
        .request_lineage_observed(&i.roots, i.source, &mut s, site())
        .unwrap();
    let end = calls.get();
    out.retire_observed(&mut s, site()).unwrap();
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
fn stopped_caller_retirement_drains_all_arrays_and_preserves_first_cause() {
    let i = fixture();
    let arm = Rc::new(Cell::new(false));
    let mut o = Observer {
        arm: Some(arm.clone()),
        ..Observer::default()
    };
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let out = i
        .manifest
        .request_lineage_observed(&i.roots, i.source, &mut s, site())
        .unwrap();
    let end = calls.get();
    arm.set(true);
    assert!(out.retire_observed(&mut s, site()).is_err());
    arm.set(false);
    assert!(
        i.manifest
            .request_lineage_observed(&i.roots, None, &mut s, site())
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
