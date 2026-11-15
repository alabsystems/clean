// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn complete_child_owned_batch_precedes_the_next_outer_flush_admission() {
    let b = bad();
    let mut base = Observer::default();
    let c = base.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut base);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut st = State::default();
    st.child(&b, Group::Provenance, &mut w).unwrap();
    let end = c.get();
    drain(&mut st, &mut w);
    drop(w);
    drop(s);
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
        let result = st.child(&b, Group::Provenance, &mut w);
        if result.is_err()
            && st.batch.as_ref().is_some_and(|v| !v.as_slice().is_empty())
            && st.pending.is_none()
            && st.errors.is_empty()
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
fn whole_pending_error_and_remaining_child_tail_stay_owned_before_outer_reserve() {
    let b = bad();
    let mut base = Observer::default();
    let c = base.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut base);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut st = State::default();
    st.child(&b, Group::Provenance, &mut w).unwrap();
    let end = c.get();
    drain(&mut st, &mut w);
    drop(w);
    drop(s);
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
        let result = st.child(&b, Group::Provenance, &mut w);
        if result.is_err()
            && st.pending.is_some()
            && st.batch.as_ref().is_some_and(|v| !v.as_slice().is_empty())
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
fn complete_actual_lineage_error_vector_is_held_before_its_single_error_wrapper() {
    let b = bad();
    let mut base = Observer::default();
    let c = base.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut base);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut st = State::default();
    st.lineage(&b, &mut w).unwrap();
    let end = c.get();
    drain(&mut st, &mut w);
    drop(w);
    drop(s);
    let expected = b
        .lineage
        .validate_against(&b.module.proof_obligations, &b.module.proof_certificates)
        .unwrap_err();
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
        let result = st.lineage(&b, &mut w);
        if result.is_err() && st.lineage == expected {
            assert!(st.pending.is_none() && st.errors.is_empty());
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
fn already_held_error_wins_cleanup_stop_with_whole_iterator_tail_and_capacities() {
    let mut rows = Vec::with_capacity(41);
    rows.push(E::TrustIrModuleHasNoWireIdentity {
        location: "held full λ\0".into(),
        construct: "raw",
    });
    rows.push(E::EmptyRequests);
    let cap = rows.capacity();
    let mut st = State {
        batch: Some(rows.into_iter()),
        batch_capacity: cap,
        lineage: vec![ProofLineageError::EmptyRoots],
        pending: Some(E::EmptyRequests),
        errors: vec![E::EmptyRequests],
    };
    let mut o = Observer {
        stop: Some(1),
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
    drop(w);
    drop(s);
    assert!(
        o.events
            .iter()
            .any(|p| p.phase == ExecutionPhase::ScratchRetirement
                && p.copy_bytes == cap * size_of::<E>())
    );
}
#[test]
fn original_healthy_and_stopped_caller_retirement_keep_their_distinct_receipts() {
    for stop in [false, true] {
        let b = bad();
        let arm = Rc::new(Cell::new(false));
        let mut o = Observer {
            arm: Some(arm.clone()),
            ..Observer::default()
        };
        let c = o.calls.clone();
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let rows = b.pre_request_errors_observed(&mut s, site()).unwrap();
        let end = c.get();
        arm.set(stop);
        assert_eq!(
            retire_native_bundle_errors_observed(rows, &mut s, site()).is_err(),
            stop
        );
        drop(s);
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
fn whole_source_module_lineage_and_provenance_remain_exact_on_any_child_stop() {
    let b = bad();
    let before = b.clone();
    let end = private_bound(&b);
    let mut o = Observer {
        stop: Some(end / 2),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert!(b.pre_request_errors_observed(&mut s, site()).is_err());
    assert_eq!(b, before);
}

#[test]
fn stale_private_owning_slots_refuse_before_lineage_child_or_replacement() {
    let b = clean();
    for which in 0..3 {
        let mut st = State::default();
        match which {
            0 => st.lineage = Vec::with_capacity(19),
            1 => st.pending = Some(E::EmptyRequests),
            _ => {
                let rows = vec![E::EmptyRequests];
                st.batch_capacity = rows.capacity();
                st.batch = Some(rows.into_iter());
            }
        }
        let capacity = st.lineage.capacity();
        let mut o = Observer::default();
        let calls = o.calls.clone();
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut w = Work {
            session: &mut s,
            site: site(),
        };
        let result = st.lineage(&b, &mut w);
        assert_eq!(result, Err(ObservedValueError::InvalidRange));
        assert_eq!(calls.get(), 2); // Only header + stale-slot guard; no child.
        assert_eq!(st.lineage.capacity(), capacity);
        assert_eq!(
            st.finish(result, &mut w),
            Err(ObservedValueError::InvalidRange)
        );
        empty(&st);
    }
}
