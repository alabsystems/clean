// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn every_partial_graph_cut_retains_then_drains_all_owned_maps_bits_edges_and_queues() {
    let m = fixture();
    let mut baseline = Observer::default();
    let calls = baseline.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    let mut st = state(&m);
    st.construct(&m, &mut work).unwrap();
    let bound = calls.get();
    drain(&mut st, &mut work);
    drop(work);
    drop(s);
    let mut saw_maps = false;
    let mut saw_bits = false;
    let mut saw_edges = false;
    let mut saw_pending = false;
    for cut in 1..=bound {
        let mut o = Observer {
            stop: Some(cut),
            cleanup_after: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut work = Work {
            session: &mut s,
            site: site(),
        };
        let mut st = state(&m);
        assert_eq!(
            st.construct(&m, &mut work),
            Err(ObservedValueError::AdmissionRefused)
        );
        saw_maps |= !st.summary.tables.structs.is_empty();
        saw_bits |= st.summary.reachable.iter().any(|v| v.capacity() != 0);
        saw_edges |= !st.edges.is_empty();
        saw_pending |= st.pending.iter().any(|v| !v.is_empty());
        drain(&mut st, &mut work);
        assert!(retired(&st));
        assert_eq!(
            work.session.first_refusal().unwrap().cause,
            "original nominal graph stop"
        );
        drop(work);
        drop(s);
        assert_eq!(&o.events[..cut], &baseline.events[..cut]);
        assert!(
            o.events[cut..]
                .iter()
                .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
        );
    }
    assert!(saw_maps && saw_bits && saw_edges && saw_pending);
}
#[test]
fn queue_reserve_and_last_mutation_refusals_leave_the_bit_and_pending_entry_unpublished() {
    let m = Module::new("");
    for cut in [4, 5] {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut work = Work {
            session: &mut s,
            site: site(),
        };
        let mut st = state(&m);
        st.summary.reachable[NominalAxis::Handle as usize] = vec![false];
        assert_eq!(
            st.mark(NominalAxis::Handle, 0, &mut work),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert!(!st.summary.reachable[1][0]);
        assert!(st.pending[1].is_empty());
        if cut == 4 {
            assert_eq!(st.pending[1].capacity(), 0);
        } else {
            assert!(st.pending[1].capacity() > 0);
        }
        drain(&mut st, &mut work);
        assert!(retired(&st));
        drop(work);
        drop(s);
        // Exact same private mark entry: read admission, actual bit get,
        // reserve probe, pre-allocation layout, then final atomic mutation.
        assert_eq!(o.events[0].work, 1);
        assert_eq!(o.events[2].copy_bytes, 0);
        assert_eq!(o.events[3].copy_bytes, size_of::<usize>());
    }
}
#[test]
fn reverse_edge_growth_refusal_keeps_the_previous_list_head_and_no_partial_edge() {
    let m = Module::new("");
    for cut in [4, 5] {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut work = Work {
            session: &mut s,
            site: site(),
        };
        let mut st = state(&m);
        st.heads = vec![NO_EDGE];
        assert_eq!(
            st.dependency(0, 0, &mut work),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(st.heads, vec![NO_EDGE]);
        assert!(st.edges.is_empty());
        if cut == 4 {
            assert_eq!(st.edges.capacity(), 0);
        } else {
            assert!(st.edges.capacity() > 0);
        }
        drain(&mut st, &mut work);
        assert!(retired(&st));
        drop(work);
        drop(s);
        assert_eq!(o.events[3].copy_bytes, size_of::<ReverseEdge>());
    }
}
#[test]
fn complete_instruction_root_vector_is_retired_when_the_next_parent_read_refuses() {
    let m = fixture();
    let inst = Inst::OpenFrame {
        def: crate::inst::BindingFrameDef::new(
            crate::value::BindingFrameId::new(7),
            "F",
            vec![
                crate::inst::BindingSlot::new("first", array(0)),
                crate::inst::BindingSlot::new("tail", array(2)),
            ],
        ),
    };
    let mut baseline = Observer::default();
    let calls = baseline.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let out = m
        .nominal_type_reachability_observed(&mut s, site())
        .unwrap();
    let start = calls.get();
    out.contains_handle_instruction_types_observed(&inst, &mut s, site())
        .unwrap();
    let end = calls.get();
    out.retire_observed(&mut s, site()).unwrap();
    drop(s);
    let child: Vec<_> = baseline.events[start..end]
        .iter()
        .enumerate()
        .filter(|(_, e)| {
            e.phase == ExecutionPhase::Publication && e.copy_bytes == size_of::<Vec<&Ty>>()
        })
        .map(|(i, _)| start + i + 1)
        .collect();
    assert_eq!(child.len(), 1);
    let cut = child[0] + 1;
    assert_eq!(baseline.events[cut - 1].phase, ExecutionPhase::Validation);
    let mut o = Observer {
        stop: Some(cut),
        ..Observer::default()
    };
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let out = m
        .nominal_type_reachability_observed(&mut s, site())
        .unwrap();
    assert_eq!(
        out.contains_handle_instruction_types_observed(&inst, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    let failed_end = calls.get();
    assert_eq!(
        out.retire_observed(&mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    drop(s);
    assert_eq!(&o.events[..cut], &baseline.events[..cut]);
    let cleanup = &o.events[cut..failed_end];
    assert!(
        cleanup
            .iter()
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
    assert!(cleanup.len() >= 8);
    assert!(
        cleanup
            .iter()
            .any(|e| e.work >= size_of::<Vec<&Ty>>() + 2 * size_of::<&Ty>())
    );
}
#[test]
fn cleanup_refusal_still_consumes_all_completed_graph_and_summary_storage() {
    let m = fixture();
    let mut o = Observer {
        cleanup_after: Some(0),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    let mut st = state(&m);
    st.construct(&m, &mut work).unwrap();
    assert!(!st.edges.is_empty());
    assert!(!st.summary.tables.structs.is_empty());
    drain(&mut st, &mut work);
    assert!(retired(&st));
    assert_eq!(work.session.first_refusal().unwrap().cause, "cleanup");
    assert_eq!(
        work.publication(0),
        Err(ObservedValueError::AdmissionRefused)
    );
    drop(work);
    drop(s);
    let first = o
        .events
        .iter()
        .position(|e| e.phase == ExecutionPhase::ScratchRetirement)
        .unwrap();
    assert!(
        o.events[first..]
            .iter()
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
    assert!(o.events.len() > first + 40);
}
#[test]
fn healthy_explicit_summary_retirement_keeps_its_final_zero_byte_publication() {
    let m = fixture();
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let out = m
        .nominal_type_reachability_observed(&mut s, site())
        .unwrap();
    let start = calls.get();
    out.retire_observed(&mut s, site()).unwrap();
    let end = calls.get();
    assert!(s.first_refusal().is_none());
    drop(s);
    assert!(end > start + 12);
    assert!(
        o.events[start..end - 1]
            .iter()
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
    assert_eq!(
        o.events[end - 1],
        ExecutionProgress {
            phase: ExecutionPhase::Publication,
            site: site(),
            work: 1,
            copy_bytes: 0
        }
    );
}
