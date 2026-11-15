// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn every_actual_lookup_stack_set_filter_merge_retirement_and_publication_can_stop() {
    let i = fixture();
    let (base, end) = observed(&i);
    for (at, p) in base.events[..end].iter().enumerate() {
        let mut o = Observer {
            stop: Some(at + 1),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert!(matches!(
            i.manifest
                .request_lineage_observed(&i.roots, i.source, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        ));
        assert_eq!(s.first_refusal().unwrap().progress, *p);
        assert_eq!(&o.events[..=at], &base.events[..=at]);
        assert!(
            o.events[at + 1..]
                .iter()
                .all(|p| p.phase == ExecutionPhase::ScratchRetirement)
        );
    }
}
#[test]
fn one_cumulative_original_work_and_copy_budget_covers_all_root_replays() {
    let i = fixture();
    let (base, _) = observed(&i);
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
        let out = i
            .manifest
            .request_lineage_observed(&i.roots, i.source, &mut s, site())
            .unwrap();
        out.retire_observed(&mut s, site()).unwrap();
        assert!(matches!(
            i.manifest
                .request_lineage_observed(&i.roots, i.source, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        ));
        assert_eq!(
            s.first_refusal().unwrap().cause,
            if copy { "copy" } else { "work" }
        );
    }
}
#[test]
fn original_interrupt_cannot_be_cleared_by_another_closure_call() {
    let i = fixture();
    let arm = Rc::new(Cell::new(true));
    let mut o = Observer {
        arm: Some(arm.clone()),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert!(
        i.manifest
            .request_lineage_observed(&i.roots, i.source, &mut s, site())
            .is_err()
    );
    arm.set(false);
    assert!(
        i.manifest
            .request_lineage_observed(&i.roots, None, &mut s, site())
            .is_err()
    );
    assert_eq!(s.first_refusal().unwrap().cause, "interrupt");
}
#[test]
fn zero_instruction_fuel_does_not_disable_full_actual_graph_work() {
    let i = fixture();
    let mut o = Observer::default();
    let mut s = ObservedSession::new(
        InterpretOptions {
            fuel: 0,
            ..InterpretOptions::default()
        },
        &mut o,
    );
    let out = i
        .manifest
        .request_lineage_observed(&i.roots, i.source, &mut s, site())
        .unwrap();
    assert_eq!(census(&out.reachable), expected(&i).0);
    out.retire_observed(&mut s, site()).unwrap();
    assert_eq!(s.remaining_fuel(), 0);
}
#[test]
fn whole_result_publication_refusal_never_returns_partial_sets() {
    let i = fixture();
    let (base, end) = observed(&i);
    assert_eq!(base.events[end - 1].phase, ExecutionPhase::Publication);
    let mut o = Observer {
        stop: Some(end),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert!(
        i.manifest
            .request_lineage_observed(&i.roots, i.source, &mut s, site())
            .is_err()
    );
    assert_eq!(s.first_refusal().unwrap().progress, base.events[end - 1]);
    assert!(
        o.events[end..]
            .iter()
            .all(|p| p.phase == ExecutionPhase::ScratchRetirement)
    );
}
#[test]
fn actual_late_reverse_lookup_can_refuse_before_any_node_payload_is_added() {
    let mut i = fixture();
    i.roots = vec![ProofLineageId::new(0)];
    i.manifest.nodes.extend((3..35).map(|n| node(n, 9)));
    let mut base = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut base);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut st = State::default();
    body(&mut st, &i, &mut w).unwrap();
    drain(&mut st, &mut w);
    drop(w);
    drop(s);
    let mut found = false;
    for cut in 1..base.events.len() {
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
            && st.seen.len() == 1
            && st.out.reachable.obligations.is_empty()
            && cut > 25
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
fn actual_late_prover_byte_comparison_can_refuse_without_publishing_false() {
    let a = certificate(0, &("a".repeat(2048) + "x"), 1);
    let b = certificate(0, &("a".repeat(2048) + "y"), 1);
    let out = NativeRequestLineage {
        reachable: Members::default(),
        bound: Members {
            certificates: vec![&a],
            ..Members::default()
        },
    };
    let mut base = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut base);
    assert!(
        !out.source_bound_certificate_contains_observed(&b, &mut s, site())
            .unwrap()
    );
    drop(s);
    let cuts: Vec<_> = base
        .events
        .iter()
        .enumerate()
        .filter(|(_, p)| p.work == 2048 && p.copy_bytes == 0)
        .map(|(at, _)| at + 1)
        .collect();
    assert_eq!(cuts.len(), 2);
    let mut o = Observer {
        stop: Some(cuts[1]),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(
        out.source_bound_certificate_contains_observed(&b, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        s.first_refusal().unwrap().progress,
        base.events[cuts[1] - 1]
    );
    out.retire_observed(&mut s, site()).unwrap_err();
}
#[test]
fn empty_scratch_cleanup_copy_stop_refuses_whole_output() {
    let mut o = Observer {
        byte_cap: Some(0),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut st = State::default();
    assert!(st.finish(Ok(()), &mut w).is_err());
    empty(&st);
}
