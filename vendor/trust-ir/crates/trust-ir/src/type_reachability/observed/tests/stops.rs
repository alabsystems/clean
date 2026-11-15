// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    clippy::field_reassign_with_default,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn every_actual_constructor_and_retirement_publication_callback_is_refusable() {
    let mut m = Module::new("");
    m.types = vec![Ty::Tuple(vec![array(0), handle()])];
    let (baseline, bound) = build_events(&m);
    for cut in 1..=bound {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert!(matches!(
            m.nominal_type_reachability_observed(&mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        ));
        assert_eq!(
            s.first_refusal().unwrap().cause,
            "original nominal graph stop"
        );
        drop(s);
        assert_eq!(&o.events[..cut], &baseline.events[..cut]);
        assert!(
            o.events[cut..]
                .iter()
                .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
        );
        assert!(o.events.iter().all(|e| e.site == site()));
    }
}
#[test]
fn every_interior_reverse_edge_and_axis_queue_operation_uses_original_owner() {
    let mut m = Module::new("");
    m.types = vec![
        array(1),
        Ty::Tuple(vec![
            array(0),
            handle(),
            dialect(),
            Ty::Func(FuncTyId::new(99)),
        ]),
    ];
    let mut baseline = Observer::default();
    let calls = baseline.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    let mut st = state(&m);
    st.prepare(&m, &mut work).unwrap();
    st.inventory(&m, &mut work).unwrap();
    let start = calls.get();
    st.solve(&mut work).unwrap();
    let end = calls.get();
    drain(&mut st, &mut work);
    drop(work);
    drop(s);
    assert!(end > start + 12);
    for cut in start + 1..=end {
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
        st.prepare(&m, &mut work).unwrap();
        st.inventory(&m, &mut work).unwrap();
        assert_eq!(
            st.solve(&mut work),
            Err(ObservedValueError::AdmissionRefused)
        );
        drain(&mut st, &mut work);
        assert!(retired(&st));
        drop(work);
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
fn every_true_false_query_callback_including_named_lookup_and_cleanup_is_refusable() {
    let mut m = Module::new("");
    m.structs = vec![structure(40, handle()), structure(70, dialect())];
    let root = Ty::Tuple(vec![
        Ty::Struct(StructId::new(70)),
        Ty::Struct(StructId::new(99)),
    ]);
    for axis in AXES {
        let mut baseline = Observer::default();
        let calls = baseline.calls.clone();
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut baseline);
        let out = m
            .nominal_type_reachability_observed(&mut s, site())
            .unwrap();
        let start = calls.get();
        query(&out, axis, &root, &mut s).unwrap();
        let end = calls.get();
        out.retire_observed(&mut s, site()).unwrap();
        drop(s);
        for cut in start + 1..=end {
            let mut o = Observer {
                stop: Some(cut),
                ..Observer::default()
            };
            let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
            let out = m
                .nominal_type_reachability_observed(&mut s, site())
                .unwrap();
            assert_eq!(
                query(&out, axis, &root, &mut s),
                Err(ObservedValueError::AdmissionRefused)
            );
            assert_eq!(
                out.retire_observed(&mut s, site()),
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
}
#[test]
fn constructing_and_explicitly_retiring_cannot_renew_cumulative_work_or_copy() {
    let m = fixture();
    let (baseline, _) = build_events(&m);
    for copy in [false, true] {
        let mut o = Observer::default();
        if copy {
            o.byte_cap = Some(baseline.total_copy.get() + 1);
        } else {
            o.work_cap = Some(baseline.total_work.get() + 1);
        }
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        m.nominal_type_reachability_observed(&mut s, site())
            .unwrap()
            .retire_observed(&mut s, site())
            .unwrap();
        assert!(matches!(
            m.nominal_type_reachability_observed(&mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        ));
        assert!(s.first_refusal().is_some());
    }
}
#[test]
fn repeated_queries_spend_the_same_original_cumulative_work_and_copy() {
    let m = fixture();
    let root = Ty::Struct(StructId::new(70));
    let mut baseline = Observer::default();
    let work_total = baseline.total_work.clone();
    let copy_total = baseline.total_copy.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let out = m
        .nominal_type_reachability_observed(&mut s, site())
        .unwrap();
    assert!(out.contains_handle_observed(&root, &mut s, site()).unwrap());
    let work_end = work_total.get();
    let copy_end = copy_total.get();
    out.retire_observed(&mut s, site()).unwrap();
    for copy in [false, true] {
        let mut o = Observer::default();
        if copy {
            o.byte_cap = Some(copy_end + 1);
        } else {
            o.work_cap = Some(work_end + 1);
        }
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let out = m
            .nominal_type_reachability_observed(&mut s, site())
            .unwrap();
        assert!(out.contains_handle_observed(&root, &mut s, site()).unwrap());
        assert_eq!(
            out.contains_handle_observed(&root, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(
            out.retire_observed(&mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
    }
}
#[test]
fn zero_interpreter_fuel_original_site_and_preexisting_refusal_are_preserved() {
    let m = fixture();
    let mut options = InterpretOptions::default();
    options.fuel = 0;
    let mut o = Observer::default();
    let mut s = ObservedSession::new(options, &mut o);
    let out = m
        .nominal_type_reachability_observed(&mut s, site())
        .unwrap();
    for axis in AXES {
        query(&out, axis, &array(0), &mut s).unwrap();
    }
    out.retire_observed(&mut s, site()).unwrap();
    assert_eq!(s.remaining_fuel(), 0);
    drop(s);
    assert!(o.events.iter().all(|e| e.site == site()));
    let mut o = Observer {
        stop: Some(1),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert!(
        s.admit(ExecutionProgress {
            phase: ExecutionPhase::Validation,
            site: site(),
            work: 1,
            copy_bytes: 0
        })
        .is_err()
    );
    assert!(matches!(
        m.nominal_type_reachability_observed(&mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    ));
    assert_eq!(
        s.first_refusal().unwrap().cause,
        "original nominal graph stop"
    );
}
#[test]
fn checked_graph_arithmetic_and_final_full_summary_publication_never_accept_on_refusal() {
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    assert_eq!(
        work.add(usize::MAX, 1),
        Err(ObservedValueError::CapacityOverflow)
    );
    let mut index = usize::MAX;
    assert_eq!(
        work.next(&mut index),
        Err(ObservedValueError::CapacityOverflow)
    );
    assert_eq!(index, usize::MAX);
    drop(work);
    drop(s);
    let m = fixture();
    let (baseline, bound) = build_events(&m);
    assert_eq!(
        baseline.events[bound - 1].copy_bytes,
        size_of::<ObservedNominalTypeReachability<'_>>()
    );
    let mut o = Observer {
        stop: Some(bound),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert!(matches!(
        m.nominal_type_reachability_observed(&mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    ));
    drop(s);
    assert_eq!(&o.events[..bound], &baseline.events[..bound]);
    assert!(
        o.events[bound..]
            .iter()
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
    assert!(o.events.len() > bound + 16);
}
