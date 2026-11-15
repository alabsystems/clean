// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn every_sort_callback_including_false_result_and_cleanup_refuses_without_boolean() {
    let a = sorts().pop().unwrap();
    for b in [a.clone(), ClauseSort::Int] {
        let (_, base) = sort(&a, &b);
        for stop in 1..=base.events.len() {
            let mut o = Observer {
                stop: Some(stop),
                ..Observer::default()
            };
            let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
            assert_eq!(
                a.structurally_eq_observed(&b, &mut s, site()),
                Err(ObservedValueError::AdmissionRefused)
            );
            assert_eq!(s.first_refusal().unwrap().progress, base.events[stop - 1]);
            assert!(
                o.events
                    .iter()
                    .skip(stop)
                    .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
            );
        }
    }
}
#[test]
fn every_formula_callback_refuses_including_nested_sort_publication_and_outer_false() {
    let a = sample();
    let mut different = a.clone();
    different.bindings[1].1.place = ClausePlace::WorldPost;
    for b in [a.clone(), different] {
        let (_, base) = formula(&a, &b);
        for stop in 1..=base.events.len() {
            let mut o = Observer {
                stop: Some(stop),
                ..Observer::default()
            };
            let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
            assert_eq!(
                a.structurally_eq_observed(&b, &mut s, site()),
                Err(ObservedValueError::AdmissionRefused)
            );
            assert_eq!(s.first_refusal().unwrap().cause, "original equality stop");
            assert_eq!(s.first_refusal().unwrap().progress, base.events[stop - 1]);
            assert!(
                o.events
                    .iter()
                    .skip(stop)
                    .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
            );
        }
    }
}
#[test]
fn actual_bounded_name_comparison_can_stop_interior_without_reaching_tail() {
    let a = ClauseSort::Datatype {
        name: "λ".repeat(2000) + "TAIL",
        constructors: vec![],
    };
    let base = raw_trace(&a, &a);
    let stop = base
        .events
        .iter()
        .enumerate()
        .filter(|(_, e)| {
            e.phase == ExecutionPhase::Validation && e.work == 1024 && e.copy_bytes == 0
        })
        .nth(1)
        .unwrap()
        .0
        + 1;
    let mut o = Observer {
        stop: Some(stop),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = State::default();
    assert_eq!(
        state.sorts(&a, &a, &mut w),
        Err(ObservedValueError::AdmissionRefused)
    );
    state.retire(&mut w);
    assert_eq!(state.tasks.capacity(), 0);
    assert_eq!(
        w.session.first_refusal().unwrap().progress,
        base.events[stop - 1]
    );
}
#[test]
fn scratch_reserve_and_transport_are_distinct_and_both_keep_retirable_storage() {
    let a = ClauseSort::Bool;
    let base = raw_trace(&a, &a);
    let cuts = base
        .events
        .iter()
        .enumerate()
        .filter(|(_, e)| {
            e.phase == ExecutionPhase::Validation
                && e.work == 1
                && e.copy_bytes == size_of::<Pair<'_>>()
        })
        .map(|(i, _)| i + 1)
        .collect::<Vec<_>>();
    // The first matches are descriptor, first allocation and transport. Later
    // Option<Pair> pop headers can have the same layout; they do not change
    // which two actual operations this custody control must refuse.
    assert!(cuts.len() >= 3);
    assert_eq!(cuts[0], 1);
    assert_eq!(cuts[1] + 1, cuts[2]);
    for (index, stop) in [cuts[1], cuts[2]].into_iter().enumerate() {
        let mut o = Observer {
            stop: Some(stop),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut w = Work {
            session: &mut s,
            site: site(),
        };
        let mut state = State::default();
        assert_eq!(
            state.sorts(&a, &a, &mut w),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert!(state.tasks.is_empty());
        assert_eq!(state.tasks.capacity() == 0, index == 0);
        state.retire(&mut w);
        assert_eq!(state.tasks.capacity(), 0);
    }
}
#[test]
fn refusal_during_retirement_preserves_first_cause_and_drains_borrowed_pending_tail() {
    let a = ClauseSort::Bool;
    let arm = Rc::new(Cell::new(false));
    let mut o = Observer {
        cleanup: Some(arm.clone()),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = State {
        tasks: vec![Pair::Sort(&a, &a), Pair::Sort(&a, &a)],
    };
    arm.set(true);
    state.retire(&mut w);
    assert_eq!(state.tasks.capacity(), 0);
    assert_eq!(
        w.finish(Ok(true)),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(w.session.first_refusal().unwrap().cause, "cleanup");
}
#[test]
fn work_copy_and_sticky_stop_cumulate_in_the_original_session_across_equalities() {
    let a = sample();
    let (_, base) = formula(&a, &a);
    for bytes in [false, true] {
        let mut o = Observer {
            work_cap: (!bytes).then_some(base.work),
            byte_cap: bytes.then_some(base.bytes),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert!(a.structurally_eq_observed(&a, &mut s, site()).unwrap());
        assert_eq!(
            a.structurally_eq_observed(&a, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        let first = s.first_refusal().unwrap().progress;
        assert_eq!(
            a.structurally_eq_observed(&a, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(s.first_refusal().unwrap().progress, first);
        assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
    }
}
#[test]
fn first_header_refusal_prevents_all_walks_and_exact_instruction_site_preserves_zero_fuel() {
    let a = sample();
    let mut o = Observer {
        byte_cap: Some(0),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(
        a.structurally_eq_observed(&a, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(o.events.len(), 1);
    let exact = ExecutionSite::Instruction(InstructionSite {
        function: FuncId::new(1),
        block: BlockId::new(2),
        instruction_index: usize::MAX,
    });
    let mut o = Observer::default();
    let mut s = ObservedSession::new(
        InterpretOptions {
            fuel: 0,
            ..InterpretOptions::default()
        },
        &mut o,
    );
    assert!(a.structurally_eq_observed(&a, &mut s, exact).unwrap());
    assert_eq!(s.remaining_fuel(), 0);
    assert!(o.events.iter().all(|e| e.site == exact));
}
