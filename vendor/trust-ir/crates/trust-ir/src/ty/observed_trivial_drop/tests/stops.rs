// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn every_actual_true_and_false_path_callback_refuses_with_the_original_cause() {
    let (ty, types) = mixed();
    for ty in [ty, Ty::Tuple(vec![Ty::Error, Ty::Array(TyId::new(0), 1)])] {
        let (_, base) = run(&ty, &types);
        for stop in 1..=base.events.len() {
            let mut o = Observer {
                stop: Some(stop),
                ..Observer::default()
            };
            let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
            assert_eq!(
                ty.is_trivially_droppable_observed(&types, &mut s, site()),
                Err(ObservedValueError::AdmissionRefused)
            );
            assert_eq!(s.first_refusal().unwrap().progress, base.events[stop - 1]);
            assert_eq!(
                s.first_refusal().unwrap().cause,
                "original drop-predicate stop"
            );
            drop(s);
            assert_eq!(&o.events[..stop], &base.events[..stop]);
            assert!(
                o.events[stop..]
                    .iter()
                    .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
            );
        }
    }
}
#[test]
fn work_and_copy_caps_accumulate_without_reset_between_queries() {
    let (ty, types) = mixed();
    let (_, base) = run(&ty, &types);
    for copy in [false, true] {
        let mut o = Observer {
            work_cap: (!copy).then_some(base.work),
            byte_cap: copy.then_some(base.bytes),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert!(
            ty.is_trivially_droppable_observed(&types, &mut s, site())
                .unwrap()
        );
        assert_eq!(
            ty.is_trivially_droppable_observed(&types, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        let first = s.first_refusal().unwrap().progress;
        assert_eq!(
            Ty::Unit.is_trivially_droppable_observed(&[], &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(s.first_refusal().unwrap().progress, first);
    }
}
#[test]
fn zero_fuel_keeps_the_exact_instruction_site_across_walk_and_cleanup() {
    let (ty, types) = mixed();
    let exact = ExecutionSite::Instruction(InstructionSite {
        function: FuncId::new(91),
        block: BlockId::new(23),
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
    assert!(
        ty.is_trivially_droppable_observed(&types, &mut s, exact)
            .unwrap()
    );
    assert_eq!(s.remaining_fuel(), 0);
    drop(s);
    assert!(o.events.iter().all(|e| e.site == exact));
}
#[test]
fn final_publication_can_refuse_both_computed_booleans_after_complete_cleanup() {
    for ty in [Ty::Tuple(vec![Ty::U32]), Ty::Tuple(vec![Ty::Error])] {
        let (_, base) = run(&ty, &[]);
        let stop = base.events.len();
        let mut o = Observer {
            stop: Some(stop),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert_eq!(
            ty.is_trivially_droppable_observed(&[], &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(s.first_refusal().unwrap().progress, base.events[stop - 1]);
        assert_eq!(
            s.first_refusal().unwrap().progress.phase,
            ExecutionPhase::Publication
        );
    }
}
#[test]
fn repeated_cleanup_refusal_preserves_the_first_stop_and_consumes_all_scratch() {
    let (ty, types) = mixed();
    let mut state = State::default();
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    assert!(state.run(&ty, &types, &mut w).unwrap());
    let begin = calls.get();
    w.drain(&mut state.stack);
    w.drain(&mut state.marks);
    let end = calls.get();
    drop(w);
    drop(s);
    for stop in begin + 1..=end {
        let mut state = State::default();
        let mut o = Observer {
            stop: Some(stop),
            cleanup_after: Some(stop),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut w = Work {
            session: &mut s,
            site: site(),
        };
        assert!(state.run(&ty, &types, &mut w).unwrap());
        w.drain(&mut state.stack);
        w.drain(&mut state.marks);
        assert_eq!(state.stack.capacity(), 0);
        assert_eq!(state.marks.capacity(), 0);
        assert_eq!(w.publication(), Err(ObservedValueError::AdmissionRefused));
        assert_eq!(
            w.session.first_refusal().unwrap().cause,
            "original drop-predicate stop"
        );
    }
}
