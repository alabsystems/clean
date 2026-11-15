// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
fn cut_all(a: &Module, ta: &Ty, b: &Module, tb: &Ty) {
    let reference = baseline(a, ta, b, tb);
    let terminal = reference
        .events
        .iter()
        .rposition(|e| e.phase == ExecutionPhase::Publication)
        .unwrap()
        + 1;
    for cut in 1..=terminal {
        let mut observer = Observer {
            stop: Some(cut),
            cleanup_fails: true,
            ..Observer::default()
        };
        {
            let mut session = ObservedSession::new(options(), &mut observer);
            assert!(matches!(
                ty_equivalence_across_observed(a, ta, b, tb, &mut session, site()),
                Err(ObservedValueError::AdmissionRefused)
            ));
            let first = session.first_refusal().unwrap();
            assert_eq!(first.cause, "first stop");
            assert_eq!(first.progress, reference.events[cut - 1]);
            assert_eq!(session.remaining_fuel(), 0);
            assert!(ty_equivalence_across_observed(a, ta, b, tb, &mut session, site()).is_err());
        }
        assert_eq!(&observer.events[..cut], &reference.events[..cut]);
        assert!(
            observer.events[cut..]
                .iter()
                .all(|e| e.phase == ExecutionPhase::ScratchRetirement && e.site == site())
        );
    }
}
#[test]
fn every_dynamic_owned_conflict_copy_and_retirement_cut_keeps_first_cause() {
    let (a, ta, b, tb) = conflict_pair();
    cut_all(&a, &ta, &b, &tb);
}
#[test]
fn every_dynamic_enum_scratch_and_final_publication_cut_is_terminal() {
    let (a, ta, b, tb) = enum_pair();
    cut_all(&a, &ta, &b, &tb);
}
#[test]
fn every_dynamic_cyclic_and_set_any_cut_keeps_original_owner_and_site() {
    let (ca, cta, cb, ctb) = pred_pair(
        vec![Pred::Conj(vec![PredId::new(0)])],
        0,
        vec![Pred::Top, Pred::Conj(vec![PredId::new(1)])],
        1,
    );
    cut_all(&ca, &cta, &cb, &ctb);

    let (a, ta, b, tb) = pred_pair(
        vec![
            Pred::Top,
            Pred::NonZero,
            Pred::Conj(vec![PredId::new(0), PredId::new(1)]),
        ],
        2,
        vec![
            Pred::NonZero,
            Pred::Top,
            Pred::Conj(vec![PredId::new(0), PredId::new(1)]),
        ],
        2,
    );
    cut_all(&a, &ta, &b, &tb);
}
#[test]
fn partial_conflict_clone_scratch_active_and_diagnostic_headers_are_all_consumed() {
    let (a, ta, b, tb) = conflict_pair();
    let reference = baseline(&a, &ta, &b, &tb);
    let terminal = reference
        .events
        .iter()
        .rposition(|e| e.phase == ExecutionPhase::Publication)
        .unwrap()
        + 1;
    for cut in 2..terminal {
        let mut observer = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(options(), &mut observer);
        let mut w = Work {
            session: &mut session,
            site: site(),
        };
        // Offset the entry header so this private machine trace joins actual entry.
        w.admit(
            1,
            size_of::<State<'_>>() + size_of::<Work<'_, '_, Observer>>(),
        )
        .unwrap();
        let mut state = State::new();
        let result = engine::run(&mut state, &a, &ta, &b, &tb, &mut w);
        state.scratch(&mut w);
        state.owned(&mut w);
        assert_state_empty(&state);
        if result.is_ok() {
            assert!(w.session.first_refusal().is_some());
        }
        assert_eq!(w.session.first_refusal().unwrap().cause, "first stop");
    }
}
#[test]
fn exact_measured_work_and_copy_succeed_and_one_short_refuses_publication() {
    let (a, ta, b, tb) = structure_pair();
    let measured = baseline(&a, &ta, &b, &tb);
    for (work_cap, copy_cap, success) in [
        (Some(measured.work), Some(measured.bytes), true),
        (Some(measured.work - 1), None, false),
        (None, Some(measured.bytes - 1), false),
    ] {
        let mut observer = Observer {
            work_cap,
            copy_cap,
            ..Observer::default()
        };
        let mut session = ObservedSession::new(options(), &mut observer);
        let answer = ty_equivalence_across_observed(&a, &ta, &b, &tb, &mut session, site());
        assert_eq!(answer.is_ok(), success);
        if success {
            assert_eq!(answer.unwrap(), TyEquivalence::Equal);
        } else {
            assert!(session.first_refusal().is_some());
        }
    }
}
#[test]
fn repeated_calls_debit_the_same_cumulative_original_owner() {
    let (a, ta, b, tb) = structure_pair();
    let measured = baseline(&a, &ta, &b, &tb);
    let mut observer = Observer {
        work_cap: Some(measured.work),
        copy_cap: Some(measured.bytes),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(options(), &mut observer);
    assert_eq!(
        ty_equivalence_across_observed(&a, &ta, &b, &tb, &mut session, site()).unwrap(),
        TyEquivalence::Equal
    );
    assert!(matches!(
        ty_equivalence_across_observed(&a, &ta, &b, &tb, &mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    ));
    assert_eq!(session.first_refusal().unwrap().cause, "work");
    assert_eq!(session.remaining_fuel(), 0);
}
#[test]
fn zero_work_is_not_free_setup_and_sticky_session_never_resumes() {
    let m = Module::new("zero");
    let mut observer = Observer {
        work_cap: Some(0),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(options(), &mut observer);
    for _ in 0..2 {
        assert!(
            ty_equivalence_across_observed(&m, &Ty::Bool, &m, &Ty::Bool, &mut session, site())
                .is_err()
        );
    }
    assert_eq!(session.first_refusal().unwrap().cause, "work");
    drop(session);
    assert_eq!(observer.events.len(), 1);
}
#[test]
fn final_publication_withholds_complete_owned_conflict_and_boolean_projection() {
    let (a, ta, b, tb) = conflict_pair();
    let reference = baseline(&a, &ta, &b, &tb);
    let cut = reference
        .events
        .iter()
        .rposition(|e| e.phase == ExecutionPhase::Publication)
        .unwrap()
        + 1;
    let mut observer = Observer {
        stop: Some(cut),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(options(), &mut observer);
    assert!(ty_structurally_eq_across_observed(&a, &ta, &b, &tb, &mut session, site()).is_err());
    assert_eq!(session.first_refusal().unwrap().cause, "first stop");
    drop(session);
    assert!(
        observer.events[cut..]
            .iter()
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
    assert!(!observer.events[cut..].is_empty());
}
#[test]
fn returned_conflict_is_consumed_by_original_owner_after_live_and_sticky_return() {
    for stopped in [false, true] {
        let (a, ta, b, tb) = conflict_pair();
        let reference = baseline(&a, &ta, &b, &tb);
        let publication = reference
            .events
            .iter()
            .rposition(|e| e.phase == ExecutionPhase::Publication)
            .unwrap()
            + 1;
        let mut observer = Observer {
            stop: stopped.then_some(publication + 1),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(options(), &mut observer);
        let TyEquivalence::OriginConflict(c) =
            ty_equivalence_across_observed(&a, &ta, &b, &tb, &mut session, site()).unwrap()
        else {
            panic!()
        };
        assert_eq!(c.retire_observed(&mut session, site()).is_ok(), !stopped);
        assert_eq!(session.first_refusal().is_some(), stopped);
    }
}

#[test]
fn caller_consumes_returned_conflict_and_owned_inline_inputs_in_the_same_session() {
    let (a, ta, b, tb) = conflict_pair();
    let ta = Ty::Tuple(vec![
        Ty::Ref(Box::new(Ty::Bool)),
        Ty::Dialect(Box::new(DialectTy::new("namespace λ", "leaf", 7))),
        ta,
    ]);
    let tb = Ty::Tuple(vec![
        Ty::Ref(Box::new(Ty::Bool)),
        Ty::Dialect(Box::new(DialectTy::new("namespace λ", "leaf", 7))),
        tb,
    ]);
    let expected = ty_equivalence_across(&a, &ta, &b, &tb);
    let mut observer = Observer::default();
    {
        let mut session = ObservedSession::new(options(), &mut observer);
        let result =
            ty_equivalence_across_observed(&a, &ta, &b, &tb, &mut session, site()).unwrap();
        assert_eq!(result, expected);
        let TyEquivalence::OriginConflict(conflict) = result else {
            panic!()
        };
        conflict.retire_observed(&mut session, site()).unwrap();
        ta.retire_observed(&mut session, site()).unwrap();
        tb.retire_observed(&mut session, site()).unwrap();
        assert!(session.first_refusal().is_none());
        assert_eq!(session.remaining_fuel(), 0);
    }
    assert!(observer.events.iter().all(|event| event.site == site()));
    assert_eq!(
        observer.events.last().unwrap().phase,
        ExecutionPhase::Publication
    );
    // The borrowed module tables remain caller-owned; no whole-module cleanup claim.
}
