// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn plan_retirement_refusal_never_publishes_previously_found_true() {
    let inst = Inst::Return { values: ids(&[1]) };
    let mut o = Observer {
        stop_phase: Some(ExecutionPhase::ScratchRetirement),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(
        inst.uses_value_operand_observed(v(1), &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        s.first_refusal().unwrap().progress.phase,
        ExecutionPhase::ScratchRetirement
    );
    drop(s);
    assert!(
        o.events
            .iter()
            .all(|e| e.phase != ExecutionPhase::Publication)
    );
}
#[test]
fn final_true_or_false_publication_refusal_returns_no_boolean() {
    for needle in [v(1), v(99)] {
        let inst = Inst::Return {
            values: ids(&[1, 2]),
        };
        let (_, base) = run(&inst, needle);
        let cut = base.events.len();
        let mut o = Observer {
            stop_at: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert_eq!(
            inst.uses_value_operand_observed(needle, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        drop(s);
        assert_eq!(o.events, base.events);
    }
}
#[test]
fn refused_actual_walk_retires_borrowed_plan_without_mutating_original_instruction() {
    let inst = switch(false, 3);
    let old = ordinary(&inst);
    let mut o = Observer {
        stop_at: Some(5),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(
        inst.uses_value_operand_observed(v(99), &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(s.first_refusal().unwrap().cause, "original stop");
    drop(s);
    assert_eq!(ordinary(&inst), old);
    assert!(
        o.events[5..]
            .iter()
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
}
#[test]
fn exact_query_allocates_no_full_operand_output_and_keeps_original_projection() {
    let inst = Inst::Return {
        values: ids(&[1, 2, 3]),
    };
    let (_, o) = run(&inst, v(3));
    assert_eq!(
        o.events
            .iter()
            .filter(|e| e.phase == ExecutionPhase::Publication)
            .count(),
        1
    );
    assert_eq!(o.events.last().unwrap().copy_bytes, size_of::<bool>());
    assert_eq!(ordinary(&inst), ids(&[1, 2, 3]));
}
