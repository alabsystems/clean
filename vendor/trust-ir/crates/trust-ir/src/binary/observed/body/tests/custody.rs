// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn complete_returned_reason_retirement_has_a_nonempty_cleanup_prefix_and_exact_terminal_receipt() {
    let m = ambiguous();
    let base = run(&m, f());
    let tail = &base.observer.events[base.split..];
    let (last, cleanup) = tail.split_last().unwrap();
    assert!(!cleanup.is_empty());
    assert!(
        cleanup
            .iter()
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement && e.site == site())
    );
    assert!(cleanup.iter().any(|e| e.copy_bytes > 0));
    assert_eq!(
        *last,
        ExecutionProgress {
            phase: ExecutionPhase::Publication,
            site: site(),
            work: 0,
            copy_bytes: 0
        }
    );
}
#[test]
fn every_returned_reason_cleanup_cut_still_consumes_every_actual_record_and_byte() {
    let m = ambiguous();
    let base = run(&m, f());
    for cut in base.split + 1..=base.observer.events.len() {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let actual = call(&m, f(), &mut s).unwrap();
        assert_eq!(
            Module::retire_function_body_digest_result_observed(actual, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(
            s.first_refusal().unwrap().progress,
            base.observer.events[cut - 1]
        );
        drop(s);
        let expected = if cut == base.observer.events.len() {
            &base.observer.events[..]
        } else {
            &base.observer.events[..base.observer.events.len() - 1]
        };
        assert_eq!(o.events, expected);
    }
}
#[test]
fn complete_typed_error_is_held_across_later_cleanup_refusal_of_owned_partial_text() {
    let mut o = Observer::default();
    let marker = Rc::clone(&o.marker);
    let control = Rc::clone(&o.dynamic_stop);
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut out = Output::counter(&mut s, site()).unwrap();
    let mut state = State::new();
    state::append(&mut state.reason, "owned partial λ", &mut out).unwrap();
    control.set(Some(marker.get() + 1));
    // The exact production finish route consumes already-owned state under
    // this SAME original session, without re-creating any ledger or owner.
    assert_eq!(
        finish(state, Err(ObservedValueError::InvalidRange), out),
        Err(ObservedValueError::InvalidRange)
    );
    assert_eq!(s.first_refusal().unwrap().cause, "body stop");
}
#[test]
fn a_nonzero_scratch_copy_can_be_the_original_first_refusal_without_a_digest() {
    let m = module();
    let base = run(&m, f());
    let at = base
        .events()
        .iter()
        .position(|e| e.phase == ExecutionPhase::ScratchRetirement && e.copy_bytes > 0)
        .unwrap();
    let cap: usize = base.events()[..=at]
        .iter()
        .map(|e| e.copy_bytes)
        .sum::<usize>()
        - 1;
    let mut o = Observer {
        copy_cap: Some(cap),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(
        call(&m, f(), &mut s),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(s.first_refusal().unwrap().progress, base.events()[at]);
    assert_eq!(s.first_refusal().unwrap().cause, "copy");
}
#[test]
fn final_result_publication_cut_retires_the_entire_held_semantic_reason() {
    let m = same_glue();
    let base = run(&m, f());
    let mut o = Observer {
        stop: Some(base.split),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(
        call(&m, f(), &mut s),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        s.first_refusal().unwrap().progress.phase,
        ExecutionPhase::Publication
    );
    drop(s);
    assert_eq!(&o.events[..base.split], base.events());
    assert!(!o.events[base.split..].is_empty());
    assert!(
        o.events[base.split..]
            .iter()
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
}
#[test]
fn complete_plan_roots_current_and_partial_strings_are_consumed_from_actual_state() {
    let m = drops();
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut out = Output::counter(&mut s, site()).unwrap();
    let mut state = State::new();
    state.run(&m, f(), &mut out).unwrap();
    assert!(state.digest.is_some());
    assert!(!state.plan.blocks.is_empty());
    assert!(!state.rows.is_empty());
    state.first_text = out
        .body_type_text(&Ty::Tuple(vec![Ty::handle("λ", "runtime::H"), Ty::I64]))
        .unwrap();
    assert!(!state.first_text.is_empty());
    state.retire_scratch(&mut out);
    assert!(state.rows.is_empty());
    assert_eq!(state.rows.capacity(), 0);
    assert!(state.roots.is_empty());
    assert!(state.frames.is_empty());
    assert!(state.current.is_none());
    assert!(state.target.is_none());
    assert!(state.first_text.is_empty());
    assert_eq!(state.first_text.capacity(), 0);
    assert!(state.plan.blocks.is_empty());
    state.retire_output(&mut out);
    assert!(state.digest.is_none());
    assert!(state.reason.is_empty());
}
#[test]
fn returned_digest_and_reason_cleanup_preserve_a_preexisting_original_cause() {
    for result in [Ok(ProofDigest::zero()), Err("full reason λ".repeat(1000))] {
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
        let cause = s.first_refusal().unwrap().progress;
        assert_eq!(
            Module::retire_function_body_digest_result_observed(result, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(s.first_refusal().unwrap().progress, cause);
        drop(s);
        assert!(o.events.len() > 1);
        assert!(
            o.events[1..]
                .iter()
                .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
        );
    }
}
#[test]
fn invalid_inline_depth_uses_owned_borrowed_frames_and_exact_original_reason_without_a_cap() {
    let mut m = module();
    let mut ty = Ty::Error;
    for _ in 0..1024 {
        ty = Ty::Tuple(vec![Ty::I64, ty]);
    }
    m.functions[0].blocks[0].params.push((v(400), ty));
    run(&m, f());
    assert!(
        m.function_body_digest(f())
            .unwrap_err()
            .contains("Ty::Error")
    );
    let ty = m.functions[0].blocks[0].params.pop().unwrap().1;
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    ty.retire_observed(&mut s, site()).unwrap();
}
