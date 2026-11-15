// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn full_name_is_pending_before_error_vector_allocation_and_transfer() {
    let e = fixture();
    let a = &e.artifacts()[1];
    let mut base = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut base);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut st = State::default();
    st.named(&e, a, Fault::Invalid("digest"), &mut w).unwrap();
    drain(&mut st, &mut w);
    let mut found = 0;
    for cut in 1..=base.events.len() {
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
        let result = st.named(&e, a, Fault::Invalid("digest"), &mut w);
        if matches!(&st.pending,Some(E::InvalidEvidenceArtifact{name,..}) if name==&a.name) {
            assert!(result.is_err());
            assert!(st.errors.is_empty());
            assert_eq!(st.text.capacity(), 0);
            found += 1;
        }
        drain(&mut st, &mut w);
        empty(&st);
    }
    assert!(found >= 2);
}
#[test]
fn partial_multibyte_artifact_name_stays_owned_through_refused_finish() {
    let e = fixture();
    let a = &e.artifacts()[1];
    let mut base = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut base);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut st = State::default();
    st.named(&e, a, Fault::Duplicate, &mut w).unwrap();
    drain(&mut st, &mut w);
    let mut found = false;
    for cut in 1..=base.events.len() {
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
        let result = st.named(&e, a, Fault::Duplicate, &mut w);
        if result.is_err() && st.text.len() > 32 && st.pending.is_none() {
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
fn prior_error_rows_and_next_whole_name_survive_later_storage_refusal() {
    let e = fixture();
    let (_, _, end) = observed(&e);
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
        let result = st.run(&e, &mut w);
        if result.is_err() && !st.errors.is_empty() && st.pending.is_some() {
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
fn a_held_local_error_keeps_precedence_over_later_cleanup_refusal() {
    let mut o = Observer {
        stop: Some(1),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut st = State {
        text: "whole".repeat(400),
        ..State::default()
    };
    assert_eq!(
        st.finish(Err(ObservedValueError::InvalidRange), &mut w),
        Err(ObservedValueError::InvalidRange)
    );
    empty(&st);
    assert_eq!(w.session.first_refusal().unwrap().cause, "interior");
}
#[test]
fn nonzero_cleanup_copy_refusal_consumes_partial_pending_and_prior_errors() {
    let mut o = Observer {
        byte_cap: Some(0),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut st = State {
        text: "partial".repeat(300),
        pending: Some(E::DuplicateEvidenceArtifact {
            request: NativeRequestId::new(2),
            name: "pending".repeat(300),
        }),
        errors: vec![E::EmptyRequests],
    };
    assert!(st.finish(Ok(()), &mut w).is_err());
    empty(&st);
    assert_eq!(w.session.first_refusal().unwrap().cause, "copy");
}
#[test]
fn successful_caller_disposal_keeps_actual_healthy_terminal_receipt() {
    let e = fixture();
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let rows = e.artifact_errors_observed(&mut s, site()).unwrap();
    let bound = calls.get();
    retire_native_bundle_errors_observed(rows, &mut s, site()).unwrap();
    drop(s);
    assert!(o.events.len() > bound);
    assert!(
        o.events[bound..o.events.len() - 1]
            .iter()
            .all(|p| p.phase == ExecutionPhase::ScratchRetirement)
    );
    assert_eq!(o.events.last().unwrap().phase, ExecutionPhase::Publication);
    assert_eq!(o.events.last().unwrap().work, 0);
}
#[test]
fn refusal_during_successful_caller_disposal_remains_original_and_sticky() {
    let e = fixture();
    let arm = Rc::new(Cell::new(false));
    let mut o = Observer {
        arm: Some(arm.clone()),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let rows = e.artifact_errors_observed(&mut s, site()).unwrap();
    arm.set(true);
    assert_eq!(
        retire_native_bundle_errors_observed(rows, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    arm.set(false);
    assert_eq!(
        e.artifact_errors_observed(&mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(s.first_refusal().unwrap().cause, "interrupt");
}
#[test]
fn equal_length_name_comparison_charges_both_full_sides_before_late_difference() {
    let a = "λ".repeat(3000) + "a";
    let b = "λ".repeat(3000) + "b";
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    assert!(!w.equal(&a, &b).unwrap());
    drop(w);
    drop(s);
    assert!(o.work >= a.len() + b.len());
    assert!(o.events.iter().any(|p| p.work == 2048 && p.copy_bytes == 0));
}
