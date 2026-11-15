// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

#![allow(
    clippy::drop_non_drop,
    clippy::field_reassign_with_default,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn pending_complete_location_is_held_before_vector_allocation_or_transport() {
    let b = fixture();
    let f = &b.module.functions[0];
    let block = &f.blocks[0];
    let expected = format!("function '{}' bb{} #0", f.name, block.id.index());
    let mut baseline = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = State::default();
    state.location(f, block, 0, &mut w).unwrap();
    drain(&mut state, &mut w);
    let mut found = 0;
    for cut in 1..=baseline.events.len() {
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
        let result = st.location(f, block, 0, &mut w);
        if matches!(&st.pending,Some(E::RustReferenceAsPermissionBorrow{location}) if location==&expected)
        {
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
fn partial_raw_function_label_remains_owned_until_interrupted_finish() {
    let b = fixture();
    let mut baseline = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = State::default();
    state
        .location(
            &b.module.functions[0],
            &b.module.functions[0].blocks[0],
            0,
            &mut w,
        )
        .unwrap();
    drain(&mut state, &mut w);
    let mut found = false;
    for cut in 1..=baseline.events.len() {
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
        let result = st.location(
            &b.module.functions[0],
            &b.module.functions[0].blocks[0],
            0,
            &mut w,
        );
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
fn prior_error_rows_and_whole_pending_row_are_consumed_after_later_failure() {
    let b = fixture();
    let mut found = false;
    let (_, base, end) = observed(&b, Rule::Reference);
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
        w.admit(1, size_of::<State>() + size_of::<Work<'_, '_, Observer>>())
            .unwrap_or(());
        let result = state_run(&mut st, &b, Rule::Reference, &mut w);
        if result.is_err() && st.pending.is_some() && !st.errors.is_empty() {
            found = true;
            assert!(st.finish(result, &mut w).is_err());
            empty(&st);
            break;
        }
        drain(&mut st, &mut w);
    }
    assert!(found);
    assert!(base.events.len() >= end);
}
#[test]
fn cleanup_refusal_cannot_replace_an_already_held_operational_error() {
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
        text: "full raw label".repeat(500),
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
fn successful_owned_diagnostics_require_same_session_caller_retirement() {
    let b = fixture();
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let rows = b
        .reference_spelling_errors_observed(&mut s, site())
        .unwrap();
    let bound = calls.get();
    assert_eq!(rows.len(), 18);
    retire_native_bundle_errors_observed(rows, &mut s, site()).unwrap();
    assert!(calls.get() > bound);
    drop(s);
    assert_eq!(o.events.last().unwrap().phase, ExecutionPhase::Publication);
    assert_eq!(o.events.last().unwrap().work, 0);
    assert!(
        o.events[bound..o.events.len() - 1]
            .iter()
            .all(|p| p.phase == ExecutionPhase::ScratchRetirement)
    );
}
#[test]
fn both_fixed_digest_diagnostics_stay_whole_before_later_transfer_refusal() {
    let b = fixture();
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut st = State::default();
    st.lineage(&b, &mut w).unwrap();
    assert_eq!(st.errors, ordinary(&b, Rule::Lineage));
    drain(&mut st, &mut w);
    empty(&st);
}
#[test]
fn original_nonzero_copy_stop_drains_all_partial_and_pending_stores() {
    let b = fixture();
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
    st.text = "held".repeat(400);
    st.pending = Some(E::RustReferenceAsPermissionBorrow {
        location: "whole".repeat(400),
    });
    st.errors = vec![E::SourceDigestNotInLineage(digest(9))];
    assert!(st.finish(Ok(()), &mut w).is_err());
    empty(&st);
    assert_eq!(w.session.first_refusal().unwrap().cause, "copy");
    drop(b);
}
#[test]
fn an_armed_interrupt_during_caller_disposal_still_keeps_first_cause() {
    let b = fixture();
    let arm = Rc::new(Cell::new(false));
    let mut o = Observer {
        arm: Some(arm.clone()),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let rows = b
        .reference_spelling_errors_observed(&mut s, site())
        .unwrap();
    arm.set(true);
    assert_eq!(
        retire_native_bundle_errors_observed(rows, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(s.first_refusal().unwrap().cause, "interrupt");
    arm.set(false);
    assert_eq!(
        run(&b, Rule::Lineage, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(s.first_refusal().unwrap().cause, "interrupt");
}
