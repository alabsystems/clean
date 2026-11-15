// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
fn bound(b: &NativeVerificationBundle) -> usize {
    let mut o = Observer::default();
    let c = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut st = State::default();
    st.run(b, &mut w).unwrap();
    let end = c.get();
    drain(&mut st, &mut w);
    end
}
#[test]
fn complete_actual_wire_child_batch_is_captured_before_next_parent_fee() {
    let b = bad();
    let expected = wire_expected(&b);
    let end = bound(&b);
    let mut found = false;
    for cut in 1..end {
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
        let result = st.run(&b, &mut w);
        if result.is_err()
            && st.batch == expected
            && st.errors == vec![E::UnsupportedSchemaVersion(u32::MAX)]
        {
            assert!(st.actual.is_none());
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
fn moved_wire_prefix_and_complete_remaining_batch_tail_stay_owned_together() {
    let b = bad();
    let expected = wire_expected(&b);
    let end = bound(&b);
    let mut found = false;
    for cut in 1..end {
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
        let result = st.run(&b, &mut w);
        if result.is_err()
            && st.batch.len() == 2
            && st.batch[0] == E::EmptyRequests
            && st.batch[1] == expected[1]
            && st.errors.len() == 2
        {
            assert_eq!(st.errors[1], expected[0]);
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
fn actual_computed_digest_is_retained_before_any_comparison_or_mismatch_transfer() {
    let b = clean();
    let expected = b.module.stable_digest();
    let end = bound(&b);
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
        let result = st.run(&b, &mut w);
        if result.is_err() && st.actual == Some(expected) {
            assert!(st.errors.is_empty() && st.pending.is_none());
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
fn complete_digest_mismatch_is_pending_before_output_reserve_or_transport() {
    let mut b = clean();
    b.trust_ir_module_digest = ProofDigest::sha256([77; 32]);
    let expected = E::TrustIrModuleDigestMismatch {
        expected: b.module.stable_digest(),
        actual: b.trust_ir_module_digest,
    };
    let end = bound(&b);
    let mut found = 0;
    for cut in 1..end {
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
        let result = st.run(&b, &mut w);
        if result.is_err() && st.pending == Some(expected.clone()) {
            assert!(st.errors.is_empty());
            found += 1;
            assert!(st.finish(result, &mut w).is_err());
            empty(&st);
        } else {
            drain(&mut st, &mut w);
        }
    }
    assert!(found >= 2);
}
#[test]
fn already_held_error_wins_cleanup_refusal_while_pending_prior_and_spare_tails_drain() {
    let mut batch = Vec::with_capacity(29);
    batch.push(E::TrustIrModuleHasNoWireIdentity {
        location: "whole raw λ\0".into(),
        construct: "raw",
    });
    let cap = batch.capacity();
    let mut st = State {
        batch,
        actual: Some(ProofDigest::sha256([9; 32])),
        pending: Some(E::EmptyRequests),
        errors: vec![E::EmptyRequests],
    };
    let mut o = Observer {
        stop: Some(1),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    assert_eq!(
        st.finish(Err(ObservedValueError::InvalidRange), &mut w),
        Err(ObservedValueError::InvalidRange)
    );
    empty(&st);
    drop(w);
    drop(s);
    assert!(
        o.events
            .iter()
            .any(|p| p.phase == ExecutionPhase::ScratchRetirement
                && p.copy_bytes == cap * size_of::<E>())
    );
}
#[test]
fn original_caller_retirement_keeps_healthy_zero_receipt_or_sticky_stop_and_source_exact() {
    for stopped in [false, true] {
        let b = bad();
        let before = b.module.clone();
        let arm = Rc::new(Cell::new(false));
        let mut o = Observer {
            arm: Some(arm.clone()),
            ..Observer::default()
        };
        let c = o.calls.clone();
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let rows = b.identity_prefix_errors_observed(&mut s, site()).unwrap();
        let end = c.get();
        arm.set(stopped);
        let result = retire_native_bundle_errors_observed(rows, &mut s, site());
        assert_eq!(result.is_err(), stopped);
        assert_eq!(b.module, before);
        drop(s);
        if stopped {
            assert!(
                o.events[end..]
                    .iter()
                    .all(|p| p.phase == ExecutionPhase::ScratchRetirement)
            );
        } else {
            let last = o.events.last().unwrap();
            assert_eq!(
                (last.phase, last.work, last.copy_bytes),
                (ExecutionPhase::Publication, 0, 0)
            );
            assert!(
                o.events[end..o.events.len() - 1]
                    .iter()
                    .all(|p| p.phase == ExecutionPhase::ScratchRetirement)
            );
        }
    }
}
