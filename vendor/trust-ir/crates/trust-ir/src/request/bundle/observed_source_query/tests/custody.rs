// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
#[test]
fn actual_digest_is_held_before_the_next_comparison_callback() {
    let (a, mut b) = minted();
    b.provenance.producer_version.push_str("-changed");
    let expected = b.stable_digest();
    let mut base = Observer::default();
    let c = base.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut base);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut st = State::default();
    st.run(&a, &b, &mut w).unwrap();
    // Digest mismatch path ends with comparison then set(false): cut the
    // actual immediate callback after full child capture, not a size collision.
    let cut = c.get() - 1;
    st.retire_scratch(&mut w);
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
    let result = st.run(&a, &b, &mut w);
    assert_eq!(result, Err(ObservedValueError::AdmissionRefused));
    assert_eq!(st.digest, Some(expected));
    assert!(st.validation.is_none());
    assert!(st.finish(result, &mut w).is_err());
    empty(&st);
}
#[test]
fn complete_actual_invalid_validation_vector_is_owned_before_answer_branch() {
    let (a, b) = tampered();
    let expected = b.validate();
    let mut base = Observer::default();
    let c = base.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut base);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut st = State::default();
    st.run(&a, &b, &mut w).unwrap();
    // Whole validation return is followed only by the branch fee and the
    // answer-slot fee. Refuse the first, with the exact full payload held.
    let cut = c.get() - 1;
    st.retire_scratch(&mut w);
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
    let result = st.run(&a, &b, &mut w);
    assert_eq!(result, Err(ObservedValueError::AdmissionRefused));
    assert_eq!(st.validation, Some(expected));
    assert!(st.answer.is_none());
    assert!(st.finish(result, &mut w).is_err());
    empty(&st);
}
#[test]
fn already_held_local_error_wins_while_full_diagnostics_are_consumed_after_stop() {
    let mut rows = Vec::with_capacity(27);
    rows.push(
        NativeVerificationBundleError::TrustIrModuleHasNoWireIdentity {
            location: "whole raw λ\0尾".into(),
            construct: "raw",
        },
    );
    let cap = rows.capacity();
    let mut st = State {
        digest: Some(ProofDigest::sha256([1; 32])),
        validation: Some(Err(rows)),
        answer: Some(false),
    };
    let mut o = Observer {
        retirement_stop: true,
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
    assert!(
        o.events
            .iter()
            .any(|p| p.phase == ExecutionPhase::ScratchRetirement
                && p.copy_bytes == cap * size_of::<NativeVerificationBundleError>())
    );
}
#[test]
fn cleanup_only_stop_refuses_even_a_precomputed_true_answer() {
    let mut st = State {
        validation: Some(Ok(())),
        answer: Some(true),
        ..State::default()
    };
    let mut o = Observer {
        retirement_stop: true,
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    assert_eq!(
        st.finish(Ok(()), &mut w),
        Err(ObservedValueError::AdmissionRefused)
    );
    empty(&st);
}
#[test]
fn refusal_does_not_consume_or_replace_the_original_private_capability() {
    let (a, b) = minted();
    let pointer = super::super::super::Arc::as_ptr(&a.nonce);
    let before = b.clone();
    let mut o = Observer {
        stop: Some(1),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert!(
        a.authorizes_bundle_kernel_less_observed(&b, &mut s, site())
            .is_err()
    );
    assert_eq!(pointer, super::super::super::Arc::as_ptr(&a.nonce));
    assert_eq!(b, before);
    assert!(a.authorizes_bundle(&b));
}
