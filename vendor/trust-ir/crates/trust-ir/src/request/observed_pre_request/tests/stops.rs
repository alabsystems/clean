// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn actual_complete_ordered_groups_accept_typed_cancellation_at_every_stage_boundary() {
    let b = bad();
    let (_, base, end) = observed(&b);
    let mut cuts = vec![1, 2, 3, end];
    for n in 1..64 {
        cuts.push(end * n / 64 + 1);
    }
    for (at, p) in base.events[..end].iter().enumerate() {
        if p.phase == ExecutionPhase::Publication {
            cuts.push(at + 1);
        }
    }
    cuts.sort_unstable();
    cuts.dedup();
    for cut in cuts {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert_eq!(
            b.pre_request_errors_observed(&mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(s.first_refusal().unwrap().progress, base.events[cut - 1]);
        drop(s);
        assert!(
            o.events[cut..]
                .iter()
                .all(|p| p.phase == ExecutionPhase::ScratchRetirement)
        );
    }
}
#[test]
fn changed_outer_batch_code_refuses_every_actual_prepare_capture_flush_and_tail_fee() {
    let b = clean();
    let mut base = Observer::default();
    let c = base.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut base);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut st = State::default();
    st.child(&b, Group::Serialization, &mut w).unwrap();
    let end = c.get();
    drain(&mut st, &mut w);
    drop(w);
    drop(s);
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
        assert!(st.child(&b, Group::Serialization, &mut w).is_err());
        drain(&mut st, &mut w);
        empty(&st);
        drop(w);
        drop(s);
        assert_eq!(&o.events[..cut], &base.events[..cut]);
        assert!(
            o.events[cut..]
                .iter()
                .all(|p| p.phase == ExecutionPhase::ScratchRetirement)
        );
    }
}
#[test]
fn original_work_and_copy_caps_cover_all_groups_and_original_caller_retirement() {
    let b = clean();
    let (_, base, _) = observed(&b);
    for copy in [false, true] {
        let mut o = if copy {
            Observer {
                byte_cap: Some(base.bytes),
                ..Observer::default()
            }
        } else {
            Observer {
                work_cap: Some(base.work),
                ..Observer::default()
            }
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let rows = b.pre_request_errors_observed(&mut s, site()).unwrap();
        retire_native_bundle_errors_observed(rows, &mut s, site()).unwrap();
        assert!(b.pre_request_errors_observed(&mut s, site()).is_err());
        assert_eq!(
            s.first_refusal().unwrap().cause,
            if copy { "copy" } else { "work" }
        );
    }
}
#[test]
fn interrupt_clear_never_reopens_any_later_original_group() {
    let b = clean();
    let arm = Rc::new(Cell::new(true));
    let mut o = Observer {
        arm: Some(arm.clone()),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert!(b.pre_request_errors_observed(&mut s, site()).is_err());
    arm.set(false);
    assert!(b.pre_request_errors_observed(&mut s, site()).is_err());
    assert_eq!(s.first_refusal().unwrap().cause, "interrupt");
}
#[test]
fn zero_instruction_fuel_keeps_every_actual_pre_request_validator_enabled() {
    let b = bad();
    let mut o = Observer::default();
    let mut s = ObservedSession::new(
        InterpretOptions {
            fuel: 0,
            ..InterpretOptions::default()
        },
        &mut o,
    );
    let rows = b.pre_request_errors_observed(&mut s, site()).unwrap();
    assert_eq!(rows, ordinary(&b));
    retire_native_bundle_errors_observed(rows, &mut s, site()).unwrap();
    assert_eq!(s.remaining_fuel(), 0);
}
#[test]
fn final_whole_group_publication_cut_hides_all_prior_and_later_diagnostics() {
    let b = bad();
    let (_, base, end) = observed(&b);
    assert_eq!(base.events[end - 1].copy_bytes, size_of::<Vec<E>>());
    let mut o = Observer {
        stop: Some(end),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert!(b.pre_request_errors_observed(&mut s, site()).is_err());
    drop(s);
    assert!(
        o.events[end..]
            .iter()
            .all(|p| p.phase == ExecutionPhase::ScratchRetirement)
    );
}
#[test]
fn cleanup_only_refusal_blocks_continuation_to_any_accepting_outer_result() {
    let b = clean();
    let mut o = Observer {
        retirement_stop: true,
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(
        b.pre_request_errors_observed(&mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(s.first_refusal().unwrap().cause, "retirement");
}
#[test]
fn unencodable_module_still_refuses_observationally_without_any_digest_hash() {
    let mut b = clean();
    b.module.types.push(Ty::Error);
    let (_, o, _) = observed(&b);
    assert!(
        !o.events
            .iter()
            .any(|p| p.phase == ExecutionPhase::CanonicalDigest)
    );
}
