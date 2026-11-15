// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn actual_abi_detail_is_pending_before_the_next_sink_admission() {
    let mut a = abi();
    a.frontend.name = "x".repeat((1 << 20) + 1);
    let mut base = Observer::default();
    let c = base.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut base);
    let mut h = Refusals::default();
    let cut = {
        let mut out = Output::checker(&mut s, site(), &mut h).unwrap();
        let Err(detail) = out.abi_result(&a).unwrap() else {
            panic!("limit");
        };
        let cut = c.get() + 1;
        out.refuse_owned(WireRefusal::SignatureAbi {
            signature: 7,
            detail,
        })
        .unwrap();
        cut
    };
    h.retire(&mut s, site());
    drop(s);
    let mut o = Observer {
        stop: Some(cut),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut h = Refusals::default();
    {
        let mut out = Output::checker(&mut s, site(), &mut h).unwrap();
        let Err(detail) = out.abi_result(&a).unwrap() else {
            panic!("limit");
        };
        assert!(
            out.refuse_owned(WireRefusal::SignatureAbi {
                signature: 7,
                detail
            })
            .is_err()
        );
    }
    assert!(
        matches!(&h.pending,Some(WireRefusal::SignatureAbi{signature:7,detail})if detail=="ABI identity exceeds wire byte limit")
    );
    assert!(h.converted.is_none());
    h.retire(&mut s, site());
    empty(&h);
}
#[test]
fn converted_complete_projection_detail_stays_owned_before_its_rank_slot_fee() {
    let detail = "whole λ\0tail";
    let mut base = Observer::default();
    let c = base.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut base);
    let mut h = Refusals::default();
    let end = {
        let mut out = Output::checker(&mut s, site(), &mut h).unwrap();
        out.admit(detail.len(), detail.len() + size_of::<WireRefusal>())
            .unwrap();
        out.refuse_owned(WireRefusal::SignatureAbi {
            signature: 3,
            detail: detail.into(),
        })
        .unwrap();
        c.get()
    };
    h.retire(&mut s, site());
    drop(s);
    let mut found = false;
    for cut in 3..=end {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut h = Refusals::default();
        {
            let mut out = Output::checker(&mut s, site(), &mut h).unwrap();
            out.admit(detail.len(), detail.len() + size_of::<WireRefusal>())
                .unwrap();
            let _ = out.refuse_owned(WireRefusal::SignatureAbi {
                signature: 3,
                detail: detail.into(),
            });
        }
        if matches!(&h.converted,Some((3,BinaryProjectionError::SignatureAbiUnencodable{signature:3,detail:d}))if d==detail)
        {
            assert!(h.first[3].is_none());
            found = true;
        }
        h.retire(&mut s, site());
        empty(&h);
    }
    assert!(found);
}
#[test]
#[cfg(target_pointer_width = "64")]
fn partial_ranked_output_and_all_remaining_rank_slots_stay_held_until_drain() {
    let mut base = Observer::default();
    let c = base.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut base);
    let mut h = Refusals::default();
    let (start, end) = {
        let mut out = Output::checker(&mut s, site(), &mut h).unwrap();
        feed(&mut out).unwrap();
        let start = c.get();
        let rows = out.take_refusals().unwrap();
        let end = c.get();
        drop(out);
        retire_wire_image_refusals_observed(rows, &mut s, site()).unwrap();
        (start, end)
    };
    drop(s);
    let mut found = false;
    for cut in start + 1..end {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut h = Refusals::default();
        {
            let mut out = Output::checker(&mut s, site(), &mut h).unwrap();
            feed(&mut out).unwrap();
            assert!(out.take_refusals().is_err());
        }
        if !h.result.is_empty() {
            assert_eq!(
                h.result.len() + h.first.iter().filter(|v| v.is_some()).count(),
                6
            );
            assert_eq!(&h.result, &ordinary_feed()[..h.result.len()]);
            found = true;
        }
        h.retire(&mut s, site());
        empty(&h);
    }
    assert!(found);
}
#[test]
fn duplicate_owned_abi_refusal_is_consumed_without_replacing_first_raw_detail() {
    let mut h = Refusals::default();
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let rows = {
        let mut out = Output::checker(&mut s, site(), &mut h).unwrap();
        for (signature, detail) in [(9, "first λ\0"), (2, "last 尾\0")] {
            out.admit(detail.len(), detail.len() + size_of::<WireRefusal>())
                .unwrap();
            out.refuse_owned(WireRefusal::SignatureAbi {
                signature,
                detail: detail.into(),
            })
            .unwrap();
        }
        out.take_refusals().unwrap()
    };
    assert_eq!(
        rows,
        vec![BinaryProjectionError::SignatureAbiUnencodable {
            signature: 9,
            detail: "first λ\0".into()
        }]
    );
    retire_wire_image_refusals_observed(rows, &mut s, site()).unwrap();
}
#[test]
fn pending_converted_rank_and_spare_output_capacity_all_drain_after_same_stop() {
    let mut raw = String::with_capacity(1011);
    raw.push_str("pending");
    let rc = raw.capacity();
    let mut converted = String::with_capacity(2023);
    converted.push_str("converted");
    let cc = converted.capacity();
    let mut rows = Vec::with_capacity(37);
    rows.push(BinaryProjectionError::ProducerInternalType);
    rows.push(BinaryProjectionError::InvalidStorageGeometry(
        crate::StorageLayout::new(79, 8),
    ));
    let cap = rows.capacity();
    let mut h = Refusals {
        pending: Some(WireRefusal::SignatureAbi {
            signature: 0,
            detail: raw,
        }),
        converted: Some((
            3,
            BinaryProjectionError::SignatureAbiUnencodable {
                signature: 1,
                detail: converted,
            },
        )),
        result: rows,
        ..Refusals::default()
    };
    h.first[3] = Some(BinaryProjectionError::SignatureAbiUnencodable {
        signature: 2,
        detail: "rank full".into(),
    });
    let mut o = Observer {
        stop: Some(1),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    h.retire(&mut s, site());
    empty(&h);
    assert_eq!(s.first_refusal().unwrap().cause, "interior");
    drop(s);
    for n in [rc, cc, cap * size_of::<BinaryProjectionError>()] {
        assert!(
            o.events
                .iter()
                .any(|p| p.phase == ExecutionPhase::ScratchRetirement && p.copy_bytes == n)
        );
    }
}
#[test]
fn actual_builder_error_returns_with_full_original_scope_and_refusal_state_closed() {
    let mut m = Module::new("x".repeat(8193));
    m.files = vec!["λ".repeat(4001)];
    let mut o = Observer {
        byte_cap: Some(1024),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert!(m.wire_image_refusals_observed(&mut s, site()).is_err());
    let first = s.first_refusal().unwrap().progress;
    assert!(m.wire_image_refusals_observed(&mut s, site()).is_err());
    assert_eq!(s.first_refusal().unwrap().progress, first);
}
#[test]
fn original_healthy_caller_retirement_keeps_terminal_zero_publication() {
    let m = all();
    let mut o = Observer::default();
    let c = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let rows = m.wire_image_refusals_observed(&mut s, site()).unwrap();
    let end = c.get();
    retire_wire_image_refusals_observed(rows, &mut s, site()).unwrap();
    drop(s);
    assert!(
        o.events[end..o.events.len() - 1]
            .iter()
            .all(|p| p.phase == ExecutionPhase::ScratchRetirement)
    );
    let last = o.events.last().unwrap();
    assert_eq!(
        (last.phase, last.work, last.copy_bytes),
        (ExecutionPhase::Publication, 0, 0)
    );
}
#[test]
fn stopped_original_caller_retirement_does_not_transfer_or_renew_any_authority() {
    let m = all();
    let arm = Rc::new(Cell::new(false));
    let mut o = Observer {
        arm: Some(arm.clone()),
        ..Observer::default()
    };
    let c = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let rows = m.wire_image_refusals_observed(&mut s, site()).unwrap();
    let end = c.get();
    arm.set(true);
    assert!(retire_wire_image_refusals_observed(rows, &mut s, site()).is_err());
    arm.set(false);
    assert!(m.wire_image_refusals_observed(&mut s, site()).is_err());
    assert_eq!(s.first_refusal().unwrap().cause, "interrupt");
    drop(s);
    assert!(
        o.events[end..]
            .iter()
            .all(|p| p.phase == ExecutionPhase::ScratchRetirement)
    );
}
#[test]
fn full_actual_module_is_unchanged_on_success_and_interior_refusal() {
    let m = all();
    let before = m.clone();
    run(&m);
    assert_eq!(m, before);
    let mut o = Observer {
        stop: Some(33),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert!(m.wire_image_refusals_observed(&mut s, site()).is_err());
    assert_eq!(m, before);
}
#[test]
fn no_diagnostic_list_or_partial_image_is_published_as_a_digest() {
    let m = all();
    let (_, o, _) = run(&m);
    assert!(
        !o.events
            .iter()
            .any(|p| p.phase == ExecutionPhase::CanonicalDigest)
    );
    assert!(
        o.events
            .iter()
            .filter(|p| p.phase == ExecutionPhase::Publication)
            .all(|p| p.copy_bytes == 0)
    );
}
