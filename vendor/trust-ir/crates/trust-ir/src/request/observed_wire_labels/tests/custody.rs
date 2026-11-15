// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn full_complete_location_pending_error_precedes_output_reserve_or_transfer() {
    let m = module();
    let row = node(900);
    let (_, _, end) = mapped(&m, &row);
    let mut found = 0;
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
        let mut r = Render::default();
        let result = r.map(&m, &row, &mut w);
        if result.is_err() && r.pending.is_some() {
            assert_eq!(r.pending, Some(ordinary(&m, &row)));
            assert!(r.text.is_empty() && r.errors.is_empty());
            found += 1;
        }
        drain(&mut r, &mut w);
        empty(&r);
    }
    assert!(found >= 2);
}
#[test]
fn actual_partial_raw_name_copy_stays_owned_across_later_original_fees() {
    let mut m = module();
    m.functions[0].name = "a".repeat(1024) + &"尾".repeat(800);
    let row = node(900);
    let (_, _, end) = mapped(&m, &row);
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
        let mut r = Render::default();
        let result = r.map(&m, &row, &mut w);
        if result.is_err() && r.text == "function '".to_owned() + &"a".repeat(1024) {
            assert!(r.pending.is_none() && r.errors.is_empty());
            found = true;
            drain(&mut r, &mut w);
            empty(&r);
            break;
        }
        drain(&mut r, &mut w);
    }
    assert!(found);
}
#[test]
fn actual_full_child_rows_are_captured_before_the_first_parent_mapping_fee() {
    let b = actual();
    let mut base = Observer::default();
    let c = base.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut base);
    let mut st = State::default();
    let bound = {
        let mut w = Work {
            session: &mut s,
            site: site(),
        };
        st.run(&b, &mut w).unwrap();
        let n = c.get();
        st.retire_scratch(&mut w);
        drain(&mut st.render, &mut w);
        n
    };
    drop(s);
    let mut found = false;
    for cut in 1..bound {
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
            && st.rows == b.module.wire_image_refusals()
            && st.render.errors.is_empty()
            && st.render.text.is_empty()
            && st.render.pending.is_none()
        {
            found = true;
            assert!(st.finish(result, &mut w).is_err());
            assert_eq!(st.rows.capacity(), 0);
            empty(&st.render);
            break;
        }
        st.retire_scratch(&mut w);
        drain(&mut st.render, &mut w);
    }
    assert!(found);
}
#[test]
fn held_local_error_keeps_precedence_while_full_raw_and_rendered_stores_drain() {
    let mut raw = Vec::with_capacity(31);
    raw.push(BinaryProjectionError::SignatureAbiUnencodable {
        signature: 7,
        detail: "raw whole λ\0".into(),
    });
    let cap = raw.capacity();
    let mut text = String::with_capacity(2011);
    text.push_str("partial");
    let tc = text.capacity();
    let mut st = State {
        rows: raw,
        render: Render {
            text,
            pending: Some(E::TrustIrModuleHasNoWireIdentity {
                location: "full pending".into(),
                construct: "raw",
            }),
            errors: vec![E::EmptyRequests],
        },
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
    assert_eq!(st.rows.capacity(), 0);
    empty(&st.render);
    drop(w);
    drop(s);
    for n in [cap * size_of::<BinaryProjectionError>(), tc] {
        assert!(
            o.events
                .iter()
                .any(|p| p.phase == ExecutionPhase::ScratchRetirement && p.copy_bytes == n)
        );
    }
}
#[test]
fn healthy_caller_cleanup_has_zero_publication_and_source_is_not_mutated() {
    let b = actual();
    let before = b.module.clone();
    let mut o = Observer::default();
    let c = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let rows = b.wire_identity_errors_observed(&mut s, site()).unwrap();
    let end = c.get();
    retire_native_bundle_errors_observed(rows, &mut s, site()).unwrap();
    assert_eq!(b.module, before);
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
fn stopped_caller_disposal_drains_without_renewing_or_publishing_result() {
    let b = actual();
    let arm = Rc::new(Cell::new(false));
    let mut o = Observer {
        arm: Some(arm.clone()),
        ..Observer::default()
    };
    let c = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let rows = b.wire_identity_errors_observed(&mut s, site()).unwrap();
    let end = c.get();
    arm.set(true);
    assert!(retire_native_bundle_errors_observed(rows, &mut s, site()).is_err());
    arm.set(false);
    assert!(b.wire_identity_errors_observed(&mut s, site()).is_err());
    drop(s);
    assert!(
        o.events[end..]
            .iter()
            .all(|p| p.phase == ExecutionPhase::ScratchRetirement)
    );
}
