// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn frame_reserve_and_transport_stops_leave_the_existing_live_stack_untouched() {
    let input = Ty::U32;
    let make = || vec![Frame::Visit(&input)];
    let mut rows = make();
    assert_eq!(rows.len(), rows.capacity());
    let old = rows.capacity();
    let mut base = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut base);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    w.push(&mut rows, Frame::Exit(7)).unwrap();
    drop(w);
    drop(s);
    assert_eq!(base.events.len(), 3);
    for stop in [2, 3] {
        let mut rows = make();
        let mut o = Observer {
            stop: Some(stop),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut w = Work {
            session: &mut s,
            site: site(),
        };
        assert_eq!(
            w.push(&mut rows, Frame::Exit(7)),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(rows.len(), 1);
        assert!(matches!(rows[0],Frame::Visit(p) if std::ptr::eq(p,&input)));
        if stop == 2 {
            assert_eq!(rows.capacity(), old)
        } else {
            assert!(rows.capacity() >= 3)
        }
        w.drain(&mut rows);
        assert_eq!(rows.capacity(), 0);
        assert_eq!(
            w.session.first_refusal().unwrap().progress,
            base.events[stop - 1]
        );
    }
}
#[test]
fn partial_array_marks_and_full_pending_frame_tail_are_retained_at_each_interior_stop() {
    let (ty, types) = mixed();
    let mut base = Observer::default();
    let mut state = State::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut base);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    state.run(&ty, &types, &mut w).unwrap();
    drop(w);
    drop(s);
    let mut held = false;
    for stop in 1..=base.events.len() {
        let mut state = State::default();
        let mut o = Observer {
            stop: Some(stop),
            cleanup_after: Some(stop),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut w = Work {
            session: &mut s,
            site: site(),
        };
        assert_eq!(
            state.run(&ty, &types, &mut w),
            Err(ObservedValueError::AdmissionRefused)
        );
        if !state.stack.is_empty() && !state.marks.is_empty() {
            held = true;
        }
        w.drain(&mut state.stack);
        w.drain(&mut state.marks);
        assert_eq!(state.stack.capacity(), 0);
        assert_eq!(state.marks.capacity(), 0);
        assert_eq!(
            w.session.first_refusal().unwrap().progress,
            base.events[stop - 1]
        );
    }
    assert!(
        held,
        "actual returned/queued descriptors must coexist with live marks at an interior cut"
    );
}
#[test]
fn copy_capacity_refusal_is_operational_not_a_nontrivial_type_answer() {
    let input = Ty::Unit;
    let mut rows = vec![Frame::Visit(&input)];
    let old = rows.capacity();
    let requested = rows.len() * 2 + 1;
    let cap = (requested + old) * size_of::<Frame<'_>>() - 1;
    let mut o = Observer {
        byte_cap: Some(cap),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    assert_eq!(
        w.push(&mut rows, Frame::Exit(19)),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(rows.len(), 1);
    assert_eq!(rows.capacity(), old);
    assert_eq!(w.session.first_refusal().unwrap().cause, "copy");
    w.drain(&mut rows);
    assert_eq!(rows.capacity(), 0);
}
