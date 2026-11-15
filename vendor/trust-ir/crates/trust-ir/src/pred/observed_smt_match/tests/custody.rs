// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
fn value() -> Constant {
    Constant::SymbolAddr {
        symbol: "full λ\0尾".repeat(1800),
        addend: i64::MIN,
    }
}
fn child(value: &Constant) -> (String, Observer) {
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let text = value.display_observed(&mut s, site()).unwrap();
    drop(s);
    (text, o)
}
#[test]
fn returned_whole_constant_text_is_held_before_the_first_comparison_fee() {
    let value = value();
    let (expected, child) = child(&value);
    let cut = 1 + child.events.len() + 1;
    let mut o = Observer {
        stop: Some(cut),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = State::default();
    assert_eq!(
        state.task(
            Task::Constant(&value),
            &PredTable::new(&[], &[]),
            &expected,
            &mut w
        ),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(state.pending.as_deref(), Some(expected.as_str()));
    assert_eq!(state.cursor, 0);
    state.retire(&mut w);
    assert!(empty(&state));
    assert!(w.session.first_refusal().is_some());
    drop(w);
    drop(s);
    assert_eq!(&o.events[1..cut - 1], child.events.as_slice());
    assert!(
        o.events[cut..]
            .iter()
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
}
#[test]
fn refusal_in_middle_of_comparison_keeps_the_complete_child_not_a_prefix() {
    let value = value();
    let (expected, _) = child(&value);
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = State::default();
    assert_eq!(
        state.task(
            Task::Constant(&value),
            &PredTable::new(&[], &[]),
            &expected,
            &mut w
        ),
        Ok(true)
    );
    state.retire(&mut w);
    drop(w);
    drop(s);
    let cut = o
        .events
        .iter()
        .enumerate()
        .filter(|(_, e)| {
            e.phase == ExecutionPhase::Validation && e.work == 1024 && e.copy_bytes == 0
        })
        .nth(1)
        .unwrap()
        .0
        + 1;
    let mut o = Observer {
        stop: Some(cut),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = State::default();
    assert_eq!(
        state.task(
            Task::Constant(&value),
            &PredTable::new(&[], &[]),
            &expected,
            &mut w
        ),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(state.pending.as_deref(), Some(expected.as_str()));
    assert_eq!(state.cursor, 0);
    state.retire(&mut w);
    assert!(empty(&state));
}
#[test]
fn actual_task_growth_refuses_before_allocation_and_retains_existing_tail() {
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = State::default();
    w.push(&mut state.tasks, Task::Text("existing tail"))
        .unwrap();
    state.tasks.shrink_to_fit();
    w.push(&mut state.tasks, Task::Text("new tail")).unwrap();
    state.retire(&mut w);
    drop(w);
    drop(s);
    let cut = o
        .events
        .iter()
        .position(|e| e.work == 4 && e.copy_bytes == 4 * size_of::<Task<'_>>())
        .unwrap()
        + 1;
    assert_eq!(o.events[cut - 1].copy_bytes, 4 * size_of::<Task<'_>>());
    let mut o = Observer {
        stop: Some(cut),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = State::default();
    w.push(&mut state.tasks, Task::Text("existing tail"))
        .unwrap();
    state.tasks.shrink_to_fit();
    assert_eq!(
        w.push(&mut state.tasks, Task::Text("new tail")),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(state.tasks.len(), 1);
    assert_eq!(state.tasks.capacity(), 1);
    assert!(matches!(state.tasks[0], Task::Text("existing tail")));
    state.retire(&mut w);
    assert!(empty(&state));
}
#[test]
fn sticky_cleanup_drains_full_pending_text_and_all_borrowed_stack_capacity() {
    let value = value();
    let text = value.to_string();
    let mut o = Observer {
        cleanup_after: Some(0),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = State {
        pending: Some(text.clone()),
        tasks: vec![Task::Text("unvisited"), Task::Constant(&value)],
        cursor: 0,
    };
    assert_eq!(state.pending.as_deref(), Some(text.as_str()));
    state.retire(&mut w);
    assert!(empty(&state));
    assert!(w.session.first_refusal().is_some());
    drop(w);
    drop(s);
    assert!(o.events.len() >= 10);
    assert!(
        o.events
            .iter()
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
    let stack: Vec<_> = o.events[4..9].iter().map(|e| e.work).collect();
    assert_eq!(
        stack,
        [
            size_of::<Option<Task<'_>>>() + 1,
            size_of::<Task<'_>>() + 1,
            size_of::<Option<Task<'_>>>() + 1,
            size_of::<Task<'_>>() + 1,
            size_of::<Option<Task<'_>>>() + 1
        ]
    );
}
#[test]
fn constant_child_publication_refusal_never_transfers_unadmitted_text() {
    let value = value();
    let (expected, child) = child(&value);
    let cut = 1 + child.events.len();
    assert_eq!(
        child.events.last().unwrap().phase,
        ExecutionPhase::Publication
    );
    let mut o = Observer {
        stop: Some(cut),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = State::default();
    assert_eq!(
        state.task(
            Task::Constant(&value),
            &PredTable::new(&[], &[]),
            &expected,
            &mut w
        ),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert!(state.pending.is_none());
    assert_eq!(state.cursor, 0);
    state.retire(&mut w);
    assert!(empty(&state));
    drop(w);
    drop(s);
    assert_eq!(&o.events[1..cut], child.events.as_slice());
    assert!(
        o.events[cut..]
            .iter()
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
}
