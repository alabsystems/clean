// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    clippy::field_reassign_with_default,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn every_actual_child_class_hash_collision_lookup_growth_cleanup_and_publication_refuses() {
    let root = sample();
    let (_, baseline, end, _) = run(&root);
    for cut in 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert!(matches!(
            root.uniform_element_lists_observed(&mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        ));
        assert_eq!(
            s.first_refusal().unwrap().cause,
            "original uniform-class stop"
        );
        drop(s);
        assert_eq!(&o.events[..cut], &baseline.events[..cut]);
        assert!(
            o.events[cut..]
                .iter()
                .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
        );
    }
}
fn collisions<'a, O: ExecutionObserver>(
    state: &mut State<'a>,
    a: &'a Constant,
    b: &'a Constant,
    records: [&'a Constant; 3],
    work: &mut Work<'_, '_, O>,
) -> R {
    for (node, expected) in [(a, 0), (b, 1), (a, 0)] {
        work.admit(1, size_of::<Option<Key<'_>>>())?;
        state.pending_key = Some(Key::Leaf(node));
        assert_eq!(state.intern_fingerprint([0; 32], work)?, expected);
    }
    for (record, child, expected) in [
        (records[0], 0, 2),
        (records[1], 0, 3),
        (records[2], 1, 4),
        (records[0], 0, 2),
    ] {
        let Constant::Record(labels) = record else {
            return Err(ObservedValueError::InvalidRange);
        };
        work.admit(1, size_of::<Option<Key<'_>>>())?;
        state.building = Some(Key::Composite {
            variant: Some(core::mem::discriminant(record)),
            payload: 0,
            labels,
            children: Vec::new(),
        });
        let Some(Key::Composite { children, .. }) = state.building.as_mut() else {
            return Err(ObservedValueError::InvalidRange);
        };
        work.reserve(children)?;
        work.admit(1, size_of::<usize>())?;
        children.push(child);
        work.admit(1, size_of::<Option<Key<'_>>>())?;
        state.pending_key = state.building.take();
        assert_eq!(state.intern_fingerprint([0; 32], work)?, expected);
    }
    Ok(())
}
#[test]
fn forced_fingerprint_collision_still_runs_complete_original_equality_and_is_interruptible() {
    let a = Constant::symbol_addr("é🦀".repeat(400));
    let b = Constant::symbol_addr("é🦀".repeat(399) + "é中z");
    let r1 = Constant::Record(vec![("é🦀".repeat(400), a.clone())]);
    let r2 = Constant::Record(vec![("é🦀".repeat(399) + "é中z", a.clone())]);
    let r3 = Constant::Record(vec![("é🦀".repeat(400), b.clone())]);
    let mut baseline = Observer::default();
    let calls = baseline.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let mut state = State::default();
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    collisions(&mut state, &a, &b, [&r1, &r2, &r3], &mut work).unwrap();
    let end = calls.get();
    assert_eq!(state.classes.len(), 5);
    assert_eq!(state.buckets.get(&[0; 32]).unwrap(), &vec![0, 1, 2, 3, 4]);
    drain(&mut state, &mut work);
    empty(&state);
    drop(work);
    drop(s);
    for cut in 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut state = State::default();
        let mut work = Work {
            session: &mut s,
            site: site(),
        };
        assert_eq!(
            collisions(&mut state, &a, &b, [&r1, &r2, &r3], &mut work),
            Err(ObservedValueError::AdmissionRefused)
        );
        drain(&mut state, &mut work);
        empty(&state);
        assert_eq!(
            work.session.first_refusal().unwrap().cause,
            "original uniform-class stop"
        );
        drop(work);
        drop(s);
        assert_eq!(&o.events[..cut], &baseline.events[..cut]);
    }
}
#[test]
fn repeated_constructors_share_both_original_cumulative_work_and_copy_caps() {
    let root = sample();
    let (_, baseline, end, _) = run(&root);
    for copy in [false, true] {
        let cap = baseline.events[..end]
            .iter()
            .map(|e| if copy { e.copy_bytes } else { e.work })
            .sum();
        let mut o = Observer::default();
        if copy {
            o.byte_cap = Some(cap)
        } else {
            o.work_cap = Some(cap)
        }
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let held = root.uniform_element_lists_observed(&mut s, site()).unwrap();
        assert!(matches!(
            root.uniform_element_lists_observed(&mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        ));
        assert_eq!(
            s.first_refusal().unwrap().cause,
            if copy { "copy" } else { "work" }
        );
        let _ = held.retire_observed(&mut s, site());
    }
}
#[test]
fn zero_instruction_fuel_and_preexisting_stop_keep_original_owner_site_and_first_cause() {
    let root = sample();
    let mut o = Observer::default();
    let mut options = InterpretOptions::default();
    options.fuel = 0;
    let mut s = ObservedSession::new(options, &mut o);
    let table = root.uniform_element_lists_observed(&mut s, site()).unwrap();
    table.retire_observed(&mut s, site()).unwrap();
    assert_eq!(s.remaining_fuel(), 0);
    drop(s);
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
    assert!(matches!(
        root.uniform_element_lists_observed(&mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    ));
    assert_eq!(
        s.first_refusal().unwrap().cause,
        "original uniform-class stop"
    );
}
#[test]
fn each_true_false_membership_and_caller_retirement_callback_remains_refusable() {
    let root = sample();
    let external = root.clone();
    let mut baseline = Observer::default();
    let calls = baseline.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let table = root.uniform_element_lists_observed(&mut s, site()).unwrap();
    let begin = calls.get();
    assert!(table.contains_observed(&root, &mut s, site()).unwrap());
    assert!(!table.contains_observed(&external, &mut s, site()).unwrap());
    table.retire_observed(&mut s, site()).unwrap();
    let end = calls.get();
    drop(s);
    for cut in begin + 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let table = root.uniform_element_lists_observed(&mut s, site()).unwrap();
        let result = table
            .contains_observed(&root, &mut s, site())
            .and_then(|_| table.contains_observed(&external, &mut s, site()));
        let cleanup = table.retire_observed(&mut s, site());
        assert!(result.is_err() || cleanup.is_err());
        assert_eq!(
            s.first_refusal().unwrap().cause,
            "original uniform-class stop"
        );
        drop(s);
        assert_eq!(&o.events[..cut], &baseline.events[..cut]);
    }
}
#[test]
fn splat_logical_length_and_unused_childless_root_bytes_do_not_fake_text_work() {
    let mut traces = Vec::new();
    for len in [2, u64::MAX] {
        let root = Constant::Splat {
            elem: Box::new(Constant::Int(1)),
            len,
        };
        let (_, o, end, _) = run(&root);
        traces.push(o.events[..end].to_vec());
    }
    assert_eq!(traces[0], traces[1]);
    let mut traces = Vec::new();
    for data in [vec![], vec![0; 100000]] {
        let (_, o, end, _) = run(&Constant::Bytes { data, utf8: false });
        traces.push(o.events[..end].to_vec());
    }
    assert_eq!(traces[0], traces[1]);
}
