// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    clippy::useless_vec,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn each_private_cursor_cut_keeps_exact_prefix_until_explicit_owned_buffer_drain() {
    let m = fixture();
    let mut baseline = Observer::default();
    let calls = baseline.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let a = setup(&m, &mut s);
    let begin = calls.get();
    let mut rows = Vec::new();
    a.ambiguous(
        &mut rows,
        &mut Work {
            session: &mut s,
            site: site(),
        },
    )
    .unwrap();
    let end = calls.get();
    Work {
        session: &mut s,
        site: site(),
    }
    .rows(rows);
    a.retire_observed(&mut s, site()).unwrap();
    drop(s);
    let mut saw = false;
    for cut in begin + 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let a = setup(&m, &mut s);
        let mut rows = Vec::new();
        assert_eq!(
            a.ambiguous(
                &mut rows,
                &mut Work {
                    session: &mut s,
                    site: site()
                }
            ),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert!(vec![3, 19].starts_with(&rows));
        saw |= rows.capacity() != 0;
        Work {
            session: &mut s,
            site: site(),
        }
        .rows(rows);
        let _ = a.retire_observed(&mut s, site());
        drop(s);
        assert_eq!(&o.events[..cut], &baseline.events[..cut]);
    }
    assert!(saw);
}
#[test]
fn complete_map_rows_retire_without_disposing_or_mutating_borrowed_module() {
    let m = fixture();
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let a = setup(&m, &mut s);
    a.retire_observed(&mut s, site()).unwrap();
    assert_eq!(m.functions.len(), 7);
    assert_eq!(m.functions[2].name, "only");
    assert_eq!(m.functions[0].id, FuncId::new(u32::MAX));
}
#[test]
fn healthy_consuming_catalog_retirement_has_one_terminal_zero_receipt() {
    let m = fixture();
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let a = setup(&m, &mut s);
    let begin = calls.get();
    a.retire_observed(&mut s, site()).unwrap();
    drop(s);
    assert!(
        o.events[begin..o.events.len() - 1]
            .iter()
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
    assert_eq!(
        *o.events.last().unwrap(),
        ExecutionProgress {
            phase: ExecutionPhase::Publication,
            site: site(),
            work: 0,
            copy_bytes: 0
        }
    );
}
#[test]
fn stopped_catalog_and_full_roster_cleanup_keep_first_refusal_and_drop_every_owned_capacity() {
    let m = fixture();
    let (_, begin, _) = run(&m);
    let mut o = Observer {
        stop: Some(begin + 1),
        cleanup_after: Some(begin + 1),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let a = setup(&m, &mut s);
    assert!(
        s.admit(ExecutionProgress {
            phase: ExecutionPhase::ModuleLookup,
            site: site(),
            work: 1,
            copy_bytes: 0
        })
        .is_err()
    );
    let mut rows = Vec::with_capacity(64);
    rows.extend([3u32, 19]);
    Work {
        session: &mut s,
        site: site(),
    }
    .rows(rows);
    assert_eq!(
        a.retire_observed(&mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        s.first_refusal().unwrap().cause,
        "original catalog query stop"
    );
    drop(s);
    assert!(
        o.events[begin + 1..]
            .iter()
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
}
