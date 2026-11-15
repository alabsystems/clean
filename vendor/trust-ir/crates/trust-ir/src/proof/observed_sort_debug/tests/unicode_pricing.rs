// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! U+1248 exercises the pinned Unicode skip-run witness; all Rust controls UNRUN.
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
type Input = ClauseSort;
type Output = String;
fn input(text: &str) -> Input {
    ClauseSort::Datatype {
        name: text.into(),
        constructors: vec![(text.into(), vec![(text.into(), ClauseSort::Int)])],
    }
}
fn oracle(input: &Input) -> Output {
    format!("{input:?}")
}
fn call(input: &Input, session: &mut ObservedSession<'_, Observer>) -> R<Output> {
    input.debug_observed(session, site())
}
fn consume(output: &mut Output, session: &mut ObservedSession<'_, Observer>) -> R {
    let mut work = Work {
        session,
        site: site(),
    };
    work.retire_text(output);
    work.publication(0, 0)
}
fn points(events: &[ExecutionProgress]) -> Vec<usize> {
    let points: Vec<_> = events
        .iter()
        .enumerate()
        .filter_map(|(index, event)| {
            (event.phase == ExecutionPhase::Validation
                && event.copy_bytes == size_of::<core::char::EscapeDebug>()
                && event.work >= 8 * u32::BITS as usize)
                .then_some(index)
        })
        .collect();
    assert!(points.len() >= 8);
    // Independent pinned-source witness: U+1248 needs 546 offset reads alone
    // (243+1+3+299), before binary-search/guard work. Not a copied tariff.
    assert!(points.iter().all(|&index| events[index].work >= 546));
    points
}
fn trace(input: &Input) -> Observer {
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(
        InterpretOptions {
            fuel: 0,
            ..InterpretOptions::default()
        },
        &mut observer,
    );
    let mut output = call(input, &mut session).unwrap();
    assert_eq!(output, oracle(input));
    consume(&mut output, &mut session).unwrap();
    assert!(output.is_empty());
    assert_eq!(session.remaining_fuel(), 0);
    assert!(session.first_refusal().is_none());
    drop(session);
    assert_eq!(
        observer
            .events
            .last()
            .map(|event| (event.phase, event.work, event.copy_bytes)),
        Some((ExecutionPhase::Publication, 0, 0))
    );
    observer
}
fn assert_tail(observer: &Observer, baseline: &[ExecutionProgress], cut: usize) {
    assert_eq!(&observer.events[..=cut], &baseline[..=cut]);
    assert!(observer.events.len() > cut + 1);
    assert!(
        observer.events[cut + 1..]
            .iter()
            .all(|event| event.phase == ExecutionPhase::ScratchRetirement)
    );
    assert!(observer.events.iter().all(|event| event.site == site()));
}
#[test]
fn u1248_public_relation_preserves_complete_ordinary_output_and_zero_fuel() {
    for text in [
        "\u{1248}".repeat(8),
        "\u{1248}'\"\\\n\0\u{301}\u{2003}".repeat(8),
    ] {
        let input = input(&text);
        let before = input.clone();
        let mut observer = Observer {
            cap: Some(1_000_000_000),
            byte_cap: Some(512 * 1024 * 1024),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(
            InterpretOptions {
                fuel: 0,
                ..InterpretOptions::default()
            },
            &mut observer,
        );
        for _ in 0..2 {
            let mut output = call(&input, &mut session).unwrap();
            assert_eq!(output, oracle(&input));
            assert!(!output.is_empty());
            assert!(format!("{output:?}").contains('\u{1248}'));
            consume(&mut output, &mut session).unwrap();
            assert!(output.is_empty());
        }
        assert!(session.first_refusal().is_none());
        assert_eq!(session.remaining_fuel(), 0);
        drop(session);
        points(&observer.events);
        assert_eq!(input, before);
    }
}
#[test]
fn u1248_original_work_and_copy_one_short_refuse_at_the_exact_public_record() {
    let input = input(&"\u{1248}".repeat(8));
    let baseline = trace(&input);
    let cut = points(&baseline.events)[0];
    let record = baseline.events[cut];
    for copy in [false, true] {
        let mut observer = Observer::default();
        if copy {
            observer.byte_cap = Some(
                baseline.events[..=cut]
                    .iter()
                    .map(|event| event.copy_bytes)
                    .sum::<usize>()
                    - 1,
            );
        } else {
            observer.cap = Some(
                baseline.events[..=cut]
                    .iter()
                    .map(|event| event.work)
                    .sum::<usize>()
                    - 1,
            );
        }
        let mut session = ObservedSession::new(
            InterpretOptions {
                fuel: 0,
                ..InterpretOptions::default()
            },
            &mut observer,
        );
        assert_eq!(
            call(&input, &mut session),
            Err(ObservedValueError::AdmissionRefused)
        );
        let cause = if copy { "bytes" } else { "work" };
        assert_eq!(session.first_refusal().unwrap().cause, cause);
        assert_eq!(session.first_refusal().unwrap().progress, record);
        assert_eq!(
            call(&input, &mut session),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(session.first_refusal().unwrap().cause, cause);
        assert_eq!(session.remaining_fuel(), 0);
        drop(session);
        assert_tail(&observer, &baseline.events, cut);
    }
}
#[test]
fn u1248_every_public_classification_cut_keeps_original_cause_and_consumes_cleanup() {
    let input = input(&"\u{1248}".repeat(8));
    let baseline = trace(&input);
    for cut in points(&baseline.events) {
        let mut observer = Observer {
            at: Some(cut + 1),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(
            InterpretOptions {
                fuel: 0,
                ..InterpretOptions::default()
            },
            &mut observer,
        );
        assert_eq!(
            call(&input, &mut session),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(
            session.first_refusal().unwrap().progress,
            baseline.events[cut]
        );
        assert_eq!(session.first_refusal().unwrap().cause, "original interior");
        assert_eq!(
            call(&input, &mut session),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(session.first_refusal().unwrap().cause, "original interior");
        drop(session);
        assert_tail(&observer, &baseline.events, cut);
    }
}
#[test]
fn u1248_whole_call_and_output_retirement_share_one_original_finite_budget() {
    let input = input(&"\u{1248}".repeat(8));
    let baseline = trace(&input);
    for copy in [false, true] {
        let mut observer = Observer::default();
        if copy {
            observer.byte_cap = Some(baseline.bytes);
        } else {
            observer.cap = Some(baseline.work);
        }
        let mut session = ObservedSession::new(
            InterpretOptions {
                fuel: 0,
                ..InterpretOptions::default()
            },
            &mut observer,
        );
        let mut output = call(&input, &mut session).unwrap();
        assert_eq!(output, oracle(&input));
        consume(&mut output, &mut session).unwrap();
        assert!(output.is_empty());
        assert!(session.first_refusal().is_none());
        assert_eq!(
            call(&input, &mut session),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(
            session.first_refusal().unwrap().cause,
            if copy { "bytes" } else { "work" }
        );
        assert_eq!(session.remaining_fuel(), 0);
        drop(session);
        assert_eq!(
            &observer.events[..baseline.events.len()],
            baseline.events.as_slice()
        );
        assert_eq!(observer.events.len(), baseline.events.len() + 1);
        assert_eq!(observer.events.last(), baseline.events.first());
    }
}
#[test]
fn u1248_helper_cut_holds_complete_prefix_until_same_owner_consuming_retirement() {
    let text = "\u{1248}".repeat(8);
    let mut baseline = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let mut output = String::new();
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    work.quoted(&text, &mut output).unwrap();
    assert_eq!(output, format!("{text:?}"));
    work.retire_text(&mut output);
    assert_eq!(output.capacity(), 0);
    work.publication(0, 0).unwrap();
    drop(work);
    drop(session);
    let cuts = points(&baseline.events);
    assert_eq!(cuts.len(), 8);
    for (completed, cut) in cuts.into_iter().enumerate() {
        let mut observer = Observer {
            at: Some(cut + 1),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        let mut output = String::new();
        let mut work = Work {
            session: &mut session,
            site: site(),
        };
        assert_eq!(
            work.quoted(&text, &mut output),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(output, "\"".to_owned() + &"\u{1248}".repeat(completed));
        work.retire_text(&mut output);
        assert_eq!(output.capacity(), 0);
        assert_eq!(
            work.publication(0, 0),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(
            work.session.first_refusal().unwrap().cause,
            "original interior"
        );
        drop(work);
        drop(session);
        assert_tail(&observer, &baseline.events, cut);
    }
    assert_eq!(text, "\u{1248}".repeat(8));
}
