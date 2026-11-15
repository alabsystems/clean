// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;

fn run(
    stop: Option<usize>,
    action: impl FnOnce(&mut Writer<'_, '_, Observer>) -> R,
) -> (R, Observer) {
    let mut observer = Observer {
        stop_at: stop,
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut out = Writer::new(&mut session, site()).unwrap();
    let result = action(&mut out);
    assert_eq!(session.remaining_fuel(), InterpretOptions::default().fuel);
    if stop.is_some() {
        assert_eq!(session.first_refusal().unwrap().cause, "interior");
    } else {
        assert!(session.first_refusal().is_none());
    }
    drop(session);
    (result, observer)
}

fn assert_held(action: impl Fn(&mut Writer<'_, '_, Observer>) -> R) {
    let (expected, baseline) = run(None, |out| action(out));
    assert_eq!(expected, Err(ObservedValueError::UnsupportedValue));
    let suffix = baseline
        .events
        .iter()
        .rposition(|p| p.phase != ExecutionPhase::ScratchRetirement)
        .unwrap()
        + 1;
    assert!(suffix < baseline.events.len());
    for cut in suffix + 1..=baseline.events.len() {
        let (actual, observed) = run(Some(cut), |out| action(out));
        assert_eq!(actual, expected);
        assert_eq!(&observed.events[..cut], &baseline.events[..cut]);
        assert!(
            observed.events[suffix..]
                .iter()
                .all(|p| p.phase == ExecutionPhase::ScratchRetirement)
        );
    }
}

#[test]
fn actual_quoted_list_and_record_parser_errors_survive_each_late_owned_cleanup_cut() {
    for text in [
        r#""partial\q""#,
        r#"[first,"partial\q"]"#,
        r#"{first=atom,second="partial\q"}"#,
    ] {
        assert_held(|out| parser::parse(text, out).map(|(arena, _)| arena.retire(out)));
    }
}

#[test]
fn actual_roundtrip_typed_field_error_survives_each_late_arena_and_text_cleanup_cut() {
    let text = minimal()
        .to_canonical_text()
        .replacen("pointer_bytes=8", "pointer_bytes=256", 1);
    assert!(SignatureAbi::from_canonical_text(&text).is_err());
    assert_held(|out| {
        out.text = text.clone(); // Fixture input only, no production serialization credit.
        round_trip(out).map(|text| out.retire(text))
    });
}

#[test]
fn actual_public_encoding_limit_error_precedes_cleanup_refusal_and_never_publishes() {
    let mut a = minimal();
    a.frontend.name = "x".repeat(MAX_ABI_TEXT_BYTES + 1);
    let mut observer = Observer {
        stop_retirement: true,
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        a.canonical_text_for_wire_observed(&mut session, site()),
        Err(ObservedValueError::UnsupportedValue)
    );
    assert_eq!(session.first_refusal().unwrap().cause, "retirement");
    drop(session);
    assert!(
        !observer
            .events
            .iter()
            .any(|p| p.phase == ExecutionPhase::Publication)
    );
}
