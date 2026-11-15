// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored UNRUN: actual ordinary nominal lexical results, no pin authority.
#![allow(
    unused_must_use,
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use crate::{FuncId, interpret::InterpretOptions};
mod stops;
#[derive(Default)]
struct Observer {
    events: Vec<ExecutionProgress>,
    stop: Option<usize>,
    work: usize,
    bytes: usize,
    work_cap: Option<usize>,
    byte_cap: Option<usize>,
}
impl ExecutionObserver for Observer {
    type Refusal = &'static str;
    fn admit(&mut self, e: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(e);
        if self.stop == Some(self.events.len()) {
            return Err("original nominal stop");
        }
        self.work = self.work.checked_add(e.work).ok_or("overflow")?;
        self.bytes = self.bytes.checked_add(e.copy_bytes).ok_or("overflow")?;
        if self.work_cap.is_some_and(|n| self.work > n) {
            return Err("work");
        }
        if self.byte_cap.is_some_and(|n| self.bytes > n) {
            return Err("copy");
        }
        Ok(())
    }
}
fn site() -> ExecutionSite {
    ExecutionSite::Entry(FuncId::new(503))
}
fn dialect(value: &DialectTy) -> (Result<(), DialectTyError>, Observer) {
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let result = value.validate_observed(&mut s, site()).unwrap();
    assert_eq!(result, value.validate());
    assert!(s.first_refusal().is_none());
    assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
    drop(s);
    assert!(o.events.iter().all(|e| e.site == site()));
    assert_eq!(o.events.last().unwrap().phase, ExecutionPhase::Publication);
    (result, o)
}
fn handle(value: &HandleTy) -> (Result<(), HandleTyError>, Observer) {
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let result = value.validate_observed(&mut s, site()).unwrap();
    assert_eq!(result, value.validate());
    assert!(s.first_refusal().is_none());
    assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
    drop(s);
    assert!(o.events.iter().all(|e| e.site == site()));
    assert_eq!(o.events.last().unwrap().phase, ExecutionPhase::Publication);
    (result, o)
}
#[test]
fn every_single_latin1_scalar_matches_actual_original_name_alphabet() {
    for n in 0..=255u8 {
        let text = char::from(n).to_string();
        let expected = n.is_ascii_alphanumeric() || n == b'_';
        assert_eq!(
            dialect(&DialectTy::new(&text, "value", 1)).0.is_ok(),
            expected
        );
        assert_eq!(dialect(&DialectTy::new("ns", &text, 1)).0.is_ok(), expected);
        assert_eq!(handle(&HandleTy::new(&text, "runtime")).0.is_ok(), expected);
        assert_eq!(handle(&HandleTy::new("Name", &text)).0.is_ok(), expected);
    }
}
#[test]
fn runtime_segments_and_all_short_colon_shapes_match_original_split_grammar() {
    for a in ["", "a", "A9_", "λ", ":", "_"] {
        for sep in ["", ":", "::", ":::", "::::"] {
            for b in ["", "b", "B9_", "尾", ":", "_"] {
                let text = format!("{a}{sep}{b}");
                handle(&HandleTy::new("Name", text));
            }
        }
    }
}
#[test]
fn exact_namespace_name_version_error_order_is_preserved() {
    for (ns, name, version, expected) in [
        ("", "", 0, Err(DialectTyError::InvalidNamespace)),
        ("valid", "", 0, Err(DialectTyError::InvalidName)),
        ("valid", "name", 0, Err(DialectTyError::ZeroVersion)),
        ("VALID_9", "Name_8", u32::MAX, Ok(())),
    ] {
        assert_eq!(dialect(&DialectTy::new(ns, name, version)).0, expected);
    }
    assert_eq!(
        handle(&HandleTy::new("", "bad:")).0,
        Err(HandleTyError::InvalidName)
    );
}
#[test]
fn unicode_nul_space_hyphen_period_and_zero_width_are_not_normalized() {
    for text in [
        "λ", "尾", "é", "e\u{301}", "\u{200b}", "a\0b", "a b", "a-b", "a.b", "a/b", "a::b",
    ] {
        assert!(dialect(&DialectTy::new(text, "n", 1)).0.is_err());
        assert!(handle(&HandleTy::new(text, "r")).0.is_err());
    }
    for text in [
        "a::λ", "a::尾", "a::b\0", "a ::b", "a::b-c", "a:::b", "::a", "a::",
    ] {
        assert!(handle(&HandleTy::new("Name", text)).0.is_err());
    }
}
#[test]
fn long_valid_names_runtime_segments_and_late_invalid_bytes_are_really_walked() {
    let name = "Ab9_".repeat(2000);
    let runtime = vec!["segment_9"; 1000].join("::");
    let (_, d) = dialect(&DialectTy::new(&name, &name, 1));
    let (_, h) = handle(&HandleTy::new(&name, &runtime));
    assert!(d.events.len() > name.len() * 2);
    assert!(h.events.len() > runtime.len());
    assert!(
        dialect(&DialectTy::new(name.clone() + "!", "name", 1))
            .0
            .is_err()
    );
    assert!(handle(&HandleTy::new("Name", runtime + "!")).0.is_err());
}
#[test]
fn first_invalid_field_leaves_later_huge_inputs_unread() {
    let (_, short) = dialect(&DialectTy::new("!", "short", 1));
    let (_, long) = dialect(&DialectTy::new("!", "huge λ\0".repeat(10000), 0));
    assert_eq!(short.events, long.events);
    let (_, short) = handle(&HandleTy::new("!", "short"));
    let (_, long) = handle(&HandleTy::new("!", "huge 尾\0".repeat(10000)));
    assert_eq!(short.events, long.events);
}
#[test]
fn static_error_message_and_display_keep_all_five_literal_spellings() {
    for (error, expected) in [
        (
            DialectTyError::InvalidNamespace,
            "dialect type namespace must be nonempty ASCII letters, digits, or '_'",
        ),
        (
            DialectTyError::InvalidName,
            "dialect type name must be nonempty ASCII letters, digits, or '_'",
        ),
        (
            DialectTyError::ZeroVersion,
            "dialect type version must be nonzero",
        ),
    ] {
        assert_eq!(error.message(), expected);
        assert_eq!(error.to_string(), expected);
    }
    for (error, expected) in [
        (
            HandleTyError::InvalidName,
            "handle type name must be nonempty ASCII letters, digits, or '_'",
        ),
        (
            HandleTyError::InvalidRuntime,
            "handle runtime must be nonempty '::'-separated segments of ASCII letters, digits, or '_'",
        ),
    ] {
        assert_eq!(error.message(), expected);
        assert_eq!(error.to_string(), expected);
    }
}
#[test]
fn successful_lexical_pair_does_not_claim_pinned_runtime_membership() {
    assert_eq!(
        handle(&HandleTy::new("NotPinned", "arbitrary::runtime::NotPinned")).0,
        Ok(())
    );
    assert_eq!(
        dialect(&DialectTy::new("unregistered_namespace", "value", 999)).0,
        Ok(())
    );
}
