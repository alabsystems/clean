// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
use crate::FuncId;
use crate::interpret::InterpretOptions;
mod fixtures;
mod held_errors;
mod limits;
mod stops;
use fixtures::{fixture, minimal};

#[derive(Default)]
struct Observer {
    events: Vec<ExecutionProgress>,
    stop_at: Option<usize>,
    stop_retirement: bool,
    work: usize,
    bytes: usize,
    work_limit: Option<usize>,
    byte_limit: Option<usize>,
}
impl ExecutionObserver for Observer {
    type Refusal = &'static str;
    fn admit(&mut self, event: ExecutionProgress) -> core::result::Result<(), Self::Refusal> {
        self.events.push(event);
        if self.stop_at == Some(self.events.len()) {
            return Err("interior");
        }
        if self.stop_retirement && event.phase == ExecutionPhase::ScratchRetirement {
            return Err("retirement");
        }
        self.work = self.work.checked_add(event.work).ok_or("work overflow")?;
        self.bytes = self
            .bytes
            .checked_add(event.copy_bytes)
            .ok_or("bytes overflow")?;
        if self.work_limit.is_some_and(|cap| self.work > cap) {
            return Err("work");
        }
        if self.byte_limit.is_some_and(|cap| self.bytes > cap) {
            return Err("bytes");
        }
        Ok(())
    }
}
fn site() -> ExecutionSite {
    ExecutionSite::Entry(FuncId::new(43))
}
fn observed(a: &SignatureAbi) -> String {
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let text = a
        .canonical_text_for_wire_observed(&mut session, site())
        .unwrap();
    assert_eq!(session.remaining_fuel(), InterpretOptions::default().fuel);
    assert!(session.first_refusal().is_none());
    assert!(observer.events.iter().all(|e| e.site == site()));
    text
}
fn read_observed(text: &str) -> R<String> {
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut out = Writer::new(&mut session, site())?;
    out.text = text.to_owned(); // Fixture input only; production builds it through Writer.
    let answer = round_trip(&mut out);
    let residue = core::mem::take(&mut out.text);
    out.retire(residue);
    out.publication()?;
    answer
}

#[test]
fn every_pass_mode_attribute_binding_and_convention_keeps_exact_canonical_text() {
    let mut a = fixture();
    for convention in crate::CallingConv::ALL {
        a.lowered_convention = convention;
        let actual = observed(&a);
        assert_eq!(actual, a.to_canonical_text());
        assert_eq!(SignatureAbi::from_canonical_text(&actual).unwrap(), a);
        assert_eq!(read_observed(&actual).unwrap(), actual);
        a.validate_encoding_limits().unwrap();
    }
}

#[test]
fn unicode_control_escaping_and_unsigned_width_extremes_match_the_old_round_trip() {
    let mut a = fixture();
    a.frontend.name = "quote\" slash\\ newline\n\r\t NUL\0 DEL\u{7f} NEXT\u{85} λ🚀".into();
    a.target.features = vec!["λ".repeat(1025), String::new(), "\u{10ffff}".into()];
    a.arguments[0].size = u64::MAX;
    a.arguments[0].align = u64::MAX;
    a.arguments[0].bindings[0].place = AbiBindingPlace::Parameter(u32::MAX);
    if let AbiPassMode::Direct(s) = &mut a.arguments[0].mode {
        s.source_offset = u64::MAX;
        s.source_bytes = u64::MAX;
        s.value_bits = u16::MAX;
        s.register.bytes = u64::MAX;
        s.attributes.pointee_size = u64::MAX;
        s.attributes.pointee_align = Some(u64::MAX);
    } else {
        panic!("fixture direct mode");
    }
    a.target.pointer_bytes = u8::MAX;
    a.fixed_count = u32::MAX;
    let actual = observed(&a);
    assert_eq!(actual, a.to_canonical_text());
    assert!(actual.contains("\\u{0}"));
    assert!(actual.contains("\\u{85}"));
    assert_eq!(SignatureAbi::from_canonical_text(&actual).unwrap(), a);
    // This intentionally contradictory target/source census remains only an
    // encoding identity. The observed helper cannot issue semantic ABI authority.
    assert!(
        a.validate(&crate::FuncTy::unrecorded(vec![], vec![], false))
            .is_err()
    );
}

#[test]
fn malformed_typed_fields_and_noncanonical_spellings_match_existing_refusals() {
    let text = fixture().to_canonical_text();
    let bad = [
        text.replacen("pointer_bytes=8", "pointer_bytes=256", 1),
        text.replacen("value_bits=8", "value_bits=65536", 1),
        text.replacen("fixed_count=6", "fixed_count=4294967296", 1),
        text.replacen("index=0", "index=4294967296", 1),
        text.replacen("source_offset=0", "source_offset=18446744073709551616", 1),
        text.replacen("fixed_count=6", "fixed_count=06", 1),
        text.replacen("can_unwind=false", "can_unwind=0", 1),
        text.replacen("class=\"integer\"", "class=\"unknown\"", 1),
        text.replacen("capture=\"any\"", "capture=\"unknown\"", 1),
        text.replacen("extension=\"none\"", "extension=\"unknown\"", 1),
        text.replacen("kind=\"direct\"", "kind=\"future\"", 1),
        text.replacen("place=\"parameter\"", "place=\"future\"", 1),
        text.replacen(
            "lowered_convention=\"ccc\"",
            "lowered_convention=\"future\"",
            1,
        ),
        text.replacen("target=", "unknown=", 1),
        text.replacen("target=", "frontend=", 1),
        format!("{text} "),
        text.replacen("frontend={name=", "frontend={revision=", 1),
        text.replacen("source_offset=0", "source_offset=-1", 1),
        text.replacen("source_offset=0", "source_offset=+1", 1),
        text.replacen("frontend={name=\"", "frontend={name=\"\\q", 1),
    ];
    for input in bad {
        assert_ne!(input, text, "mutation must reach a real field");
        assert!(
            SignatureAbi::from_canonical_text(&input).is_err(),
            "old: {input}"
        );
        assert_eq!(
            read_observed(&input),
            Err(ObservedValueError::UnsupportedValue)
        );
    }
}

#[test]
fn changing_a_load_bearing_abi_claim_changes_observed_text_without_authorizing_it() {
    let a = fixture();
    let original = observed(&a);
    let mut changed = a.clone();
    changed.arguments[0].bindings[0].carrier_offset = 1;
    assert_ne!(observed(&changed), original);
    assert_eq!(observed(&changed), changed.to_canonical_text());
    changed = a;
    changed.target.target_spec.push('!');
    assert_ne!(observed(&changed), original);
}
