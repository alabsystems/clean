// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;

struct Allow;
impl ExecutionObserver for Allow {
    type Refusal = ();
    fn admit(&mut self, _: ExecutionProgress) -> core::result::Result<(), ()> {
        Ok(())
    }
}

#[test]
fn actual_byte_node_and_depth_limits_refuse_without_a_partial_text_publication() {
    let mut too_many_nodes = minimal();
    too_many_nodes.target.features = vec![String::new(); MAX_NODES];
    assert!(too_many_nodes.validate_encoding_limits().is_err());
    let mut too_many_bytes = minimal();
    too_many_bytes.frontend.name = "x".repeat(MAX_ABI_TEXT_BYTES + 1);
    assert!(too_many_bytes.validate_encoding_limits().is_err());
    // Identity strings fit, but their canonical escaped text does not.
    let mut escaped = minimal();
    escaped.frontend.name = "\0".repeat(MAX_ABI_TEXT_BYTES / 2);
    assert!(escaped.validate_encoding_limits().is_err());
    for a in [&too_many_nodes, &too_many_bytes, &escaped] {
        let mut observer = Allow;
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        assert_eq!(
            a.canonical_text_for_wire_observed(&mut session, site()),
            Err(ObservedValueError::UnsupportedValue)
        );
    }
    for text in [
        "[".repeat(MAX_DEPTH + 2) + &"]".repeat(MAX_DEPTH + 2),
        " ".repeat(MAX_ABI_TEXT_BYTES + 1),
    ] {
        assert!(SignatureAbi::from_canonical_text(&text).is_err());
        assert_eq!(
            read_observed(&text),
            Err(ObservedValueError::UnsupportedValue)
        );
    }
}

#[test]
fn first_string_and_node_growth_are_admitted_before_the_owned_allocation() {
    let mut observer = Observer {
        byte_limit: Some(0),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    // Create the fixed writer before refusing the first variable allocation.
    let mut out = Writer {
        session: &mut session,
        site: site(),
        text: String::new(),
    };
    assert_eq!(
        out.append("first"),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(out.text.len(), 0);
    assert_eq!(out.text.capacity(), 0);
    let mut observer = Observer {
        byte_limit: Some(0),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut out = Writer {
        session: &mut session,
        site: site(),
        text: String::new(),
    };
    let mut nodes: Vec<usize> = Vec::new();
    assert_eq!(
        out.reserve(&mut nodes, 1),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(nodes.capacity(), 0);
}

#[test]
fn bounded_flat_reader_checks_real_escape_and_numeric_interiors() {
    let text = fixture().to_canonical_text();
    let bad = [
        text.replacen("name=\"producer\"", "name=\"\\u{110000}\"", 1),
        text.replacen("name=\"producer\"", "name=\"\\u{d800}\"", 1),
        text.replacen("name=\"producer\"", "name=\"\\u{}\"", 1),
        text.replacen(
            "name=\"producer\"",
            "name=\"\\u{000000000000000000000000000000000000000061}\"",
            1,
        ),
    ];
    for input in bad {
        assert_ne!(input, text);
        assert!(SignatureAbi::from_canonical_text(&input).is_err());
        assert_eq!(
            read_observed(&input),
            Err(ObservedValueError::UnsupportedValue)
        );
    }
}
