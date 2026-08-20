// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// Module.obligation_diagnostics sidecar: actionable verifier output keyed by
// obligation id. Closes the audit gap "a failed proof obligation is a bare enum
// tag with no counterexample, location, or actionable payload". Round-trips
// through binary / canonical text / serde.

use trust_ir::value::{ProofId, SourceSpan};
use trust_ir::{
    DiagnosticSeverity, Module, ObligationDiagnostic, ObligationKind, ProofObligation, ProofStatus,
};

// Used only by the feature-gated round-trip tests below (binary/parser/serde).
// In a no-feature `--all-targets` build none of them compile, so the helper is
// dead — allow it precisely in that configuration (its body still references
// its imports, so `unused_imports` does not fire).
#[cfg_attr(
    not(any(feature = "binary", feature = "parser", feature = "serde")),
    allow(dead_code)
)]
fn module_with_diags() -> Module {
    let mut m = Module::new("diag");
    m.proof_obligations.push(ProofObligation::new(
        ProofId::new(0),
        ObligationKind::Precondition,
        ProofStatus::Failed,
        "x must be in bounds",
    ));
    let f = m.intern_file("src/main.rs");
    m.obligation_diagnostics.push(
        ObligationDiagnostic::error(ProofId::new(0), "could not prove x < len")
            .with_location(SourceSpan {
                file: f,
                line: 12,
                col: 5,
            })
            .with_detail("counterexample: x=len, len=4"),
    );
    m.obligation_diagnostics.push(ObligationDiagnostic {
        obligation: ProofId::new(0),
        severity: DiagnosticSeverity::Note,
        message: "discharged elsewhere via Trusted".into(),
        location: None,
        detail: None,
    });
    m
}

#[test]
fn severity_default_is_error_and_displays() {
    assert_eq!(DiagnosticSeverity::default(), DiagnosticSeverity::Error);
    assert_eq!(format!("{}", DiagnosticSeverity::Warning), "warning");
}

#[test]
fn resolve_span_resolves_known_files_and_rejects_dangling() {
    let mut m = Module::new("dbg");
    let f = m.intern_file("src/main.rs");
    let span = SourceSpan {
        file: f,
        line: 12,
        col: 5,
    };
    assert_eq!(m.resolve_span(&span), Some(("src/main.rs", 12, 5)));
    let dangling = SourceSpan {
        file: f + 1,
        line: 1,
        col: 1,
    };
    assert_eq!(m.resolve_span(&dangling), None);
}

#[test]
fn render_diagnostic_is_a_compiler_style_one_liner() {
    let m = module_with_diags();
    // Located + detail: full `path:line:col: severity: message [detail]`.
    assert_eq!(
        m.render_diagnostic(&m.obligation_diagnostics[0]),
        "src/main.rs:12:5: error: could not prove x < len [counterexample: x=len, len=4]"
    );
    // No location, no detail: bare `severity: message`.
    assert_eq!(
        m.render_diagnostic(&m.obligation_diagnostics[1]),
        "note: discharged elsewhere via Trusted"
    );
    // No location, detail only: `severity: message [detail]`.
    let d = ObligationDiagnostic::error(ProofId::new(0), "unlocated").with_detail("model: x=4");
    assert_eq!(m.render_diagnostic(&d), "error: unlocated [model: x=4]");
    // A dangling file index renders without the location prefix rather than
    // inventing a path.
    let d = ObligationDiagnostic::error(ProofId::new(0), "dangling").with_location(SourceSpan {
        file: 99,
        line: 1,
        col: 1,
    });
    assert_eq!(m.render_diagnostic(&d), "error: dangling");
}

#[cfg(feature = "binary")]
#[test]
fn diagnostics_binary_round_trip() {
    let m = module_with_diags();
    let bytes = trust_ir::binary::serialize_module(&m);
    let back = trust_ir::binary::deserialize_module(&bytes).expect("binary round trip");
    assert_eq!(back.obligation_diagnostics, m.obligation_diagnostics);
}

#[cfg(feature = "binary")]
#[test]
fn empty_diagnostics_binary_round_trip() {
    let m = Module::new("none");
    let back = trust_ir::binary::deserialize_module(&trust_ir::binary::serialize_module(&m))
        .expect("round trip");
    assert!(back.obligation_diagnostics.is_empty());
}

#[cfg(feature = "parser")]
#[test]
fn diagnostics_text_round_trip() {
    let m = module_with_diags();
    let text = format!("{m}");
    assert!(
        text.contains("diagnostic 0 error \"could not prove x < len\""),
        "{text}"
    );
    assert!(text.contains("at 0 12 5"), "{text}");
    assert!(text.contains("detail \"counterexample"), "{text}");
    let back = trust_ir::parser::parse_module(&text).expect("text round trip");
    assert_eq!(back.obligation_diagnostics, m.obligation_diagnostics);
}

#[cfg(feature = "serde")]
#[test]
fn diagnostics_serde_round_trip() {
    let m = module_with_diags();
    let json = serde_json::to_string(&m).expect("json");
    let back: Module = serde_json::from_str(&json).expect("json back");
    assert_eq!(back.obligation_diagnostics, m.obligation_diagnostics);
}

// R3 #5 regression (`ObligationDiagnostic::location`): positional MessagePack
// (`rmp_serde::to_vec`) may only skip a TRAILING field. Skipping a `None`
// `location` when `detail` is `Some` shifted the detail string into the
// location slot and failed decode with "invalid type: string, expected struct
// SourceSpan". `location` must always be emitted; only the trailing `detail`
// may skip.
#[cfg(feature = "serde")]
#[test]
fn diagnostic_location_none_detail_some_round_trips_json_and_msgpack() {
    let d = ObligationDiagnostic::error(ProofId::new(3), "no location, has detail")
        .with_detail("counterexample: x=len, len=4");

    let json = serde_json::to_string(&d).expect("json");
    let back: ObligationDiagnostic = serde_json::from_str(&json).expect("json back");
    assert_eq!(back, d);

    let bytes = rmp_serde::to_vec(&d).expect("msgpack");
    let back: ObligationDiagnostic = rmp_serde::from_slice(&bytes).expect("msgpack back");
    assert_eq!(back, d);

    // Same shape carried module-level, through the canonical Module codec.
    let mut m = module_with_diags();
    m.obligation_diagnostics.push(d);
    let bytes = rmp_serde::to_vec(&m).expect("module msgpack");
    let back: Module = rmp_serde::from_slice(&bytes).expect("module msgpack back");
    assert_eq!(back.obligation_diagnostics, m.obligation_diagnostics);
}
