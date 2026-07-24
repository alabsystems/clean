// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for #2643: registration-aware warning merge and diagnostics publish.

use super::warnings::merge_registration_sorry_warning;
use crate::document::{Document, Warning, WarningCode};
use tower_lsp::lsp_types::Url;

#[test]
fn test_explicit_registration_warning_is_not_duplicated() {
    // Surface scan already found a sorry token — registration report is
    // ExplicitSorry. The merge should keep the precise surface warning and
    // not add a duplicate declaration-level one.
    let surface = vec![Warning {
        start: 20,
        end: 25,
        message: "declaration uses `sorry` (incomplete proof)".to_string(),
        code: WarningCode::IncompleteProof,
        related: Vec::new(),
    }];

    let report = clean_elab::RegistrationWarning {
        decl_name: "myDef".parse::<clean_kernel::Name>().unwrap(),
        kind: clean_elab::RegistrationWarningKind::ExplicitSorry,
        summary: clean_kernel::env::DeclarationTrustSummary {
            has_explicit_sorry: true,
            has_synthetic_sorry: false,
            trusted_arith_count: 0,
            trusted_ay_count: 0,
        },
    };

    let result = merge_registration_sorry_warning(surface, Some(&report), "myDef", (0, 40));

    assert_eq!(
        result.len(),
        1,
        "should keep exactly the original surface warning"
    );
    assert_eq!(result[0].start, 20);
    assert_eq!(result[0].end, 25);
    assert_eq!(result[0].code, WarningCode::IncompleteProof);
}

#[test]
fn test_synthetic_registration_warning_uses_declaration_span() {
    // No surface incomplete-proof warning; registration report is
    // SyntheticSorry. The merge should add one declaration-level warning.
    let surface: Vec<Warning> = vec![];

    let report = clean_elab::RegistrationWarning {
        decl_name: "myThm".parse::<clean_kernel::Name>().unwrap(),
        kind: clean_elab::RegistrationWarningKind::SyntheticSorry,
        summary: clean_kernel::env::DeclarationTrustSummary {
            has_explicit_sorry: false,
            has_synthetic_sorry: true,
            trusted_arith_count: 0,
            trusted_ay_count: 0,
        },
    };

    let result = merge_registration_sorry_warning(surface, Some(&report), "myThm", (0, 50));

    assert_eq!(
        result.len(),
        1,
        "should produce exactly one synthetic warning"
    );
    assert_eq!(result[0].start, 0);
    assert_eq!(result[0].end, 50);
    assert_eq!(result[0].code, WarningCode::IncompleteProof);
    assert!(
        result[0].message.contains("synthetic sorry"),
        "message should mention synthetic sorry: {}",
        result[0].message
    );
}

#[test]
fn test_synthetic_registration_warning_overrides_surface_warning() {
    // Surface scan found explicit sorry tokens, but registration says
    // SyntheticSorry (which wins). The merge should remove the surface
    // incomplete-proof warnings and produce one declaration-level one.
    let surface = vec![
        Warning {
            start: 10,
            end: 15,
            message: "declaration uses `sorry` (incomplete proof)".to_string(),
            code: WarningCode::IncompleteProof,
            related: Vec::new(),
        },
        Warning {
            start: 5,
            end: 8,
            message: "unused variable `x`".to_string(),
            code: WarningCode::UnusedVariable,
            related: Vec::new(),
        },
    ];

    let report = clean_elab::RegistrationWarning {
        decl_name: "myDef".parse::<clean_kernel::Name>().unwrap(),
        kind: clean_elab::RegistrationWarningKind::SyntheticSorry,
        summary: clean_kernel::env::DeclarationTrustSummary {
            has_explicit_sorry: true,
            has_synthetic_sorry: true,
            trusted_arith_count: 0,
            trusted_ay_count: 0,
        },
    };

    let result = merge_registration_sorry_warning(surface, Some(&report), "myDef", (0, 40));

    // Should have: 1 unused-variable + 1 synthetic incomplete-proof
    assert_eq!(result.len(), 2);
    let incomplete: Vec<_> = result
        .iter()
        .filter(|w| w.code == WarningCode::IncompleteProof)
        .collect();
    assert_eq!(incomplete.len(), 1);
    assert_eq!(incomplete[0].start, 0);
    assert_eq!(incomplete[0].end, 40);
    assert!(incomplete[0].message.contains("synthetic sorry"));

    let unused: Vec<_> = result
        .iter()
        .filter(|w| w.code == WarningCode::UnusedVariable)
        .collect();
    assert_eq!(unused.len(), 1, "unrelated warnings must be preserved");
}

#[test]
fn test_explicit_registration_warning_fallback_when_no_surface_incomplete() {
    // Registration says ExplicitSorry but surface scan did NOT find any
    // IncompleteProof warnings (sorry was inside a tactic block or nested
    // expression the surface scanner doesn't traverse). The merge should
    // add one declaration-level fallback warning.
    let surface = vec![Warning {
        start: 5,
        end: 8,
        message: "unused variable `y`".to_string(),
        code: WarningCode::UnusedVariable,
        related: Vec::new(),
    }];

    let report = clean_elab::RegistrationWarning {
        decl_name: "myLemma".parse::<clean_kernel::Name>().unwrap(),
        kind: clean_elab::RegistrationWarningKind::ExplicitSorry,
        summary: clean_kernel::env::DeclarationTrustSummary {
            has_explicit_sorry: true,
            has_synthetic_sorry: false,
            trusted_arith_count: 0,
            trusted_ay_count: 0,
        },
    };

    let result = merge_registration_sorry_warning(surface, Some(&report), "myLemma", (0, 60));

    // Should have: 1 unused-variable (preserved) + 1 declaration-level
    // IncompleteProof fallback
    assert_eq!(result.len(), 2);
    let incomplete: Vec<_> = result
        .iter()
        .filter(|w| w.code == WarningCode::IncompleteProof)
        .collect();
    assert_eq!(
        incomplete.len(),
        1,
        "should produce one fallback incomplete-proof warning"
    );
    assert_eq!(incomplete[0].start, 0);
    assert_eq!(incomplete[0].end, 60);
    assert!(
        incomplete[0].message.contains("explicit sorry"),
        "message should mention explicit sorry: {}",
        incomplete[0].message
    );

    let unused: Vec<_> = result
        .iter()
        .filter(|w| w.code == WarningCode::UnusedVariable)
        .collect();
    assert_eq!(unused.len(), 1, "unrelated warnings must be preserved");
}

#[test]
fn test_none_registration_report_preserves_surface_warnings() {
    let surface = vec![Warning {
        start: 10,
        end: 15,
        message: "declaration uses `sorry` (incomplete proof)".to_string(),
        code: WarningCode::IncompleteProof,
        related: Vec::new(),
    }];

    let result = merge_registration_sorry_warning(surface.clone(), None, "myDef", (0, 40));

    assert_eq!(result.len(), surface.len());
    assert_eq!(result[0].start, 10);
}

#[test]
fn test_generate_all_diagnostics_includes_warning() {
    // Verify that the shared diagnostics generator (now used by the live
    // backend) actually surfaces warning diagnostics, not just errors.
    use crate::document::{ElaboratedDocument, ParsedDocument};

    let uri = Url::parse("file:///test.lean").unwrap();
    let mut doc = Document::new(
        uri,
        1,
        "theorem t : True := sorry\n".to_string(),
        "lean".to_string(),
    );

    doc.parsed = Some(ParsedDocument {
        errors: vec![],
        commands: vec![],
    });

    doc.elaborated = Some(ElaboratedDocument {
        errors: vec![],
        warnings: vec![Warning {
            start: 20,
            end: 25,
            message: "declaration uses `sorry` (incomplete proof)".to_string(),
            code: WarningCode::IncompleteProof,
            related: Vec::new(),
        }],
        declarations: vec![],
        holes: vec![],
        widget_modules: vec![],
    });

    let diagnostics = crate::diagnostics::generate_all_diagnostics(&doc);

    assert_eq!(
        diagnostics.len(),
        1,
        "should produce one warning diagnostic"
    );
    assert_eq!(
        diagnostics[0].severity,
        Some(tower_lsp::lsp_types::DiagnosticSeverity::WARNING)
    );
    assert_eq!(
        diagnostics[0].code,
        Some(tower_lsp::lsp_types::NumberOrString::String(
            "incomplete-proof".to_string()
        ))
    );
}
