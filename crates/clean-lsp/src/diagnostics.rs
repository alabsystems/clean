// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Diagnostic generation from parse errors, type errors, and warnings
//!
//! Converts clean parser and elaborator errors/warnings into LSP diagnostics.

use crate::document::{Document, ElaboratedDocument, ParsedDocument, RelatedLocation, WarningCode};
use tower_lsp::lsp_types::{
    Diagnostic, DiagnosticRelatedInformation, DiagnosticSeverity, DiagnosticTag, Location,
    NumberOrString, Range,
};

/// Convert document-relative related locations into the LSP
/// `DiagnosticRelatedInformation` shape (a `Location { uri, range }` plus a
/// message), resolving byte offsets against the owning document.
///
/// Returns `None` when there are no related locations, so diagnostics without
/// genuine secondary context keep `related_information: None` (backward
/// compatible — no fabricated locations).
fn build_related_information(
    doc: &Document,
    related: &[RelatedLocation],
) -> Option<Vec<DiagnosticRelatedInformation>> {
    if related.is_empty() {
        return None;
    }

    Some(
        related
            .iter()
            .map(|rel| DiagnosticRelatedInformation {
                location: Location {
                    uri: doc.uri.clone(),
                    range: Range {
                        start: doc.offset_to_position(rel.start),
                        end: doc.offset_to_position(rel.end),
                    },
                },
                message: rel.message.clone(),
            })
            .collect(),
    )
}

/// Generate LSP diagnostics from a parsed document
#[must_use]
pub fn generate_parse_diagnostics(doc: &Document, parsed: &ParsedDocument) -> Vec<Diagnostic> {
    parsed
        .errors
        .iter()
        .map(|err| {
            let start = doc.offset_to_position(err.start);
            let end = doc.offset_to_position(err.end);

            Diagnostic {
                range: Range { start, end },
                severity: Some(DiagnosticSeverity::ERROR),
                code: Some(NumberOrString::String("parse-error".to_string())),
                code_description: None,
                source: Some("clean".to_string()),
                message: err.message.clone(),
                related_information: build_related_information(doc, &err.related),
                tags: None,
                data: None,
            }
        })
        .collect()
}

/// Generate LSP diagnostics from an elaborated document's type errors
#[must_use]
pub fn generate_type_diagnostics(doc: &Document, elab: &ElaboratedDocument) -> Vec<Diagnostic> {
    elab.errors
        .iter()
        .map(|err| {
            let start = doc.offset_to_position(err.start);
            let end = doc.offset_to_position(err.end);

            Diagnostic {
                range: Range { start, end },
                severity: Some(DiagnosticSeverity::ERROR),
                code: Some(NumberOrString::String("type-error".to_string())),
                code_description: None,
                source: Some("clean".to_string()),
                message: err.message.clone(),
                related_information: build_related_information(doc, &err.related),
                tags: None,
                data: None,
            }
        })
        .collect()
}

/// Generate LSP diagnostics from an elaborated document's warnings
#[must_use]
pub fn generate_warning_diagnostics(doc: &Document, elab: &ElaboratedDocument) -> Vec<Diagnostic> {
    elab.warnings
        .iter()
        .map(|warn| {
            let start = doc.offset_to_position(warn.start);
            let end = doc.offset_to_position(warn.end);

            // Map warning codes to diagnostic codes and tags
            let (code_str, tags) = match warn.code {
                WarningCode::UnusedVariable | WarningCode::UnusedImport => {
                    ("unused".to_string(), Some(vec![DiagnosticTag::UNNECESSARY]))
                }
                WarningCode::DeprecatedFeature => (
                    "deprecated".to_string(),
                    Some(vec![DiagnosticTag::DEPRECATED]),
                ),
                WarningCode::UnreachableCode => (
                    "unreachable".to_string(),
                    Some(vec![DiagnosticTag::UNNECESSARY]),
                ),
                WarningCode::IncompleteProof => (
                    "incomplete-proof".to_string(),
                    None, // No special tag - just a warning
                ),
                WarningCode::Other => ("warning".to_string(), None),
            };

            Diagnostic {
                range: Range { start, end },
                severity: Some(DiagnosticSeverity::WARNING),
                code: Some(NumberOrString::String(code_str)),
                code_description: None,
                source: Some("clean".to_string()),
                message: warn.message.clone(),
                related_information: build_related_information(doc, &warn.related),
                tags,
                data: None,
            }
        })
        .collect()
}

/// Combine all diagnostics for a document
#[must_use]
pub fn generate_all_diagnostics(doc: &Document) -> Vec<Diagnostic> {
    let mut diagnostics = Vec::new();

    if let Some(parsed) = &doc.parsed {
        diagnostics.extend(generate_parse_diagnostics(doc, parsed));
    }

    if let Some(elab) = &doc.elaborated {
        diagnostics.extend(generate_type_diagnostics(doc, elab));
        diagnostics.extend(generate_warning_diagnostics(doc, elab));
    }

    diagnostics
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::document::{ParseError, TypeError};
    use tower_lsp::lsp_types::Url;

    #[test]
    fn test_parse_diagnostic_generation() {
        let uri = Url::parse("file:///test.lean").unwrap();
        let doc = Document::new(uri, 1, "def x :=\n".to_string(), "lean".to_string());

        let parsed = ParsedDocument {
            errors: vec![ParseError {
                start: 8,
                end: 9,
                message: "expected expression".to_string(),
                related: Vec::new(),
            }],
            commands: vec![],
        };

        let diagnostics = generate_parse_diagnostics(&doc, &parsed);

        assert_eq!(diagnostics.len(), 1);
        assert_eq!(diagnostics[0].severity, Some(DiagnosticSeverity::ERROR));
        assert_eq!(diagnostics[0].message, "expected expression");
        assert_eq!(diagnostics[0].source, Some("clean".to_string()));
    }

    #[test]
    fn test_type_diagnostic_generation() {
        let uri = Url::parse("file:///test.lean").unwrap();
        let doc = Document::new(
            uri,
            1,
            "def x : Nat := \"hello\"\n".to_string(),
            "lean".to_string(),
        );

        let elab = ElaboratedDocument {
            errors: vec![TypeError {
                start: 15,
                end: 22,
                message: "type mismatch: expected Nat, got String".to_string(),
                related: Vec::new(),
            }],
            warnings: vec![],
            declarations: vec![],
            holes: vec![],
            widget_modules: vec![],
        };

        let diagnostics = generate_type_diagnostics(&doc, &elab);

        assert_eq!(diagnostics.len(), 1);
        assert_eq!(diagnostics[0].severity, Some(DiagnosticSeverity::ERROR));
        assert!(diagnostics[0].message.contains("type mismatch"));
    }

    #[test]
    fn test_empty_diagnostics() {
        let uri = Url::parse("file:///test.lean").unwrap();
        let doc = Document::new(uri, 1, "def x := 1\n".to_string(), "lean".to_string());

        let parsed = ParsedDocument {
            errors: vec![],
            commands: vec![],
        };

        let diagnostics = generate_parse_diagnostics(&doc, &parsed);
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn test_combined_diagnostics() {
        let uri = Url::parse("file:///test.lean").unwrap();
        let mut doc = Document::new(uri, 1, "def x := 1\n".to_string(), "lean".to_string());

        doc.parsed = Some(ParsedDocument {
            errors: vec![ParseError {
                start: 0,
                end: 3,
                message: "parse error".to_string(),
                related: Vec::new(),
            }],
            commands: vec![],
        });

        doc.elaborated = Some(ElaboratedDocument {
            errors: vec![TypeError {
                start: 9,
                end: 10,
                message: "type error".to_string(),
                related: Vec::new(),
            }],
            warnings: vec![],
            declarations: vec![],
            holes: vec![],
            widget_modules: vec![],
        });

        let diagnostics = generate_all_diagnostics(&doc);
        assert_eq!(diagnostics.len(), 2);

        // Verify one is a parse error and one is a type error
        let codes: Vec<String> = diagnostics
            .iter()
            .filter_map(|d| d.code.as_ref())
            .map(|c| match c {
                NumberOrString::String(s) => s.clone(),
                NumberOrString::Number(n) => n.to_string(),
            })
            .collect();
        assert!(
            codes.contains(&"parse-error".to_string()),
            "should contain parse error"
        );
        assert!(
            codes.contains(&"type-error".to_string()),
            "should contain type error"
        );

        // Both should be ERROR severity
        for d in &diagnostics {
            assert_eq!(d.severity, Some(DiagnosticSeverity::ERROR));
        }

        // Verify messages propagated
        let messages: Vec<&str> = diagnostics.iter().map(|d| d.message.as_str()).collect();
        assert!(
            messages.contains(&"parse error"),
            "parse error message should propagate"
        );
        assert!(
            messages.contains(&"type error"),
            "type error message should propagate"
        );
    }

    #[test]
    fn test_warning_diagnostic_generation() {
        use crate::document::Warning;

        let uri = Url::parse("file:///test.lean").unwrap();
        let doc = Document::new(
            uri,
            1,
            "def x (unused : Nat) := 1\n".to_string(),
            "lean".to_string(),
        );

        let elab = ElaboratedDocument {
            errors: vec![],
            warnings: vec![Warning {
                start: 7,
                end: 13,
                message: "unused variable 'unused'".to_string(),
                code: WarningCode::UnusedVariable,
                related: Vec::new(),
            }],
            declarations: vec![],
            holes: vec![],
            widget_modules: vec![],
        };

        let diagnostics = generate_warning_diagnostics(&doc, &elab);

        assert_eq!(diagnostics.len(), 1);
        assert_eq!(diagnostics[0].severity, Some(DiagnosticSeverity::WARNING));
        assert!(diagnostics[0].message.contains("unused variable"));
        assert_eq!(
            diagnostics[0].code,
            Some(NumberOrString::String("unused".to_string()))
        );
        assert_eq!(diagnostics[0].tags, Some(vec![DiagnosticTag::UNNECESSARY]));
    }

    #[test]
    fn test_deprecated_warning() {
        use crate::document::Warning;

        let uri = Url::parse("file:///test.lean").unwrap();
        let doc = Document::new(
            uri,
            1,
            "def x := oldFunction\n".to_string(),
            "lean".to_string(),
        );

        let elab = ElaboratedDocument {
            errors: vec![],
            warnings: vec![Warning {
                start: 9,
                end: 20,
                message: "'oldFunction' is deprecated".to_string(),
                code: WarningCode::DeprecatedFeature,
                related: Vec::new(),
            }],
            declarations: vec![],
            holes: vec![],
            widget_modules: vec![],
        };

        let diagnostics = generate_warning_diagnostics(&doc, &elab);

        assert_eq!(diagnostics.len(), 1);
        assert_eq!(diagnostics[0].severity, Some(DiagnosticSeverity::WARNING));
        assert_eq!(
            diagnostics[0].code,
            Some(NumberOrString::String("deprecated".to_string()))
        );
        assert_eq!(diagnostics[0].tags, Some(vec![DiagnosticTag::DEPRECATED]));
    }

    #[test]
    fn test_combined_errors_and_warnings() {
        use crate::document::Warning;

        let uri = Url::parse("file:///test.lean").unwrap();
        let mut doc = Document::new(
            uri,
            1,
            "def x (y : Nat) := 1\n".to_string(),
            "lean".to_string(),
        );

        doc.parsed = Some(ParsedDocument {
            errors: vec![],
            commands: vec![],
        });

        doc.elaborated = Some(ElaboratedDocument {
            errors: vec![TypeError {
                start: 0,
                end: 3,
                message: "type error".to_string(),
                related: Vec::new(),
            }],
            warnings: vec![Warning {
                start: 7,
                end: 8,
                message: "unused variable 'y'".to_string(),
                code: WarningCode::UnusedVariable,
                related: Vec::new(),
            }],
            declarations: vec![],
            holes: vec![],
            widget_modules: vec![],
        });

        let diagnostics = generate_all_diagnostics(&doc);
        assert_eq!(diagnostics.len(), 2);

        // One error, one warning
        let errors: Vec<_> = diagnostics
            .iter()
            .filter(|d| d.severity == Some(DiagnosticSeverity::ERROR))
            .collect();
        let warnings: Vec<_> = diagnostics
            .iter()
            .filter(|d| d.severity == Some(DiagnosticSeverity::WARNING))
            .collect();

        assert_eq!(errors.len(), 1);
        assert_eq!(warnings.len(), 1);
    }

    #[test]
    fn test_warning_with_related_location_populates_related_information() {
        use crate::document::{RelatedLocation, Warning};

        // "def f (x : Nat) (x : Nat) := 1": the second `x` is a duplicate
        // binder; the related location points at the first `x`.
        let uri = Url::parse("file:///test.lean").unwrap();
        let text = "def f (x : Nat) (x : Nat) := 1\n".to_string();
        let first_x = text.find("(x").expect("first binder") + 1;
        let second_x = text.rfind("(x").expect("second binder") + 1;
        let doc = Document::new(uri.clone(), 1, text, "lean".to_string());

        let elab = ElaboratedDocument {
            errors: vec![],
            warnings: vec![Warning {
                start: second_x,
                end: second_x + 1,
                message: "duplicate binder `x`".to_string(),
                code: WarningCode::Other,
                related: vec![RelatedLocation {
                    start: first_x,
                    end: first_x + 1,
                    message: "first binding of `x` is here".to_string(),
                }],
            }],
            declarations: vec![],
            holes: vec![],
            widget_modules: vec![],
        };

        let diagnostics = generate_warning_diagnostics(&doc, &elab);
        assert_eq!(diagnostics.len(), 1);

        let related = diagnostics[0]
            .related_information
            .as_ref()
            .expect("related_information should be populated");
        assert_eq!(related.len(), 1);
        // The related location points at the first binder's range and URI.
        assert_eq!(related[0].location.uri, uri);
        assert_eq!(
            related[0].location.range.start,
            doc.offset_to_position(first_x)
        );
        assert_eq!(
            related[0].location.range.end,
            doc.offset_to_position(first_x + 1)
        );
        assert_eq!(related[0].message, "first binding of `x` is here");
    }

    #[test]
    fn test_diagnostic_without_related_context_has_none() {
        // A plain warning with no related locations keeps related_information None.
        use crate::document::Warning;

        let uri = Url::parse("file:///test.lean").unwrap();
        let doc = Document::new(
            uri,
            1,
            "def x (y : Nat) := 1\n".to_string(),
            "lean".to_string(),
        );

        let elab = ElaboratedDocument {
            errors: vec![],
            warnings: vec![Warning {
                start: 7,
                end: 8,
                message: "unused variable `y`".to_string(),
                code: WarningCode::UnusedVariable,
                related: Vec::new(),
            }],
            declarations: vec![],
            holes: vec![],
            widget_modules: vec![],
        };

        let diagnostics = generate_warning_diagnostics(&doc, &elab);
        assert_eq!(diagnostics.len(), 1);
        assert!(
            diagnostics[0].related_information.is_none(),
            "no related context means related_information stays None"
        );
    }

    #[test]
    fn test_type_error_related_information_matches_lsp_shape() {
        use crate::document::{RelatedLocation, TypeError};

        let uri = Url::parse("file:///test.lean").unwrap();
        let doc = Document::new(
            uri.clone(),
            1,
            "def a : Nat := 0\ndef b : Nat := a true\n".to_string(),
            "lean".to_string(),
        );

        let elab = ElaboratedDocument {
            errors: vec![TypeError {
                start: 31,
                end: 32,
                message: "type mismatch".to_string(),
                related: vec![RelatedLocation {
                    start: 4,
                    end: 5,
                    message: "expected type comes from `a`".to_string(),
                }],
            }],
            warnings: vec![],
            declarations: vec![],
            holes: vec![],
            widget_modules: vec![],
        };

        let diagnostics = generate_type_diagnostics(&doc, &elab);
        let related = diagnostics[0]
            .related_information
            .as_ref()
            .expect("type error should carry related_information");

        // Serialize the diagnostic and check the DiagnosticRelatedInformation
        // JSON shape: `relatedInformation: [{ location: { uri, range }, message }]`.
        let json = serde_json::to_value(&diagnostics[0]).expect("diagnostic serializes");
        let rel_json = json
            .get("relatedInformation")
            .and_then(|v| v.as_array())
            .expect("relatedInformation array present");
        assert_eq!(rel_json.len(), 1);
        let entry = &rel_json[0];
        assert!(entry.get("location").is_some(), "location field present");
        assert!(
            entry.get("location").and_then(|l| l.get("uri")).is_some(),
            "location.uri present"
        );
        assert!(
            entry.get("location").and_then(|l| l.get("range")).is_some(),
            "location.range present"
        );
        assert_eq!(
            entry.get("message").and_then(|m| m.as_str()),
            Some("expected type comes from `a`")
        );
        // And the typed value round-trips with the source URI.
        assert_eq!(related[0].location.uri, uri);
    }
}
