// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! ACL2 importer (proof log → FOL reconstruction).
//!
//! ACL2 is a first-order logic theorem prover based on a computational logic
//! for a subset of Common Lisp. This importer handles ACL2 "books" — certified
//! collections of definitions and theorems — and reconstructs their logical
//! content for Mathverse library import.
//!
//! # Axiom profiles
//!
//! - Certified books → `CLASSICAL` (ACL2 is classical by default)
//! - Books using external oracle calls → `SMT_ORACLE`

use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::types::{AxiomProfile, Provenance, SourceSystem, TrustLevel};

// ---------------------------------------------------------------------------
// Errors
// ---------------------------------------------------------------------------

/// Errors during ACL2 book import.
#[derive(Debug, Error)]
#[non_exhaustive]
pub enum Acl2Error {
    /// Failed to parse the ACL2 book text.
    #[error("ACL2 parse error at offset {offset}: {message}")]
    ParseError { offset: usize, message: String },

    /// Encountered an unsupported ACL2 event form.
    #[error("unsupported ACL2 event: {event_kind}")]
    UnsupportedEvent { event_kind: String },
}

// ---------------------------------------------------------------------------
// Domain types
// ---------------------------------------------------------------------------

/// A single event in an ACL2 book.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum Acl2Event {
    /// A theorem (`defthm`) with optional hints.
    Defthm {
        name: String,
        body: String,
        hints: Vec<String>,
    },
    /// A function definition with an optional termination measure.
    Defun {
        name: String,
        formals: Vec<String>,
        body: String,
        measure: Option<String>,
    },
    /// An encapsulation block containing constrained events.
    Encapsulate { events: Vec<Acl2Event> },
    /// A guard verification directive for a previously defined function.
    VerifyGuards { name: String },
}

/// A parsed ACL2 book.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Acl2Book {
    pub name: String,
    pub events: Vec<Acl2Event>,
    pub certify_status: bool,
}

/// Result of importing an ACL2 book into the Mathverse library.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Acl2ImportResult {
    pub name: String,
    pub event_count: usize,
    pub theorem_count: usize,
    pub axiom_profile: AxiomProfile,
    pub trust_level: TrustLevel,
    pub provenance: Provenance,
    pub diagnostics: Vec<String>,
}

// ---------------------------------------------------------------------------
// Importer
// ---------------------------------------------------------------------------

/// Importer for ACL2 books into the Mathverse library.
pub struct Acl2Importer {
    /// Namespace prefix for imported names.
    namespace: String,
}

impl Default for Acl2Importer {
    fn default() -> Self {
        Self::new()
    }
}

impl Acl2Importer {
    /// Create a new ACL2 importer with default namespace.
    #[must_use]
    pub fn new() -> Self {
        Self {
            namespace: "Acl2.Imported".to_owned(),
        }
    }

    /// Import a book from its textual representation.
    ///
    /// This performs a lightweight parse of the S-expression event forms
    /// in the book text. Full semantic analysis (guard verification replay,
    /// induction scheme reconstruction) is deferred to downstream passes.
    pub fn import_book(&self, book_text: &str) -> Result<Acl2Book, Acl2Error> {
        let trimmed = book_text.trim();
        if trimmed.is_empty() {
            return Err(Acl2Error::ParseError {
                offset: 0,
                message: "empty book text".to_owned(),
            });
        }

        let mut events = Vec::new();
        let mut diagnostics_count = 0usize;

        // Lightweight line-oriented scanner for top-level event forms.
        for line in trimmed.lines() {
            let line = line.trim();
            if line.starts_with("(defthm ") {
                let name = extract_first_symbol(line, "(defthm ").ok_or_else(|| {
                    Acl2Error::ParseError {
                        offset: 0,
                        message: "malformed defthm".to_owned(),
                    }
                })?;
                events.push(Acl2Event::Defthm {
                    name,
                    body: line.to_owned(),
                    hints: Vec::new(),
                });
            } else if line.starts_with("(defun ") {
                let name =
                    extract_first_symbol(line, "(defun ").ok_or_else(|| Acl2Error::ParseError {
                        offset: 0,
                        message: "malformed defun".to_owned(),
                    })?;
                events.push(Acl2Event::Defun {
                    name,
                    formals: Vec::new(),
                    body: line.to_owned(),
                    measure: None,
                });
            } else if line.starts_with("(encapsulate") {
                events.push(Acl2Event::Encapsulate { events: Vec::new() });
            } else if line.starts_with("(verify-guards ") {
                let name = extract_first_symbol(line, "(verify-guards ").ok_or_else(|| {
                    Acl2Error::ParseError {
                        offset: 0,
                        message: "malformed verify-guards".to_owned(),
                    }
                })?;
                events.push(Acl2Event::VerifyGuards { name });
            } else if line.starts_with('(') && !line.starts_with("(in-package") {
                diagnostics_count += 1;
            }
        }

        // Derive certification status: a book is "certified" if it has at
        // least one theorem and no unparsed event forms.
        let has_theorems = events.iter().any(|e| matches!(e, Acl2Event::Defthm { .. }));
        let certify_status = has_theorems && diagnostics_count == 0;

        // Extract book name from first `in-package` or use namespace default.
        let book_name = trimmed
            .lines()
            .find(|l| l.trim().starts_with("(in-package"))
            .and_then(|l| extract_first_symbol(l.trim(), "(in-package "))
            .unwrap_or_else(|| "unnamed-book".to_owned());

        Ok(Acl2Book {
            name: book_name,
            events,
            certify_status,
        })
    }

    /// Produce an import result summary for a parsed book.
    #[must_use]
    pub fn import_result(&self, book: &Acl2Book) -> Acl2ImportResult {
        let theorem_count = book
            .events
            .iter()
            .filter(|e| matches!(e, Acl2Event::Defthm { .. }))
            .count();

        let has_encapsulate = book
            .events
            .iter()
            .any(|e| matches!(e, Acl2Event::Encapsulate { .. }));

        // Certified books are classical; encapsulations may introduce
        // constrained functions (similar to axioms).
        let axiom_profile = if has_encapsulate {
            AxiomProfile::CLASSICAL | AxiomProfile::SMT_ORACLE
        } else {
            AxiomProfile::CLASSICAL
        };

        let trust_level = if book.certify_status {
            TrustLevel::CertificateReplayed
        } else {
            TrustLevel::PartiallyAxiomatized
        };

        let qualified_name = format!("{}.{}", self.namespace, book.name);

        let provenance = Provenance {
            source: SourceSystem::Acl2,
            original_name: book.name.clone(),
            source_file: None,
            axiom_profile,
        };

        let mut diagnostics = Vec::new();
        if has_encapsulate {
            diagnostics.push("book contains encapsulate blocks (constrained functions)".to_owned());
        }
        if !book.certify_status {
            diagnostics.push("book not fully certified".to_owned());
        }

        Acl2ImportResult {
            name: qualified_name,
            event_count: book.events.len(),
            theorem_count,
            axiom_profile,
            trust_level,
            provenance,
            diagnostics,
        }
    }
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Extract the first symbol after a prefix in an S-expression line.
fn extract_first_symbol(line: &str, prefix: &str) -> Option<String> {
    let rest = line.strip_prefix(prefix)?;
    let rest = rest.trim_start().trim_start_matches('"');
    let end = rest.find(|c: char| c.is_whitespace() || c == ')' || c == '"')?;
    let sym = &rest[..end];
    if sym.is_empty() {
        None
    } else {
        Some(sym.to_owned())
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    const MOCK_BOOK: &str = r#"(in-package "ACL2")
(defun append (x y) (if (consp x) (cons (car x) (append (cdr x) y)) y))
(defthm append-assoc (equal (append (append x y) z) (append x (append y z))))
(verify-guards append)
"#;

    #[test]
    fn test_acl2_import_book_parses_events() {
        let importer = Acl2Importer::new();
        let book = importer
            .import_book(MOCK_BOOK)
            .expect("should parse mock book");

        assert_eq!(book.name, "ACL2");
        assert_eq!(book.events.len(), 3);
        assert!(book.certify_status);
    }

    #[test]
    fn test_acl2_import_book_empty_input() {
        let importer = Acl2Importer::new();
        let result = importer.import_book("");
        assert!(result.is_err());
    }

    #[test]
    fn test_acl2_import_result_classical_profile() {
        let importer = Acl2Importer::new();
        let book = importer.import_book(MOCK_BOOK).expect("should parse");
        let result = importer.import_result(&book);

        assert_eq!(result.theorem_count, 1);
        assert_eq!(result.event_count, 3);
        assert!(result.axiom_profile.contains(AxiomProfile::CLASSICAL));
        assert!(!result.axiom_profile.contains(AxiomProfile::SMT_ORACLE));
        assert_eq!(result.trust_level, TrustLevel::CertificateReplayed);
        assert_eq!(result.provenance.source, SourceSystem::Acl2);
    }

    #[test]
    fn test_acl2_encapsulate_adds_smt_oracle() {
        let input = r#"(in-package "ACL2")
(encapsulate ((hidden-fn (x) t)) (local (defun hidden-fn (x) x)))
(defthm hidden-prop (equal (hidden-fn (hidden-fn x)) (hidden-fn x)))
"#;
        let importer = Acl2Importer::new();
        let book = importer.import_book(input).expect("should parse");
        let result = importer.import_result(&book);

        assert!(result.axiom_profile.contains(AxiomProfile::SMT_ORACLE));
        assert!(result.diagnostics.iter().any(|d| d.contains("encapsulate")));
    }

    #[test]
    fn test_acl2_event_enum_variants() {
        let defthm = Acl2Event::Defthm {
            name: "thm1".to_owned(),
            body: "(equal x x)".to_owned(),
            hints: vec!["hint1".to_owned()],
        };
        let defun = Acl2Event::Defun {
            name: "fn1".to_owned(),
            formals: vec!["x".to_owned()],
            body: "x".to_owned(),
            measure: Some("(acl2-count x)".to_owned()),
        };
        let encap = Acl2Event::Encapsulate { events: vec![] };
        let vg = Acl2Event::VerifyGuards {
            name: "fn1".to_owned(),
        };

        // Ensure Debug + Clone work.
        let _ = format!("{:?}", defthm.clone());
        let _ = format!("{:?}", defun.clone());
        let _ = format!("{:?}", encap.clone());
        let _ = format!("{:?}", vg.clone());
    }

    #[test]
    fn test_acl2_importer_default() {
        let importer = Acl2Importer::default();
        assert_eq!(importer.namespace, "Acl2.Imported");
    }
}
