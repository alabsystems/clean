// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Nuprl importer (CTT → clean direct extraction).
//!
//! Nuprl is a constructive type theory (CTT) prover that produces proof objects
//! with computational content ("extracts"). This importer handles Nuprl library
//! dumps containing declarations, each with an optional proof extract and a
//! proof status.
//!
//! # Axiom profiles
//!
//! - Fully proved declarations → `CLASSICAL` (Nuprl's classical rules)
//! - Axiom declarations → `CLASSICAL` (conservatively marked)

use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::types::{AxiomProfile, Provenance, SourceSystem, TrustLevel};

// ---------------------------------------------------------------------------
// Errors
// ---------------------------------------------------------------------------

/// Errors during Nuprl library import.
#[derive(Debug, Error)]
#[non_exhaustive]
pub enum NuprlError {
    /// Failed to parse the Nuprl library text.
    #[error("Nuprl parse error at offset {offset}: {message}")]
    ParseError { offset: usize, message: String },

    /// Encountered an unsupported tactic reference.
    #[error("unsupported Nuprl tactic: {tactic_name}")]
    UnsupportedTactic { tactic_name: String },

    /// Type mismatch during term reconstruction.
    #[error("Nuprl type mismatch: expected {expected}, got {actual}")]
    TypeMismatch { expected: String, actual: String },
}

// ---------------------------------------------------------------------------
// Domain types
// ---------------------------------------------------------------------------

/// Nuprl term representation (core CTT terms).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum NuprlTerm {
    /// Variable reference.
    Var(String),
    /// Lambda abstraction: `λx. body`.
    Lambda(String, Box<NuprlTerm>),
    /// Application: `f a`.
    Apply(Box<NuprlTerm>, Box<NuprlTerm>),
    /// Universe level: `U_i`.
    Universe(u32),
    /// Intersection type: `⋂x:A. B`.
    Isect(String, Box<NuprlTerm>, Box<NuprlTerm>),
    /// Set type: `{x:A | B}`.
    Set(String, Box<NuprlTerm>, Box<NuprlTerm>),
    /// Equality type: `a = b ∈ T`.
    Equal(Box<NuprlTerm>, Box<NuprlTerm>, Box<NuprlTerm>),
}

/// Proof status of a Nuprl declaration.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum ProofStatus {
    /// Fully proved with extract term.
    Proved,
    /// Proof incomplete (partial extract or holes).
    Incomplete,
    /// Asserted as axiom (no proof).
    Axiom,
}

/// A single declaration in a Nuprl library.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct NuprlDeclaration {
    pub name: String,
    pub term: NuprlTerm,
    pub extract: Option<NuprlTerm>,
    pub status: ProofStatus,
}

/// A parsed Nuprl library.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct NuprlLibrary {
    pub name: String,
    pub declarations: Vec<NuprlDeclaration>,
}

/// Result of importing a Nuprl library into the Mathverse library.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct NuprlImportResult {
    pub name: String,
    pub decl_count: usize,
    pub proved_count: usize,
    pub axiom_profile: AxiomProfile,
    pub trust_level: TrustLevel,
    pub provenance: Provenance,
    pub diagnostics: Vec<String>,
}

// ---------------------------------------------------------------------------
// Importer
// ---------------------------------------------------------------------------

/// Importer for Nuprl libraries into the Mathverse library.
pub struct NuprlImporter {
    namespace: String,
}

impl Default for NuprlImporter {
    fn default() -> Self {
        Self::new()
    }
}

impl NuprlImporter {
    /// Create a new Nuprl importer with default namespace.
    #[must_use]
    pub fn new() -> Self {
        Self {
            namespace: "Nuprl.Imported".to_owned(),
        }
    }

    /// Import a library from its textual representation.
    ///
    /// Performs a lightweight parse of the declaration dump format. Each
    /// declaration line has the form: `STATUS NAME : TERM [>> EXTRACT]`
    pub fn import_library(&self, lib_text: &str) -> Result<NuprlLibrary, NuprlError> {
        let trimmed = lib_text.trim();
        if trimmed.is_empty() {
            return Err(NuprlError::ParseError {
                offset: 0,
                message: "empty library text".to_owned(),
            });
        }

        let mut declarations = Vec::new();
        let mut lib_name = "unnamed-library".to_owned();

        for line in trimmed.lines() {
            let line = line.trim();

            // Library header line.
            if line.starts_with("LIBRARY ") {
                lib_name = line
                    .strip_prefix("LIBRARY ")
                    .unwrap_or("unnamed-library")
                    .trim()
                    .to_owned();
                continue;
            }

            // Skip comments and blank lines.
            if line.is_empty() || line.starts_with('#') || line.starts_with("--") {
                continue;
            }

            // Parse declaration: STATUS NAME : TYPE [>> EXTRACT]
            let (status, rest) = parse_status_prefix(line)?;
            let (name, type_str, extract_str) = parse_decl_body(rest)?;

            let term = parse_simple_term(type_str);
            let extract = extract_str.map(parse_simple_term);

            declarations.push(NuprlDeclaration {
                name,
                term,
                extract,
                status,
            });
        }

        Ok(NuprlLibrary {
            name: lib_name,
            declarations,
        })
    }

    /// Produce an import result summary for a parsed library.
    #[must_use]
    pub fn import_result(&self, lib: &NuprlLibrary) -> NuprlImportResult {
        let decl_count = lib.declarations.len();
        let proved_count = lib
            .declarations
            .iter()
            .filter(|d| d.status == ProofStatus::Proved)
            .count();
        let axiom_count = lib
            .declarations
            .iter()
            .filter(|d| d.status == ProofStatus::Axiom)
            .count();
        let incomplete_count = lib
            .declarations
            .iter()
            .filter(|d| d.status == ProofStatus::Incomplete)
            .count();

        // Nuprl is classically flavored; all imports carry CLASSICAL.
        let axiom_profile = AxiomProfile::CLASSICAL;

        let trust_level = if axiom_count > 0 || incomplete_count > 0 {
            TrustLevel::PartiallyAxiomatized
        } else {
            TrustLevel::CertificateReplayed
        };

        let qualified_name = format!("{}.{}", self.namespace, lib.name);

        let provenance = Provenance {
            source: SourceSystem::Nuprl,
            original_name: lib.name.clone(),
            source_file: None,
            axiom_profile,
        };

        let mut diagnostics = Vec::new();
        if axiom_count > 0 {
            diagnostics.push(format!("{axiom_count} axiom declaration(s) without proof"));
        }
        if incomplete_count > 0 {
            diagnostics.push(format!("{incomplete_count} incomplete proof(s)"));
        }

        NuprlImportResult {
            name: qualified_name,
            decl_count,
            proved_count,
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

/// Parse the status prefix from a declaration line.
fn parse_status_prefix(line: &str) -> Result<(ProofStatus, &str), NuprlError> {
    if let Some(rest) = line.strip_prefix("PROVED ") {
        Ok((ProofStatus::Proved, rest))
    } else if let Some(rest) = line.strip_prefix("INCOMPLETE ") {
        Ok((ProofStatus::Incomplete, rest))
    } else if let Some(rest) = line.strip_prefix("AXIOM ") {
        Ok((ProofStatus::Axiom, rest))
    } else {
        Err(NuprlError::ParseError {
            offset: 0,
            message: format!("expected status prefix (PROVED/INCOMPLETE/AXIOM): {line}"),
        })
    }
}

/// Parse the body of a declaration after the status prefix.
/// Format: `NAME : TYPE [>> EXTRACT]`
fn parse_decl_body(rest: &str) -> Result<(String, &str, Option<&str>), NuprlError> {
    let (name_part, type_and_extract) =
        rest.split_once(" : ")
            .ok_or_else(|| NuprlError::ParseError {
                offset: 0,
                message: format!("expected ' : ' separator in declaration: {rest}"),
            })?;

    let name = name_part.trim().to_owned();
    if name.is_empty() {
        return Err(NuprlError::ParseError {
            offset: 0,
            message: "empty declaration name".to_owned(),
        });
    }

    let (type_str, extract_str) = if let Some((t, e)) = type_and_extract.split_once(" >> ") {
        (t.trim(), Some(e.trim()))
    } else {
        (type_and_extract.trim(), None)
    };

    Ok((name, type_str, extract_str))
}

/// Parse a simple term from a string representation.
///
/// This is a placeholder parser that wraps the string in a `Var` node
/// for simple identifiers and `Universe(n)` for `U<n>` patterns. A full
/// implementation would recursively parse the Nuprl term grammar.
fn parse_simple_term(s: &str) -> NuprlTerm {
    let s = s.trim();
    if let Some(rest) = s.strip_prefix('U') {
        if let Ok(level) = rest.parse::<u32>() {
            return NuprlTerm::Universe(level);
        }
    }
    NuprlTerm::Var(s.to_owned())
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    const MOCK_LIBRARY: &str = r#"LIBRARY BasicArith
PROVED add_comm : ∀x,y:ℕ. x+y = y+x ∈ ℕ >> λx.λy.ind(x; ...)
PROVED add_assoc : ∀x,y,z:ℕ. (x+y)+z = x+(y+z) ∈ ℕ >> λx.λy.λz.ind(x; ...)
AXIOM add_ident : ∀x:ℕ. x+0 = x ∈ ℕ
"#;

    #[test]
    fn test_nuprl_import_library_parses_declarations() {
        let importer = NuprlImporter::new();
        let lib = importer
            .import_library(MOCK_LIBRARY)
            .expect("should parse mock library");

        assert_eq!(lib.name, "BasicArith");
        assert_eq!(lib.declarations.len(), 3);
        assert_eq!(lib.declarations[0].status, ProofStatus::Proved);
        assert_eq!(lib.declarations[2].status, ProofStatus::Axiom);
    }

    #[test]
    fn test_nuprl_import_library_empty_input() {
        let importer = NuprlImporter::new();
        let result = importer.import_library("");
        assert!(result.is_err());
    }

    #[test]
    fn test_nuprl_import_result_counts() {
        let importer = NuprlImporter::new();
        let lib = importer.import_library(MOCK_LIBRARY).expect("should parse");
        let result = importer.import_result(&lib);

        assert_eq!(result.decl_count, 3);
        assert_eq!(result.proved_count, 2);
        assert!(result.axiom_profile.contains(AxiomProfile::CLASSICAL));
        assert_eq!(result.trust_level, TrustLevel::PartiallyAxiomatized);
        assert_eq!(result.provenance.source, SourceSystem::Nuprl);
    }

    #[test]
    fn test_nuprl_fully_proved_library() {
        let input = r#"LIBRARY FullyProved
PROVED thm1 : P >> extract1
PROVED thm2 : Q >> extract2
"#;
        let importer = NuprlImporter::new();
        let lib = importer.import_library(input).expect("should parse");
        let result = importer.import_result(&lib);

        assert_eq!(result.trust_level, TrustLevel::CertificateReplayed);
        assert!(result.diagnostics.is_empty());
    }

    #[test]
    fn test_nuprl_term_variants() {
        let var = NuprlTerm::Var("x".to_owned());
        let lam = NuprlTerm::Lambda("x".to_owned(), Box::new(NuprlTerm::Var("x".to_owned())));
        let app = NuprlTerm::Apply(
            Box::new(NuprlTerm::Var("f".to_owned())),
            Box::new(NuprlTerm::Var("x".to_owned())),
        );
        let univ = NuprlTerm::Universe(1);
        let isect = NuprlTerm::Isect(
            "x".to_owned(),
            Box::new(NuprlTerm::Universe(0)),
            Box::new(NuprlTerm::Var("x".to_owned())),
        );
        let set = NuprlTerm::Set(
            "x".to_owned(),
            Box::new(NuprlTerm::Universe(0)),
            Box::new(NuprlTerm::Var("x".to_owned())),
        );
        let eq = NuprlTerm::Equal(
            Box::new(NuprlTerm::Var("a".to_owned())),
            Box::new(NuprlTerm::Var("b".to_owned())),
            Box::new(NuprlTerm::Universe(0)),
        );

        // Verify Debug + Clone + PartialEq.
        assert_eq!(var.clone(), var);
        let _ = format!("{:?}", lam);
        let _ = format!("{:?}", app);
        let _ = format!("{:?}", univ);
        let _ = format!("{:?}", isect);
        let _ = format!("{:?}", set);
        let _ = format!("{:?}", eq);
    }

    #[test]
    fn test_nuprl_parse_simple_term_universe() {
        let term = parse_simple_term("U3");
        assert_eq!(term, NuprlTerm::Universe(3));
    }

    #[test]
    fn test_nuprl_importer_default() {
        let importer = NuprlImporter::default();
        assert_eq!(importer.namespace, "Nuprl.Imported");
    }

    #[test]
    fn test_nuprl_incomplete_proof_diagnostic() {
        let input = r#"LIBRARY Partial
PROVED thm1 : P >> e1
INCOMPLETE thm2 : Q
"#;
        let importer = NuprlImporter::new();
        let lib = importer.import_library(input).expect("should parse");
        let result = importer.import_result(&lib);

        assert_eq!(result.trust_level, TrustLevel::PartiallyAxiomatized);
        assert!(result.diagnostics.iter().any(|d| d.contains("incomplete")));
    }
}
