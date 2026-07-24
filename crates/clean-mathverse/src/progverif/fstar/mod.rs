// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! F* program verification importer.
//!
//! F* is a proof-oriented programming language with an extensional type theory
//! that supports dependent types, refinement types, and monadic effects. The
//! F* verifier encodes VCs as SMT queries discharged by Z3.
//!
//! Trust model:
//! - Verified modules with Z3 discharge: `SMT_ORACLE | EXTENSIONALITY`, `TrustedOracle`
//! - Certificate-replayed modules: `SAT_CERT | EXTENSIONALITY`, `CertificateReplayed`
//! - Unverified modules: `SMT_ORACLE | EXTENSIONALITY`, `TrustedOracle`
//!
//! F* is inherently extensional (function extensionality is built into its
//! type theory), so `EXTENSIONALITY` is always part of the axiom profile.

use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::types::{AxiomProfile, Provenance, SourceSystem, TrustLevel};

// ============================================================================
// Errors
// ============================================================================

/// Errors raised during F* import operations.
#[derive(Debug, Error)]
#[non_exhaustive]
pub enum FStarError {
    /// Failed to parse an F* module or verification result.
    #[error("failed to parse F* module: {reason}")]
    ParseError { reason: String },

    /// F* module structure is invalid.
    #[error("F* module error in `{module_name}`: {reason}")]
    ModuleError { module_name: String, reason: String },

    /// An effect declaration references an unknown effect.
    #[error("unknown F* effect: `{effect}`")]
    UnknownEffect { effect: String },

    /// A verification condition could not be encoded.
    #[error("F* VC encoding error: {reason}")]
    VcEncodingError { reason: String },

    /// Unsupported F* language feature.
    #[error("unsupported F* feature: {feature}")]
    UnsupportedFeature { feature: String },
}

// ============================================================================
// Data types
// ============================================================================

/// A `val` declaration in an F* module (type signature without definition).
///
/// In F*, `val` declares a function's type signature, typically annotated with
/// effect and refinement types. A `val` may or may not have a corresponding
/// verified `let` binding.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub struct FStarValDecl {
    /// Qualified name of the val declaration.
    pub name: String,
    /// Type annotation as a string (F* syntax).
    pub type_annot: String,
    /// Whether this val has been verified by the F* checker.
    pub verified: bool,
}

/// A `let` binding in an F* module (definition with optional proof).
///
/// `let` bindings may carry proofs (via refinement types or `Lemma` effect)
/// or be computational definitions.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub struct FStarLetDecl {
    /// Qualified name of the let binding.
    pub name: String,
    /// Whether this let binding has been verified.
    pub verified: bool,
    /// Effect annotation (e.g., "Tot", "Lemma", "ML", "ST").
    pub effect: String,
    /// Source file, if known.
    pub source_file: Option<String>,
    /// Source line, if known.
    pub source_line: Option<u32>,
}

/// An effect declaration in an F* module.
///
/// F* supports user-defined effects via the `new_effect` mechanism. Common
/// built-in effects include `Tot`, `Lemma`, `ML`, `ST`, `Exn`, `Div`.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub struct FStarEffectDecl {
    /// Effect name.
    pub name: String,
    /// Whether this effect is a sub-effect of another.
    pub parent_effect: Option<String>,
    /// Whether the effect is total (terminating).
    pub is_total: bool,
}

/// An F* module with its declarations and verification status.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[non_exhaustive]
pub struct FStarModule {
    /// Fully qualified module name (e.g., "FStar.List.Tot").
    pub name: String,
    /// `val` declarations.
    pub val_decls: Vec<FStarValDecl>,
    /// `let` bindings.
    pub let_decls: Vec<FStarLetDecl>,
    /// Effect declarations.
    pub effect_decls: Vec<FStarEffectDecl>,
    /// Source file name, if known.
    pub source_file: Option<String>,
}

/// Result of importing an F* module.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[non_exhaustive]
pub struct FStarImportResult {
    /// Module name.
    pub name: String,
    /// Total number of verification conditions (val + let bindings).
    pub vc_count: usize,
    /// Number of VCs successfully verified.
    pub verified_count: usize,
    /// Axiom profile for the imported result.
    pub axiom_profile: AxiomProfile,
    /// Trust level assigned to the imported result.
    pub trust_level: TrustLevel,
    /// Provenance record for the import.
    pub provenance: Provenance,
    /// Diagnostic messages from the import process.
    pub diagnostics: Vec<String>,
}

/// Known F* effects and their totality classification.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum EffectCategory {
    /// Total (terminating) effects: Tot, Lemma.
    Total,
    /// Partial (potentially non-terminating) effects: Div, ML.
    Partial,
    /// Stateful effects: ST, Exn.
    Stateful,
}

// ============================================================================
// Importer
// ============================================================================

/// Imports F* verification results into the Mathverse trust framework.
///
/// Parses F* module metadata (val/let declarations, verification status) and
/// assigns trust levels based on the verification state and axiom profile.
pub struct FStarImporter {
    /// Whether to attempt certificate replay for upgraded trust.
    cert_replay_enabled: bool,
}

impl Default for FStarImporter {
    fn default() -> Self {
        Self::new()
    }
}

impl FStarImporter {
    /// Create a new F* importer with default settings.
    #[must_use]
    pub fn new() -> Self {
        Self {
            cert_replay_enabled: false,
        }
    }

    /// Enable certificate replay for upgraded trust.
    #[must_use]
    pub fn with_cert_replay(mut self, enabled: bool) -> Self {
        self.cert_replay_enabled = enabled;
        self
    }

    /// Import an F* module from its textual representation.
    ///
    /// Performs a lightweight parse extracting module name, val declarations,
    /// let bindings, and effect declarations from a simplified F* module
    /// representation. The format uses comment metadata lines similar to the
    /// Dafny importer.
    pub fn import_module(&self, module_text: &str) -> Result<FStarModule, FStarError> {
        let trimmed = module_text.trim();
        if trimmed.is_empty() {
            return Err(FStarError::ParseError {
                reason: "empty module text".to_string(),
            });
        }

        // Extract module name from `(* Module: <name> *)` comment.
        let name =
            extract_fstar_comment(trimmed, "Module:").ok_or_else(|| FStarError::ParseError {
                reason: "missing (* Module: <name> *) declaration".to_string(),
            })?;

        // Extract source file from `(* File: <path> *)` comment.
        let source_file = extract_fstar_comment(trimmed, "File:");

        // Extract val declarations from `(* val: <name> : <type> [verified|unverified] *)`.
        let val_decls = extract_val_decls(trimmed);

        // Extract let declarations from `(* let: <name> <effect> [verified|unverified] *)`.
        let let_decls = extract_let_decls(trimmed, source_file.as_deref());

        // Extract effect declarations from `(* effect: <name> [parent:<p>] [total|partial] *)`.
        let effect_decls = extract_effect_decls(trimmed);

        if val_decls.is_empty() && let_decls.is_empty() {
            return Err(FStarError::ModuleError {
                module_name: name,
                reason: "no val or let declarations found".to_string(),
            });
        }

        Ok(FStarModule {
            name,
            val_decls,
            let_decls,
            effect_decls,
            source_file,
        })
    }

    /// Produce an import result from a parsed F* module.
    #[must_use]
    pub fn import_result(&self, module: &FStarModule) -> FStarImportResult {
        let val_verified = module.val_decls.iter().filter(|v| v.verified).count();
        let let_verified = module.let_decls.iter().filter(|l| l.verified).count();
        let vc_count = module.val_decls.len() + module.let_decls.len();
        let verified_count = val_verified + let_verified;

        // F* is extensional, so EXTENSIONALITY is always in the profile.
        let base_axiom = AxiomProfile::EXTENSIONALITY;

        let (axiom_profile, trust_level) =
            if verified_count == vc_count && vc_count > 0 && self.cert_replay_enabled {
                // All VCs verified + certificate replay → upgraded trust.
                (
                    base_axiom | AxiomProfile::SAT_CERT,
                    TrustLevel::CertificateReplayed,
                )
            } else {
                // Default: SMT oracle trust with extensionality.
                (
                    base_axiom | AxiomProfile::SMT_ORACLE,
                    TrustLevel::TrustedOracle,
                )
            };

        let mut diagnostics = Vec::new();
        if verified_count < vc_count {
            diagnostics.push(format!(
                "not all VCs verified: {verified_count}/{vc_count} passed"
            ));
        }

        // Report effect usage.
        let effect_names: Vec<&str> = module
            .let_decls
            .iter()
            .map(|l| l.effect.as_str())
            .collect::<std::collections::BTreeSet<_>>()
            .into_iter()
            .collect();
        if !effect_names.is_empty() {
            diagnostics.push(format!("effects: {}", effect_names.join(", ")));
        }

        let provenance = Provenance {
            source: SourceSystem::FStar,
            original_name: module.name.clone(),
            source_file: module.source_file.clone(),
            axiom_profile,
        };

        FStarImportResult {
            name: module.name.clone(),
            vc_count,
            verified_count,
            axiom_profile,
            trust_level,
            provenance,
            diagnostics,
        }
    }
}

// ============================================================================
// Effect classification
// ============================================================================

/// Classify an F* effect name into its category.
pub(crate) fn classify_effect(name: &str) -> EffectCategory {
    let lower = name.to_ascii_lowercase();
    match lower.as_str() {
        "tot" | "lemma" | "pure" | "ghost" => EffectCategory::Total,
        "st" | "exn" | "stack" | "heap" => EffectCategory::Stateful,
        _ => EffectCategory::Partial,
    }
}

// ============================================================================
// Parsing helpers
// ============================================================================

/// Extract a value from an F* comment line: `(* <prefix> <value> *)`.
fn extract_fstar_comment(text: &str, prefix: &str) -> Option<String> {
    for line in text.lines() {
        let line = line.trim();
        if let Some(rest) = line.strip_prefix("(*") {
            let rest = rest.trim();
            if let Some(value) = rest.strip_prefix(prefix) {
                let value = value.trim();
                // Strip trailing `*)`
                let value = value.strip_suffix("*)").unwrap_or(value).trim();
                if !value.is_empty() {
                    return Some(value.to_string());
                }
            }
        }
    }
    None
}

/// Extract val declarations from comment metadata lines.
fn extract_val_decls(text: &str) -> Vec<FStarValDecl> {
    let mut decls = Vec::new();
    for line in text.lines() {
        let line = line.trim();
        if let Some(rest) = line.strip_prefix("(*") {
            let rest = rest.trim();
            if let Some(val_rest) = rest.strip_prefix("val:") {
                let val_rest = val_rest.trim();
                let val_rest = val_rest.strip_suffix("*)").unwrap_or(val_rest).trim();
                // Format: "<name> : <type> [verified|unverified]"
                if let Some((name_and_type, status)) = val_rest.rsplit_once(' ') {
                    let verified = status == "verified";
                    let name_and_type = name_and_type.trim();
                    if let Some((name, type_annot)) = name_and_type.split_once(':') {
                        decls.push(FStarValDecl {
                            name: name.trim().to_string(),
                            type_annot: type_annot.trim().to_string(),
                            verified,
                        });
                    }
                }
            }
        }
    }
    decls
}

/// Extract let declarations from comment metadata lines.
fn extract_let_decls(text: &str, source_file: Option<&str>) -> Vec<FStarLetDecl> {
    let mut decls = Vec::new();
    for line in text.lines() {
        let line = line.trim();
        if let Some(rest) = line.strip_prefix("(*") {
            let rest = rest.trim();
            if let Some(let_rest) = rest.strip_prefix("let:") {
                let let_rest = let_rest.trim();
                let let_rest = let_rest.strip_suffix("*)").unwrap_or(let_rest).trim();
                // Format: "<name> <effect> [verified|unverified] [line:<n>]"
                let parts: Vec<&str> = let_rest.split_whitespace().collect();
                if parts.len() >= 3 {
                    let name = parts[0].to_string();
                    let effect = parts[1].to_string();
                    let verified = parts[2] == "verified";
                    let source_line = parts
                        .iter()
                        .find_map(|p| p.strip_prefix("line:").and_then(|n| n.parse::<u32>().ok()));
                    decls.push(FStarLetDecl {
                        name,
                        verified,
                        effect,
                        source_file: source_file.map(ToString::to_string),
                        source_line,
                    });
                }
            }
        }
    }
    decls
}

/// Extract effect declarations from comment metadata lines.
fn extract_effect_decls(text: &str) -> Vec<FStarEffectDecl> {
    let mut decls = Vec::new();
    for line in text.lines() {
        let line = line.trim();
        if let Some(rest) = line.strip_prefix("(*") {
            let rest = rest.trim();
            if let Some(eff_rest) = rest.strip_prefix("effect:") {
                let eff_rest = eff_rest.trim();
                let eff_rest = eff_rest.strip_suffix("*)").unwrap_or(eff_rest).trim();
                let parts: Vec<&str> = eff_rest.split_whitespace().collect();
                if !parts.is_empty() {
                    let name = parts[0].to_string();
                    let parent_effect = parts
                        .iter()
                        .find_map(|p| p.strip_prefix("parent:").map(ToString::to_string));
                    let is_total = parts.contains(&"total");
                    decls.push(FStarEffectDecl {
                        name,
                        parent_effect,
                        is_total,
                    });
                }
            }
        }
    }
    decls
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    const MOCK_MODULE: &str = "\
(* Module: FStar.List.Tot *)
(* File: list_tot.fst *)
(* val: length : list 'a -> Tot nat verified *)
(* val: map : ('a -> 'b) -> list 'a -> Tot (list 'b) verified *)
(* val: filter : ('a -> bool) -> list 'a -> Tot (list 'a) unverified *)
(* let: length Tot verified line:10 *)
(* let: map Tot verified line:25 *)
(* let: filter Tot unverified line:40 *)
(* effect: MyEff parent:Tot total *)
let length (#a:Type) (l:list a) : Tot nat = List.length l";

    #[test]
    fn test_import_module_parses_metadata() {
        let importer = FStarImporter::new();
        let module = importer.import_module(MOCK_MODULE).unwrap();

        assert_eq!(module.name, "FStar.List.Tot");
        assert_eq!(module.source_file.as_deref(), Some("list_tot.fst"));
        assert_eq!(module.val_decls.len(), 3);
        assert_eq!(module.let_decls.len(), 3);
        assert_eq!(module.effect_decls.len(), 1);
    }

    #[test]
    fn test_import_module_val_decls() {
        let importer = FStarImporter::new();
        let module = importer.import_module(MOCK_MODULE).unwrap();

        let v0 = &module.val_decls[0];
        assert_eq!(v0.name, "length");
        assert_eq!(v0.type_annot, "list 'a -> Tot nat");
        assert!(v0.verified);

        let v2 = &module.val_decls[2];
        assert_eq!(v2.name, "filter");
        assert!(!v2.verified);
    }

    #[test]
    fn test_import_module_let_decls() {
        let importer = FStarImporter::new();
        let module = importer.import_module(MOCK_MODULE).unwrap();

        let l0 = &module.let_decls[0];
        assert_eq!(l0.name, "length");
        assert_eq!(l0.effect, "Tot");
        assert!(l0.verified);
        assert_eq!(l0.source_line, Some(10));
        assert_eq!(l0.source_file.as_deref(), Some("list_tot.fst"));
    }

    #[test]
    fn test_import_module_effect_decls() {
        let importer = FStarImporter::new();
        let module = importer.import_module(MOCK_MODULE).unwrap();

        let e0 = &module.effect_decls[0];
        assert_eq!(e0.name, "MyEff");
        assert_eq!(e0.parent_effect.as_deref(), Some("Tot"));
        assert!(e0.is_total);
    }

    #[test]
    fn test_import_module_empty_input_errors() {
        let importer = FStarImporter::new();
        let result = importer.import_module("");
        assert!(result.is_err());
        assert!(matches!(result.unwrap_err(), FStarError::ParseError { .. }));
    }

    #[test]
    fn test_import_module_no_decls_errors() {
        let importer = FStarImporter::new();
        let result = importer.import_module("(* Module: Empty *)");
        assert!(result.is_err());
        assert!(matches!(
            result.unwrap_err(),
            FStarError::ModuleError { .. }
        ));
    }

    #[test]
    fn test_import_result_partial_verification() {
        let importer = FStarImporter::new();
        let module = importer.import_module(MOCK_MODULE).unwrap();
        let result = importer.import_result(&module);

        assert_eq!(result.name, "FStar.List.Tot");
        assert_eq!(result.vc_count, 6); // 3 val + 3 let
        assert_eq!(result.verified_count, 4); // 2 val + 2 let verified
        assert!(result.axiom_profile.contains(AxiomProfile::EXTENSIONALITY));
        assert!(result.axiom_profile.contains(AxiomProfile::SMT_ORACLE));
        assert_eq!(result.trust_level, TrustLevel::TrustedOracle);
        assert_eq!(result.provenance.source, SourceSystem::FStar);
        assert!(
            result.diagnostics.iter().any(|d| d.contains("not all VCs")),
            "expected unverified diagnostic"
        );
    }

    #[test]
    fn test_import_result_all_verified_no_cert() {
        let text = "\
(* Module: Verified.Mod *)
(* val: f : int -> Tot int verified *)
(* let: f Tot verified *)";
        let importer = FStarImporter::new();
        let module = importer.import_module(text).unwrap();
        let result = importer.import_result(&module);

        assert_eq!(result.verified_count, 2);
        assert_eq!(result.vc_count, 2);
        // Without cert replay, still SMT_ORACLE.
        assert!(result.axiom_profile.contains(AxiomProfile::SMT_ORACLE));
        assert_eq!(result.trust_level, TrustLevel::TrustedOracle);
    }

    #[test]
    fn test_import_result_all_verified_with_cert() {
        let text = "\
(* Module: Verified.Mod *)
(* val: f : int -> Tot int verified *)
(* let: f Tot verified *)";
        let importer = FStarImporter::new().with_cert_replay(true);
        let module = importer.import_module(text).unwrap();
        let result = importer.import_result(&module);

        assert_eq!(result.verified_count, 2);
        assert!(result.axiom_profile.contains(AxiomProfile::SAT_CERT));
        assert!(result.axiom_profile.contains(AxiomProfile::EXTENSIONALITY));
        assert_eq!(result.trust_level, TrustLevel::CertificateReplayed);
    }

    #[test]
    fn test_import_result_extensionality_always_present() {
        let text = "\
(* Module: Test *)
(* val: g : nat -> Tot nat verified *)";
        let importer = FStarImporter::new();
        let module = importer.import_module(text).unwrap();
        let result = importer.import_result(&module);

        assert!(
            result.axiom_profile.contains(AxiomProfile::EXTENSIONALITY),
            "F* axiom profile must always include EXTENSIONALITY"
        );
    }

    #[test]
    fn test_classify_effect_total() {
        assert_eq!(classify_effect("Tot"), EffectCategory::Total);
        assert_eq!(classify_effect("Lemma"), EffectCategory::Total);
        assert_eq!(classify_effect("Pure"), EffectCategory::Total);
        assert_eq!(classify_effect("Ghost"), EffectCategory::Total);
    }

    #[test]
    fn test_classify_effect_stateful() {
        assert_eq!(classify_effect("ST"), EffectCategory::Stateful);
        assert_eq!(classify_effect("Exn"), EffectCategory::Stateful);
    }

    #[test]
    fn test_classify_effect_partial() {
        assert_eq!(classify_effect("ML"), EffectCategory::Partial);
        assert_eq!(classify_effect("Div"), EffectCategory::Partial);
        assert_eq!(classify_effect("CustomEff"), EffectCategory::Partial);
    }

    #[test]
    fn test_fstar_importer_default() {
        let importer = FStarImporter::default();
        assert!(!importer.cert_replay_enabled);
    }

    #[test]
    fn test_extract_fstar_comment_present() {
        let text = "(* Module: Foo.Bar *)\n(* File: foo.fst *)";
        assert_eq!(
            extract_fstar_comment(text, "Module:"),
            Some("Foo.Bar".to_string())
        );
        assert_eq!(
            extract_fstar_comment(text, "File:"),
            Some("foo.fst".to_string())
        );
    }

    #[test]
    fn test_extract_fstar_comment_missing() {
        assert!(extract_fstar_comment("let x = 5", "Module:").is_none());
    }
}
