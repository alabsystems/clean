// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KeY / Frama-C / SPARK importer (VC export → SMT cert replay).
//!
//! Three program verification tools share a common import structure based on
//! verification conditions (VCs) generated from annotated source code:
//!
//! - **KeY**: Java/JML deductive verification
//! - **Frama-C**: C/ACSL deductive verification (WP plugin)
//! - **SPARK**: Ada/SPARK formal verification (GNATprove)
//!
//! Each tool generates proof obligations from source-level contracts
//! (preconditions, postconditions, invariants, assertions, loop variants)
//! and discharges them via SMT solvers or interactive provers.
//!
//! # Axiom profiles
//!
//! All imports carry `SMT_ORACLE` since the tools rely on SMT solvers
//! for discharging proof obligations.

use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::types::{AxiomProfile, Provenance, SourceSystem, TrustLevel};

// ---------------------------------------------------------------------------
// Errors
// ---------------------------------------------------------------------------

/// Errors during KeY/Frama-C/SPARK bundle import.
#[derive(Debug, Error)]
#[non_exhaustive]
pub enum KeYFramaCSparkError {
    /// Failed to parse the verification bundle.
    #[error("parse error at offset {offset}: {message}")]
    ParseError { offset: usize, message: String },

    /// Unsupported tool identifier in the bundle.
    #[error("unsupported verification tool: {tool_name}")]
    UnsupportedTool { tool_name: String },

    /// Contract specification could not be translated.
    #[error("contract error in {name}: {reason}")]
    ContractError { name: String, reason: String },
}

// ---------------------------------------------------------------------------
// Domain types
// ---------------------------------------------------------------------------

/// Verification tool that generated the proof obligations.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum VerificationTool {
    /// KeY — Java/JML deductive verifier.
    KeY,
    /// Frama-C — C/ACSL verification framework (WP plugin).
    FramaC,
    /// SPARK — Ada/SPARK formal verification (GNATprove).
    Spark,
}

impl VerificationTool {
    /// Human-readable name for this tool.
    #[must_use]
    pub fn display_name(self) -> &'static str {
        match self {
            Self::KeY => "KeY",
            Self::FramaC => "Frama-C",
            Self::Spark => "SPARK/GNATprove",
        }
    }
}

/// Kind of contract annotation.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum ContractKind {
    /// Function/method precondition.
    Precondition,
    /// Function/method postcondition.
    Postcondition,
    /// Loop or class invariant.
    Invariant,
    /// Inline assertion.
    Assertion,
    /// Loop variant (termination measure).
    LoopVariant,
}

/// A single verified (or unverified) contract from source code.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct VerifiedContract {
    /// Name of the contract (often the function/method name + contract index).
    pub name: String,
    /// Kind of contract.
    pub kind: ContractKind,
    /// Tool that generated the proof obligation.
    pub tool: VerificationTool,
    /// Source file containing the contract.
    pub source_file: String,
    /// Line number in source file.
    pub source_line: u32,
    /// Whether the contract was successfully discharged.
    pub verified: bool,
    /// Number of proof obligations generated for this contract.
    pub proof_obligations: u32,
}

/// A bundle of verification results from a single tool run.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct VerificationBundle {
    /// Tool that produced this bundle.
    pub tool: VerificationTool,
    /// Name of the verified program/module.
    pub program_name: String,
    /// Individual contract verification results.
    pub contracts: Vec<VerifiedContract>,
}

/// Result of importing a verification bundle into the Mathverse library.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct KeYFramaCSparkImportResult {
    pub name: String,
    pub contract_count: usize,
    pub verified_count: usize,
    pub axiom_profile: AxiomProfile,
    pub trust_level: TrustLevel,
    pub provenance: Provenance,
    pub diagnostics: Vec<String>,
}

// ---------------------------------------------------------------------------
// Importer
// ---------------------------------------------------------------------------

/// Importer for KeY/Frama-C/SPARK verification bundles.
pub struct KeYFramaCSparkImporter {
    namespace: String,
}

impl Default for KeYFramaCSparkImporter {
    fn default() -> Self {
        Self::new()
    }
}

impl KeYFramaCSparkImporter {
    /// Create a new importer with default namespace.
    #[must_use]
    pub fn new() -> Self {
        Self {
            namespace: "ProgVerif.Imported".to_owned(),
        }
    }

    /// Import a verification bundle from its textual representation.
    ///
    /// Expected format (line-oriented):
    /// ```text
    /// TOOL <KeY|FramaC|SPARK>
    /// PROGRAM <name>
    /// CONTRACT <name> <kind> <source_file> <line> <verified> <po_count>
    /// ...
    /// ```
    pub fn import_bundle(
        &self,
        bundle_text: &str,
    ) -> Result<VerificationBundle, KeYFramaCSparkError> {
        let trimmed = bundle_text.trim();
        if trimmed.is_empty() {
            return Err(KeYFramaCSparkError::ParseError {
                offset: 0,
                message: "empty bundle text".to_owned(),
            });
        }

        let mut tool: Option<VerificationTool> = None;
        let mut program_name = "unnamed-program".to_owned();
        let mut contracts = Vec::new();

        for line in trimmed.lines() {
            let line = line.trim();
            if line.is_empty() || line.starts_with('#') {
                continue;
            }

            if let Some(tool_str) = line.strip_prefix("TOOL ") {
                tool = Some(parse_tool_name(tool_str.trim())?);
                continue;
            }

            if let Some(name) = line.strip_prefix("PROGRAM ") {
                program_name = name.trim().to_owned();
                continue;
            }

            if let Some(rest) = line.strip_prefix("CONTRACT ") {
                let resolved_tool = tool.ok_or_else(|| KeYFramaCSparkError::ParseError {
                    offset: 0,
                    message: "CONTRACT before TOOL declaration".to_owned(),
                })?;
                let contract = parse_contract_line(rest.trim(), resolved_tool)?;
                contracts.push(contract);
            }
        }

        let resolved_tool = tool.ok_or_else(|| KeYFramaCSparkError::ParseError {
            offset: 0,
            message: "missing TOOL declaration".to_owned(),
        })?;

        Ok(VerificationBundle {
            tool: resolved_tool,
            program_name,
            contracts,
        })
    }

    /// Produce an import result summary for a parsed verification bundle.
    #[must_use]
    pub fn import_result(&self, bundle: &VerificationBundle) -> KeYFramaCSparkImportResult {
        let contract_count = bundle.contracts.len();
        let verified_count = bundle.contracts.iter().filter(|c| c.verified).count();
        let unverified_count = contract_count - verified_count;
        let total_pos: u32 = bundle.contracts.iter().map(|c| c.proof_obligations).sum();

        // All three tools rely on SMT solvers.
        let axiom_profile = AxiomProfile::SMT_ORACLE;

        let trust_level = if unverified_count > 0 {
            TrustLevel::PartiallyAxiomatized
        } else {
            TrustLevel::TrustedOracle
        };

        let qualified_name = format!(
            "{}.{}.{}",
            self.namespace,
            bundle.tool.display_name().replace('/', "_"),
            bundle.program_name
        );

        let provenance = Provenance {
            source: SourceSystem::KeyFramacSpark,
            original_name: bundle.program_name.clone(),
            source_file: None,
            axiom_profile,
        };

        let mut diagnostics = Vec::new();
        diagnostics.push(format!(
            "tool: {}, {} total proof obligations",
            bundle.tool.display_name(),
            total_pos
        ));
        if unverified_count > 0 {
            diagnostics.push(format!(
                "{unverified_count} contract(s) not fully discharged"
            ));
        }

        KeYFramaCSparkImportResult {
            name: qualified_name,
            contract_count,
            verified_count,
            axiom_profile,
            trust_level,
            provenance,
            diagnostics,
        }
    }
}

// ---------------------------------------------------------------------------
// Sub-importers and annotation tracking
// ---------------------------------------------------------------------------

/// Annotation kind for source-level specification languages.
///
/// Each verification tool uses a different specification language:
/// - KeY uses JML (Java Modeling Language) annotations
/// - Frama-C uses ACSL (ANSI/ISO C Specification Language) annotations
/// - SPARK uses SPARK/Ada contract aspects
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum AnnotationKind {
    /// JML annotation (KeY): `//@ requires`, `//@ ensures`, `/*@ invariant */`
    Jml,
    /// ACSL annotation (Frama-C): `/*@ requires`, `/*@ ensures`, `/*@ loop invariant */`
    Acsl,
    /// SPARK aspect (GNATprove): `Pre =>`, `Post =>`, `Loop_Invariant`
    Spark,
}

impl AnnotationKind {
    /// Human-readable name for this annotation kind.
    #[must_use]
    pub fn display_name(self) -> &'static str {
        match self {
            Self::Jml => "JML",
            Self::Acsl => "ACSL",
            Self::Spark => "SPARK",
        }
    }

    /// Associated verification tool for this annotation kind.
    #[must_use]
    pub fn tool(self) -> VerificationTool {
        match self {
            Self::Jml => VerificationTool::KeY,
            Self::Acsl => VerificationTool::FramaC,
            Self::Spark => VerificationTool::Spark,
        }
    }
}

/// A source-level annotation with file and line tracking.
///
/// Tracks the exact location of a JML/ACSL/SPARK annotation in the original
/// source code, enabling diagnostic mapping when verification fails.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct AnnotationSource {
    /// Kind of annotation language.
    pub kind: AnnotationKind,
    /// Contract type (pre/post/invariant/etc.).
    pub contract_kind: ContractKind,
    /// Source file containing the annotation.
    pub file: String,
    /// Line number of the annotation.
    pub line: u32,
    /// Column number of the annotation, if known.
    pub column: Option<u32>,
    /// Raw annotation text.
    pub text: String,
}

/// Sub-importer specialized for JML (Java Modeling Language) annotations.
///
/// JML annotations are embedded in Java source code as special comments
/// (`//@ ...` or `/*@ ... */`) and processed by the KeY verifier.
#[derive(Debug, Clone, Default)]
pub struct JmlImporter {
    /// Collected annotation sources.
    annotations: Vec<AnnotationSource>,
}

impl JmlImporter {
    /// Create a new JML sub-importer.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Extract JML annotations from Java source text.
    ///
    /// Scans for `//@ <text>` and `/*@ <text> */` patterns and records
    /// their source locations.
    pub fn extract_annotations(&mut self, source_text: &str, file_name: &str) {
        for (line_num, line) in source_text.lines().enumerate() {
            let line = line.trim();
            let line_u32 = (line_num + 1) as u32;

            // Single-line JML: //@ <text>
            if let Some(rest) = line.strip_prefix("//@") {
                let text = rest.trim();
                if !text.is_empty() {
                    let contract_kind = infer_contract_kind_from_text(text);
                    self.annotations.push(AnnotationSource {
                        kind: AnnotationKind::Jml,
                        contract_kind,
                        file: file_name.to_owned(),
                        line: line_u32,
                        column: None,
                        text: text.to_owned(),
                    });
                }
            }
            // Block JML start: /*@ <text> */
            else if let Some(rest) = line.strip_prefix("/*@") {
                let text = rest.trim().trim_end_matches("*/").trim();
                if !text.is_empty() {
                    let contract_kind = infer_contract_kind_from_text(text);
                    self.annotations.push(AnnotationSource {
                        kind: AnnotationKind::Jml,
                        contract_kind,
                        file: file_name.to_owned(),
                        line: line_u32,
                        column: None,
                        text: text.to_owned(),
                    });
                }
            }
        }
    }

    /// Get the collected annotations.
    #[must_use]
    pub fn annotations(&self) -> &[AnnotationSource] {
        &self.annotations
    }

    /// Number of collected annotations.
    #[must_use]
    pub fn annotation_count(&self) -> usize {
        self.annotations.len()
    }
}

/// Sub-importer specialized for ACSL (ANSI/ISO C Specification Language) annotations.
///
/// ACSL annotations are embedded in C source code as special comments
/// (`/*@ ... */`) and processed by the Frama-C WP plugin.
#[derive(Debug, Clone, Default)]
pub struct AcslImporter {
    /// Collected annotation sources.
    annotations: Vec<AnnotationSource>,
}

impl AcslImporter {
    /// Create a new ACSL sub-importer.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Extract ACSL annotations from C source text.
    ///
    /// Scans for `/*@ <text> */` patterns and records their source locations.
    pub fn extract_annotations(&mut self, source_text: &str, file_name: &str) {
        for (line_num, line) in source_text.lines().enumerate() {
            let line = line.trim();
            let line_u32 = (line_num + 1) as u32;

            if let Some(rest) = line.strip_prefix("/*@") {
                let text = rest.trim().trim_end_matches("*/").trim();
                if !text.is_empty() {
                    let contract_kind = infer_contract_kind_from_text(text);
                    self.annotations.push(AnnotationSource {
                        kind: AnnotationKind::Acsl,
                        contract_kind,
                        file: file_name.to_owned(),
                        line: line_u32,
                        column: None,
                        text: text.to_owned(),
                    });
                }
            }
        }
    }

    /// Get the collected annotations.
    #[must_use]
    pub fn annotations(&self) -> &[AnnotationSource] {
        &self.annotations
    }

    /// Number of collected annotations.
    #[must_use]
    pub fn annotation_count(&self) -> usize {
        self.annotations.len()
    }
}

/// Sub-importer specialized for SPARK contract aspects.
///
/// SPARK annotations use Ada's aspect syntax (`Pre =>`, `Post =>`,
/// `Loop_Invariant`) and are processed by GNATprove.
#[derive(Debug, Clone, Default)]
pub struct SparkImporter {
    /// Collected annotation sources.
    annotations: Vec<AnnotationSource>,
}

impl SparkImporter {
    /// Create a new SPARK sub-importer.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Extract SPARK contract aspects from Ada source text.
    ///
    /// Scans for `Pre =>`, `Post =>`, `Loop_Invariant`, `Contract_Cases`,
    /// and `Loop_Variant` patterns.
    pub fn extract_annotations(&mut self, source_text: &str, file_name: &str) {
        for (line_num, line) in source_text.lines().enumerate() {
            let line = line.trim();
            let line_u32 = (line_num + 1) as u32;

            let contract_kind = if line.contains("Pre =>") || line.contains("Precondition") {
                Some(ContractKind::Precondition)
            } else if line.contains("Post =>") || line.contains("Postcondition") {
                Some(ContractKind::Postcondition)
            } else if line.contains("Loop_Invariant") {
                Some(ContractKind::Invariant)
            } else if line.contains("Loop_Variant") {
                Some(ContractKind::LoopVariant)
            } else if line.contains("pragma Assert") {
                Some(ContractKind::Assertion)
            } else {
                None
            };

            if let Some(kind) = contract_kind {
                self.annotations.push(AnnotationSource {
                    kind: AnnotationKind::Spark,
                    contract_kind: kind,
                    file: file_name.to_owned(),
                    line: line_u32,
                    column: None,
                    text: line.to_owned(),
                });
            }
        }
    }

    /// Get the collected annotations.
    #[must_use]
    pub fn annotations(&self) -> &[AnnotationSource] {
        &self.annotations
    }

    /// Number of collected annotations.
    #[must_use]
    pub fn annotation_count(&self) -> usize {
        self.annotations.len()
    }
}

/// Infer contract kind from annotation text heuristically.
fn infer_contract_kind_from_text(text: &str) -> ContractKind {
    let lower = text.to_ascii_lowercase();
    if lower.starts_with("requires") || lower.starts_with("pre") {
        ContractKind::Precondition
    } else if lower.starts_with("ensures") || lower.starts_with("post") {
        ContractKind::Postcondition
    } else if lower.starts_with("invariant")
        || lower.starts_with("loop_invariant")
        || lower.starts_with("loop invariant")
    {
        ContractKind::Invariant
    } else if lower.starts_with("assert") || lower.starts_with("check") {
        ContractKind::Assertion
    } else if lower.starts_with("decreases") || lower.starts_with("variant") {
        ContractKind::LoopVariant
    } else {
        ContractKind::Assertion // default
    }
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Parse a tool name string into a `VerificationTool`.
fn parse_tool_name(s: &str) -> Result<VerificationTool, KeYFramaCSparkError> {
    match s {
        "KeY" | "key" | "KEY" => Ok(VerificationTool::KeY),
        "FramaC" | "Frama-C" | "frama-c" | "framac" => Ok(VerificationTool::FramaC),
        "SPARK" | "Spark" | "spark" | "GNATprove" | "gnatprove" => Ok(VerificationTool::Spark),
        other => Err(KeYFramaCSparkError::UnsupportedTool {
            tool_name: other.to_owned(),
        }),
    }
}

/// Parse a contract kind string.
fn parse_contract_kind(s: &str) -> Result<ContractKind, KeYFramaCSparkError> {
    match s {
        "pre" | "precondition" | "requires" => Ok(ContractKind::Precondition),
        "post" | "postcondition" | "ensures" => Ok(ContractKind::Postcondition),
        "inv" | "invariant" | "loop_invariant" => Ok(ContractKind::Invariant),
        "assert" | "assertion" | "check" => Ok(ContractKind::Assertion),
        "variant" | "loop_variant" | "decreases" => Ok(ContractKind::LoopVariant),
        other => Err(KeYFramaCSparkError::ContractError {
            name: String::new(),
            reason: format!("unknown contract kind: {other}"),
        }),
    }
}

/// Parse a CONTRACT line into a `VerifiedContract`.
///
/// Format: `<name> <kind> <source_file> <line> <verified> <po_count>`
fn parse_contract_line(
    rest: &str,
    tool: VerificationTool,
) -> Result<VerifiedContract, KeYFramaCSparkError> {
    let parts: Vec<&str> = rest.split_whitespace().collect();
    if parts.len() < 6 {
        return Err(KeYFramaCSparkError::ParseError {
            offset: 0,
            message: format!("CONTRACT line needs 6 fields, got {}: {rest}", parts.len()),
        });
    }

    let name = parts[0].to_owned();
    let kind = parse_contract_kind(parts[1])?;
    let source_file = parts[2].to_owned();
    let source_line = parts[3]
        .parse::<u32>()
        .map_err(|_| KeYFramaCSparkError::ParseError {
            offset: 0,
            message: format!("invalid line number: {}", parts[3]),
        })?;
    let verified = matches!(parts[4], "true" | "yes" | "1" | "verified");
    let proof_obligations =
        parts[5]
            .parse::<u32>()
            .map_err(|_| KeYFramaCSparkError::ParseError {
                offset: 0,
                message: format!("invalid proof obligation count: {}", parts[5]),
            })?;

    Ok(VerifiedContract {
        name,
        kind,
        tool,
        source_file,
        source_line,
        verified,
        proof_obligations,
    })
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    fn mock_key_bundle() -> &'static str {
        "TOOL KeY\n\
         PROGRAM BankAccount\n\
         CONTRACT deposit_pre pre BankAccount.java 42 true 3\n\
         CONTRACT deposit_post post BankAccount.java 42 true 5\n\
         CONTRACT balance_inv inv BankAccount.java 10 true 2\n"
    }

    fn mock_framac_bundle() -> &'static str {
        "TOOL FramaC\n\
         PROGRAM binary_search\n\
         CONTRACT search_pre requires binary_search.c 15 true 2\n\
         CONTRACT search_post ensures binary_search.c 16 true 4\n\
         CONTRACT search_loop invariant binary_search.c 20 false 3\n\
         CONTRACT search_variant variant binary_search.c 21 true 1\n"
    }

    fn mock_spark_bundle() -> &'static str {
        "TOOL SPARK\n\
         PROGRAM Stack_Package\n\
         CONTRACT push_pre pre stack.ads 30 true 1\n\
         CONTRACT push_post post stack.ads 31 true 2\n\
         CONTRACT pop_assert assert stack.adb 55 true 1\n"
    }

    #[test]
    fn test_key_bundle_import() {
        let importer = KeYFramaCSparkImporter::new();
        let bundle = importer
            .import_bundle(mock_key_bundle())
            .expect("should parse KeY bundle");

        assert_eq!(bundle.tool, VerificationTool::KeY);
        assert_eq!(bundle.program_name, "BankAccount");
        assert_eq!(bundle.contracts.len(), 3);
        assert!(bundle.contracts.iter().all(|c| c.verified));
    }

    #[test]
    fn test_framac_bundle_import() {
        let importer = KeYFramaCSparkImporter::new();
        let bundle = importer
            .import_bundle(mock_framac_bundle())
            .expect("should parse Frama-C bundle");

        assert_eq!(bundle.tool, VerificationTool::FramaC);
        assert_eq!(bundle.program_name, "binary_search");
        assert_eq!(bundle.contracts.len(), 4);

        let unverified: Vec<_> = bundle.contracts.iter().filter(|c| !c.verified).collect();
        assert_eq!(unverified.len(), 1);
        assert_eq!(unverified[0].kind, ContractKind::Invariant);
    }

    #[test]
    fn test_spark_bundle_import() {
        let importer = KeYFramaCSparkImporter::new();
        let bundle = importer
            .import_bundle(mock_spark_bundle())
            .expect("should parse SPARK bundle");

        assert_eq!(bundle.tool, VerificationTool::Spark);
        assert_eq!(bundle.program_name, "Stack_Package");
        assert_eq!(bundle.contracts.len(), 3);
    }

    #[test]
    fn test_import_result_all_verified() {
        let importer = KeYFramaCSparkImporter::new();
        let bundle = importer
            .import_bundle(mock_key_bundle())
            .expect("should parse");
        let result = importer.import_result(&bundle);

        assert_eq!(result.contract_count, 3);
        assert_eq!(result.verified_count, 3);
        assert!(result.axiom_profile.contains(AxiomProfile::SMT_ORACLE));
        assert_eq!(result.trust_level, TrustLevel::TrustedOracle);
        assert_eq!(result.provenance.source, SourceSystem::KeyFramacSpark);
    }

    #[test]
    fn test_import_result_partial_verification() {
        let importer = KeYFramaCSparkImporter::new();
        let bundle = importer
            .import_bundle(mock_framac_bundle())
            .expect("should parse");
        let result = importer.import_result(&bundle);

        assert_eq!(result.contract_count, 4);
        assert_eq!(result.verified_count, 3);
        assert_eq!(result.trust_level, TrustLevel::PartiallyAxiomatized);
        assert!(result
            .diagnostics
            .iter()
            .any(|d| d.contains("not fully discharged")));
    }

    #[test]
    fn test_empty_bundle_error() {
        let importer = KeYFramaCSparkImporter::new();
        let result = importer.import_bundle("");
        assert!(result.is_err());
    }

    #[test]
    fn test_unsupported_tool_error() {
        let input = "TOOL UnknownVerifier\nPROGRAM test\n";
        let importer = KeYFramaCSparkImporter::new();
        let result = importer.import_bundle(input);
        assert!(result.is_err());
        let err = result.unwrap_err();
        assert!(matches!(err, KeYFramaCSparkError::UnsupportedTool { .. }));
    }

    #[test]
    fn test_contract_kinds() {
        assert_eq!(
            parse_contract_kind("pre").expect("should parse"),
            ContractKind::Precondition
        );
        assert_eq!(
            parse_contract_kind("ensures").expect("should parse"),
            ContractKind::Postcondition
        );
        assert_eq!(
            parse_contract_kind("invariant").expect("should parse"),
            ContractKind::Invariant
        );
        assert_eq!(
            parse_contract_kind("assert").expect("should parse"),
            ContractKind::Assertion
        );
        assert_eq!(
            parse_contract_kind("decreases").expect("should parse"),
            ContractKind::LoopVariant
        );
    }

    #[test]
    fn test_verification_tool_display_name() {
        assert_eq!(VerificationTool::KeY.display_name(), "KeY");
        assert_eq!(VerificationTool::FramaC.display_name(), "Frama-C");
        assert_eq!(VerificationTool::Spark.display_name(), "SPARK/GNATprove");
    }

    #[test]
    fn test_importer_default() {
        let importer = KeYFramaCSparkImporter::default();
        assert_eq!(importer.namespace, "ProgVerif.Imported");
    }

    #[test]
    fn test_missing_tool_declaration() {
        let input = "PROGRAM test\nCONTRACT foo pre bar.c 1 true 1\n";
        let importer = KeYFramaCSparkImporter::new();
        let result = importer.import_bundle(input);
        assert!(result.is_err());
    }

    // -----------------------------------------------------------------------
    // AnnotationKind tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_annotation_kind_display_name() {
        assert_eq!(AnnotationKind::Jml.display_name(), "JML");
        assert_eq!(AnnotationKind::Acsl.display_name(), "ACSL");
        assert_eq!(AnnotationKind::Spark.display_name(), "SPARK");
    }

    #[test]
    fn test_annotation_kind_tool() {
        assert_eq!(AnnotationKind::Jml.tool(), VerificationTool::KeY);
        assert_eq!(AnnotationKind::Acsl.tool(), VerificationTool::FramaC);
        assert_eq!(AnnotationKind::Spark.tool(), VerificationTool::Spark);
    }

    #[test]
    fn test_annotation_kind_serde_round_trip() {
        let kinds = [
            AnnotationKind::Jml,
            AnnotationKind::Acsl,
            AnnotationKind::Spark,
        ];
        for kind in &kinds {
            let json = serde_json::to_string(kind).expect("serialize");
            let restored: AnnotationKind = serde_json::from_str(&json).expect("deserialize");
            assert_eq!(&restored, kind);
        }
    }

    // -----------------------------------------------------------------------
    // JmlImporter tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_jml_importer_extract_single_line() {
        let source = r#"
public class Account {
    //@ requires balance >= 0;
    //@ ensures \result >= 0;
    public int getBalance() { return balance; }
}
"#;
        let mut jml = JmlImporter::new();
        jml.extract_annotations(source, "Account.java");

        assert_eq!(jml.annotation_count(), 2);
        let annots = jml.annotations();
        assert_eq!(annots[0].kind, AnnotationKind::Jml);
        assert_eq!(annots[0].contract_kind, ContractKind::Precondition);
        assert_eq!(annots[0].file, "Account.java");
        assert_eq!(annots[0].line, 3);
        assert!(annots[0].text.contains("requires"));

        assert_eq!(annots[1].contract_kind, ContractKind::Postcondition);
        assert_eq!(annots[1].line, 4);
    }

    #[test]
    fn test_jml_importer_extract_block_comment() {
        let source = r#"
/*@ invariant size >= 0 */
public class Stack {}
"#;
        let mut jml = JmlImporter::new();
        jml.extract_annotations(source, "Stack.java");

        assert_eq!(jml.annotation_count(), 1);
        assert_eq!(jml.annotations()[0].contract_kind, ContractKind::Invariant);
    }

    #[test]
    fn test_jml_importer_empty_source() {
        let mut jml = JmlImporter::new();
        jml.extract_annotations("", "Empty.java");
        assert_eq!(jml.annotation_count(), 0);
    }

    #[test]
    fn test_jml_importer_no_annotations() {
        let source = "public class Plain { int x = 5; }";
        let mut jml = JmlImporter::new();
        jml.extract_annotations(source, "Plain.java");
        assert_eq!(jml.annotation_count(), 0);
    }

    // -----------------------------------------------------------------------
    // AcslImporter tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_acsl_importer_extract_annotations() {
        let source = r#"
/*@ requires n > 0; */
/*@ ensures \result >= 0; */
int abs(int n) { return n >= 0 ? n : -n; }
/*@ loop invariant 0 <= i <= n; */
"#;
        let mut acsl = AcslImporter::new();
        acsl.extract_annotations(source, "abs.c");

        assert_eq!(acsl.annotation_count(), 3);
        assert_eq!(acsl.annotations()[0].kind, AnnotationKind::Acsl);
        assert_eq!(
            acsl.annotations()[0].contract_kind,
            ContractKind::Precondition
        );
        assert_eq!(
            acsl.annotations()[1].contract_kind,
            ContractKind::Postcondition
        );
        assert_eq!(acsl.annotations()[2].contract_kind, ContractKind::Invariant);
    }

    #[test]
    fn test_acsl_importer_empty_source() {
        let mut acsl = AcslImporter::new();
        acsl.extract_annotations("", "empty.c");
        assert_eq!(acsl.annotation_count(), 0);
    }

    // -----------------------------------------------------------------------
    // SparkImporter tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_spark_importer_extract_annotations() {
        let source = r#"
procedure Push (S : in out Stack; E : Element)
  with Pre => not Is_Full(S),
       Post => Top(S) = E;
pragma Assert (Count > 0);
"#;
        let mut spark = SparkImporter::new();
        spark.extract_annotations(source, "stack.ads");

        assert_eq!(spark.annotation_count(), 3);
        assert_eq!(spark.annotations()[0].kind, AnnotationKind::Spark);
        assert_eq!(
            spark.annotations()[0].contract_kind,
            ContractKind::Precondition
        );
        assert_eq!(
            spark.annotations()[1].contract_kind,
            ContractKind::Postcondition
        );
        assert_eq!(
            spark.annotations()[2].contract_kind,
            ContractKind::Assertion
        );
    }

    #[test]
    fn test_spark_importer_loop_constructs() {
        let source = r#"
pragma Loop_Invariant (I <= N);
pragma Loop_Variant (N - I);
"#;
        let mut spark = SparkImporter::new();
        spark.extract_annotations(source, "loop.adb");

        assert_eq!(spark.annotation_count(), 2);
        assert_eq!(
            spark.annotations()[0].contract_kind,
            ContractKind::Invariant
        );
        assert_eq!(
            spark.annotations()[1].contract_kind,
            ContractKind::LoopVariant
        );
    }

    #[test]
    fn test_spark_importer_empty_source() {
        let mut spark = SparkImporter::new();
        spark.extract_annotations("", "empty.ads");
        assert_eq!(spark.annotation_count(), 0);
    }

    // -----------------------------------------------------------------------
    // AnnotationSource tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_annotation_source_serde_round_trip() {
        let ann = AnnotationSource {
            kind: AnnotationKind::Acsl,
            contract_kind: ContractKind::Postcondition,
            file: "search.c".to_owned(),
            line: 42,
            column: Some(5),
            text: "ensures \\result >= 0;".to_owned(),
        };
        let json = serde_json::to_string(&ann).expect("serialize");
        let restored: AnnotationSource = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(restored.kind, AnnotationKind::Acsl);
        assert_eq!(restored.contract_kind, ContractKind::Postcondition);
        assert_eq!(restored.file, "search.c");
        assert_eq!(restored.line, 42);
        assert_eq!(restored.column, Some(5));
    }

    // -----------------------------------------------------------------------
    // infer_contract_kind_from_text tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_infer_contract_kind_requires() {
        assert_eq!(
            infer_contract_kind_from_text("requires x > 0;"),
            ContractKind::Precondition
        );
        assert_eq!(
            infer_contract_kind_from_text("Pre => Is_Valid(S)"),
            ContractKind::Precondition
        );
    }

    #[test]
    fn test_infer_contract_kind_ensures() {
        assert_eq!(
            infer_contract_kind_from_text("ensures \\result >= 0;"),
            ContractKind::Postcondition
        );
        assert_eq!(
            infer_contract_kind_from_text("Post => Length(S) > 0"),
            ContractKind::Postcondition
        );
    }

    #[test]
    fn test_infer_contract_kind_invariant() {
        assert_eq!(
            infer_contract_kind_from_text("invariant 0 <= i <= n;"),
            ContractKind::Invariant
        );
        assert_eq!(
            infer_contract_kind_from_text("loop_invariant i > 0;"),
            ContractKind::Invariant
        );
    }

    #[test]
    fn test_infer_contract_kind_variant() {
        assert_eq!(
            infer_contract_kind_from_text("decreases n - i;"),
            ContractKind::LoopVariant
        );
        assert_eq!(
            infer_contract_kind_from_text("variant (N - I)"),
            ContractKind::LoopVariant
        );
    }

    #[test]
    fn test_infer_contract_kind_default() {
        assert_eq!(
            infer_contract_kind_from_text("some random text"),
            ContractKind::Assertion
        );
    }
}
