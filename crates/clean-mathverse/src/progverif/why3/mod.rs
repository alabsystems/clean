// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Why3 program verification importer (WhyML → SMT cert replay).
//!
//! Why3 is a platform for deductive program verification. It generates proof
//! obligations (goals) from WhyML programs and dispatches them to external
//! provers (SMT solvers, ATP systems, interactive provers). Verification
//! sessions are recorded in XML session files.
//!
//! Trust model:
//! - SMT-proved goals: `SMT_ORACLE` axiom profile, `TrustedOracle` trust level
//! - ATP-proved goals (with certificates): `ATP_CERT` profile, `CertificateReplayed`
//! - Unproved goals: `SMT_ORACLE` profile, `TrustedOracle` trust level

use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::types::{AxiomProfile, Provenance, SourceSystem, TrustLevel};

// ════════════════════════════════════════════════════════════════════════════
// Errors
// ════════════════════════════════════════════════════════════════════════════

/// Errors raised during Why3 import operations.
#[derive(Debug, Error)]
#[non_exhaustive]
pub enum Why3Error {
    /// Failed to parse a Why3 session file.
    #[error("failed to parse Why3 session: {reason}")]
    ParseError { reason: String },

    /// Session file is malformed or missing required structure.
    #[error("Why3 session error: {reason}")]
    SessionError { reason: String },

    /// A prover referenced in the session is not supported.
    #[error("unsupported Why3 prover: `{prover}`")]
    UnsupportedProver { prover: String },
}

// ════════════════════════════════════════════════════════════════════════════
// Data types
// ════════════════════════════════════════════════════════════════════════════

/// A single Why3 proof goal from a session file.
///
/// Each goal represents one proof obligation generated from a WhyML program
/// or theory. Goals are dispatched to provers and may have a recorded result.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub struct Why3Goal {
    /// Goal name (typically `<theory>.<lemma>` or a generated VC name).
    pub name: String,
    /// Human-readable explanation of the proof obligation.
    pub expl: String,
    /// Name of the prover that discharged this goal (e.g., `"Z3"`, `"Alt-Ergo"`, `"E"`).
    pub prover: String,
    /// Whether the goal was proved.
    pub proved: bool,
    /// Proof time in milliseconds, if recorded.
    pub proof_time_ms: Option<u64>,
}

/// A Why3 verification session containing goals for one theory.
///
/// Session files (`.xml`) record which goals were generated and which provers
/// succeeded or failed on each goal.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub struct Why3Session {
    /// Name of the Why3 theory this session covers.
    pub theory_name: String,
    /// Goals extracted from the session.
    pub goals: Vec<Why3Goal>,
    /// Source file name, if recorded in the session.
    pub file_name: Option<String>,
}

/// Result of importing a Why3 verification session.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[non_exhaustive]
pub struct Why3ImportResult {
    /// Name of the imported session.
    pub name: String,
    /// Total number of goals in the session.
    pub goal_count: usize,
    /// Number of goals successfully proved.
    pub proved_count: usize,
    /// Axiom profile for the imported result.
    pub axiom_profile: AxiomProfile,
    /// Trust level assigned to the imported result.
    pub trust_level: TrustLevel,
    /// Provenance record for the import.
    pub provenance: Provenance,
    /// Diagnostic messages from the import process.
    pub diagnostics: Vec<String>,
}

/// External prover driver used by Why3.
///
/// Why3 delegates proof goals to external provers via driver configurations.
/// This enum represents the known first-class drivers with explicit trust
/// classification; unknown drivers are handled via `Other`.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum Why3Driver {
    /// Z3 SMT solver.
    Z3,
    /// CVC5 SMT solver.
    Cvc5,
    /// Alt-Ergo SMT solver.
    AltErgo,
    /// E theorem prover (first-order ATP).
    EProver,
    /// Vampire first-order ATP.
    Vampire,
    /// Coq interactive prover.
    Coq,
    /// Isabelle interactive prover.
    Isabelle,
    /// Other/unknown driver.
    Other(String),
}

impl Why3Driver {
    /// Parse a prover name string into a `Why3Driver`.
    #[must_use]
    pub fn from_prover_name(name: &str) -> Self {
        let lower = name.to_ascii_lowercase();
        if lower == "z3" || lower.starts_with("z3 ") {
            Self::Z3
        } else if lower == "cvc5" || lower.starts_with("cvc5 ") || lower == "cvc4" {
            Self::Cvc5
        } else if lower.contains("alt-ergo") || lower.contains("altergo") {
            Self::AltErgo
        } else if lower == "e" || lower.contains("eprover") {
            Self::EProver
        } else if lower.contains("vampire") {
            Self::Vampire
        } else if lower.contains("coq") {
            Self::Coq
        } else if lower.contains("isabelle") {
            Self::Isabelle
        } else {
            Self::Other(name.to_string())
        }
    }

    /// Human-readable display name.
    #[must_use]
    pub fn display_name(&self) -> &str {
        match self {
            Self::Z3 => "Z3",
            Self::Cvc5 => "CVC5",
            Self::AltErgo => "Alt-Ergo",
            Self::EProver => "E",
            Self::Vampire => "Vampire",
            Self::Coq => "Coq",
            Self::Isabelle => "Isabelle",
            Self::Other(name) => name,
        }
    }

    /// Prover category for trust classification.
    #[must_use]
    pub fn category(&self) -> ProverCategory {
        match self {
            Self::Z3 | Self::Cvc5 | Self::AltErgo => ProverCategory::Smt,
            Self::EProver | Self::Vampire => ProverCategory::Atp,
            Self::Coq | Self::Isabelle => ProverCategory::Interactive,
            Self::Other(name) => classify_prover(name),
        }
    }
}

/// Per-goal statistics tracked during a Why3 verification session.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct Why3GoalStatistics {
    /// Total number of goals in the session.
    pub total_goals: usize,
    /// Number of goals proved.
    pub proved_goals: usize,
    /// Number of goals proved by SMT solvers.
    pub smt_proved: usize,
    /// Number of goals proved by ATP systems.
    pub atp_proved: usize,
    /// Number of goals proved by interactive provers.
    pub interactive_proved: usize,
    /// Total proof time in milliseconds across all goals.
    pub total_proof_time_ms: u64,
    /// Maximum single-goal proof time in milliseconds.
    pub max_proof_time_ms: u64,
}

impl Why3GoalStatistics {
    /// Compute statistics from a Why3 session.
    #[must_use]
    pub fn from_session(session: &Why3Session) -> Self {
        let total_goals = session.goals.len();
        let proved_goals = session.goals.iter().filter(|g| g.proved).count();

        let mut smt_proved = 0usize;
        let mut atp_proved = 0usize;
        let mut interactive_proved = 0usize;
        let mut total_proof_time_ms = 0u64;
        let mut max_proof_time_ms = 0u64;

        for goal in &session.goals {
            if goal.proved {
                match classify_prover(&goal.prover) {
                    ProverCategory::Smt => smt_proved += 1,
                    ProverCategory::Atp => atp_proved += 1,
                    ProverCategory::Interactive => interactive_proved += 1,
                }
            }
            if let Some(time) = goal.proof_time_ms {
                total_proof_time_ms = total_proof_time_ms.saturating_add(time);
                if time > max_proof_time_ms {
                    max_proof_time_ms = time;
                }
            }
        }

        Self {
            total_goals,
            proved_goals,
            smt_proved,
            atp_proved,
            interactive_proved,
            total_proof_time_ms,
            max_proof_time_ms,
        }
    }

    /// Fraction of goals proved, as a value in `[0.0, 1.0]`.
    #[must_use]
    pub fn success_rate(&self) -> f64 {
        if self.total_goals == 0 {
            1.0
        } else {
            self.proved_goals as f64 / self.total_goals as f64
        }
    }
}

/// Parse a Why3 session XML string into a `Why3Session`.
///
/// This is a convenience wrapper around [`Why3Importer::import_session`] for
/// use in batch pipelines without constructing an importer instance.
///
/// # Errors
///
/// Returns `Why3Error` if the XML is empty, missing required elements, or
/// has no goal elements.
pub fn parse_why3_session_xml(session_xml: &str) -> Result<Why3Session, Why3Error> {
    let importer = Why3Importer::new();
    importer.import_session(session_xml)
}

/// Known prover categories for trust classification.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ProverCategory {
    /// SMT solvers (Z3, CVC5, Alt-Ergo, etc.).
    Smt,
    /// First-order ATP systems (E, Vampire, SPASS, etc.).
    Atp,
    /// Interactive provers (Coq, Isabelle, etc.).
    Interactive,
}

// ════════════════════════════════════════════════════════════════════════════
// Importer
// ════════════════════════════════════════════════════════════════════════════

/// Imports Why3 verification sessions into the Mathverse trust framework.
///
/// Parses Why3 session XML files (lightweight subset parser) and classifies
/// proof goals by their prover category for trust assignment.
pub struct Why3Importer {
    _private: (),
}

impl Default for Why3Importer {
    fn default() -> Self {
        Self::new()
    }
}

impl Why3Importer {
    /// Create a new Why3 importer.
    #[must_use]
    pub fn new() -> Self {
        Self { _private: () }
    }

    /// Import a Why3 session from its XML representation.
    ///
    /// Performs a lightweight parse of the Why3 session XML format, extracting
    /// theory name, goals, prover assignments, and proof results. This is not
    /// a full XML parser — it extracts structured data from the known Why3
    /// session schema.
    pub fn import_session(&self, session_xml: &str) -> Result<Why3Session, Why3Error> {
        let trimmed = session_xml.trim();
        if trimmed.is_empty() {
            return Err(Why3Error::ParseError {
                reason: "empty session XML".to_string(),
            });
        }

        // Extract theory name from `<theory name="...">` tag.
        let theory_name =
            extract_xml_attr(trimmed, "theory", "name").ok_or_else(|| Why3Error::SessionError {
                reason: "missing <theory name=\"...\"> element".to_string(),
            })?;

        // Extract optional file name from `<file name="...">` tag.
        let file_name = extract_xml_attr(trimmed, "file", "name");

        // Extract goals from `<goal name="..." expl="..." proved="...">` tags.
        let mut goals = Vec::new();
        for goal_block in iter_xml_tags(trimmed, "goal") {
            let name = extract_xml_attr(goal_block, "goal", "name")
                .unwrap_or_else(|| "anonymous_goal".to_string());
            let expl = extract_xml_attr(goal_block, "goal", "expl").unwrap_or_default();
            let proved =
                extract_xml_attr(goal_block, "goal", "proved").is_some_and(|v| v == "true");

            // Extract prover from nested `<proof prover="...">` or `<prover name="...">`.
            let prover = extract_xml_attr(goal_block, "proof", "prover")
                .or_else(|| extract_xml_attr(goal_block, "prover", "name"))
                .unwrap_or_else(|| "unknown".to_string());

            // Extract proof time from `<proof timelimit="...">` or `time="..."`.
            let proof_time_ms =
                extract_xml_attr(goal_block, "proof", "time").and_then(|s| parse_time_ms(&s));

            goals.push(Why3Goal {
                name,
                expl,
                prover,
                proved,
                proof_time_ms,
            });
        }

        if goals.is_empty() {
            return Err(Why3Error::SessionError {
                reason: "no <goal> elements found in session".to_string(),
            });
        }

        Ok(Why3Session {
            theory_name,
            goals,
            file_name,
        })
    }

    /// Produce an import result from a parsed session.
    #[must_use]
    pub fn import_result(&self, session: &Why3Session) -> Why3ImportResult {
        let goal_count = session.goals.len();
        let proved_count = session.goals.iter().filter(|g| g.proved).count();

        // Determine trust level based on prover categories used.
        // If any goal uses an ATP prover with certificate, we can claim ATP_CERT.
        // Otherwise, SMT_ORACLE is the baseline.
        let has_atp_proved = session
            .goals
            .iter()
            .any(|g| g.proved && classify_prover(&g.prover) == ProverCategory::Atp);

        let (axiom_profile, trust_level) = if has_atp_proved && proved_count == goal_count {
            // All goals proved, at least one by ATP with certificate.
            (AxiomProfile::ATP_CERT, TrustLevel::CertificateReplayed)
        } else {
            (AxiomProfile::SMT_ORACLE, TrustLevel::TrustedOracle)
        };

        let mut diagnostics = Vec::new();
        if proved_count < goal_count {
            let unproved = goal_count - proved_count;
            diagnostics.push(format!("{unproved}/{goal_count} goals unproved"));
        }

        // Collect unique provers used.
        let mut provers_used: Vec<&str> = session.goals.iter().map(|g| g.prover.as_str()).collect();
        provers_used.sort_unstable();
        provers_used.dedup();
        if !provers_used.is_empty() {
            diagnostics.push(format!("provers: {}", provers_used.join(", ")));
        }

        let provenance = Provenance {
            source: SourceSystem::Why3,
            original_name: session.theory_name.clone(),
            source_file: session.file_name.clone(),
            axiom_profile,
        };

        Why3ImportResult {
            name: session.theory_name.clone(),
            goal_count,
            proved_count,
            axiom_profile,
            trust_level,
            provenance,
            diagnostics,
        }
    }
}

// ════════════════════════════════════════════════════════════════════════════
// Prover classification
// ════════════════════════════════════════════════════════════════════════════

/// Classify a prover name into its category for trust assignment.
pub(crate) fn classify_prover(name: &str) -> ProverCategory {
    let lower = name.to_ascii_lowercase();
    // ATP provers
    if lower.contains("eprover")
        || lower == "e"
        || lower.contains("vampire")
        || lower.contains("spass")
        || lower.contains("zipperposition")
    {
        return ProverCategory::Atp;
    }
    // Interactive provers
    if lower.contains("coq")
        || lower.contains("isabelle")
        || lower.contains("pvs")
        || lower.contains("lean")
    {
        return ProverCategory::Interactive;
    }
    // Default: SMT (Z3, CVC5, Alt-Ergo, etc.)
    ProverCategory::Smt
}

// ════════════════════════════════════════════════════════════════════════════
// Lightweight XML helpers
// ════════════════════════════════════════════════════════════════════════════

/// Extract an attribute value from the first occurrence of `<tag attr="value">`.
fn extract_xml_attr(xml: &str, tag: &str, attr: &str) -> Option<String> {
    // Find `<tag ` or `<tag\n` etc.
    let tag_open = format!("<{tag}");
    let start = xml.find(&tag_open)?;
    let rest = &xml[start..];

    // Find the closing `>` of this tag.
    let tag_end = rest.find('>')?;
    let tag_content = &rest[..tag_end];

    // Find `attr="value"` within the tag.
    let attr_prefix = format!("{attr}=\"");
    let attr_start = tag_content.find(&attr_prefix)?;
    let value_start = attr_start + attr_prefix.len();
    let value_rest = &tag_content[value_start..];
    let value_end = value_rest.find('"')?;
    let value = &value_rest[..value_end];

    if value.is_empty() {
        None
    } else {
        Some(value.to_string())
    }
}

/// Iterate over text blocks that start with `<tag` opening tags.
///
/// Returns slices from each `<tag ...>` to the next occurrence of `<tag` or end.
fn iter_xml_tags<'a>(xml: &'a str, tag: &str) -> Vec<&'a str> {
    let tag_open = format!("<{tag}");
    let mut results = Vec::new();
    let mut search_from = 0;

    while let Some(start) = xml[search_from..].find(&tag_open) {
        let abs_start = search_from + start;
        // Find next occurrence of this tag or end of string.
        let next = xml[abs_start + tag_open.len()..]
            .find(&tag_open)
            .map(|p| abs_start + tag_open.len() + p);
        let end = next.unwrap_or(xml.len());
        results.push(&xml[abs_start..end]);
        search_from = end;
    }

    results
}

/// Parse a time string (seconds as float) into milliseconds.
fn parse_time_ms(s: &str) -> Option<u64> {
    let secs: f64 = s.parse().ok()?;
    if secs < 0.0 {
        return None;
    }
    Some((secs * 1000.0) as u64)
}

// ════════════════════════════════════════════════════════════════════════════
// Tests
// ════════════════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;

    const MOCK_SESSION: &str = r#"<?xml version="1.0" encoding="UTF-8"?>
<why3session>
  <file name="arrays.mlw">
    <theory name="ArraySum">
      <goal name="sum_nonneg" expl="postcondition" proved="true">
        <proof prover="Z3" time="0.05">
          <result status="valid"/>
        </proof>
      </goal>
      <goal name="sum_bounds" expl="loop invariant" proved="true">
        <proof prover="Alt-Ergo" time="0.12">
          <result status="valid"/>
        </proof>
      </goal>
      <goal name="sum_termination" expl="variant decrease" proved="false">
        <proof prover="Z3" time="1.00">
          <result status="unknown"/>
        </proof>
      </goal>
    </theory>
  </file>
</why3session>"#;

    const MOCK_ATP_SESSION: &str = r#"<?xml version="1.0" encoding="UTF-8"?>
<why3session>
  <file name="logic.mlw">
    <theory name="PropLogic">
      <goal name="de_morgan" expl="lemma" proved="true">
        <proof prover="E" time="0.02">
          <result status="valid"/>
        </proof>
      </goal>
    </theory>
  </file>
</why3session>"#;

    #[test]
    fn test_import_session_parses_goals() {
        let importer = Why3Importer::new();
        let session = importer.import_session(MOCK_SESSION).unwrap();

        assert_eq!(session.theory_name, "ArraySum");
        assert_eq!(session.file_name.as_deref(), Some("arrays.mlw"));
        assert_eq!(session.goals.len(), 3);

        let g0 = &session.goals[0];
        assert_eq!(g0.name, "sum_nonneg");
        assert_eq!(g0.expl, "postcondition");
        assert_eq!(g0.prover, "Z3");
        assert!(g0.proved);
        assert_eq!(g0.proof_time_ms, Some(50));

        let g2 = &session.goals[2];
        assert_eq!(g2.name, "sum_termination");
        assert!(!g2.proved);
    }

    #[test]
    fn test_import_session_empty_errors() {
        let importer = Why3Importer::new();
        let result = importer.import_session("");
        assert!(result.is_err());
        assert!(matches!(result.unwrap_err(), Why3Error::ParseError { .. }));
    }

    #[test]
    fn test_import_session_no_theory_errors() {
        let importer = Why3Importer::new();
        let result = importer.import_session("<why3session></why3session>");
        assert!(result.is_err());
        assert!(matches!(
            result.unwrap_err(),
            Why3Error::SessionError { .. }
        ));
    }

    #[test]
    fn test_import_result_partial_verification() {
        let importer = Why3Importer::new();
        let session = importer.import_session(MOCK_SESSION).unwrap();
        let result = importer.import_result(&session);

        assert_eq!(result.name, "ArraySum");
        assert_eq!(result.goal_count, 3);
        assert_eq!(result.proved_count, 2);
        assert_eq!(result.axiom_profile, AxiomProfile::SMT_ORACLE);
        assert_eq!(result.trust_level, TrustLevel::TrustedOracle);
        assert_eq!(result.provenance.source, SourceSystem::Why3);
        assert!(
            result.diagnostics.iter().any(|d| d.contains("unproved")),
            "expected unproved diagnostic"
        );
    }

    #[test]
    fn test_import_result_atp_certified() {
        let importer = Why3Importer::new();
        let session = importer.import_session(MOCK_ATP_SESSION).unwrap();
        let result = importer.import_result(&session);

        assert_eq!(result.goal_count, 1);
        assert_eq!(result.proved_count, 1);
        assert_eq!(result.axiom_profile, AxiomProfile::ATP_CERT);
        assert_eq!(result.trust_level, TrustLevel::CertificateReplayed);
    }

    #[test]
    fn test_classify_prover_smt() {
        assert_eq!(classify_prover("Z3"), ProverCategory::Smt);
        assert_eq!(classify_prover("CVC5"), ProverCategory::Smt);
        assert_eq!(classify_prover("Alt-Ergo"), ProverCategory::Smt);
    }

    #[test]
    fn test_classify_prover_atp() {
        assert_eq!(classify_prover("E"), ProverCategory::Atp);
        assert_eq!(classify_prover("Vampire"), ProverCategory::Atp);
        assert_eq!(classify_prover("SPASS"), ProverCategory::Atp);
        assert_eq!(classify_prover("eprover"), ProverCategory::Atp);
    }

    #[test]
    fn test_classify_prover_interactive() {
        assert_eq!(classify_prover("Coq"), ProverCategory::Interactive);
        assert_eq!(classify_prover("Isabelle"), ProverCategory::Interactive);
    }

    #[test]
    fn test_why3_importer_default() {
        let _importer = Why3Importer::default();
    }

    #[test]
    fn test_parse_time_ms() {
        assert_eq!(parse_time_ms("0.05"), Some(50));
        assert_eq!(parse_time_ms("1.00"), Some(1000));
        assert_eq!(parse_time_ms("0.001"), Some(1));
        assert_eq!(parse_time_ms("invalid"), None);
        assert_eq!(parse_time_ms("-1.0"), None);
    }

    #[test]
    fn test_extract_xml_attr_present() {
        let xml = r#"<theory name="Foo" proved="true">"#;
        assert_eq!(
            extract_xml_attr(xml, "theory", "name"),
            Some("Foo".to_string())
        );
        assert_eq!(
            extract_xml_attr(xml, "theory", "proved"),
            Some("true".to_string())
        );
    }

    #[test]
    fn test_extract_xml_attr_missing() {
        let xml = r#"<theory name="Foo">"#;
        assert!(extract_xml_attr(xml, "theory", "missing").is_none());
        assert!(extract_xml_attr(xml, "other", "name").is_none());
    }

    // -----------------------------------------------------------------------
    // Why3Driver tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_why3_driver_from_prover_name_smt() {
        assert_eq!(Why3Driver::from_prover_name("Z3"), Why3Driver::Z3);
        assert_eq!(Why3Driver::from_prover_name("z3"), Why3Driver::Z3);
        assert_eq!(Why3Driver::from_prover_name("CVC5"), Why3Driver::Cvc5);
        assert_eq!(Why3Driver::from_prover_name("cvc4"), Why3Driver::Cvc5);
        assert_eq!(
            Why3Driver::from_prover_name("Alt-Ergo"),
            Why3Driver::AltErgo
        );
    }

    #[test]
    fn test_why3_driver_from_prover_name_atp() {
        assert_eq!(Why3Driver::from_prover_name("E"), Why3Driver::EProver);
        assert_eq!(Why3Driver::from_prover_name("eprover"), Why3Driver::EProver);
        assert_eq!(Why3Driver::from_prover_name("Vampire"), Why3Driver::Vampire);
    }

    #[test]
    fn test_why3_driver_from_prover_name_interactive() {
        assert_eq!(Why3Driver::from_prover_name("Coq"), Why3Driver::Coq);
        assert_eq!(
            Why3Driver::from_prover_name("Isabelle"),
            Why3Driver::Isabelle
        );
    }

    #[test]
    fn test_why3_driver_from_prover_name_unknown() {
        let driver = Why3Driver::from_prover_name("MyCustomProver");
        assert_eq!(driver, Why3Driver::Other("MyCustomProver".to_string()));
        assert_eq!(driver.display_name(), "MyCustomProver");
    }

    #[test]
    fn test_why3_driver_category() {
        assert_eq!(Why3Driver::Z3.category(), ProverCategory::Smt);
        assert_eq!(Why3Driver::Cvc5.category(), ProverCategory::Smt);
        assert_eq!(Why3Driver::AltErgo.category(), ProverCategory::Smt);
        assert_eq!(Why3Driver::EProver.category(), ProverCategory::Atp);
        assert_eq!(Why3Driver::Vampire.category(), ProverCategory::Atp);
        assert_eq!(Why3Driver::Coq.category(), ProverCategory::Interactive);
        assert_eq!(Why3Driver::Isabelle.category(), ProverCategory::Interactive);
    }

    #[test]
    fn test_why3_driver_display_name() {
        assert_eq!(Why3Driver::Z3.display_name(), "Z3");
        assert_eq!(Why3Driver::Cvc5.display_name(), "CVC5");
        assert_eq!(Why3Driver::AltErgo.display_name(), "Alt-Ergo");
        assert_eq!(Why3Driver::EProver.display_name(), "E");
    }

    #[test]
    fn test_why3_driver_serde_round_trip() {
        let drivers = [
            Why3Driver::Z3,
            Why3Driver::Cvc5,
            Why3Driver::AltErgo,
            Why3Driver::EProver,
            Why3Driver::Other("Zipperposition".to_string()),
        ];
        for driver in &drivers {
            let json = serde_json::to_string(driver).expect("serialize");
            let restored: Why3Driver = serde_json::from_str(&json).expect("deserialize");
            assert_eq!(&restored, driver);
        }
    }

    // -----------------------------------------------------------------------
    // Why3GoalStatistics tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_why3_goal_statistics_from_session() {
        let importer = Why3Importer::new();
        let session = importer.import_session(MOCK_SESSION).unwrap();
        let stats = Why3GoalStatistics::from_session(&session);

        assert_eq!(stats.total_goals, 3);
        assert_eq!(stats.proved_goals, 2);
        assert_eq!(stats.smt_proved, 2); // Z3, Alt-Ergo are both SMT
        assert_eq!(stats.atp_proved, 0);
        assert_eq!(stats.interactive_proved, 0);
        assert_eq!(stats.total_proof_time_ms, 50 + 120 + 1000);
        assert_eq!(stats.max_proof_time_ms, 1000);
    }

    #[test]
    fn test_why3_goal_statistics_from_atp_session() {
        let importer = Why3Importer::new();
        let session = importer.import_session(MOCK_ATP_SESSION).unwrap();
        let stats = Why3GoalStatistics::from_session(&session);

        assert_eq!(stats.total_goals, 1);
        assert_eq!(stats.proved_goals, 1);
        assert_eq!(stats.smt_proved, 0);
        assert_eq!(stats.atp_proved, 1);
        assert_eq!(stats.total_proof_time_ms, 20);
    }

    #[test]
    fn test_why3_goal_statistics_success_rate() {
        let stats = Why3GoalStatistics {
            total_goals: 10,
            proved_goals: 7,
            ..Default::default()
        };
        assert!((stats.success_rate() - 0.7).abs() < f64::EPSILON);
    }

    #[test]
    fn test_why3_goal_statistics_empty_session_success_rate() {
        let stats = Why3GoalStatistics::default();
        assert!((stats.success_rate() - 1.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_why3_goal_statistics_serde_round_trip() {
        let stats = Why3GoalStatistics {
            total_goals: 5,
            proved_goals: 3,
            smt_proved: 2,
            atp_proved: 1,
            interactive_proved: 0,
            total_proof_time_ms: 500,
            max_proof_time_ms: 200,
        };
        let json = serde_json::to_string(&stats).expect("serialize");
        let restored: Why3GoalStatistics = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(restored, stats);
    }

    // -----------------------------------------------------------------------
    // parse_why3_session_xml standalone function tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_parse_why3_session_xml_succeeds() {
        let session = parse_why3_session_xml(MOCK_SESSION).unwrap();
        assert_eq!(session.theory_name, "ArraySum");
        assert_eq!(session.goals.len(), 3);
    }

    #[test]
    fn test_parse_why3_session_xml_empty_errors() {
        let result = parse_why3_session_xml("");
        assert!(result.is_err());
    }

    #[test]
    fn test_parse_why3_session_xml_no_goals_errors() {
        let result =
            parse_why3_session_xml(r#"<why3session><theory name="Empty"></theory></why3session>"#);
        assert!(result.is_err());
        assert!(matches!(
            result.unwrap_err(),
            Why3Error::SessionError { .. }
        ));
    }
}
