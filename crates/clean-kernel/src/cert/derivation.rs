// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Derivation Trace Parsers for External Geometry Solvers
//!
//! This module parses derivation traces from external geometry solvers
//! (Newclid, AlphaGeometry, etc.) into `GeomStep` sequences for certificate
//! generation.
//!
//! ## Supported Formats
//!
//! ### Newclid/Yuclid Format
//! ```text
//! DERIVE collinear(A,B,C) FROM midpoint_collinear USING midpoint(M,A,B) AND collinear(M,C,B)
//! GIVEN on_circle(A, mathverse)
//! CONSTRUCT midpoint M FROM A B
//! ```
//!
//! ### AlphaGeometry DD Format
//! ```text
//! A B C coll <- A B M midp & M C B coll
//! A mathverse on_circle [given]
//! M = midpoint(A, B)
//! ```
//!
//! ## Usage
//!
//! ```text
//! // Parse Newclid format
//! let steps = NewclidParser::parse_trace(newclid_output)?;
//!
//! // Parse AlphaGeometry format
//! let steps = AlphaGeometryParser::parse_trace(dd_output)?;
//!
//! // Convert to certificates
//! for step in steps {
//!     let cert = generator.step_to_cert(&step)?;
//! }
//! ```

use super::geometry::GeomStep;
use serde::{Deserialize, Serialize};

/// Errors during derivation parsing.
#[derive(Debug, Clone, thiserror::Error)]
#[non_exhaustive]
pub enum DerivationParseError {
    /// Invalid syntax in derivation line
    #[error("Syntax error on line {line}: {message}")]
    SyntaxError {
        /// Line number where the error occurred.
        line: usize,
        /// Description of the syntax error.
        message: String,
    },
    /// Unknown predicate name
    #[error("Unknown predicate: {0}")]
    UnknownPredicate(String),
    /// Unknown lemma name
    #[error("Unknown lemma: {0}")]
    UnknownLemma(String),
    /// Missing required component
    #[error("Missing component: {0}")]
    MissingComponent(String),
    /// Malformed arguments
    #[error("Malformed arguments: {0}")]
    MalformedArgs(String),
}

/// Parser for Newclid/Yuclid derivation format.
///
/// Newclid output format:
/// ```text
/// DERIVE <predicate>(<args>) FROM <lemma> [USING <premise1> AND <premise2> ...]
/// GIVEN <predicate>(<args>)
/// CONSTRUCT <kind> <name> FROM <source_args>
/// ```
#[derive(Debug, Default)]
pub struct NewclidParser;

impl NewclidParser {
    /// Parse a complete derivation trace.
    pub fn parse_trace(input: &str) -> Result<Vec<GeomStep>, DerivationParseError> {
        let mut steps = Vec::new();

        for (line_num, line) in input.lines().enumerate() {
            let line = line.trim();
            if line.is_empty() || line.starts_with('#') || line.starts_with("//") {
                continue;
            }

            let step = Self::parse_line(line, line_num + 1)?;
            steps.push(step);
        }

        Ok(steps)
    }

    /// Parse a single derivation line.
    fn parse_line(line: &str, line_num: usize) -> Result<GeomStep, DerivationParseError> {
        let line_upper = line.to_uppercase();

        if line_upper.starts_with("DERIVE ") {
            Self::parse_derive(line, line_num)
        } else if line_upper.starts_with("GIVEN ") {
            Self::parse_given(line, line_num)
        } else if line_upper.starts_with("CONSTRUCT ") {
            Self::parse_construct(line, line_num)
        } else if line_upper.starts_with("AXIOM ") {
            Self::parse_axiom(line, line_num)
        } else {
            Err(DerivationParseError::SyntaxError {
                line: line_num,
                message: format!("Unknown statement type: {}", line),
            })
        }
    }

    /// Parse a DERIVE statement.
    ///
    /// Format: `DERIVE predicate(args) FROM lemma [USING premise1 AND premise2 ...]`
    fn parse_derive(line: &str, line_num: usize) -> Result<GeomStep, DerivationParseError> {
        // Remove "DERIVE " prefix (case-insensitive)
        let rest = &line[7..].trim();

        // Split by "FROM" (case-insensitive)
        let from_idx = rest.to_uppercase().find(" FROM ").ok_or_else(|| {
            DerivationParseError::SyntaxError {
                line: line_num,
                message: "DERIVE missing FROM clause".to_string(),
            }
        })?;

        let conclusion = &rest[..from_idx].trim();
        let from_part = &rest[from_idx + 6..].trim();

        // Parse conclusion predicate
        let (predicate, args) = Self::parse_predicate(conclusion)?;

        // Split by "USING" (case-insensitive)
        let (lemma_name, premises) =
            if let Some(using_idx) = from_part.to_uppercase().find(" USING ") {
                let lemma = from_part[..using_idx].trim().to_string();
                let premises_str = &from_part[using_idx + 7..];
                let premises = Self::parse_premises(premises_str)?;
                (lemma, premises)
            } else {
                (from_part.to_string(), Vec::new())
            };

        Ok(GeomStep::Apply {
            predicate,
            lemma: lemma_name,
            premises,
            args,
        })
    }

    /// Parse a GIVEN statement.
    ///
    /// Format: `GIVEN predicate(args)`
    fn parse_given(line: &str, line_num: usize) -> Result<GeomStep, DerivationParseError> {
        let rest = &line[6..].trim();
        let (predicate, args) =
            Self::parse_predicate(rest).map_err(|_| DerivationParseError::SyntaxError {
                line: line_num,
                message: "Invalid GIVEN predicate".to_string(),
            })?;

        Ok(GeomStep::Given { predicate, args })
    }

    /// Parse a CONSTRUCT statement.
    ///
    /// Format: `CONSTRUCT kind name FROM source_args`
    fn parse_construct(line: &str, line_num: usize) -> Result<GeomStep, DerivationParseError> {
        let rest = &line[10..].trim();

        // Split by "FROM" (case-insensitive)
        let from_idx = rest.to_uppercase().find(" FROM ").ok_or_else(|| {
            DerivationParseError::SyntaxError {
                line: line_num,
                message: "CONSTRUCT missing FROM clause".to_string(),
            }
        })?;

        let kind_name = &rest[..from_idx].trim();
        let from_args = &rest[from_idx + 6..].trim();

        // Split kind and name
        let parts: Vec<&str> = kind_name.split_whitespace().collect();
        if parts.len() < 2 {
            return Err(DerivationParseError::SyntaxError {
                line: line_num,
                message: "CONSTRUCT needs kind and name".to_string(),
            });
        }

        let kind = parts[0].to_string();
        let name = parts[1].to_string();
        let from: Vec<String> = from_args
            .split_whitespace()
            .map(|s| s.to_string())
            .collect();

        Ok(GeomStep::Construct { kind, name, from })
    }

    /// Parse an AXIOM statement.
    ///
    /// Format: `AXIOM predicate(args)`
    fn parse_axiom(line: &str, line_num: usize) -> Result<GeomStep, DerivationParseError> {
        let rest = &line[6..].trim();
        let (name, args) =
            Self::parse_predicate(rest).map_err(|_| DerivationParseError::SyntaxError {
                line: line_num,
                message: "Invalid AXIOM predicate".to_string(),
            })?;

        Ok(GeomStep::Axiom { name, args })
    }

    /// Parse a predicate expression like `collinear(A, B, C)`.
    fn parse_predicate(s: &str) -> Result<(String, Vec<String>), DerivationParseError> {
        let s = s.trim();

        // Find opening paren
        let paren_idx = s.find('(').ok_or_else(|| {
            DerivationParseError::MalformedArgs(format!("Missing parentheses in: {}", s))
        })?;

        let name = s[..paren_idx].trim().to_string();

        // Find closing paren
        let close_idx = s.rfind(')').ok_or_else(|| {
            DerivationParseError::MalformedArgs(format!("Missing closing paren in: {}", s))
        })?;

        let args_str = &s[paren_idx + 1..close_idx];
        let args: Vec<String> = args_str
            .split(',')
            .map(|a| a.trim().to_string())
            .filter(|a| !a.is_empty())
            .collect();

        Ok((name, args))
    }

    /// Parse premises separated by AND.
    fn parse_premises(s: &str) -> Result<Vec<GeomStep>, DerivationParseError> {
        let mut premises = Vec::new();

        for part in s.split(" AND ") {
            let part = part.trim();
            if part.is_empty() {
                continue;
            }

            // Each premise is a predicate(args)
            let (name, args) = Self::parse_predicate(part)?;
            premises.push(GeomStep::Axiom { name, args });
        }

        Ok(premises)
    }
}

/// Parser for AlphaGeometry DD (deductive database) format.
///
/// DD format:
/// ```text
/// A B C coll <- A B M midp & M C B coll
/// A mathverse on_circle [given]
/// M = midpoint(A, B)
/// ```
#[derive(Debug, Default)]
pub struct AlphaGeometryParser;

impl AlphaGeometryParser {
    /// Parse a complete derivation trace.
    pub fn parse_trace(input: &str) -> Result<Vec<GeomStep>, DerivationParseError> {
        let mut steps = Vec::new();

        for (line_num, line) in input.lines().enumerate() {
            let line = line.trim();
            if line.is_empty() || line.starts_with('#') {
                continue;
            }

            let step = Self::parse_line(line, line_num + 1)?;
            steps.push(step);
        }

        Ok(steps)
    }

    /// Parse a single DD line.
    fn parse_line(line: &str, line_num: usize) -> Result<GeomStep, DerivationParseError> {
        let line = line.trim();

        // Check for given marker
        if line.ends_with("[given]") || line.ends_with("[GIVEN]") {
            let content = line[..line.len() - 7].trim();
            let (predicate, args) = Self::parse_dd_predicate(content)?;
            return Ok(GeomStep::Given { predicate, args });
        }

        // Check for construction: M = midpoint(A, B)
        if line.contains(" = ") {
            return Self::parse_construction(line, line_num);
        }

        // Check for derivation: conclusion <- premises (or conclusion <- with empty premises)
        if line.contains(" <- ")
            || line.contains(" ← ")
            || line.ends_with(" <-")
            || line.ends_with(" ←")
        {
            return Self::parse_derivation(line, line_num);
        }

        // Standalone predicate (axiom)
        let (name, args) = Self::parse_dd_predicate(line)?;
        Ok(GeomStep::Axiom { name, args })
    }

    /// Parse a DD derivation line.
    ///
    /// Format: `A B C coll <- A B M midp & M C B coll`
    fn parse_derivation(line: &str, _line_num: usize) -> Result<GeomStep, DerivationParseError> {
        // Split by arrow - find the delimiter and split once
        // Handle both "conclusion <- premises" and "conclusion <-" (empty premises after trim)
        let (conclusion, premises_str) = if let Some(idx) = line.find(" <- ") {
            (&line[..idx], &line[idx + 4..])
        } else if let Some(idx) = line.find(" ← ") {
            // UTF-8 arrow is 3 bytes
            (&line[..idx], &line[idx + 4..])
        } else if let Some(stripped) = line.strip_suffix(" <-") {
            (stripped, "")
        } else if let Some(stripped) = line.strip_suffix(" ←") {
            (stripped, "")
        } else {
            return Err(DerivationParseError::MissingComponent(
                "Missing arrow in derivation".to_string(),
            ));
        };

        // Parse conclusion
        let (predicate, args) = Self::parse_dd_predicate(conclusion)?;

        // Parse premises (separated by &)
        let mut premises = Vec::new();
        for premise in premises_str.split('&') {
            let premise = premise.trim();
            if premise.is_empty() {
                continue;
            }
            let (name, args) = Self::parse_dd_predicate(premise)?;
            premises.push(GeomStep::Axiom { name, args });
        }

        // Determine lemma name from predicate structure
        // This is a heuristic - in practice, the solver would provide the lemma name
        let lemma = Self::infer_lemma_name(&premises);

        Ok(GeomStep::Apply {
            predicate,
            lemma,
            premises,
            args,
        })
    }

    /// Parse a DD construction line.
    ///
    /// Format: `M = midpoint(A, B)`
    fn parse_construction(line: &str, _line_num: usize) -> Result<GeomStep, DerivationParseError> {
        let parts: Vec<&str> = line.splitn(2, " = ").collect();
        if parts.len() < 2 {
            return Err(DerivationParseError::MalformedArgs(
                "Invalid construction format".to_string(),
            ));
        }

        let name = parts[0].trim().to_string();
        let def = parts[1].trim();

        // Parse construction like midpoint(A, B)
        let paren_idx = def.find('(').ok_or_else(|| {
            DerivationParseError::MalformedArgs("Construction needs parentheses".to_string())
        })?;

        let kind = def[..paren_idx].trim().to_string();
        let close_idx = def.rfind(')').ok_or_else(|| {
            DerivationParseError::MalformedArgs("Missing closing paren".to_string())
        })?;

        let args_str = &def[paren_idx + 1..close_idx];
        let from: Vec<String> = args_str
            .split(',')
            .map(|a| a.trim().to_string())
            .filter(|a| !a.is_empty())
            .collect();

        Ok(GeomStep::Construct { kind, name, from })
    }

    /// Parse a DD-format predicate (space-separated).
    ///
    /// Format: `A B C coll` or `A mathverse on_circle`
    fn parse_dd_predicate(s: &str) -> Result<(String, Vec<String>), DerivationParseError> {
        let s = s.trim();
        let parts: Vec<&str> = s.split_whitespace().collect();

        // Last part is the predicate name; everything before it is arguments.
        let Some((pred_name, arg_parts)) = parts.split_last() else {
            return Err(DerivationParseError::MalformedArgs(
                "Empty predicate".to_string(),
            ));
        };
        let pred_name = pred_name.to_string();
        let args: Vec<String> = arg_parts.iter().map(|s| s.to_string()).collect();

        Ok((pred_name, args))
    }

    /// Infer lemma name from premises (heuristic).
    fn infer_lemma_name(premises: &[GeomStep]) -> String {
        // Look for patterns to infer the lemma
        // This is a simple heuristic; real implementations would have explicit lemma names

        let premise_preds: Vec<&str> = premises
            .iter()
            .filter_map(|p| {
                if let GeomStep::Axiom { name, .. } = p {
                    Some(name.as_str())
                } else {
                    None
                }
            })
            .collect();

        if premise_preds.contains(&"midp") || premise_preds.contains(&"midpoint") {
            return "midpoint_collinear".to_string();
        }

        if premise_preds.contains(&"para") || premise_preds.contains(&"parallel") {
            return "parallel_trans".to_string();
        }

        if premise_preds.contains(&"coll") || premise_preds.contains(&"collinear") {
            return "collinear_trans".to_string();
        }

        // Default: use first premise predicate + "_inference"
        if !premise_preds.is_empty() {
            return format!("{}_inference", premise_preds[0]);
        }

        "unknown_lemma".to_string()
    }
}

/// A complete derivation trace from a geometry solver.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DerivationTrace {
    /// Source format of the trace
    pub format: DerivationFormat,

    /// Problem ID this derivation solves
    pub problem_id: String,

    /// Ordered derivation steps
    pub steps: Vec<GeomStep>,

    /// Whether the derivation completes a proof
    pub complete: bool,

    /// Solver metadata
    #[serde(default)]
    pub metadata: TraceMetadata,
}

/// Format of the derivation trace.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum DerivationFormat {
    /// Newclid format from Newclid geometry solver.
    Newclid,
    /// AlphaGeometry format from DeepMind's AlphaGeometry.
    AlphaGeometry,
    /// Custom user-defined format.
    Custom,
    /// JSON format for structured traces.
    Json,
}

/// Metadata about the derivation trace.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct TraceMetadata {
    /// Solver that produced the trace
    #[serde(default)]
    pub solver: Option<String>,

    /// Solver version
    #[serde(default)]
    pub solver_version: Option<String>,

    /// Time to produce the derivation (ms)
    #[serde(default)]
    pub solve_time_ms: Option<u64>,

    /// Number of auxiliary constructions
    #[serde(default)]
    pub aux_construction_count: Option<usize>,
}

impl DerivationTrace {
    /// Parse a derivation trace from raw text with auto-detected format.
    pub fn parse_auto(input: &str, problem_id: &str) -> Result<Self, DerivationParseError> {
        // Try to detect format
        let format = Self::detect_format(input);

        let steps = match format {
            DerivationFormat::Newclid => NewclidParser::parse_trace(input)?,
            DerivationFormat::AlphaGeometry => AlphaGeometryParser::parse_trace(input)?,
            DerivationFormat::Json => Self::parse_json_steps(input)?,
            DerivationFormat::Custom => {
                return Err(DerivationParseError::SyntaxError {
                    line: 0,
                    message: "Cannot auto-parse custom format".to_string(),
                })
            }
        };

        Ok(Self {
            format,
            problem_id: problem_id.to_string(),
            steps,
            complete: true,
            metadata: TraceMetadata::default(),
        })
    }

    /// Parse a derivation trace from JSON.
    pub fn from_json(json_str: &str) -> Result<Self, DerivationParseError> {
        serde_json::from_str(json_str).map_err(|e| DerivationParseError::SyntaxError {
            line: 0,
            message: format!("JSON parse error: {}", e),
        })
    }

    /// Detect the format of a derivation trace.
    fn detect_format(input: &str) -> DerivationFormat {
        let upper = input.to_uppercase();

        // Newclid uses DERIVE/GIVEN/CONSTRUCT keywords
        if upper.contains("DERIVE ") || upper.contains("GIVEN ") || upper.contains("CONSTRUCT ") {
            return DerivationFormat::Newclid;
        }

        // AlphaGeometry uses <- arrows and space-separated predicates
        if input.contains(" <- ") || input.contains(" ← ") {
            return DerivationFormat::AlphaGeometry;
        }

        // Check for JSON
        if input.trim().starts_with('{') || input.trim().starts_with('[') {
            return DerivationFormat::Json;
        }

        // Default to Newclid format
        DerivationFormat::Newclid
    }

    /// Parse JSON-formatted steps.
    fn parse_json_steps(input: &str) -> Result<Vec<GeomStep>, DerivationParseError> {
        let input = input.trim();

        // Try parsing as array of steps
        if input.starts_with('[') {
            return serde_json::from_str(input).map_err(|e| DerivationParseError::SyntaxError {
                line: 0,
                message: format!("JSON array parse error: {}", e),
            });
        }

        // Try parsing as full trace
        let trace: DerivationTrace =
            serde_json::from_str(input).map_err(|e| DerivationParseError::SyntaxError {
                line: 0,
                message: format!("JSON trace parse error: {}", e),
            })?;

        Ok(trace.steps)
    }

    /// Serialize the trace to JSON.
    pub fn to_json(&self) -> Result<String, DerivationParseError> {
        serde_json::to_string_pretty(self).map_err(|e| DerivationParseError::SyntaxError {
            line: 0,
            message: format!("JSON serialize error: {}", e),
        })
    }

    /// Get the number of derivation steps.
    pub fn len(&self) -> usize {
        self.steps.len()
    }

    /// Check if the trace is empty.
    pub fn is_empty(&self) -> bool {
        self.steps.is_empty()
    }

    /// Count auxiliary constructions.
    pub fn construction_count(&self) -> usize {
        self.steps
            .iter()
            .filter(|s| matches!(s, GeomStep::Construct { .. }))
            .count()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_newclid_derive() {
        let input = "DERIVE collinear(A, B, C) FROM midpoint_collinear USING midpoint(M, A, B) AND collinear(M, C, B)";
        let steps = NewclidParser::parse_trace(input).unwrap();

        assert_eq!(steps.len(), 1);
        if let GeomStep::Apply {
            predicate,
            lemma,
            premises,
            args,
        } = &steps[0]
        {
            assert_eq!(predicate, "collinear");
            assert_eq!(lemma, "midpoint_collinear");
            assert_eq!(args, &["A", "B", "C"]);
            assert_eq!(premises.len(), 2);
        } else {
            panic!("Expected Apply step");
        }
    }

    #[test]
    fn test_newclid_given() {
        let input = "GIVEN on_circle(A, mathverse)";
        let steps = NewclidParser::parse_trace(input).unwrap();

        assert_eq!(steps.len(), 1);
        if let GeomStep::Given { predicate, args } = &steps[0] {
            assert_eq!(predicate, "on_circle");
            assert_eq!(args, &["A", "mathverse"]);
        } else {
            panic!("Expected Given step");
        }
    }

    #[test]
    fn test_newclid_construct() {
        let input = "CONSTRUCT midpoint M FROM A B";
        let steps = NewclidParser::parse_trace(input).unwrap();

        assert_eq!(steps.len(), 1);
        if let GeomStep::Construct { kind, name, from } = &steps[0] {
            assert_eq!(kind, "midpoint");
            assert_eq!(name, "M");
            assert_eq!(from, &["A", "B"]);
        } else {
            panic!("Expected Construct step");
        }
    }

    #[test]
    fn test_newclid_multiline() {
        let input = r#"
        # This is a comment
        GIVEN not_equal(A, B)
        GIVEN on_line(C, l)
        CONSTRUCT midpoint M FROM A B
        DERIVE collinear(A, M, B) FROM midpoint_on_segment
        "#;

        let steps = NewclidParser::parse_trace(input).unwrap();
        assert_eq!(steps.len(), 4);
    }

    #[test]
    fn test_alphageometry_derivation() {
        let input = "A B C coll <- A B M midp & M C B coll";
        let steps = AlphaGeometryParser::parse_trace(input).unwrap();

        assert_eq!(steps.len(), 1);
        if let GeomStep::Apply {
            predicate,
            premises,
            args,
            ..
        } = &steps[0]
        {
            assert_eq!(predicate, "coll");
            assert_eq!(args, &["A", "B", "C"]);
            assert_eq!(premises.len(), 2);
        } else {
            panic!("Expected Apply step");
        }
    }

    #[test]
    fn test_alphageometry_given() {
        let input = "A mathverse on_circle [given]";
        let steps = AlphaGeometryParser::parse_trace(input).unwrap();

        assert_eq!(steps.len(), 1);
        if let GeomStep::Given { predicate, args } = &steps[0] {
            assert_eq!(predicate, "on_circle");
            assert_eq!(args, &["A", "mathverse"]);
        } else {
            panic!("Expected Given step");
        }
    }

    #[test]
    fn test_alphageometry_construction() {
        let input = "M = midpoint(A, B)";
        let steps = AlphaGeometryParser::parse_trace(input).unwrap();

        assert_eq!(steps.len(), 1);
        if let GeomStep::Construct { kind, name, from } = &steps[0] {
            assert_eq!(kind, "midpoint");
            assert_eq!(name, "M");
            assert_eq!(from, &["A", "B"]);
        } else {
            panic!("Expected Construct step");
        }
    }

    #[test]
    fn test_format_detection() {
        assert_eq!(
            DerivationTrace::detect_format("DERIVE x FROM y"),
            DerivationFormat::Newclid
        );
        assert_eq!(
            DerivationTrace::detect_format("A B C coll <- X"),
            DerivationFormat::AlphaGeometry
        );
        assert_eq!(
            DerivationTrace::detect_format("[{\"Axiom\": {}}]"),
            DerivationFormat::Json
        );
    }

    #[test]
    fn test_trace_construction_count() {
        let input = r#"
        GIVEN on_circle(A, mathverse)
        CONSTRUCT midpoint M FROM A B
        CONSTRUCT circumcenter O FROM A B C
        DERIVE collinear(A, M, B) FROM midpoint_on_segment
        "#;

        let trace = DerivationTrace::parse_auto(input, "test").unwrap();
        assert_eq!(trace.construction_count(), 2);
        assert_eq!(trace.len(), 4);
    }

    #[test]
    fn test_trace_roundtrip() {
        let input = r#"
        GIVEN not_equal(A, B)
        CONSTRUCT midpoint M FROM A B
        "#;

        let trace = DerivationTrace::parse_auto(input, "roundtrip_test").unwrap();
        let json = trace.to_json().unwrap();
        let reparsed = DerivationTrace::from_json(&json).unwrap();

        assert_eq!(trace.problem_id, reparsed.problem_id);
        assert_eq!(trace.steps.len(), reparsed.steps.len());
    }
}
