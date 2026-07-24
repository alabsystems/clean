// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Liquid Haskell importer (refinement types → propositions).
//!
//! Liquid Haskell extends Haskell with refinement types, where types carry
//! logical predicates checked by an SMT solver. This importer converts
//! LH refinement annotations into Mathverse library entries with appropriate
//! trust tracking.
//!
//! # Axiom profiles
//!
//! All Liquid Haskell imports carry `SMT_ORACLE` because LH relies on
//! external SMT solvers (typically Z3) for refinement checking. The SMT
//! solver's result is trusted without a proof certificate.

use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::types::{AxiomProfile, Provenance, SourceSystem, TrustLevel};

// ---------------------------------------------------------------------------
// Errors
// ---------------------------------------------------------------------------

/// Errors during Liquid Haskell module import.
#[derive(Debug, Error)]
#[non_exhaustive]
pub enum LiquidHaskellError {
    /// Failed to parse the LH module text.
    #[error("Liquid Haskell parse error at offset {offset}: {message}")]
    ParseError { offset: usize, message: String },

    /// Refinement type predicate could not be translated.
    #[error("refinement error in {name}: {reason}")]
    RefinementError { name: String, reason: String },

    /// Encountered an unsupported annotation form.
    #[error("unsupported LH annotation: {annotation}")]
    UnsupportedAnnotation { annotation: String },
}

// ---------------------------------------------------------------------------
// Domain types
// ---------------------------------------------------------------------------

/// A single refinement type annotation from a Liquid Haskell module.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct LhRefinement {
    /// Name of the refined binding.
    pub name: String,
    /// Base Haskell type (e.g., `Int`, `[a]`).
    pub base_type: String,
    /// Refinement predicate (e.g., `v > 0`).
    pub predicate: String,
    /// Module this refinement belongs to.
    pub module_name: String,
    /// Whether the SMT solver verified this refinement.
    pub verified: bool,
}

/// A parsed Liquid Haskell module with its refinement annotations.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct LhModule {
    pub name: String,
    pub refinements: Vec<LhRefinement>,
    pub imports: Vec<String>,
}

/// Result of importing a Liquid Haskell module into the Mathverse library.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct LhImportResult {
    pub name: String,
    pub refinement_count: usize,
    pub verified_count: usize,
    pub axiom_profile: AxiomProfile,
    pub trust_level: TrustLevel,
    pub provenance: Provenance,
    pub diagnostics: Vec<String>,
}

// ---------------------------------------------------------------------------
// Importer
// ---------------------------------------------------------------------------

/// Importer for Liquid Haskell modules into the Mathverse library.
pub struct LhImporter {
    namespace: String,
}

impl Default for LhImporter {
    fn default() -> Self {
        Self::new()
    }
}

impl LhImporter {
    /// Create a new Liquid Haskell importer with default namespace.
    #[must_use]
    pub fn new() -> Self {
        Self {
            namespace: "LiquidHaskell.Imported".to_owned(),
        }
    }

    /// Import a module from its textual representation.
    ///
    /// Parses `{-@ ... @-}` annotation blocks and `module` / `import`
    /// declarations from the source text.
    pub fn import_module(&self, module_text: &str) -> Result<LhModule, LiquidHaskellError> {
        let trimmed = module_text.trim();
        if trimmed.is_empty() {
            return Err(LiquidHaskellError::ParseError {
                offset: 0,
                message: "empty module text".to_owned(),
            });
        }

        let mut module_name = "UnknownModule".to_owned();
        let mut imports = Vec::new();
        let mut refinements = Vec::new();

        for line in trimmed.lines() {
            let line = line.trim();

            if line.starts_with("module ") {
                module_name = line
                    .strip_prefix("module ")
                    .and_then(|r| r.split_whitespace().next())
                    .unwrap_or("UnknownModule")
                    .to_owned();
                continue;
            }

            if line.starts_with("import ") {
                let import_name = line
                    .strip_prefix("import ")
                    .and_then(|r| {
                        let r = r.strip_prefix("qualified ").unwrap_or(r);
                        r.split_whitespace().next()
                    })
                    .unwrap_or("")
                    .to_owned();
                if !import_name.is_empty() {
                    imports.push(import_name);
                }
                continue;
            }

            // Parse inline LH annotations: {-@ name :: {v:Type | pred} @-}
            if line.starts_with("{-@") && line.ends_with("@-}") {
                if let Some(refinement) = parse_lh_annotation(line, &module_name) {
                    refinements.push(refinement);
                }
            }
        }

        Ok(LhModule {
            name: module_name,
            refinements,
            imports,
        })
    }

    /// Produce an import result summary for a parsed module.
    #[must_use]
    pub fn import_result(&self, module: &LhModule) -> LhImportResult {
        let refinement_count = module.refinements.len();
        let verified_count = module.refinements.iter().filter(|r| r.verified).count();
        let unverified_count = refinement_count - verified_count;

        // LH always uses SMT solvers — mark accordingly.
        let axiom_profile = AxiomProfile::SMT_ORACLE;

        let trust_level = if unverified_count > 0 {
            TrustLevel::PartiallyAxiomatized
        } else {
            TrustLevel::TrustedOracle
        };

        let qualified_name = format!("{}.{}", self.namespace, module.name);

        let provenance = Provenance {
            source: SourceSystem::LiquidHaskell,
            original_name: module.name.clone(),
            source_file: None,
            axiom_profile,
        };

        let mut diagnostics = Vec::new();
        if unverified_count > 0 {
            diagnostics.push(format!(
                "{unverified_count} refinement(s) not verified by SMT solver"
            ));
        }
        diagnostics.push("all verification relies on external SMT oracle".to_owned());

        LhImportResult {
            name: qualified_name,
            refinement_count,
            verified_count,
            axiom_profile,
            trust_level,
            provenance,
            diagnostics,
        }
    }
}

// ---------------------------------------------------------------------------
// Extended types
// ---------------------------------------------------------------------------

/// A refinement type constraint from a Liquid Haskell fixpoint query.
///
/// Liquid Haskell generates fixpoint queries from refinement type annotations.
/// Each constraint represents a subtyping obligation: the environment must
/// imply that the left-hand type is a subtype of the right-hand type.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct LhConstraint {
    /// Constraint identifier.
    pub id: u64,
    /// Environment bindings (name -> refinement type).
    pub environment: Vec<(String, String)>,
    /// Left-hand (actual) refinement type expression.
    pub lhs: String,
    /// Right-hand (expected) refinement type expression.
    pub rhs: String,
    /// Source location tag from the fixpoint file.
    pub source_tag: Option<String>,
    /// Whether this constraint was satisfiable.
    pub satisfiable: bool,
}

/// Statistics from a Liquid Haskell verification session.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct LhStatistics {
    /// Total refinement annotations in the module.
    pub refinements_total: usize,
    /// Refinements verified by the SMT solver.
    pub refinements_verified: usize,
    /// Total fixpoint constraints generated.
    pub constraints_total: usize,
    /// Fixpoint constraints satisfiable.
    pub constraints_satisfiable: usize,
    /// Number of imports in the module.
    pub imports_count: usize,
    /// Solver time in milliseconds (if tracked).
    pub solver_time_ms: u64,
}

impl LhStatistics {
    /// Compute statistics from a parsed module.
    #[must_use]
    pub fn from_module(module: &LhModule) -> Self {
        let refinements_total = module.refinements.len();
        let refinements_verified = module.refinements.iter().filter(|r| r.verified).count();
        Self {
            refinements_total,
            refinements_verified,
            constraints_total: 0,
            constraints_satisfiable: 0,
            imports_count: module.imports.len(),
            solver_time_ms: 0,
        }
    }

    /// Compute statistics from a module and its fixpoint constraints.
    #[must_use]
    pub fn from_module_and_constraints(module: &LhModule, constraints: &[LhConstraint]) -> Self {
        let mut stats = Self::from_module(module);
        stats.constraints_total = constraints.len();
        stats.constraints_satisfiable = constraints.iter().filter(|c| c.satisfiable).count();
        stats
    }

    /// Fraction of refinements verified, as a value in `[0.0, 1.0]`.
    #[must_use]
    pub fn verification_rate(&self) -> f64 {
        if self.refinements_total == 0 {
            1.0
        } else {
            self.refinements_verified as f64 / self.refinements_total as f64
        }
    }
}

/// Parse a Liquid Haskell fixpoint query from its textual representation.
///
/// Fixpoint queries are generated by Liquid Haskell's constraint generation
/// phase and discharged by the fixpoint solver (backed by Z3). The format
/// is a sequence of `constraint` blocks:
///
/// ```text
/// constraint:
///   env [x : {v:Int | v > 0}]
///   lhs {v:Int | v > 0}
///   rhs {v:Int | v >= 0}
///   id 1
///   tag "Main.hs:10:5"
/// ```
///
/// # Errors
///
/// Returns `LiquidHaskellError::ParseError` if the input is empty.
pub fn parse_liquid_fixpoint(fixpoint_text: &str) -> Result<Vec<LhConstraint>, LiquidHaskellError> {
    let trimmed = fixpoint_text.trim();
    if trimmed.is_empty() {
        return Err(LiquidHaskellError::ParseError {
            offset: 0,
            message: "empty fixpoint text".to_owned(),
        });
    }

    let mut constraints = Vec::new();
    let mut current_id: u64 = 0;
    let mut current_lhs = String::new();
    let mut current_rhs = String::new();
    let mut current_tag: Option<String> = None;
    let mut current_env: Vec<(String, String)> = Vec::new();
    let mut in_constraint = false;

    for line in trimmed.lines() {
        let line = line.trim();

        if line == "constraint:" {
            // Flush previous constraint if any.
            if in_constraint {
                constraints.push(LhConstraint {
                    id: current_id,
                    environment: current_env.clone(),
                    lhs: current_lhs.clone(),
                    rhs: current_rhs.clone(),
                    source_tag: current_tag.clone(),
                    satisfiable: true, // default to satisfiable
                });
            }
            in_constraint = true;
            current_id = 0;
            current_lhs.clear();
            current_rhs.clear();
            current_tag = None;
            current_env.clear();
            continue;
        }

        if !in_constraint {
            continue;
        }

        if let Some(rest) = line.strip_prefix("id ") {
            current_id = rest.trim().parse().unwrap_or(0);
        } else if let Some(rest) = line.strip_prefix("lhs ") {
            current_lhs = rest.trim().to_owned();
        } else if let Some(rest) = line.strip_prefix("rhs ") {
            current_rhs = rest.trim().to_owned();
        } else if let Some(rest) = line.strip_prefix("tag ") {
            let tag = rest.trim().trim_matches('"').to_owned();
            if !tag.is_empty() {
                current_tag = Some(tag);
            }
        } else if let Some(rest) = line.strip_prefix("env ") {
            // Parse env entry: [name : type]
            let rest = rest.trim();
            let inner = rest.strip_prefix('[').and_then(|r| r.strip_suffix(']'));
            if let Some(inner) = inner {
                if let Some((name, ty)) = inner.split_once(':') {
                    current_env.push((name.trim().to_owned(), ty.trim().to_owned()));
                }
            }
        }
    }

    // Flush last constraint.
    if in_constraint {
        constraints.push(LhConstraint {
            id: current_id,
            environment: current_env,
            lhs: current_lhs,
            rhs: current_rhs,
            source_tag: current_tag,
            satisfiable: true,
        });
    }

    Ok(constraints)
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Parse a single `{-@ ... @-}` annotation line into a refinement.
///
/// Expected format: `{-@ name :: {v:BaseType | predicate} @-}`
/// Also accepts simple type signatures: `{-@ name :: Type @-}`
fn parse_lh_annotation(line: &str, module_name: &str) -> Option<LhRefinement> {
    // Strip annotation delimiters.
    let inner = line.strip_prefix("{-@")?.strip_suffix("@-}")?.trim();

    // Split on `::`
    let (name_part, type_part) = inner.split_once("::")?;
    let name = name_part.trim().to_owned();
    if name.is_empty() {
        return None;
    }

    let type_part = type_part.trim();

    // Try to parse refinement type: {v:Base | pred}
    if let Some((base_type, predicate)) = parse_refinement_type(type_part) {
        Some(LhRefinement {
            name,
            base_type,
            predicate,
            module_name: module_name.to_owned(),
            verified: true, // assume verified if present in annotation
        })
    } else {
        // Simple type signature without refinement predicate.
        Some(LhRefinement {
            name,
            base_type: type_part.to_owned(),
            predicate: "true".to_owned(),
            module_name: module_name.to_owned(),
            verified: true,
        })
    }
}

/// Parse a refinement type `{v:Base | pred}` into `(base_type, predicate)`.
fn parse_refinement_type(s: &str) -> Option<(String, String)> {
    let s = s.trim();
    // For function types like `x:Int -> {v:Int | v >= 0}`, extract from last `{...}` block.
    let (inner_start, inner_end) = if s.starts_with('{') {
        (1, s.len().checked_sub(1)?)
    } else {
        let brace_pos = s.rfind('{')?;
        (brace_pos + 1, s.len().checked_sub(1)?)
    };
    let candidate = &s[inner_start..inner_end];
    let candidate = candidate.strip_suffix('}').unwrap_or(candidate);
    let (binder_and_type, predicate) = candidate.split_once('|')?;

    // binder_and_type is `v:Base` — extract the base type after `:`
    let base_type = binder_and_type
        .split_once(':')
        .map(|(_, t)| t.trim().to_owned())
        .unwrap_or_else(|| binder_and_type.trim().to_owned());

    let predicate = predicate.trim().to_owned();
    Some((base_type, predicate))
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    const MOCK_MODULE: &str = r#"module Data.SafeList where
import Data.List
import qualified Data.Map
{-@ length :: xs:[a] -> {v:Int | v >= 0} @-}
{-@ head :: {v:[a] | len v > 0} -> a @-}
{-@ tail :: {v:[a] | len v > 0} -> [a] @-}
"#;

    #[test]
    fn test_lh_import_module_parses_refinements() {
        let importer = LhImporter::new();
        let module = importer
            .import_module(MOCK_MODULE)
            .expect("should parse mock module");

        assert_eq!(module.name, "Data.SafeList");
        assert_eq!(module.refinements.len(), 3);
        assert_eq!(module.imports.len(), 2);
    }

    #[test]
    fn test_lh_import_module_empty_input() {
        let importer = LhImporter::new();
        let result = importer.import_module("");
        assert!(result.is_err());
    }

    #[test]
    fn test_lh_import_result_smt_oracle_profile() {
        let importer = LhImporter::new();
        let module = importer.import_module(MOCK_MODULE).expect("should parse");
        let result = importer.import_result(&module);

        assert_eq!(result.refinement_count, 3);
        assert_eq!(result.verified_count, 3);
        assert!(result.axiom_profile.contains(AxiomProfile::SMT_ORACLE));
        assert_eq!(result.trust_level, TrustLevel::TrustedOracle);
        assert_eq!(result.provenance.source, SourceSystem::LiquidHaskell);
    }

    #[test]
    fn test_lh_refinement_parsing() {
        let line = "{-@ abs :: x:Int -> {v:Int | v >= 0} @-}";
        let refinement = parse_lh_annotation(line, "TestModule").expect("should parse annotation");

        assert_eq!(refinement.name, "abs");
        assert_eq!(refinement.base_type, "Int");
        assert_eq!(refinement.predicate, "v >= 0");
        assert_eq!(refinement.module_name, "TestModule");
        assert!(refinement.verified);
    }

    #[test]
    fn test_lh_simple_type_annotation() {
        let line = "{-@ type Nat = {v:Int | v >= 0} @-}";
        let refinement = parse_lh_annotation(line, "TestModule");
        // "type Nat = {v:Int | v >= 0}" has `::` nowhere, so returns None.
        assert!(refinement.is_none());
    }

    #[test]
    fn test_lh_module_with_unverified_refinement() {
        let module = LhModule {
            name: "Test".to_owned(),
            refinements: vec![
                LhRefinement {
                    name: "f".to_owned(),
                    base_type: "Int".to_owned(),
                    predicate: "v > 0".to_owned(),
                    module_name: "Test".to_owned(),
                    verified: true,
                },
                LhRefinement {
                    name: "g".to_owned(),
                    base_type: "Int".to_owned(),
                    predicate: "v < 100".to_owned(),
                    module_name: "Test".to_owned(),
                    verified: false,
                },
            ],
            imports: Vec::new(),
        };

        let importer = LhImporter::new();
        let result = importer.import_result(&module);

        assert_eq!(result.verified_count, 1);
        assert_eq!(result.trust_level, TrustLevel::PartiallyAxiomatized);
        assert!(result
            .diagnostics
            .iter()
            .any(|d| d.contains("not verified")));
    }

    #[test]
    fn test_lh_importer_default() {
        let importer = LhImporter::default();
        assert_eq!(importer.namespace, "LiquidHaskell.Imported");
    }

    #[test]
    fn test_lh_parse_refinement_type() {
        let (base, pred) =
            parse_refinement_type("{v:Int | v >= 0}").expect("should parse refinement");
        assert_eq!(base, "Int");
        assert_eq!(pred, "v >= 0");
    }

    #[test]
    fn test_lh_qualified_import_parsing() {
        let input = r#"module Foo where
import qualified Data.Map
import Data.Set
"#;
        let importer = LhImporter::new();
        let module = importer.import_module(input).expect("should parse");
        assert_eq!(module.imports, vec!["Data.Map", "Data.Set"]);
    }

    // -----------------------------------------------------------------------
    // LhConstraint tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_lh_constraint_creation() {
        let constraint = LhConstraint {
            id: 1,
            environment: vec![("x".to_owned(), "{v:Int | v > 0}".to_owned())],
            lhs: "{v:Int | v > 0}".to_owned(),
            rhs: "{v:Int | v >= 0}".to_owned(),
            source_tag: Some("Main.hs:10:5".to_owned()),
            satisfiable: true,
        };
        assert_eq!(constraint.id, 1);
        assert!(constraint.satisfiable);
        assert_eq!(constraint.environment.len(), 1);
    }

    #[test]
    fn test_lh_constraint_serde_round_trip() {
        let constraint = LhConstraint {
            id: 42,
            environment: vec![
                ("x".to_owned(), "Int".to_owned()),
                ("y".to_owned(), "Bool".to_owned()),
            ],
            lhs: "{v:Int | v > x}".to_owned(),
            rhs: "{v:Int | v >= 0}".to_owned(),
            source_tag: None,
            satisfiable: false,
        };
        let json = serde_json::to_string(&constraint).expect("serialize");
        let restored: LhConstraint = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(restored, constraint);
    }

    // -----------------------------------------------------------------------
    // LhStatistics tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_lh_statistics_from_module() {
        let importer = LhImporter::new();
        let module = importer.import_module(MOCK_MODULE).expect("should parse");
        let stats = LhStatistics::from_module(&module);

        assert_eq!(stats.refinements_total, 3);
        assert_eq!(stats.refinements_verified, 3);
        assert_eq!(stats.imports_count, 2);
        assert_eq!(stats.constraints_total, 0);
    }

    #[test]
    fn test_lh_statistics_from_module_and_constraints() {
        let importer = LhImporter::new();
        let module = importer.import_module(MOCK_MODULE).expect("should parse");
        let constraints = vec![
            LhConstraint {
                id: 1,
                environment: vec![],
                lhs: "p1".to_owned(),
                rhs: "q1".to_owned(),
                source_tag: None,
                satisfiable: true,
            },
            LhConstraint {
                id: 2,
                environment: vec![],
                lhs: "p2".to_owned(),
                rhs: "q2".to_owned(),
                source_tag: None,
                satisfiable: false,
            },
        ];
        let stats = LhStatistics::from_module_and_constraints(&module, &constraints);

        assert_eq!(stats.refinements_total, 3);
        assert_eq!(stats.constraints_total, 2);
        assert_eq!(stats.constraints_satisfiable, 1);
    }

    #[test]
    fn test_lh_statistics_verification_rate() {
        let stats = LhStatistics {
            refinements_total: 10,
            refinements_verified: 8,
            ..Default::default()
        };
        assert!((stats.verification_rate() - 0.8).abs() < f64::EPSILON);
    }

    #[test]
    fn test_lh_statistics_verification_rate_empty() {
        let stats = LhStatistics::default();
        assert!((stats.verification_rate() - 1.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_lh_statistics_serde_round_trip() {
        let stats = LhStatistics {
            refinements_total: 5,
            refinements_verified: 3,
            constraints_total: 10,
            constraints_satisfiable: 8,
            imports_count: 2,
            solver_time_ms: 150,
        };
        let json = serde_json::to_string(&stats).expect("serialize");
        let restored: LhStatistics = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(restored, stats);
    }

    // -----------------------------------------------------------------------
    // parse_liquid_fixpoint tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_parse_liquid_fixpoint_single_constraint() {
        let text = r#"constraint:
  id 1
  env [x : {v:Int | v > 0}]
  lhs {v:Int | v > 0}
  rhs {v:Int | v >= 0}
  tag "Main.hs:10:5"
"#;
        let constraints = parse_liquid_fixpoint(text).expect("should parse");
        assert_eq!(constraints.len(), 1);
        assert_eq!(constraints[0].id, 1);
        assert_eq!(constraints[0].lhs, "{v:Int | v > 0}");
        assert_eq!(constraints[0].rhs, "{v:Int | v >= 0}");
        assert_eq!(constraints[0].source_tag.as_deref(), Some("Main.hs:10:5"));
        assert_eq!(constraints[0].environment.len(), 1);
        assert_eq!(constraints[0].environment[0].0, "x");
    }

    #[test]
    fn test_parse_liquid_fixpoint_multiple_constraints() {
        let text = r#"constraint:
  id 1
  lhs {v:Int | v > 0}
  rhs {v:Int | v >= 0}
constraint:
  id 2
  lhs {v:Bool | v}
  rhs {v:Bool | true}
"#;
        let constraints = parse_liquid_fixpoint(text).expect("should parse");
        assert_eq!(constraints.len(), 2);
        assert_eq!(constraints[0].id, 1);
        assert_eq!(constraints[1].id, 2);
    }

    #[test]
    fn test_parse_liquid_fixpoint_empty_errors() {
        let result = parse_liquid_fixpoint("");
        assert!(result.is_err());
    }

    #[test]
    fn test_parse_liquid_fixpoint_no_constraints_returns_empty() {
        let constraints = parse_liquid_fixpoint("-- just a comment\n").expect("should parse");
        assert!(constraints.is_empty());
    }

    #[test]
    fn test_parse_liquid_fixpoint_no_tag() {
        let text = "constraint:\n  id 5\n  lhs A\n  rhs B\n";
        let constraints = parse_liquid_fixpoint(text).expect("should parse");
        assert_eq!(constraints.len(), 1);
        assert!(constraints[0].source_tag.is_none());
    }

    #[test]
    fn test_parse_liquid_fixpoint_multiple_env_bindings() {
        let text = r#"constraint:
  id 10
  env [x : Int]
  env [y : Bool]
  lhs P
  rhs Q
"#;
        let constraints = parse_liquid_fixpoint(text).expect("should parse");
        assert_eq!(constraints[0].environment.len(), 2);
        assert_eq!(constraints[0].environment[0].0, "x");
        assert_eq!(constraints[0].environment[1].0, "y");
    }
}
