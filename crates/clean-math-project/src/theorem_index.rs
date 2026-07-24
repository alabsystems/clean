// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Shared model for precomputed math-project theorem indexes.

use std::fs;
use std::path::{Path, PathBuf};

use serde::{Deserialize, Serialize};
use serde_json::Value;

use crate::MathProjectError;

pub const MATH_THEOREM_INDEX_SCHEMA_VERSION: &str = "clean-math-theorem-index-v1";

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct MathTheoremIndexReport {
    pub schema_version: String,
    pub project: MathTheoremIndexProject,
    pub profile: String,
    #[serde(default)]
    pub files_scanned: usize,
    #[serde(default)]
    pub memory: MathTheoremMemory,
    #[serde(default)]
    pub candidates: Vec<ProjectTheoremCandidate>,
    #[serde(default)]
    pub factory_report: Value,
}

impl MathTheoremIndexReport {
    #[must_use]
    pub fn is_supported_schema(&self) -> bool {
        self.schema_version == MATH_THEOREM_INDEX_SCHEMA_VERSION
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct MathTheoremIndexProject {
    pub schema_version: String,
    pub project_path: String,
    pub project_root: String,
    pub name: String,
    pub domain_profile: String,
    pub owner: String,
    pub trust_policy: String,
    #[serde(default)]
    pub require_artifact_replay: bool,
    #[serde(default)]
    pub allow_synthetic_sorry: bool,
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct MathTheoremMemory {
    #[serde(default)]
    pub candidate_count: usize,
    #[serde(default)]
    pub local_count: usize,
    #[serde(default)]
    pub project_count: usize,
    #[serde(default)]
    pub domain_count: usize,
    #[serde(default)]
    pub imported_count: usize,
    #[serde(default)]
    pub artifact_derived_count: usize,
    #[serde(default)]
    pub trust_policy_conforming_count: usize,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ProjectTheoremCandidate {
    pub name: String,
    pub source_path: String,
    pub module: String,
    pub candidate_fingerprint: String,
    pub classification: CandidateClassification,
    pub domain_signals: CandidateDomainSignals,
    pub trust_decision: CandidateTrustDecision,
    #[serde(default)]
    pub memory: CandidateStructuredMemory,
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct CandidateStructuredMemory {
    #[serde(default)]
    pub normal_form_heads: Vec<String>,
    #[serde(default)]
    pub side_condition_kinds: Vec<String>,
    #[serde(default)]
    pub artifact_kinds: Vec<String>,
    #[serde(default)]
    pub direct_imports: Vec<String>,
    #[serde(default)]
    pub import_closure: Vec<String>,
    #[serde(default)]
    pub direct_only: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CandidateClassification {
    pub scope: String,
    #[serde(default)]
    pub local: bool,
    #[serde(default)]
    pub project: bool,
    #[serde(default)]
    pub domain: bool,
    #[serde(default)]
    pub imported: bool,
    #[serde(default)]
    pub artifact_derived: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CandidateDomainSignals {
    pub profile: String,
    #[serde(default)]
    pub module_match: bool,
    #[serde(default)]
    pub semantic_head_matches: Vec<String>,
    #[serde(default)]
    pub ranking_signal_matches: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CandidateTrustDecision {
    pub policy: String,
    pub conformance: String,
    pub kernel_proof_status: String,
    #[serde(default)]
    pub trust_debt: Vec<String>,
    #[serde(default)]
    pub promotion_allowed: bool,
    #[serde(default)]
    pub reasons: Vec<String>,
}

pub fn parse_theorem_index_json_str(
    text: &str,
) -> Result<MathTheoremIndexReport, serde_json::Error> {
    serde_json::from_str(text)
}

pub fn load_theorem_index(path: &Path) -> Result<MathTheoremIndexReport, MathProjectError> {
    let contents = fs::read_to_string(path).map_err(|source| MathProjectError::Io {
        path: PathBuf::from(path),
        source,
    })?;
    serde_json::from_str(&contents).map_err(|source| MathProjectError::Json {
        path: PathBuf::from(path),
        source,
    })
}
