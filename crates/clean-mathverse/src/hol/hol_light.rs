// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! HOL Light specific importer configuration.
//!
//! HOL Light exports its proofs via the OpenTheory article (`.art`) format.
//! This module provides a `HolLightImporter` that wraps the generic
//! [`OtMathverseBridge`] with HOL Light-specific namespace, axiom profile, and
//! bulk directory import.

use std::path::Path;

use clean_kernel::Name as LeanName;

use crate::types::{AxiomProfile, SourceSystem, TrustLevel};

use super::error::{HolError, HolResult};
use super::opentheory_bridge::{
    ImportStatistics, ImportedConstantKind, MathverseImportedConstant, OtMathverseBridge,
};

/// Default namespace for HOL Light imports in the Mathverse library.
const HOL_LIGHT_NAMESPACE: &str = "HolLight.Imported";

/// HOL Light importer configuration.
///
/// Wraps the OpenTheory bridge with HOL Light-specific defaults:
/// - Namespace: `HolLight.Imported`
/// - Source system: `SourceSystem::HolLight`
/// - Axiom profile: `CLASSICAL | EXTENSIONALITY | HOL_EMBEDDING`
pub struct HolLightImporter {
    namespace: LeanName,
}

impl Default for HolLightImporter {
    fn default() -> Self {
        Self {
            namespace: LeanName::from_string(HOL_LIGHT_NAMESPACE),
        }
    }
}

impl HolLightImporter {
    /// Create a new HOL Light importer with a custom namespace.
    #[must_use]
    pub(crate) fn with_namespace(namespace: &str) -> Self {
        Self {
            namespace: LeanName::from_string(namespace),
        }
    }

    /// Import a single `.art` file.
    pub fn import_file(
        &self,
        path: &Path,
    ) -> HolResult<(Vec<MathverseImportedConstant>, ImportStatistics)> {
        let bridge = self.make_bridge(Some(path));
        bridge.import_file(path)
    }

    /// Import an OpenTheory article from raw text.
    pub(crate) fn import_text(
        &self,
        input: &str,
    ) -> HolResult<(Vec<MathverseImportedConstant>, ImportStatistics)> {
        let bridge = self.make_bridge(None);
        bridge.import_article_text(input)
    }

    /// Bulk-import all `.art` files from a directory.
    ///
    /// Returns the combined list of imported constants and aggregate statistics.
    /// Files that fail to parse or import are collected as errors but do not
    /// stop the overall import.
    pub fn import_directory(
        &self,
        dir: &Path,
    ) -> HolResult<(
        Vec<MathverseImportedConstant>,
        ImportStatistics,
        Vec<HolError>,
    )> {
        let art_files = collect_art_files(dir)?;
        if art_files.is_empty() {
            return Err(HolError::NoArticlesFound {
                path: dir.display().to_string(),
            });
        }

        let mut all_constants = Vec::new();
        let mut aggregate_stats = ImportStatistics::default();
        let mut errors = Vec::new();

        for file_path in &art_files {
            match self.import_file(file_path) {
                Ok((constants, stats)) => {
                    all_constants.extend(constants);
                    aggregate_stats.support_count += stats.support_count;
                    aggregate_stats.assumption_count += stats.assumption_count;
                    aggregate_stats.theorem_count += stats.theorem_count;
                }
                Err(e) => {
                    errors.push(e);
                }
            }
        }

        Ok((all_constants, aggregate_stats, errors))
    }

    /// Import a collection of OpenTheory article texts as a named theory.
    ///
    /// Processes each article through the OpenTheory bridge and collects
    /// all results into a `HolLightTheory`. Articles that fail to parse
    /// are counted as failures in the statistics but do not abort the import.
    pub(crate) fn import_theory(
        &self,
        theory_name: &str,
        articles: &[&str],
    ) -> HolResult<HolLightTheory> {
        let bridge = self.make_bridge(None);

        let mut axioms = Vec::new();
        let mut definitions = Vec::new();
        let mut theorems = Vec::new();
        let mut stats = HolLightStatistics {
            total_articles: articles.len(),
            imported_constants: 0,
            failed_articles: 0,
            theorem_count: 0,
            axiom_count: 0,
            definition_count: 0,
        };

        for article_text in articles {
            match bridge.import_article_text(article_text) {
                Ok((constants, _import_stats)) => {
                    for constant in constants {
                        stats.imported_constants += 1;
                        match constant.kind {
                            ImportedConstantKind::Assumption => {
                                stats.axiom_count += 1;
                                axioms.push(constant);
                            }
                            ImportedConstantKind::Support => {
                                stats.definition_count += 1;
                                definitions.push(constant);
                            }
                            ImportedConstantKind::Theorem => {
                                stats.theorem_count += 1;
                                theorems.push(constant);
                            }
                        }
                    }
                }
                Err(_) => {
                    stats.failed_articles += 1;
                }
            }
        }

        Ok(HolLightTheory {
            theory_name: theory_name.to_owned(),
            axioms,
            definitions,
            theorems,
            statistics: stats,
        })
    }

    /// Build an `OtMathverseBridge` configured for HOL Light.
    fn make_bridge(&self, source_path: Option<&Path>) -> OtMathverseBridge {
        let bridge = OtMathverseBridge::new(self.namespace.clone(), SourceSystem::HolLight);
        match source_path {
            Some(path) => bridge.with_source_file(&path.display().to_string()),
            None => bridge,
        }
    }
}

/// A complete HOL Light theory, aggregated from one or more OpenTheory articles.
///
/// Groups imported constants into axioms (assumptions), definitions (support
/// declarations), and proved theorems for structured access.
#[derive(Clone, Debug)]
pub(crate) struct HolLightTheory {
    /// Name of this theory (e.g., `"bool"`, `"arith"`, `"topology"`).
    pub(crate) theory_name: String,
    /// Assumptions (unproved axioms) imported from the articles.
    pub(crate) axioms: Vec<MathverseImportedConstant>,
    /// Support declarations (type operators, constants) from the articles.
    pub(crate) definitions: Vec<MathverseImportedConstant>,
    /// Proved theorems exported via `thm` in the articles.
    pub(crate) theorems: Vec<MathverseImportedConstant>,
    /// Aggregate statistics for this theory import.
    pub(crate) statistics: HolLightStatistics,
}

impl HolLightTheory {
    /// Total number of constants across all categories.
    #[must_use]
    pub(crate) fn total_constants(&self) -> usize {
        self.axioms.len() + self.definitions.len() + self.theorems.len()
    }

    /// The combined axiom profile for all constants in the theory.
    ///
    /// Returns the union of all individual axiom profiles.
    #[must_use]
    pub(crate) fn combined_axiom_profile(&self) -> AxiomProfile {
        let all_constants = self
            .axioms
            .iter()
            .chain(self.definitions.iter())
            .chain(self.theorems.iter());

        let mut combined = AxiomProfile::NONE;
        for c in all_constants {
            combined |= c.axiom_profile;
        }
        combined
    }

    /// The minimum trust level across all constants in the theory.
    ///
    /// Returns `None` if the theory has no constants.
    #[must_use]
    pub(crate) fn min_trust_level(&self) -> Option<TrustLevel> {
        let all_constants = self
            .axioms
            .iter()
            .chain(self.definitions.iter())
            .chain(self.theorems.iter());

        all_constants.map(|c| c.trust_level).min()
    }

    /// Names of all theorems in the theory.
    #[must_use]
    pub(crate) fn theorem_names(&self) -> Vec<String> {
        self.theorems.iter().map(|t| t.name.to_string()).collect()
    }

    /// Names of all axioms in the theory.
    #[must_use]
    pub(crate) fn axiom_names(&self) -> Vec<String> {
        self.axioms.iter().map(|a| a.name.to_string()).collect()
    }
}

/// Statistics for a HOL Light theory import.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct HolLightStatistics {
    /// Total number of article texts provided for import.
    pub(crate) total_articles: usize,
    /// Total number of constants successfully imported.
    pub(crate) imported_constants: usize,
    /// Number of articles that failed to parse or import.
    pub(crate) failed_articles: usize,
    /// Number of proved theorems imported.
    pub(crate) theorem_count: usize,
    /// Number of assumptions (axioms) imported.
    pub(crate) axiom_count: usize,
    /// Number of support declarations (definitions) imported.
    pub(crate) definition_count: usize,
}

impl HolLightStatistics {
    /// Success rate as a fraction in [0.0, 1.0].
    ///
    /// Returns 1.0 if no articles were provided.
    #[must_use]
    pub(crate) fn success_rate(&self) -> f64 {
        if self.total_articles == 0 {
            return 1.0;
        }
        let successful = self.total_articles - self.failed_articles;
        successful as f64 / self.total_articles as f64
    }
}

/// HOL Light primitive inference rules.
///
/// These correspond to the 10 primitive inference rules of HOL Light's
/// kernel. Every HOL Light theorem is ultimately built from these rules.
/// See: Harrison, "HOL Light: An Overview", TPHOLs 2009.
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub(crate) enum HolLightProofStep {
    /// `REFL t`: Produces `|- t = t`.
    Refl {
        /// String representation of the term.
        term: String,
    },
    /// `TRANS (|- s = t) (|- t = u)`: Produces `|- s = u`.
    Trans {
        /// Index of the left premise in the proof tree.
        left: usize,
        /// Index of the right premise in the proof tree.
        right: usize,
    },
    /// `MK_COMB (|- f = g) (|- x = y)`: Produces `|- f x = g y`.
    MkComb {
        /// Index of the function equality premise.
        func: usize,
        /// Index of the argument equality premise.
        arg: usize,
    },
    /// `ABS v (|- s = t)`: Produces `|- (\v. s) = (\v. t)`.
    Abs {
        /// Variable being abstracted.
        var: String,
        /// Index of the body equality premise.
        body: usize,
    },
    /// `BETA (\v. t) v`: Produces `|- (\v. t) v = t`.
    Beta {
        /// String representation of the lambda term.
        lambda_term: String,
    },
    /// `ASSUME p`: Produces `{p} |- p`.
    Assume {
        /// The proposition being assumed.
        prop: String,
    },
    /// `EQ_MP (|- p <=> q) (|- p)`: Produces `|- q`.
    EqMp {
        /// Index of the equivalence premise.
        equiv: usize,
        /// Index of the proof of the left side.
        proof: usize,
    },
    /// `DEDUCT_ANTISYM_RULE (A |- p) (B |- q)`: Produces `(A - {q}) u (B - {p}) |- p <=> q`.
    Deduct {
        /// Index of the first premise.
        left: usize,
        /// Index of the second premise.
        right: usize,
    },
    /// `INST [(t1, v1); ...] (A |- p)`: Term instantiation.
    Inst {
        /// Index of the premise theorem.
        theorem: usize,
        /// Substitution pairs: (replacement_term, variable).
        substitutions: Vec<(String, String)>,
    },
    /// `INST_TYPE [(ty1, tv1); ...] (A |- p)`: Type instantiation.
    InstType {
        /// Index of the premise theorem.
        theorem: usize,
        /// Type substitution pairs: (replacement_type, type_variable).
        type_substitutions: Vec<(String, String)>,
    },
}

impl HolLightProofStep {
    /// Human-readable name of this proof rule.
    #[must_use]
    pub(crate) fn rule_name(&self) -> &'static str {
        match self {
            Self::Refl { .. } => "REFL",
            Self::Trans { .. } => "TRANS",
            Self::MkComb { .. } => "MK_COMB",
            Self::Abs { .. } => "ABS",
            Self::Beta { .. } => "BETA",
            Self::Assume { .. } => "ASSUME",
            Self::EqMp { .. } => "EQ_MP",
            Self::Deduct { .. } => "DEDUCT_ANTISYM_RULE",
            Self::Inst { .. } => "INST",
            Self::InstType { .. } => "INST_TYPE",
        }
    }

    /// Whether this step is a leaf (has no premise references).
    #[must_use]
    pub(crate) fn is_leaf(&self) -> bool {
        matches!(
            self,
            Self::Refl { .. } | Self::Beta { .. } | Self::Assume { .. }
        )
    }

    /// Collect the indices of all premises referenced by this step.
    #[must_use]
    pub(crate) fn premise_indices(&self) -> Vec<usize> {
        match self {
            Self::Refl { .. } | Self::Beta { .. } | Self::Assume { .. } => Vec::new(),
            Self::Trans { left, right }
            | Self::MkComb {
                func: left,
                arg: right,
            }
            | Self::Deduct { left, right }
            | Self::EqMp {
                equiv: left,
                proof: right,
            } => vec![*left, *right],
            Self::Abs { body, .. } => vec![*body],
            Self::Inst { theorem, .. } | Self::InstType { theorem, .. } => vec![*theorem],
        }
    }
}

/// A proof tree reconstructed from HOL Light's proof export log.
///
/// Each node in the tree corresponds to a primitive inference step.
/// Steps reference earlier steps by index (DAG structure, since
/// intermediate results may be shared).
#[derive(Clone, Debug)]
pub(crate) struct HolLightProofTree {
    /// The sequence of proof steps, in order of construction.
    /// Later steps may reference earlier ones by index.
    pub(crate) steps: Vec<HolLightProofStep>,
    /// The conclusion of the proof (index of the final step).
    pub(crate) conclusion: Option<usize>,
    /// Name of the theorem being proved, if known.
    pub(crate) theorem_name: Option<String>,
}

impl HolLightProofTree {
    /// Create an empty proof tree.
    #[must_use]
    pub(crate) fn new() -> Self {
        Self {
            steps: Vec::new(),
            conclusion: None,
            theorem_name: None,
        }
    }

    /// Create a proof tree with a given theorem name.
    #[must_use]
    pub(crate) fn with_name(name: &str) -> Self {
        Self {
            steps: Vec::new(),
            conclusion: None,
            theorem_name: Some(name.to_owned()),
        }
    }

    /// Add a proof step and return its index.
    pub(crate) fn add_step(&mut self, step: HolLightProofStep) -> usize {
        let idx = self.steps.len();
        self.steps.push(step);
        idx
    }

    /// Set the conclusion index.
    pub(crate) fn set_conclusion(&mut self, idx: usize) {
        self.conclusion = Some(idx);
    }

    /// Number of steps in the proof tree.
    #[must_use]
    pub(crate) fn step_count(&self) -> usize {
        self.steps.len()
    }

    /// Whether the proof tree is empty.
    #[must_use]
    pub(crate) fn is_empty(&self) -> bool {
        self.steps.is_empty()
    }

    /// Count the number of leaf steps (steps with no premises).
    #[must_use]
    pub(crate) fn leaf_count(&self) -> usize {
        self.steps.iter().filter(|s| s.is_leaf()).count()
    }

    /// Count occurrences of each proof rule in the tree.
    #[must_use]
    pub(crate) fn rule_histogram(&self) -> std::collections::HashMap<&'static str, usize> {
        let mut counts = std::collections::HashMap::new();
        for step in &self.steps {
            *counts.entry(step.rule_name()).or_insert(0) += 1;
        }
        counts
    }

    /// Get the step at a given index.
    #[must_use]
    pub(crate) fn get_step(&self, idx: usize) -> Option<&HolLightProofStep> {
        self.steps.get(idx)
    }

    /// Validate that all premise references point to valid earlier steps.
    #[must_use]
    pub(crate) fn is_valid(&self) -> bool {
        for (idx, step) in self.steps.iter().enumerate() {
            for premise in step.premise_indices() {
                if premise >= idx {
                    return false; // Forward reference.
                }
            }
        }
        if let Some(conclusion) = self.conclusion {
            if conclusion >= self.steps.len() {
                return false;
            }
        }
        true
    }

    /// Compute the depth of the proof tree (longest path from a leaf to conclusion).
    #[must_use]
    pub(crate) fn depth(&self) -> usize {
        if self.steps.is_empty() {
            return 0;
        }
        let mut depths = vec![0usize; self.steps.len()];
        for (idx, step) in self.steps.iter().enumerate() {
            let max_premise_depth = step
                .premise_indices()
                .iter()
                .filter_map(|&p| depths.get(p))
                .max()
                .copied()
                .unwrap_or(0);
            depths[idx] = max_premise_depth + 1;
        }
        depths.into_iter().max().unwrap_or(0)
    }
}

/// Tracks which axioms each theorem depends on in a HOL Light proof.
///
/// Axiom tracking is essential for determining the trust level of
/// imported theorems. A theorem that depends only on the standard
/// HOL Light axioms (infinity, eta, choice) gets a higher trust
/// level than one depending on user-defined axioms.
#[derive(Clone, Debug)]
pub(crate) struct HolLightAxiomTracker {
    /// Map from theorem name to the set of axiom names it depends on.
    dependencies: std::collections::HashMap<String, Vec<String>>,
}

impl HolLightAxiomTracker {
    /// Create an empty tracker.
    #[must_use]
    pub(crate) fn new() -> Self {
        Self {
            dependencies: std::collections::HashMap::new(),
        }
    }

    /// Record that `theorem_name` depends on `axiom_name`.
    pub(crate) fn add_dependency(&mut self, theorem_name: &str, axiom_name: &str) {
        self.dependencies
            .entry(theorem_name.to_owned())
            .or_default()
            .push(axiom_name.to_owned());
    }

    /// Record that `theorem_name` depends on all axioms listed.
    pub(crate) fn add_dependencies(&mut self, theorem_name: &str, axiom_names: &[&str]) {
        let entry = self
            .dependencies
            .entry(theorem_name.to_owned())
            .or_default();
        for name in axiom_names {
            entry.push((*name).to_owned());
        }
    }

    /// Get the axiom dependencies for a given theorem.
    #[must_use]
    pub(crate) fn get_dependencies(&self, theorem_name: &str) -> Vec<&str> {
        self.dependencies
            .get(theorem_name)
            .map(|deps| deps.iter().map(|s| s.as_str()).collect())
            .unwrap_or_default()
    }

    /// Whether a theorem has any recorded axiom dependencies.
    #[must_use]
    pub(crate) fn has_dependencies(&self, theorem_name: &str) -> bool {
        self.dependencies
            .get(theorem_name)
            .map(|deps| !deps.is_empty())
            .unwrap_or(false)
    }

    /// Number of tracked theorems.
    #[must_use]
    pub(crate) fn theorem_count(&self) -> usize {
        self.dependencies.len()
    }

    /// All tracked theorem names, sorted.
    #[must_use]
    pub(crate) fn theorem_names(&self) -> Vec<&str> {
        let mut names: Vec<&str> = self.dependencies.keys().map(|s| s.as_str()).collect();
        names.sort();
        names
    }

    /// Whether a theorem depends only on the three standard HOL Light axioms:
    /// `INFINITY_AX`, `ETA_AX`, `SELECT_AX` (axiom of choice).
    #[must_use]
    pub(crate) fn uses_only_standard_axioms(&self, theorem_name: &str) -> bool {
        const STANDARD_AXIOMS: &[&str] = &["INFINITY_AX", "ETA_AX", "SELECT_AX"];
        let deps = self.get_dependencies(theorem_name);
        if deps.is_empty() {
            return true; // No axiom dependencies at all.
        }
        deps.iter().all(|d| STANDARD_AXIOMS.contains(d))
    }

    /// Count theorems that use only standard axioms.
    #[must_use]
    pub(crate) fn standard_axiom_count(&self) -> usize {
        self.dependencies
            .keys()
            .filter(|name| self.uses_only_standard_axioms(name))
            .count()
    }

    /// Count theorems that use non-standard (user-defined) axioms.
    #[must_use]
    pub(crate) fn nonstandard_axiom_count(&self) -> usize {
        self.theorem_count() - self.standard_axiom_count()
    }
}

/// Parse a HOL Light proof log line into a proof step.
///
/// HOL Light proof logs use a simple text format where each line describes
/// one inference step:
/// - `REFL <term>`
/// - `TRANS <left_idx> <right_idx>`
/// - `MK_COMB <func_idx> <arg_idx>`
/// - `ABS <var> <body_idx>`
/// - `BETA <lambda_term>`
/// - `ASSUME <prop>`
/// - `EQ_MP <equiv_idx> <proof_idx>`
/// - `DEDUCT <left_idx> <right_idx>`
/// - `INST <theorem_idx> <subst_pairs>`
/// - `INST_TYPE <theorem_idx> <type_subst_pairs>`
///
/// Returns `None` if the line cannot be parsed.
#[must_use]
pub(crate) fn parse_proof_log_line(line: &str) -> Option<HolLightProofStep> {
    let trimmed = line.trim();
    if trimmed.is_empty() {
        return None;
    }

    let parts: Vec<&str> = trimmed.splitn(2, ' ').collect();
    if parts.is_empty() {
        return None;
    }

    let rule = parts[0];
    let args = if parts.len() > 1 { parts[1] } else { "" };

    match rule {
        "REFL" => Some(HolLightProofStep::Refl {
            term: args.to_owned(),
        }),
        "TRANS" => {
            let indices: Vec<&str> = args.split_whitespace().collect();
            if indices.len() >= 2 {
                let left = indices[0].parse().ok()?;
                let right = indices[1].parse().ok()?;
                Some(HolLightProofStep::Trans { left, right })
            } else {
                None
            }
        }
        "MK_COMB" => {
            let indices: Vec<&str> = args.split_whitespace().collect();
            if indices.len() >= 2 {
                let func = indices[0].parse().ok()?;
                let arg = indices[1].parse().ok()?;
                Some(HolLightProofStep::MkComb { func, arg })
            } else {
                None
            }
        }
        "ABS" => {
            let parts: Vec<&str> = args.splitn(2, ' ').collect();
            if parts.len() >= 2 {
                let var = parts[0].to_owned();
                let body = parts[1].parse().ok()?;
                Some(HolLightProofStep::Abs { var, body })
            } else {
                None
            }
        }
        "BETA" => Some(HolLightProofStep::Beta {
            lambda_term: args.to_owned(),
        }),
        "ASSUME" => Some(HolLightProofStep::Assume {
            prop: args.to_owned(),
        }),
        "EQ_MP" => {
            let indices: Vec<&str> = args.split_whitespace().collect();
            if indices.len() >= 2 {
                let equiv = indices[0].parse().ok()?;
                let proof = indices[1].parse().ok()?;
                Some(HolLightProofStep::EqMp { equiv, proof })
            } else {
                None
            }
        }
        "DEDUCT" => {
            let indices: Vec<&str> = args.split_whitespace().collect();
            if indices.len() >= 2 {
                let left = indices[0].parse().ok()?;
                let right = indices[1].parse().ok()?;
                Some(HolLightProofStep::Deduct { left, right })
            } else {
                None
            }
        }
        "INST" => {
            // Format: INST <theorem_idx> [<repl1>/<var1>, ...]
            let parts: Vec<&str> = args.splitn(2, ' ').collect();
            if parts.is_empty() {
                return None;
            }
            let theorem = parts[0].parse().ok()?;
            let substitutions = if parts.len() > 1 {
                parse_substitution_pairs(parts[1])
            } else {
                Vec::new()
            };
            Some(HolLightProofStep::Inst {
                theorem,
                substitutions,
            })
        }
        "INST_TYPE" => {
            let parts: Vec<&str> = args.splitn(2, ' ').collect();
            if parts.is_empty() {
                return None;
            }
            let theorem = parts[0].parse().ok()?;
            let type_substitutions = if parts.len() > 1 {
                parse_substitution_pairs(parts[1])
            } else {
                Vec::new()
            };
            Some(HolLightProofStep::InstType {
                theorem,
                type_substitutions,
            })
        }
        _ => None,
    }
}

/// Parse a full proof log (one step per line) into a `HolLightProofTree`.
///
/// Empty lines and unparseable lines are skipped. The last successfully
/// parsed step becomes the conclusion.
#[must_use]
pub(crate) fn parse_proof_log(text: &str) -> HolLightProofTree {
    let mut tree = HolLightProofTree::new();

    for line in text.lines() {
        if let Some(step) = parse_proof_log_line(line) {
            let idx = tree.add_step(step);
            tree.set_conclusion(idx);
        }
    }

    tree
}

/// Parse substitution pairs from a string like "t1/v1,t2/v2".
fn parse_substitution_pairs(s: &str) -> Vec<(String, String)> {
    s.split(',')
        .filter_map(|pair| {
            let parts: Vec<&str> = pair.splitn(2, '/').collect();
            if parts.len() == 2 {
                Some((parts[0].trim().to_owned(), parts[1].trim().to_owned()))
            } else {
                None
            }
        })
        .collect()
}

/// Collect all `.art` files in a directory (non-recursive).
fn collect_art_files(dir: &Path) -> HolResult<Vec<std::path::PathBuf>> {
    let mut files = Vec::new();
    for entry in std::fs::read_dir(dir)? {
        let entry = entry?;
        let path = entry.path();
        if path.extension().and_then(|e| e.to_str()) == Some("art") && path.is_file() {
            files.push(path);
        }
    }
    files.sort();
    Ok(files)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hol::opentheory_bridge::HOL_BASE_PROFILE;

    /// Minimal refl article (x = x) for testing.
    const TEST_REFL: &str = r#"
6
version
"x"
"A"
varType
3
def
var
1
def
varTerm
2
def
refl
4
def
"bool"
typeOp
nil
opType
5
def
"->"
typeOp
3
ref
5
ref
nil
cons
cons
opType
6
def
"->"
typeOp
3
ref
6
ref
nil
cons
cons
opType
7
def
"="
const
7
ref
constTerm
2
ref
appTerm
2
ref
appTerm
8
def
4
ref
nil
8
ref
thm
"#;

    #[test]
    fn test_default_namespace() {
        let importer = HolLightImporter::default();
        assert_eq!(
            importer.namespace,
            LeanName::from_string(HOL_LIGHT_NAMESPACE)
        );
    }

    #[test]
    fn test_custom_namespace() {
        let importer = HolLightImporter::with_namespace("Custom.HolLight");
        assert_eq!(importer.namespace, LeanName::from_string("Custom.HolLight"));
    }

    #[test]
    fn test_import_theory_single_article() {
        let importer = HolLightImporter::default();
        let theory = importer
            .import_theory("refl_theory", &[TEST_REFL])
            .expect("theory import should succeed");

        assert_eq!(theory.theory_name, "refl_theory");
        assert_eq!(theory.statistics.total_articles, 1);
        assert_eq!(theory.statistics.failed_articles, 0);
        assert!(theory.statistics.imported_constants > 0);
        assert_eq!(theory.statistics.theorem_count, theory.theorems.len());
    }

    #[test]
    fn test_import_theory_multiple_articles() {
        let importer = HolLightImporter::default();
        let theory = importer
            .import_theory("multi", &[TEST_REFL, TEST_REFL])
            .expect("theory import should succeed");

        assert_eq!(theory.statistics.total_articles, 2);
        assert_eq!(theory.statistics.failed_articles, 0);
        assert_eq!(theory.statistics.theorem_count, 2);
    }

    #[test]
    fn test_import_theory_with_bad_article() {
        let importer = HolLightImporter::default();
        let theory = importer
            .import_theory("mixed", &[TEST_REFL, "garbage\n"])
            .expect("theory import should succeed despite bad article");

        assert_eq!(theory.statistics.total_articles, 2);
        assert_eq!(theory.statistics.failed_articles, 1);
        assert_eq!(theory.statistics.theorem_count, 1);
    }

    #[test]
    fn test_import_theory_empty_articles() {
        let importer = HolLightImporter::default();
        let theory = importer
            .import_theory("empty", &[])
            .expect("empty theory import should succeed");

        assert_eq!(theory.statistics.total_articles, 0);
        assert_eq!(theory.total_constants(), 0);
    }

    #[test]
    fn test_theory_total_constants() {
        let importer = HolLightImporter::default();
        let theory = importer
            .import_theory("count", &[TEST_REFL])
            .expect("theory import should succeed");

        let expected = theory.axioms.len() + theory.definitions.len() + theory.theorems.len();
        assert_eq!(theory.total_constants(), expected);
    }

    #[test]
    fn test_theory_combined_axiom_profile() {
        let importer = HolLightImporter::default();
        let theory = importer
            .import_theory("profile", &[TEST_REFL])
            .expect("theory import should succeed");

        let profile = theory.combined_axiom_profile();
        assert!(profile.contains(AxiomProfile::CLASSICAL));
        assert!(profile.contains(AxiomProfile::EXTENSIONALITY));
        assert!(profile.contains(AxiomProfile::HOL_EMBEDDING));
    }

    #[test]
    fn test_theory_min_trust_level() {
        let importer = HolLightImporter::default();
        let theory = importer
            .import_theory("trust", &[TEST_REFL])
            .expect("theory import should succeed");

        let min_trust = theory.min_trust_level();
        assert!(min_trust.is_some());
    }

    #[test]
    fn test_theory_min_trust_level_empty() {
        let importer = HolLightImporter::default();
        let theory = importer
            .import_theory("empty_trust", &[])
            .expect("empty theory import should succeed");

        assert!(theory.min_trust_level().is_none());
    }

    #[test]
    fn test_theory_theorem_names() {
        let importer = HolLightImporter::default();
        let theory = importer
            .import_theory("names", &[TEST_REFL])
            .expect("theory import should succeed");

        let names = theory.theorem_names();
        assert_eq!(names.len(), theory.theorems.len());
        for name in &names {
            assert!(!name.is_empty());
        }
    }

    #[test]
    fn test_statistics_success_rate_all_good() {
        let stats = HolLightStatistics {
            total_articles: 5,
            imported_constants: 10,
            failed_articles: 0,
            theorem_count: 5,
            axiom_count: 2,
            definition_count: 3,
        };
        assert!((stats.success_rate() - 1.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_statistics_success_rate_with_failures() {
        let stats = HolLightStatistics {
            total_articles: 4,
            imported_constants: 5,
            failed_articles: 1,
            theorem_count: 3,
            axiom_count: 1,
            definition_count: 1,
        };
        assert!((stats.success_rate() - 0.75).abs() < f64::EPSILON);
    }

    #[test]
    fn test_statistics_success_rate_empty() {
        let stats = HolLightStatistics::default();
        assert!((stats.success_rate() - 1.0).abs() < f64::EPSILON);
    }
}
