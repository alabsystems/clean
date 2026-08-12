// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Mathverse Engine pipeline: orchestrates the full arXiv → clean formalization flow.
//!
//! Pipeline stages:
//!   1. **Ingest**: download arXiv source, extract LaTeX
//!   2. **Parse**: extract theorems, definitions, proofs, macros
//!   3. **Import**: produce Mathverse Library constants (axiomatized)
//!   4. **Formalize**: convert LaTeX → clean via LLM (definition-first)
//!   5. **Validate**: semantic alignment checks
//!   6. **Admit**: quarantine staging (candidate → audited → verified)
//!
//! This module defines the pipeline configuration and orchestration types.
//! The actual LLM calls are external (pluggable via trait).

use super::error_categories::{ErrorCategory, ErrorDistribution};
use super::formalize::AdmissionTier;
use super::importer::{ArxivImportConfig, ArxivImportResult, ArxivImporter};
use super::validation::{self, ValidationReport};
use serde::{Deserialize, Serialize};

// ════════════════════════════════════════════════════════════════════════════
// Pipeline Configuration
// ════════════════════════════════════════════════════════════════════════════

/// Configuration for the Mathverse Engine pipeline.
#[derive(Clone, Debug)]
pub struct PipelineConfig {
    /// Whether to run the formalization step (requires LLM).
    pub run_formalization: bool,
    /// Whether to run semantic validation (requires LLM for roundtrip).
    pub run_semantic_validation: bool,
    /// Maximum papers to process (0 = no limit).
    pub paper_limit: usize,
    /// Maximum retries per statement formalization.
    pub max_retries: u32,
    /// Import configuration.
    pub import_config: ArxivImportConfig,
    /// Minimum similarity score for roundtrip acceptance.
    pub roundtrip_threshold: f64,
}

impl Default for PipelineConfig {
    fn default() -> Self {
        Self {
            run_formalization: true,
            run_semantic_validation: false, // requires LLM, off by default
            paper_limit: 0,
            max_retries: 3,
            import_config: ArxivImportConfig::default(),
            roundtrip_threshold: 0.7,
        }
    }
}

// ════════════════════════════════════════════════════════════════════════════
// Pipeline Statistics
// ════════════════════════════════════════════════════════════════════════════

/// Aggregate statistics from a pipeline run.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct PipelineStats {
    /// Total papers processed.
    pub papers_processed: usize,
    /// Papers that failed to parse.
    pub papers_failed: usize,
    /// Total theorems extracted.
    pub theorems_extracted: usize,
    /// Total definitions extracted.
    pub definitions_extracted: usize,
    /// Total proofs found.
    pub proofs_found: usize,
    /// Custom environments discovered.
    pub custom_environments: usize,
    /// Statements sent to LLM for formalization.
    pub formalization_attempted: usize,
    /// Statements that received valid Lean code from LLM.
    pub formalization_generated: usize,
    /// Statements that passed structural validation.
    pub structural_pass: usize,
    /// Statements that passed semantic validation.
    pub semantic_pass: usize,
    /// Statements admitted at each tier.
    pub tier_counts: TierCounts,
}

/// Counts per admission tier.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct TierCounts {
    pub candidate: usize,
    pub type_checked: usize,
    pub audited_alignment: usize,
    pub kernel_proved: usize,
}

// ════════════════════════════════════════════════════════════════════════════
// Batch Processing
// ════════════════════════════════════════════════════════════════════════════

/// Result of processing a batch of papers.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct BatchResult {
    /// Aggregate statistics across all papers.
    pub stats: PipelineStats,
    /// Error distribution across all formalization failures.
    pub error_distribution: ErrorDistribution,
    /// Per-paper import results (paper_id -> import result summary).
    pub paper_summaries: Vec<PaperSummary>,
}

/// Summary of one paper's processing result.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct PaperSummary {
    pub paper_id: String,
    pub title: String,
    pub theorems: usize,
    pub definitions: usize,
    pub proofs: usize,
    pub custom_envs: usize,
    pub diagnostics: Vec<String>,
}

/// Process a batch of papers through the import-only pipeline.
///
/// Returns aggregate statistics and per-paper summaries. Reports progress
/// via the `on_progress` callback (paper index, total, paper_id).
#[must_use]
pub fn import_batch<F>(
    papers: &[(&str, &str)],
    config: &PipelineConfig,
    mut on_progress: F,
) -> BatchResult
where
    F: FnMut(usize, usize, &str),
{
    let mut batch = BatchResult::default();
    let limit = if config.paper_limit > 0 {
        config.paper_limit.min(papers.len())
    } else {
        papers.len()
    };

    for (i, (paper_id, latex)) in papers.iter().take(limit).enumerate() {
        on_progress(i, limit, paper_id);

        let (result, paper_stats) = import_paper(paper_id, latex, config);

        batch.paper_summaries.push(PaperSummary {
            paper_id: result.paper_id.clone(),
            title: result.title.clone(),
            theorems: result.theorem_count,
            definitions: result.definition_count,
            proofs: result.proofs_found,
            custom_envs: result.custom_environments,
            diagnostics: result.diagnostics.clone(),
        });

        // Accumulate stats
        batch.stats.papers_processed += paper_stats.papers_processed;
        batch.stats.theorems_extracted += paper_stats.theorems_extracted;
        batch.stats.definitions_extracted += paper_stats.definitions_extracted;
        batch.stats.proofs_found += paper_stats.proofs_found;
        batch.stats.custom_environments += paper_stats.custom_environments;

        if result.diagnostics.iter().any(|d| d.contains("failed")) {
            batch.stats.papers_failed += 1;
        }

        // Categorize any diagnostics as errors
        for diag in &result.diagnostics {
            let cat = ErrorCategory::classify(diag);
            batch.error_distribution.record(&cat);
        }
    }

    batch
}

impl PipelineStats {
    /// Formalization success rate (generated / attempted).
    #[must_use]
    pub fn formalization_rate(&self) -> f64 {
        if self.formalization_attempted == 0 {
            0.0
        } else {
            self.formalization_generated as f64 / self.formalization_attempted as f64
        }
    }

    /// Total statements extracted.
    #[must_use]
    pub fn total_extracted(&self) -> usize {
        self.theorems_extracted + self.definitions_extracted
    }

    /// Proof coverage rate.
    #[must_use]
    pub fn proof_coverage(&self) -> f64 {
        if self.theorems_extracted == 0 {
            0.0
        } else {
            self.proofs_found as f64 / self.theorems_extracted as f64
        }
    }

    /// Record a formalization attempt result.
    pub fn record_formalization(&mut self, tier: &AdmissionTier) {
        match tier {
            AdmissionTier::Candidate => self.tier_counts.candidate += 1,
            AdmissionTier::TypeChecked => self.tier_counts.type_checked += 1,
            AdmissionTier::AuditedAlignment => self.tier_counts.audited_alignment += 1,
            AdmissionTier::KernelProved => self.tier_counts.kernel_proved += 1,
        }
    }
}

// ════════════════════════════════════════════════════════════════════════════
// Pipeline Run (import-only, no LLM)
// ════════════════════════════════════════════════════════════════════════════

/// Run the import-only pipeline on a single paper's LaTeX source.
///
/// This performs stages 1-3 (parse + import) without formalization.
/// Returns the import result and extraction statistics.
#[must_use]
pub(crate) fn import_paper(
    paper_id: &str,
    latex: &str,
    config: &PipelineConfig,
) -> (ArxivImportResult, PipelineStats) {
    let importer = ArxivImporter::new(config.import_config.clone());
    let result = importer
        .import_latex(paper_id, latex)
        .unwrap_or_else(|e| ArxivImportResult {
            paper_id: paper_id.to_string(),
            title: String::new(),
            constants: Vec::new(),
            theorem_count: 0,
            definition_count: 0,
            proofs_found: 0,
            custom_environments: 0,
            diagnostics: vec![format!("import failed: {e}")],
        });

    let stats = PipelineStats {
        papers_processed: 1,
        theorems_extracted: result.theorem_count,
        definitions_extracted: result.definition_count,
        proofs_found: result.proofs_found,
        custom_environments: result.custom_environments,
        ..Default::default()
    };

    (result, stats)
}

/// Run structural validation on a Lean formalization.
///
/// This is the no-LLM validation that can be run locally.
#[must_use]
pub fn validate_formalization(
    lean_code: &str,
    original_latex: &str,
    kind: &str,
    type_checks: bool,
) -> ValidationReport {
    validation::validate(lean_code, original_latex, kind, type_checks, false)
}

// ════════════════════════════════════════════════════════════════════════════
// Tests
// ════════════════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;

    const SIMPLE_LATEX: &str = r#"
\documentclass{article}
\newtheorem{theorem}{Theorem}
\newtheorem{definition}{Definition}
\begin{document}
\title{Test Paper}
\begin{abstract}
This is a test.
\end{abstract}
\begin{definition}\label{def:foo}
Let $X$ be a set.
\end{definition}
\begin{theorem}\label{thm:bar}
$X$ has property P.
\end{theorem}
\begin{proof}
By definition of $X$.
\end{proof}
\end{document}
"#;

    #[test]
    fn test_import_paper() {
        let config = PipelineConfig::default();
        let (result, stats) = import_paper("test.0001", SIMPLE_LATEX, &config);

        assert_eq!(result.paper_id, "test.0001");
        assert_eq!(stats.theorems_extracted, 1);
        assert_eq!(stats.definitions_extracted, 1);
        assert_eq!(stats.proofs_found, 1);
        assert_eq!(stats.papers_processed, 1);
    }

    #[test]
    fn test_pipeline_stats_rates() {
        let mut stats = PipelineStats {
            theorems_extracted: 100,
            definitions_extracted: 50,
            proofs_found: 62,
            formalization_attempted: 150,
            formalization_generated: 90,
            ..Default::default()
        };

        assert_eq!(stats.total_extracted(), 150);
        assert!((stats.proof_coverage() - 0.62).abs() < 0.01);
        assert!((stats.formalization_rate() - 0.60).abs() < 0.01);

        stats.record_formalization(&AdmissionTier::TypeChecked);
        assert_eq!(stats.tier_counts.type_checked, 1);
    }

    #[test]
    fn test_validate_good_theorem() {
        let lean = "theorem foo (n : Nat) : n + 0 = n := Nat.add_zero n";
        let report = validate_formalization(lean, "For all n, n + 0 = n", "theorem", true);
        assert!(report.structural.unwrap().outcome.is_pass());
    }

    #[test]
    fn test_validate_sorry_theorem() {
        let lean = "theorem foo : True := by sorry";
        let report = validate_formalization(lean, "Truth", "theorem", true);
        // sorry should be flagged
        assert!(report.structural.unwrap().outcome.is_fail());
    }

    // ── Batch processing tests ──────────────────────────────────────────

    #[test]
    fn test_import_batch() {
        let papers = vec![("test.0001", SIMPLE_LATEX), ("test.0002", SIMPLE_LATEX)];
        let config = PipelineConfig::default();
        let mut progress_calls = 0usize;

        let batch = import_batch(&papers, &config, |_i, _total, _id| {
            progress_calls += 1;
        });

        assert_eq!(progress_calls, 2, "progress callback should fire per paper");
        assert_eq!(batch.stats.papers_processed, 2);
        assert_eq!(batch.stats.theorems_extracted, 2);
        assert_eq!(batch.stats.definitions_extracted, 2);
        assert_eq!(batch.paper_summaries.len(), 2);
        assert_eq!(batch.paper_summaries[0].paper_id, "test.0001");
        assert_eq!(batch.paper_summaries[1].paper_id, "test.0002");
    }

    #[test]
    fn test_import_batch_with_limit() {
        let papers = vec![
            ("test.0001", SIMPLE_LATEX),
            ("test.0002", SIMPLE_LATEX),
            ("test.0003", SIMPLE_LATEX),
        ];
        let config = PipelineConfig {
            paper_limit: 2,
            ..PipelineConfig::default()
        };

        let batch = import_batch(&papers, &config, |_, _, _| {});

        assert_eq!(
            batch.stats.papers_processed, 2,
            "should respect paper_limit"
        );
        assert_eq!(batch.paper_summaries.len(), 2);
    }
}
