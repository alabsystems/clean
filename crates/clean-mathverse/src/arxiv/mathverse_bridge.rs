// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Bridge between arXiv formalization results and Mathverse Library shards.
//!
//! Tracks formalization provenance. Source text and a claimed admission tier
//! are not typed shard declarations and cannot authorize a shard export.

use std::collections::HashMap;
use std::path::Path;

use serde::{Deserialize, Serialize};

use super::formalize::{AdmissionTier, FormalizationResult, PaperFormalization};
use crate::error::{MathverseError, MathverseResult};

// ════════════════════════════════════════════════════════════════════════════
// Export Statistics
// ════════════════════════════════════════════════════════════════════════════

/// Statistics from an mathverse shard export operation.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct ExportStats {
    /// Total formalizations considered.
    pub total_input: usize,
    /// Formalizations that met the minimum tier for export.
    pub eligible: usize,
    /// Formalizations successfully written to shard.
    pub exported: usize,
    /// Formalizations skipped (tier too low or missing Lean code).
    pub skipped: usize,
    /// Papers represented in the export.
    pub papers: usize,
}

// ════════════════════════════════════════════════════════════════════════════
// Provenance
// ════════════════════════════════════════════════════════════════════════════

/// Provenance record linking an mathverse constant back to its arXiv source.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ArxivProvenance {
    /// arXiv paper ID (e.g., "2603.28636").
    pub paper_id: String,
    /// Statement label in the paper (e.g., "Theorem 1.3").
    pub label: String,
    /// Original LaTeX statement.
    pub original_latex: String,
    /// Admission tier at export time.
    pub tier: AdmissionTier,
}

// ════════════════════════════════════════════════════════════════════════════
// Bridge
// ════════════════════════════════════════════════════════════════════════════

/// Connects formalized arXiv results to the Mathverse Library shard format.
pub struct ArxivMathverseBridge {
    /// arXiv paper ID -> list of constant indices in the shard.
    paper_index: HashMap<String, Vec<u32>>,
    /// constant index -> provenance record.
    provenance_map: HashMap<u32, ArxivProvenance>,
    /// Next constant index to assign.
    next_idx: u32,
}

impl ArxivMathverseBridge {
    /// Create a new empty bridge.
    #[must_use]
    pub fn new() -> Self {
        Self {
            paper_index: HashMap::new(),
            provenance_map: HashMap::new(),
            next_idx: 0,
        }
    }

    /// Reject source-only formalizations that lack typed shard declarations.
    ///
    /// A claimed admission tier does not supply an elaborated type or proof.
    /// Eligible nonempty source text returns an error without creating or
    /// modifying the destination. Empty or ineligible inputs return their
    /// no-output statistics.
    pub fn export_formalized(
        formalizations: &[PaperFormalization],
        _output_path: &Path,
    ) -> MathverseResult<ExportStats> {
        let mut stats = ExportStats::default();
        let mut papers_seen = std::collections::HashSet::new();
        for paper in formalizations {
            for result in paper.definitions.iter().chain(paper.theorems.iter()) {
                stats.total_input += 1;
                if claims_admitted_tier(result) {
                    stats.eligible += 1;
                    papers_seen.insert(&paper.paper_id);
                    if !result.best_lean.is_empty() {
                        return Err(MathverseError::ImportFailed {
                            system: "arXiv".to_string(),
                            reason: format!(
                                "formalization '{}' from '{}' contains source text; \
                                 elaborate it into typed declarations before shard export",
                                result.label, paper.paper_id
                            ),
                        });
                    }
                }
                stats.skipped += 1;
            }
        }
        stats.papers = papers_seen.len();
        Ok(stats)
    }

    /// Register a formalization result, tracking its provenance.
    pub fn register(&mut self, paper_id: &str, result: &FormalizationResult) -> u32 {
        let idx = self.next_idx;
        self.next_idx += 1;

        self.paper_index
            .entry(paper_id.to_string())
            .or_default()
            .push(idx);

        self.provenance_map.insert(
            idx,
            ArxivProvenance {
                paper_id: paper_id.to_string(),
                label: result.label.clone(),
                original_latex: result.original_latex.clone(),
                tier: result.tier.clone(),
            },
        );

        idx
    }

    /// Search for formalized constants from a specific paper.
    #[must_use]
    pub fn search_by_paper(&self, arxiv_id: &str) -> Vec<u32> {
        self.paper_index.get(arxiv_id).cloned().unwrap_or_default()
    }

    /// Get provenance for a constant index.
    #[must_use]
    pub fn provenance(&self, constant_idx: u32) -> Option<&ArxivProvenance> {
        self.provenance_map.get(&constant_idx)
    }

    /// Total number of registered constants.
    #[must_use]
    pub fn total_constants(&self) -> usize {
        self.provenance_map.len()
    }

    /// Number of distinct papers registered.
    #[must_use]
    pub fn total_papers(&self) -> usize {
        self.paper_index.len()
    }
}

impl Default for ArxivMathverseBridge {
    fn default() -> Self {
        Self::new()
    }
}

// ════════════════════════════════════════════════════════════════════════════
// Helpers
// ════════════════════════════════════════════════════════════════════════════

/// Whether the caller claims a tier considered for an export attempt.
fn claims_admitted_tier(result: &FormalizationResult) -> bool {
    matches!(
        result.tier,
        AdmissionTier::TypeChecked | AdmissionTier::AuditedAlignment | AdmissionTier::KernelProved
    )
}

// ════════════════════════════════════════════════════════════════════════════
// Tests
// ════════════════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;

    fn make_result(label: &str, tier: AdmissionTier, lean: &str) -> FormalizationResult {
        FormalizationResult {
            paper_id: "test.0001".to_string(),
            label: label.to_string(),
            kind: "theorem".to_string(),
            original_latex: "some latex".to_string(),
            proof_latex: String::new(),
            depends_on: vec![],
            attempts: vec![],
            best_lean: lean.to_string(),
            success: !lean.is_empty(),
            tier,
        }
    }

    fn make_paper(results: Vec<FormalizationResult>) -> PaperFormalization {
        let thm_formalized = results.iter().filter(|r| r.success).count();
        PaperFormalization {
            paper_id: "test.0001".to_string(),
            title: "Test Paper".to_string(),
            definitions: vec![],
            theorems: results,
            def_formalized: 0,
            def_total: 0,
            thm_formalized,
            thm_total: 0,
        }
    }

    fn assert_source_only_export_refused(tier: AdmissionTier, lean: &str) {
        let dir = tempfile::tempdir().expect("temporary output directory");
        let path = dir.path().join("source-only.mathverse");
        for existing in [false, true] {
            if existing {
                std::fs::write(&path, b"existing shard must remain unchanged")
                    .expect("write existing destination");
            }
            let paper = make_paper(vec![make_result("Claimed proof", tier.clone(), lean)]);
            let error = ArxivMathverseBridge::export_formalized(&[paper], &path)
                .expect_err("source text and a claimed tier do not establish a typed declaration");
            assert!(matches!(
                error,
                MathverseError::ImportFailed { system, reason }
                    if system == "arXiv" && reason.contains("typed declarations")
            ));
            if existing {
                assert_eq!(
                    std::fs::read(&path).expect("existing destination"),
                    b"existing shard must remain unchanged"
                );
            } else {
                assert!(!path.exists(), "refusal must not publish a shard");
            }
        }
    }

    #[test]
    fn source_only_claimed_kernel_proof_is_refused() {
        assert_source_only_export_refused(
            AdmissionTier::KernelProved,
            "theorem fabricated : False := by trivial",
        );
    }

    #[test]
    fn source_only_claimed_type_check_is_refused() {
        assert_source_only_export_refused(
            AdmissionTier::TypeChecked,
            "theorem fabricated : False := by trivial",
        );
    }

    #[test]
    fn source_only_claimed_alignment_is_refused() {
        assert_source_only_export_refused(
            AdmissionTier::AuditedAlignment,
            "theorem fabricated : False := by trivial",
        );
    }

    #[test]
    fn source_only_valid_text_still_requires_typed_declarations() {
        assert_source_only_export_refused(
            AdmissionTier::KernelProved,
            "theorem valid : True := True.intro",
        );
    }

    #[test]
    fn test_bridge_register_and_search() {
        let mut bridge = ArxivMathverseBridge::new();
        let r1 = make_result(
            "Theorem 1",
            AdmissionTier::TypeChecked,
            "theorem t1 : True := trivial",
        );
        let r2 = make_result("Theorem 2", AdmissionTier::Candidate, "");

        let idx1 = bridge.register("2603.00001", &r1);
        let idx2 = bridge.register("2603.00001", &r2);
        let idx3 = bridge.register("2603.00002", &r1);

        assert_eq!(bridge.search_by_paper("2603.00001"), vec![idx1, idx2]);
        assert_eq!(bridge.search_by_paper("2603.00002"), vec![idx3]);
        assert!(bridge.search_by_paper("nonexistent").is_empty());
    }

    #[test]
    fn test_bridge_provenance() {
        let mut bridge = ArxivMathverseBridge::new();
        let r = make_result(
            "Theorem 3",
            AdmissionTier::AuditedAlignment,
            "theorem t3 : True := trivial",
        );
        let idx = bridge.register("2603.12345", &r);

        let prov = bridge.provenance(idx).expect("should have provenance");
        assert_eq!(prov.paper_id, "2603.12345");
        assert_eq!(prov.label, "Theorem 3");
        assert_eq!(prov.tier, AdmissionTier::AuditedAlignment);

        assert!(bridge.provenance(999).is_none());
    }

    #[test]
    fn test_ineligible_and_empty_sources_write_nothing() {
        let r_good = make_result("Theorem 1", AdmissionTier::TypeChecked, "");
        let r_bad = make_result("Theorem 2", AdmissionTier::Candidate, "bad code");
        let paper = make_paper(vec![r_good, r_bad]);

        let dir = tempfile::tempdir().expect("temporary output directory");
        let shard_path = dir.path().join("arxiv_test.mathverse");

        let stats = ArxivMathverseBridge::export_formalized(&[paper], &shard_path)
            .expect("export should succeed");

        assert_eq!(stats.total_input, 2);
        assert_eq!(stats.eligible, 1);
        assert_eq!(stats.exported, 0);
        assert_eq!(stats.skipped, 2);
        assert_eq!(stats.papers, 1);

        assert!(!shard_path.exists(), "no typed declarations to export");
    }

    #[test]
    fn test_export_empty_formalizations() {
        let paper = make_paper(vec![]);
        let dir = tempfile::tempdir().expect("temporary output directory");
        let shard_path = dir.path().join("empty.mathverse");

        let stats = ArxivMathverseBridge::export_formalized(&[paper], &shard_path)
            .expect("export should succeed even with no data");

        assert_eq!(stats.exported, 0);
        // No shard should be written when nothing was exported
        assert!(!shard_path.exists());
    }

    #[test]
    fn test_claimed_admission_tiers() {
        let candidate = make_result("T", AdmissionTier::Candidate, "x");
        let tc = make_result("T", AdmissionTier::TypeChecked, "x");
        let aa = make_result("T", AdmissionTier::AuditedAlignment, "x");
        let kp = make_result("T", AdmissionTier::KernelProved, "x");

        assert!(!claims_admitted_tier(&candidate));
        assert!(claims_admitted_tier(&tc));
        assert!(claims_admitted_tier(&aa));
        assert!(claims_admitted_tier(&kp));
    }
}
