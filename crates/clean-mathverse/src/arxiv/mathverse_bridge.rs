// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Bridge between arXiv formalization results and Mathverse Library shards.
//!
//! Converts successfully type-checked formalizations into `.mathverse` shard
//! entries with full provenance, axiom profile, and trust metadata.

use std::collections::HashMap;
use std::path::Path;

use serde::{Deserialize, Serialize};

use super::formalize::{AdmissionTier, FormalizationResult, PaperFormalization};
use crate::error::{MathverseError, MathverseResult};
use crate::shard::ShardWriter;
use crate::types::{
    AxiomProfile, ContentDomain, ImportConfidence, MathverseConstantHeader, SourceSystem, NO_VALUE,
};

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

    /// Convert successfully type-checked formalizations to an mathverse shard file.
    ///
    /// Only formalizations at `TypeChecked` tier or above are exported.
    /// The shard is written to `output_path`.
    pub fn export_formalized(
        formalizations: &[PaperFormalization],
        output_path: &Path,
    ) -> MathverseResult<ExportStats> {
        let mut writer = ShardWriter::new();
        let mut stats = ExportStats::default();
        let mut papers_seen = std::collections::HashSet::new();

        for paper in formalizations {
            let eligible_results: Vec<&FormalizationResult> = paper
                .definitions
                .iter()
                .chain(paper.theorems.iter())
                .filter(|r| is_exportable(r))
                .collect();

            stats.total_input += paper.definitions.len() + paper.theorems.len();

            if eligible_results.is_empty() {
                continue;
            }

            papers_seen.insert(&paper.paper_id);

            for result in eligible_results {
                stats.eligible += 1;

                if result.best_lean.is_empty() {
                    stats.skipped += 1;
                    continue;
                }

                let name = format!(
                    "Arxiv.{}.{}",
                    sanitize_paper_id(&paper.paper_id),
                    sanitize_label(&result.label),
                );
                let name_idx = writer.add_string(&name);

                // Store the Lean code as a string (no expression arena encoding
                // for NL-imported formalizations — that requires kernel elaboration).
                let lean_idx = writer.add_string(&result.best_lean);

                let confidence = match result.tier {
                    AdmissionTier::KernelProved => ImportConfidence::KernelVerified,
                    AdmissionTier::AuditedAlignment => ImportConfidence::Translated,
                    AdmissionTier::TypeChecked => ImportConfidence::Axiomatized,
                    AdmissionTier::Candidate => ImportConfidence::Unverified,
                };

                // The `kind` field is a free-form string from the LLM
                // extraction pass ("theorem"/"lemma"/"definition"/…). Treat
                // definitional tokens as Definition, everything else as
                // Theorem; both preserve the Arxiv axiom profile.
                let kind_lc = result.kind.to_ascii_lowercase();
                let decl_kind = if kind_lc.contains("def") {
                    crate::types::DeclKind::Definition
                } else {
                    crate::types::DeclKind::Theorem
                };
                let header = MathverseConstantHeader {
                    name_idx,
                    type_idx: lean_idx,  // Store lean code ref in type slot
                    value_idx: NO_VALUE, // No proof term yet
                    source_system: SourceSystem::Arxiv as u8,
                    import_confidence: confidence as u8,
                    content_domain: ContentDomain::PureMath as u8,
                    decl_kind: decl_kind as u8,
                    axiom_profile: AxiomProfile::AXIOMATIZED.union(AxiomProfile::ARXIV_NL_IMPORT),
                    sidecar_digest: 0,
                    provenance_idx: 0,
                    level_params_start: 0,
                    level_params_count: 0,
                    _pad2: [0u8; 26],
                };
                writer.add_constant(header);
                stats.exported += 1;
            }
        }

        stats.skipped += stats.total_input - stats.eligible;
        stats.papers = papers_seen.len();

        if stats.exported > 0 {
            writer
                .write_to_file(output_path)
                .map_err(|e| e.with_context("writing arxiv mathverse shard"))?;
        }

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

/// A formalization is exportable if it has reached at least `TypeChecked` tier.
fn is_exportable(result: &FormalizationResult) -> bool {
    matches!(
        result.tier,
        AdmissionTier::TypeChecked | AdmissionTier::AuditedAlignment | AdmissionTier::KernelProved
    )
}

fn sanitize_paper_id(id: &str) -> String {
    id.replace(['.', '/', '-'], "_")
}

fn sanitize_label(label: &str) -> String {
    label
        .replace([' ', '.', '-', ':'], "_")
        .replace(['\'', '"'], "")
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
    fn test_arxiv_to_mathverse_export() {
        let r_good = make_result(
            "Theorem 1",
            AdmissionTier::TypeChecked,
            "theorem foo (n : Nat) : n + 0 = n := Nat.add_zero n",
        );
        let r_bad = make_result("Theorem 2", AdmissionTier::Candidate, "bad code");
        let paper = make_paper(vec![r_good, r_bad]);

        let dir = std::env::temp_dir().join("arxiv_mathverse_test");
        std::fs::create_dir_all(&dir).expect("create temp dir");
        let shard_path = dir.join("arxiv_test.mathverse");

        let stats = ArxivMathverseBridge::export_formalized(&[paper], &shard_path)
            .expect("export should succeed");

        assert_eq!(stats.total_input, 2);
        assert_eq!(stats.eligible, 1);
        assert_eq!(stats.exported, 1);
        assert_eq!(stats.skipped, 1);
        assert_eq!(stats.papers, 1);

        // Shard file should exist
        assert!(shard_path.exists(), "shard file should be created");

        // clean up
        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn test_export_empty_formalizations() {
        let paper = make_paper(vec![]);
        let dir = std::env::temp_dir().join("arxiv_mathverse_empty_test");
        std::fs::create_dir_all(&dir).expect("create temp dir");
        let shard_path = dir.join("empty.mathverse");

        let stats = ArxivMathverseBridge::export_formalized(&[paper], &shard_path)
            .expect("export should succeed even with no data");

        assert_eq!(stats.exported, 0);
        // No shard should be written when nothing was exported
        assert!(!shard_path.exists());

        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn test_is_exportable_tiers() {
        let candidate = make_result("T", AdmissionTier::Candidate, "x");
        let tc = make_result("T", AdmissionTier::TypeChecked, "x");
        let aa = make_result("T", AdmissionTier::AuditedAlignment, "x");
        let kp = make_result("T", AdmissionTier::KernelProved, "x");

        assert!(!is_exportable(&candidate));
        assert!(is_exportable(&tc));
        assert!(is_exportable(&aa));
        assert!(is_exportable(&kp));
    }
}
