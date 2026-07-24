// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Import statistics and summary reporting for the Mathverse Library.
//!
//! Tracks per-source-system import counts, trust level distributions, axiom
//! profile coverage, and training-exportable fractions. Supports merging
//! stats from parallel import workers.

use hashbrown::HashMap;
use serde::{Deserialize, Serialize};

use crate::types::{AxiomProfile, TrustLevel};

/// Per-source-system import statistics.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct SourceStats {
    pub constant_count: u64,
    pub theorem_count: u64,
    pub axiom_bit_sum: u64,
    pub trust_distribution: HashMap<TrustLevel, u64>,
}

impl SourceStats {
    #[must_use]
    pub fn avg_axiom_bits(&self) -> f64 {
        if self.constant_count == 0 {
            0.0
        } else {
            self.axiom_bit_sum as f64 / self.constant_count as f64
        }
    }
}

/// Aggregate import statistics across all source systems.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct ImportStats {
    pub total_constants: u64,
    pub total_theorems: u64,
    pub by_source: HashMap<String, SourceStats>,
    pub by_trust_level: HashMap<TrustLevel, u64>,
    pub kernel_verified_count: u64,
    pub training_exportable_count: u64,
}

impl ImportStats {
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Record one imported constant.
    pub fn record(&mut self, source: &str, trust: TrustLevel, profile: AxiomProfile) {
        self.total_constants += 1;

        let source_stats = self.by_source.entry(source.to_owned()).or_default();
        source_stats.constant_count += 1;
        source_stats.axiom_bit_sum += u64::from(profile.axiom_count());
        *source_stats.trust_distribution.entry(trust).or_insert(0) += 1;

        *self.by_trust_level.entry(trust).or_insert(0) += 1;

        if trust == TrustLevel::KernelVerified && profile.is_kernel_verified() {
            self.kernel_verified_count += 1;
            self.training_exportable_count += 1;
        }
    }

    /// Record a theorem (a constant that represents a proposition).
    pub fn record_theorem(&mut self, source: &str) {
        self.total_theorems += 1;
        self.by_source
            .entry(source.to_owned())
            .or_default()
            .theorem_count += 1;
    }

    /// Merge another ImportStats into this one (for parallel import workers).
    pub fn merge(&mut self, other: &ImportStats) {
        self.total_constants += other.total_constants;
        self.total_theorems += other.total_theorems;
        self.kernel_verified_count += other.kernel_verified_count;
        self.training_exportable_count += other.training_exportable_count;

        for (source, stats) in &other.by_source {
            let entry = self.by_source.entry(source.clone()).or_default();
            entry.constant_count += stats.constant_count;
            entry.theorem_count += stats.theorem_count;
            entry.axiom_bit_sum += stats.axiom_bit_sum;
            for (&trust, &count) in &stats.trust_distribution {
                *entry.trust_distribution.entry(trust).or_insert(0) += count;
            }
        }

        for (&trust, &count) in &other.by_trust_level {
            *self.by_trust_level.entry(trust).or_insert(0) += count;
        }
    }

    /// Fraction of constants that are kernel-verified.
    #[must_use]
    pub fn kernel_verified_fraction(&self) -> f64 {
        if self.total_constants == 0 {
            0.0
        } else {
            self.kernel_verified_count as f64 / self.total_constants as f64
        }
    }

    /// Fraction of constants exportable for training.
    #[must_use]
    pub fn training_exportable_fraction(&self) -> f64 {
        if self.total_constants == 0 {
            0.0
        } else {
            self.training_exportable_count as f64 / self.total_constants as f64
        }
    }

    /// Source breakdown sorted by count descending.
    #[must_use]
    pub fn source_breakdown(&self) -> Vec<(String, SourceStats)> {
        let mut entries: Vec<_> = self
            .by_source
            .iter()
            .map(|(k, v)| (k.clone(), v.clone()))
            .collect();
        entries.sort_by_key(|b| std::cmp::Reverse(b.1.constant_count));
        entries
    }

    /// Human-readable summary.
    #[must_use]
    pub fn summary(&self) -> String {
        let mut s = format!(
            "Mathverse Import: {} constants, {} theorems\n",
            self.total_constants, self.total_theorems
        );
        s.push_str(&format!(
            "  Kernel verified: {} ({:.1}%)\n",
            self.kernel_verified_count,
            self.kernel_verified_fraction() * 100.0
        ));
        s.push_str(&format!(
            "  Training exportable: {} ({:.1}%)\n",
            self.training_exportable_count,
            self.training_exportable_fraction() * 100.0
        ));
        for (source, stats) in self.source_breakdown() {
            s.push_str(&format!(
                "  {}: {} constants, {:.1} avg axiom bits\n",
                source,
                stats.constant_count,
                stats.avg_axiom_bits()
            ));
        }
        s
    }
}

/// High-level Mathverse Library summary for reporting.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct MathverseSummary {
    pub version: String,
    pub import_stats: ImportStats,
    pub trust_audit_clean: bool,
    pub verification_properties_passed: u32,
    pub verification_properties_total: u32,
}

impl MathverseSummary {
    /// Check if the library is in a healthy state.
    #[must_use]
    pub fn is_healthy(&self) -> bool {
        self.trust_audit_clean
            && self.verification_properties_passed == self.verification_properties_total
    }

    /// Serialize to JSON.
    #[must_use]
    pub fn to_json(&self) -> String {
        serde_json::to_string_pretty(self).unwrap_or_else(|_| "{}".to_owned())
    }

    /// Format as a markdown summary table.
    #[must_use]
    pub fn to_markdown(&self) -> String {
        let mut md = String::from("# Mathverse Library Summary\n\n");
        md.push_str(&format!("**Version:** {}\n\n", self.version));
        md.push_str("| Metric | Value |\n|--------|-------|\n");
        md.push_str(&format!(
            "| Total constants | {} |\n",
            self.import_stats.total_constants
        ));
        md.push_str(&format!(
            "| Total theorems | {} |\n",
            self.import_stats.total_theorems
        ));
        md.push_str(&format!(
            "| Kernel verified | {} ({:.1}%) |\n",
            self.import_stats.kernel_verified_count,
            self.import_stats.kernel_verified_fraction() * 100.0
        ));
        md.push_str(&format!(
            "| Training exportable | {} ({:.1}%) |\n",
            self.import_stats.training_exportable_count,
            self.import_stats.training_exportable_fraction() * 100.0
        ));
        md.push_str(&format!(
            "| Trust audit | {} |\n",
            if self.trust_audit_clean {
                "CLEAN"
            } else {
                "VIOLATIONS"
            }
        ));
        md.push_str(&format!(
            "| Verification | {}/{} |\n",
            self.verification_properties_passed, self.verification_properties_total
        ));
        md.push_str(&format!(
            "| Health | {} |\n",
            if self.is_healthy() {
                "HEALTHY"
            } else {
                "DEGRADED"
            }
        ));
        md
    }
}

// ════════════════════════════════════════════════════════════════════════════
// Source breakdown
// ════════════════════════════════════════════════════════════════════════════

/// Detailed breakdown of constants from a single source system.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct SourceBreakdown {
    /// Which source system this breakdown is for.
    pub source: String,
    /// Total constants from this source.
    pub constants: usize,
    /// Number of constants that are kernel-verified.
    pub kernel_verified: usize,
    /// Number of constants that depend on axioms.
    pub axiom_dependent: usize,
    /// Average number of axiom bits per constant.
    pub avg_axiom_bits: f64,
}

impl SourceBreakdown {
    /// Fraction of constants from this source that are kernel-verified.
    #[must_use]
    pub fn kernel_verified_fraction(&self) -> f64 {
        if self.constants == 0 {
            0.0
        } else {
            self.kernel_verified as f64 / self.constants as f64
        }
    }
}

// ════════════════════════════════════════════════════════════════════════════
// Trust breakdown
// ════════════════════════════════════════════════════════════════════════════

/// Per-trust-level distribution entry.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct TrustBreakdown {
    /// Which trust level.
    pub trust_level: TrustLevel,
    /// Number of constants at this trust level.
    pub count: usize,
    /// Fraction of total constants at this trust level.
    pub fraction: f64,
}

// ════════════════════════════════════════════════════════════════════════════
// Axiom breakdown
// ════════════════════════════════════════════════════════════════════════════

/// Per-axiom-bit statistics.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct AxiomBreakdown {
    /// Name of this axiom bit (e.g., "CLASSICAL").
    pub name: String,
    /// Bit index in the `AxiomProfile` bitvector.
    pub bit_index: u32,
    /// Number of constants that have this bit set.
    pub count: usize,
    /// Fraction of total constants that have this bit set.
    pub fraction: f64,
}

// ════════════════════════════════════════════════════════════════════════════
// Trend report
// ════════════════════════════════════════════════════════════════════════════

/// Delta for a single metric between two snapshots.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct MetricDelta {
    /// Metric name.
    pub name: String,
    /// Value in the baseline snapshot.
    pub baseline: f64,
    /// Value in the current snapshot.
    pub current: f64,
    /// Absolute change (current - baseline).
    pub delta: f64,
    /// Percentage change ((current - baseline) / baseline * 100).
    pub pct_change: f64,
}

/// Report comparing two `MathverseSummary` snapshots.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct TrendReport {
    /// Changes in per-source constant counts.
    pub source_deltas: Vec<MetricDelta>,
    /// Changes in per-trust-level distributions.
    pub trust_deltas: Vec<MetricDelta>,
    /// Sources that appear in the current snapshot but not in the baseline.
    pub new_sources: Vec<String>,
    /// Sources that appear in the baseline but not in the current snapshot.
    pub removed_sources: Vec<String>,
    /// Overall constant count delta.
    pub total_constants_delta: MetricDelta,
    /// Overall kernel-verified fraction delta.
    pub kernel_verified_delta: MetricDelta,
}

impl TrendReport {
    /// Whether the trend shows improvement (more kernel-verified fraction).
    #[must_use]
    pub fn is_improving(&self) -> bool {
        self.kernel_verified_delta.delta > 0.0
    }

    /// Whether the trend shows regression.
    #[must_use]
    pub fn is_regressing(&self) -> bool {
        self.kernel_verified_delta.delta < 0.0
    }
}

/// Compare two `MathverseSummary` snapshots and produce a trend report.
#[must_use]
pub fn trend_analysis(baseline: &MathverseSummary, current: &MathverseSummary) -> TrendReport {
    let mut source_deltas = Vec::new();
    let mut new_sources = Vec::new();
    let mut removed_sources = Vec::new();

    // Collect all source names from both snapshots.
    let baseline_sources: Vec<String> = baseline.import_stats.by_source.keys().cloned().collect();
    let current_sources: Vec<String> = current.import_stats.by_source.keys().cloned().collect();

    for source in &current_sources {
        let curr_count = current
            .import_stats
            .by_source
            .get(source)
            .map_or(0, |s| s.constant_count);
        let base_count = baseline
            .import_stats
            .by_source
            .get(source)
            .map_or(0, |s| s.constant_count);

        if base_count == 0 {
            new_sources.push(source.clone());
        }

        let delta = curr_count as f64 - base_count as f64;
        let pct = if base_count == 0 {
            if curr_count > 0 {
                100.0
            } else {
                0.0
            }
        } else {
            delta / base_count as f64 * 100.0
        };

        source_deltas.push(MetricDelta {
            name: source.clone(),
            baseline: base_count as f64,
            current: curr_count as f64,
            delta,
            pct_change: pct,
        });
    }

    for source in &baseline_sources {
        if !current.import_stats.by_source.contains_key(source) {
            removed_sources.push(source.clone());
        }
    }

    // Trust level deltas.
    let trust_levels = [
        TrustLevel::KernelVerified,
        TrustLevel::AxiomDependent,
        TrustLevel::CertificateReplayed,
        TrustLevel::PartiallyAxiomatized,
        TrustLevel::TrustedOracle,
    ];
    let trust_deltas: Vec<MetricDelta> = trust_levels
        .iter()
        .map(|level| {
            let base = baseline
                .import_stats
                .by_trust_level
                .get(level)
                .copied()
                .unwrap_or(0) as f64;
            let curr = current
                .import_stats
                .by_trust_level
                .get(level)
                .copied()
                .unwrap_or(0) as f64;
            let d = curr - base;
            let pct = if base == 0.0 {
                if curr > 0.0 {
                    100.0
                } else {
                    0.0
                }
            } else {
                d / base * 100.0
            };
            MetricDelta {
                name: format!("{level:?}"),
                baseline: base,
                current: curr,
                delta: d,
                pct_change: pct,
            }
        })
        .collect();

    let base_total = baseline.import_stats.total_constants as f64;
    let curr_total = current.import_stats.total_constants as f64;
    let total_delta = curr_total - base_total;
    let total_pct = if base_total == 0.0 {
        if curr_total > 0.0 {
            100.0
        } else {
            0.0
        }
    } else {
        total_delta / base_total * 100.0
    };

    let base_kv = baseline.import_stats.kernel_verified_fraction();
    let curr_kv = current.import_stats.kernel_verified_fraction();
    let kv_delta = curr_kv - base_kv;
    let kv_pct = if base_kv == 0.0 {
        if curr_kv > 0.0 {
            100.0
        } else {
            0.0
        }
    } else {
        kv_delta / base_kv * 100.0
    };

    TrendReport {
        source_deltas,
        trust_deltas,
        new_sources,
        removed_sources,
        total_constants_delta: MetricDelta {
            name: "total_constants".to_owned(),
            baseline: base_total,
            current: curr_total,
            delta: total_delta,
            pct_change: total_pct,
        },
        kernel_verified_delta: MetricDelta {
            name: "kernel_verified_fraction".to_owned(),
            baseline: base_kv,
            current: curr_kv,
            delta: kv_delta,
            pct_change: kv_pct,
        },
    }
}

// ════════════════════════════════════════════════════════════════════════════
// Full breakdown generation
// ════════════════════════════════════════════════════════════════════════════

impl ImportStats {
    /// Generate detailed per-source breakdowns.
    #[must_use]
    pub fn source_breakdowns(&self) -> Vec<SourceBreakdown> {
        let mut breakdowns = Vec::new();
        for (source, stats) in &self.by_source {
            let kv = stats
                .trust_distribution
                .get(&TrustLevel::KernelVerified)
                .copied()
                .unwrap_or(0) as usize;
            breakdowns.push(SourceBreakdown {
                source: source.clone(),
                constants: stats.constant_count as usize,
                kernel_verified: kv,
                axiom_dependent: stats.constant_count as usize - kv,
                avg_axiom_bits: stats.avg_axiom_bits(),
            });
        }
        breakdowns.sort_by_key(|b| std::cmp::Reverse(b.constants));
        breakdowns
    }

    /// Generate per-trust-level breakdowns.
    #[must_use]
    pub fn trust_breakdowns(&self) -> Vec<TrustBreakdown> {
        let total = self.total_constants as f64;
        let mut breakdowns = Vec::new();
        let trust_levels = [
            TrustLevel::KernelVerified,
            TrustLevel::AxiomDependent,
            TrustLevel::CertificateReplayed,
            TrustLevel::PartiallyAxiomatized,
            TrustLevel::TrustedOracle,
        ];
        for level in trust_levels {
            let count = self.by_trust_level.get(&level).copied().unwrap_or(0) as usize;
            let fraction = if total == 0.0 {
                0.0
            } else {
                count as f64 / total
            };
            breakdowns.push(TrustBreakdown {
                trust_level: level,
                count,
                fraction,
            });
        }
        breakdowns
    }

    /// Generate per-axiom-bit breakdowns.
    ///
    /// Requires the raw axiom profiles tracked elsewhere; here we produce
    /// a template from the known bit names. The caller fills in counts.
    #[must_use]
    pub fn axiom_bit_names() -> Vec<(&'static str, u32)> {
        vec![
            ("CLASSICAL", 0),
            ("EXTENSIONALITY", 1),
            ("CHOICE", 2),
            ("PROOF_IRRELEVANCE", 3),
            ("HOL_EMBEDDING", 8),
            ("MIZAR_SOFT_TYPE", 9),
            ("COQ_SPROP", 10),
            ("COQ_MODULE_FUNCTOR", 11),
            ("COQ_COINDUCTIVE", 12),
            ("ISABELLE_LCF_ERASED", 13),
            ("AGDA_CUBICAL", 14),
            ("IDRIS_QTT", 15),
            ("SMT_ORACLE", 16),
            ("SAT_CERT", 17),
            ("ATP_CERT", 18),
            ("FLOAT_APPROX", 24),
            ("NN_ABSTRACTION", 25),
        ]
    }
}

impl MathverseSummary {
    /// Generate a full breakdown report including source, trust, and axiom details.
    #[must_use]
    pub fn full_report(&self) -> String {
        let mut out = self.to_markdown();
        out.push_str("\n## Source Breakdown\n\n");
        out.push_str("| Source | Constants | KV | KV% | Avg Axiom Bits |\n");
        out.push_str("|--------|-----------|-----|------|----------------|\n");
        for bd in self.import_stats.source_breakdowns() {
            out.push_str(&format!(
                "| {} | {} | {} | {:.1}% | {:.2} |\n",
                bd.source,
                bd.constants,
                bd.kernel_verified,
                bd.kernel_verified_fraction() * 100.0,
                bd.avg_axiom_bits,
            ));
        }
        out.push_str("\n## Trust Breakdown\n\n");
        out.push_str("| Trust Level | Count | Fraction |\n");
        out.push_str("|-------------|-------|----------|\n");
        for bd in self.import_stats.trust_breakdowns() {
            out.push_str(&format!(
                "| {:?} | {} | {:.1}% |\n",
                bd.trust_level,
                bd.count,
                bd.fraction * 100.0,
            ));
        }
        out
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_record_constants() {
        let mut stats = ImportStats::new();
        stats.record("Lean4", TrustLevel::KernelVerified, AxiomProfile::NONE);
        stats.record(
            "HolLight",
            TrustLevel::CertificateReplayed,
            AxiomProfile::CLASSICAL,
        );
        assert_eq!(stats.total_constants, 2);
        assert_eq!(stats.kernel_verified_count, 1);
        assert_eq!(stats.training_exportable_count, 1);
    }

    #[test]
    fn test_kernel_verified_fraction() {
        let mut stats = ImportStats::new();
        stats.record("Lean4", TrustLevel::KernelVerified, AxiomProfile::NONE);
        stats.record("Lean4", TrustLevel::KernelVerified, AxiomProfile::NONE);
        stats.record(
            "Mizar",
            TrustLevel::PartiallyAxiomatized,
            AxiomProfile::CLASSICAL,
        );
        assert!((stats.kernel_verified_fraction() - 2.0 / 3.0).abs() < 1e-10);
    }

    #[test]
    fn test_merge() {
        let mut a = ImportStats::new();
        a.record("Lean4", TrustLevel::KernelVerified, AxiomProfile::NONE);
        let mut b = ImportStats::new();
        b.record(
            "HolLight",
            TrustLevel::CertificateReplayed,
            AxiomProfile::CLASSICAL,
        );
        a.merge(&b);
        assert_eq!(a.total_constants, 2);
        assert_eq!(a.by_source.len(), 2);
    }

    #[test]
    fn test_source_breakdown_sorted() {
        let mut stats = ImportStats::new();
        stats.record("A", TrustLevel::KernelVerified, AxiomProfile::NONE);
        stats.record("B", TrustLevel::KernelVerified, AxiomProfile::NONE);
        stats.record("B", TrustLevel::KernelVerified, AxiomProfile::NONE);
        let breakdown = stats.source_breakdown();
        assert_eq!(breakdown[0].0, "B");
        assert_eq!(breakdown[0].1.constant_count, 2);
    }

    #[test]
    fn test_summary_format() {
        let mut stats = ImportStats::new();
        stats.record("Lean4", TrustLevel::KernelVerified, AxiomProfile::NONE);
        let summary = stats.summary();
        assert!(summary.contains("1 constants"));
        assert!(summary.contains("Kernel verified: 1"));
    }

    #[test]
    fn test_mathverse_summary_healthy() {
        let summary = MathverseSummary {
            version: "0.1.0".to_owned(),
            import_stats: ImportStats::new(),
            trust_audit_clean: true,
            verification_properties_passed: 6,
            verification_properties_total: 6,
        };
        assert!(summary.is_healthy());
    }

    #[test]
    fn test_mathverse_summary_unhealthy() {
        let summary = MathverseSummary {
            version: "0.1.0".to_owned(),
            import_stats: ImportStats::new(),
            trust_audit_clean: false,
            verification_properties_passed: 5,
            verification_properties_total: 6,
        };
        assert!(!summary.is_healthy());
    }

    #[test]
    fn test_mathverse_summary_json() {
        let summary = MathverseSummary {
            version: "0.1.0".to_owned(),
            import_stats: ImportStats::new(),
            trust_audit_clean: true,
            verification_properties_passed: 6,
            verification_properties_total: 6,
        };
        let json = summary.to_json();
        assert!(json.contains("0.1.0"));
    }

    #[test]
    fn test_mathverse_summary_markdown() {
        let mut stats = ImportStats::new();
        stats.record("Lean4", TrustLevel::KernelVerified, AxiomProfile::NONE);
        let summary = MathverseSummary {
            version: "0.1.0".to_owned(),
            import_stats: stats,
            trust_audit_clean: true,
            verification_properties_passed: 6,
            verification_properties_total: 6,
        };
        let md = summary.to_markdown();
        assert!(md.contains("HEALTHY"));
        assert!(md.contains("CLEAN"));
    }

    #[test]
    fn test_record_theorem() {
        let mut stats = ImportStats::new();
        stats.record(
            "HolLight",
            TrustLevel::CertificateReplayed,
            AxiomProfile::CLASSICAL,
        );
        stats.record_theorem("HolLight");
        assert_eq!(stats.total_theorems, 1);
        assert_eq!(stats.by_source.get("HolLight").unwrap().theorem_count, 1);
    }

    // ── Source breakdown tests ──

    #[test]
    fn test_source_breakdowns() {
        let mut stats = ImportStats::new();
        stats.record("Lean4", TrustLevel::KernelVerified, AxiomProfile::NONE);
        stats.record("Lean4", TrustLevel::KernelVerified, AxiomProfile::NONE);
        stats.record(
            "Mizar",
            TrustLevel::PartiallyAxiomatized,
            AxiomProfile::CLASSICAL,
        );
        let breakdowns = stats.source_breakdowns();
        assert_eq!(breakdowns.len(), 2);
        // Sorted by count descending, so Lean4 (2) comes first.
        assert_eq!(breakdowns[0].source, "Lean4");
        assert_eq!(breakdowns[0].constants, 2);
        assert_eq!(breakdowns[0].kernel_verified, 2);
        assert!((breakdowns[0].kernel_verified_fraction() - 1.0).abs() < 1e-10);
        assert_eq!(breakdowns[1].source, "Mizar");
        assert_eq!(breakdowns[1].constants, 1);
        assert_eq!(breakdowns[1].kernel_verified, 0);
    }

    #[test]
    fn test_source_breakdown_empty() {
        let stats = ImportStats::new();
        let breakdowns = stats.source_breakdowns();
        assert!(breakdowns.is_empty());
    }

    #[test]
    fn test_source_breakdown_fraction_zero_constants() {
        let bd = SourceBreakdown {
            source: "Empty".to_owned(),
            constants: 0,
            kernel_verified: 0,
            axiom_dependent: 0,
            avg_axiom_bits: 0.0,
        };
        assert!((bd.kernel_verified_fraction() - 0.0).abs() < 1e-10);
    }

    // ── Trust breakdown tests ──

    #[test]
    fn test_trust_breakdowns() {
        let mut stats = ImportStats::new();
        stats.record("A", TrustLevel::KernelVerified, AxiomProfile::NONE);
        stats.record(
            "B",
            TrustLevel::CertificateReplayed,
            AxiomProfile::CLASSICAL,
        );
        stats.record("C", TrustLevel::TrustedOracle, AxiomProfile::SMT_ORACLE);
        let breakdowns = stats.trust_breakdowns();
        // Should have 5 entries (one per trust level).
        assert_eq!(breakdowns.len(), 5);
        let kv = breakdowns
            .iter()
            .find(|b| b.trust_level == TrustLevel::KernelVerified)
            .unwrap();
        assert_eq!(kv.count, 1);
        assert!((kv.fraction - 1.0 / 3.0).abs() < 1e-10);
    }

    #[test]
    fn test_trust_breakdowns_empty() {
        let stats = ImportStats::new();
        let breakdowns = stats.trust_breakdowns();
        assert_eq!(breakdowns.len(), 5);
        for bd in &breakdowns {
            assert_eq!(bd.count, 0);
            assert!((bd.fraction - 0.0).abs() < 1e-10);
        }
    }

    // ── Axiom bit names ──

    #[test]
    fn test_axiom_bit_names() {
        let names = ImportStats::axiom_bit_names();
        assert!(names.len() >= 17);
        assert_eq!(names[0].0, "CLASSICAL");
        assert_eq!(names[0].1, 0);
        // Verify all bit indices are unique.
        let mut seen = std::collections::HashSet::new();
        for (_, bit) in &names {
            assert!(seen.insert(bit), "duplicate bit index: {bit}");
        }
    }

    // ── Trend analysis tests ──

    #[test]
    fn test_trend_analysis_identical() {
        let summary = MathverseSummary {
            version: "0.1.0".to_owned(),
            import_stats: ImportStats::new(),
            trust_audit_clean: true,
            verification_properties_passed: 6,
            verification_properties_total: 6,
        };
        let trend = trend_analysis(&summary, &summary);
        assert!((trend.total_constants_delta.delta - 0.0).abs() < 1e-10);
        assert!((trend.kernel_verified_delta.delta - 0.0).abs() < 1e-10);
        assert!(trend.new_sources.is_empty());
        assert!(trend.removed_sources.is_empty());
        assert!(!trend.is_improving());
        assert!(!trend.is_regressing());
    }

    #[test]
    fn test_trend_analysis_improvement() {
        let mut baseline_stats = ImportStats::new();
        baseline_stats.record(
            "Lean4",
            TrustLevel::PartiallyAxiomatized,
            AxiomProfile::CLASSICAL,
        );
        let baseline = MathverseSummary {
            version: "0.1.0".to_owned(),
            import_stats: baseline_stats,
            trust_audit_clean: true,
            verification_properties_passed: 6,
            verification_properties_total: 6,
        };

        let mut current_stats = ImportStats::new();
        current_stats.record("Lean4", TrustLevel::KernelVerified, AxiomProfile::NONE);
        current_stats.record("Lean4", TrustLevel::KernelVerified, AxiomProfile::NONE);
        let current = MathverseSummary {
            version: "0.2.0".to_owned(),
            import_stats: current_stats,
            trust_audit_clean: true,
            verification_properties_passed: 6,
            verification_properties_total: 6,
        };

        let trend = trend_analysis(&baseline, &current);
        assert!(trend.total_constants_delta.delta > 0.0);
        assert!(trend.is_improving());
        assert!(!trend.is_regressing());
    }

    #[test]
    fn test_trend_analysis_new_source() {
        let baseline = MathverseSummary {
            version: "0.1.0".to_owned(),
            import_stats: ImportStats::new(),
            trust_audit_clean: true,
            verification_properties_passed: 6,
            verification_properties_total: 6,
        };

        let mut current_stats = ImportStats::new();
        current_stats.record("NewSystem", TrustLevel::KernelVerified, AxiomProfile::NONE);
        let current = MathverseSummary {
            version: "0.2.0".to_owned(),
            import_stats: current_stats,
            trust_audit_clean: true,
            verification_properties_passed: 6,
            verification_properties_total: 6,
        };

        let trend = trend_analysis(&baseline, &current);
        assert!(trend.new_sources.contains(&"NewSystem".to_owned()));
    }

    #[test]
    fn test_trend_analysis_removed_source() {
        let mut baseline_stats = ImportStats::new();
        baseline_stats.record("OldSystem", TrustLevel::KernelVerified, AxiomProfile::NONE);
        let baseline = MathverseSummary {
            version: "0.1.0".to_owned(),
            import_stats: baseline_stats,
            trust_audit_clean: true,
            verification_properties_passed: 6,
            verification_properties_total: 6,
        };

        let current = MathverseSummary {
            version: "0.2.0".to_owned(),
            import_stats: ImportStats::new(),
            trust_audit_clean: true,
            verification_properties_passed: 6,
            verification_properties_total: 6,
        };

        let trend = trend_analysis(&baseline, &current);
        assert!(trend.removed_sources.contains(&"OldSystem".to_owned()));
    }

    // ── Full report tests ──

    #[test]
    fn test_mathverse_summary_full_report() {
        let mut stats = ImportStats::new();
        stats.record("Lean4", TrustLevel::KernelVerified, AxiomProfile::NONE);
        stats.record(
            "Mizar",
            TrustLevel::PartiallyAxiomatized,
            AxiomProfile::CLASSICAL,
        );
        let summary = MathverseSummary {
            version: "0.1.0".to_owned(),
            import_stats: stats,
            trust_audit_clean: true,
            verification_properties_passed: 6,
            verification_properties_total: 6,
        };
        let report = summary.full_report();
        assert!(report.contains("Source Breakdown"));
        assert!(report.contains("Trust Breakdown"));
        assert!(report.contains("Lean4"));
        assert!(report.contains("Mizar"));
    }
}
