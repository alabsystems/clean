// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Reporting module for discovery run results.
//!
//! Builds structured reports from `DiscoveryResults` with markdown and
//! JSON output formats. Used for logging discovery outcomes and
//! generating human-readable summaries.
//!
//! Part of #3274.

use serde::{Deserialize, Serialize};

use crate::runner::DiscoveryResults;

/// Per-family statistics within a discovery report.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
#[non_exhaustive]
pub struct FamilyStats {
    /// Family name (from `TheoremFamily::to_string`).
    pub family: String,
    /// Total candidates evaluated for this family.
    pub candidates: u64,
    /// Candidates that passed verification.
    pub verified: u64,
    /// Fraction of candidates that verified (0.0 .. 1.0).
    pub acceptance_rate: f64,
    /// Parameter strings of the best (fastest) verified theorem.
    pub best_params: Vec<String>,
}

/// A structured report summarizing a discovery run.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
#[non_exhaustive]
pub struct DiscoveryReport {
    /// Report title.
    pub title: String,
    /// ISO 8601 timestamp (epoch seconds).
    pub timestamp: String,
    /// Per-family breakdowns.
    pub family_stats: Vec<FamilyStats>,
    /// Total candidates evaluated across all families.
    pub total_candidates: u64,
    /// Total verified across all families.
    pub total_verified: u64,
    /// Wall-clock time in seconds.
    pub wall_time_secs: f64,
    /// Throughput in candidates per second.
    pub throughput_per_sec: f64,
}

impl DiscoveryReport {
    /// Build a report from completed discovery results.
    pub fn from_results(results: &DiscoveryResults) -> Self {
        let wall_time_secs = results.total_wall_time_ns as f64 / 1_000_000_000.0;
        let throughput_per_sec = if wall_time_secs > 0.0 {
            results.total_evaluated as f64 / wall_time_secs
        } else {
            0.0
        };

        let family_stats: Vec<FamilyStats> = results
            .family_results
            .iter()
            .map(|(fam, search_result)| {
                let candidates = search_result.stats.total_evaluated;
                let verified = search_result.stats.total_verified;
                let acceptance_rate = if candidates > 0 {
                    verified as f64 / candidates as f64
                } else {
                    0.0
                };

                // Best = fastest verified outcome
                let best_params = search_result
                    .outcomes
                    .iter()
                    .filter(|o| o.verified)
                    .min_by_key(|o| o.time_ns)
                    .map(|_best| {
                        // We don't have direct access to candidate params from
                        // outcomes alone; report the family name as a placeholder.
                        // Callers who need params should cross-reference via
                        // candidate_id.
                        vec![fam.to_string()]
                    })
                    .unwrap_or_default();

                FamilyStats {
                    family: fam.to_string(),
                    candidates,
                    verified,
                    acceptance_rate,
                    best_params,
                }
            })
            .collect();

        let timestamp = {
            let dur = std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap_or_default();
            format!("{}", dur.as_secs())
        };

        Self {
            title: "Discovery Run Report".to_string(),
            timestamp,
            family_stats,
            total_candidates: results.total_evaluated,
            total_verified: results.total_verified,
            wall_time_secs,
            throughput_per_sec,
        }
    }

    /// Render the report as a Markdown string.
    #[must_use]
    pub fn to_markdown(&self) -> String {
        let mut md = String::new();

        md.push_str(&format!("# {}\n\n", self.title));
        md.push_str(&format!("**Timestamp:** {}\n\n", self.timestamp));

        // Summary table
        md.push_str("## Summary\n\n");
        md.push_str("| Metric | Value |\n");
        md.push_str("|--------|-------|\n");
        md.push_str(&format!(
            "| Total candidates | {} |\n",
            self.total_candidates
        ));
        md.push_str(&format!("| Total verified | {} |\n", self.total_verified));
        let overall_rate = if self.total_candidates > 0 {
            self.total_verified as f64 / self.total_candidates as f64
        } else {
            0.0
        };
        md.push_str(&format!(
            "| Acceptance rate | {:.1}% |\n",
            overall_rate * 100.0
        ));
        md.push_str(&format!("| Wall time | {:.3}s |\n", self.wall_time_secs));
        md.push_str(&format!(
            "| Throughput | {:.0} candidates/sec |\n",
            self.throughput_per_sec
        ));

        // Per-family breakdown
        if !self.family_stats.is_empty() {
            md.push_str("\n## Per-Family Breakdown\n\n");
            md.push_str("| Family | Candidates | Verified | Rate |\n");
            md.push_str("|--------|-----------|----------|------|\n");
            for fs in &self.family_stats {
                md.push_str(&format!(
                    "| {} | {} | {} | {:.1}% |\n",
                    fs.family,
                    fs.candidates,
                    fs.verified,
                    fs.acceptance_rate * 100.0,
                ));
            }
        }

        // Best results
        let best: Vec<&FamilyStats> = self
            .family_stats
            .iter()
            .filter(|fs| fs.verified > 0)
            .collect();
        if !best.is_empty() {
            md.push_str("\n## Best Results\n\n");
            for fs in &best {
                md.push_str(&format!(
                    "- **{}**: {} verified out of {} ({:.1}%)\n",
                    fs.family,
                    fs.verified,
                    fs.candidates,
                    fs.acceptance_rate * 100.0,
                ));
            }
        }

        md
    }

    /// Render the report as a JSON string.
    #[must_use]
    pub fn to_json(&self) -> String {
        serde_json::to_string_pretty(self).unwrap_or_else(|_| "{}".to_string())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::candidate::{CandidateId, VerificationOutcome};
    use crate::family::TheoremFamily;
    use crate::runner::DiscoveryResults;
    use crate::search::{SearchResult, SearchStats};

    fn sample_results() -> DiscoveryResults {
        let outcomes = vec![
            VerificationOutcome {
                candidate_id: CandidateId(0),
                verified: true,
                inferred_type: None,
                error: None,
                time_ns: 100,
            },
            VerificationOutcome {
                candidate_id: CandidateId(1),
                verified: false,
                inferred_type: None,
                error: Some("type error".to_string()),
                time_ns: 200,
            },
        ];
        let stats = SearchStats {
            total_evaluated: 2,
            total_verified: 1,
            total_failed: 1,
            wall_time_ns: 1_000_000_000,
            throughput_per_sec: 2.0,
        };
        DiscoveryResults {
            family_results: vec![(
                TheoremFamily::CertSizeBound,
                SearchResult { outcomes, stats },
            )],
            total_evaluated: 2,
            total_verified: 1,
            total_wall_time_ns: 1_000_000_000,
        }
    }

    #[test]
    fn test_from_results_populates_fields() {
        let results = sample_results();
        let report = DiscoveryReport::from_results(&results);

        assert_eq!(report.total_candidates, 2);
        assert_eq!(report.total_verified, 1);
        assert!(report.wall_time_secs > 0.0);
        assert!(report.throughput_per_sec > 0.0);
        assert_eq!(report.family_stats.len(), 1);
        assert_eq!(report.family_stats[0].family, "CertSizeBound");
        assert_eq!(report.family_stats[0].candidates, 2);
        assert_eq!(report.family_stats[0].verified, 1);
    }

    #[test]
    fn test_from_results_acceptance_rate() {
        let results = sample_results();
        let report = DiscoveryReport::from_results(&results);

        let rate = report.family_stats[0].acceptance_rate;
        assert!((rate - 0.5).abs() < f64::EPSILON);
    }

    #[test]
    fn test_to_markdown_contains_structure() {
        let results = sample_results();
        let report = DiscoveryReport::from_results(&results);
        let md = report.to_markdown();

        assert!(md.contains("# Discovery Run Report"));
        assert!(md.contains("## Summary"));
        assert!(md.contains("Total candidates"));
        assert!(md.contains("## Per-Family Breakdown"));
        assert!(md.contains("CertSizeBound"));
        assert!(md.contains("## Best Results"));
    }

    #[test]
    fn test_to_markdown_no_best_when_zero_verified() {
        let results = DiscoveryResults {
            family_results: vec![(
                TheoremFamily::CertSizeBound,
                SearchResult {
                    outcomes: vec![VerificationOutcome {
                        candidate_id: CandidateId(0),
                        verified: false,
                        inferred_type: None,
                        error: Some("fail".to_string()),
                        time_ns: 100,
                    }],
                    stats: SearchStats {
                        total_evaluated: 1,
                        total_verified: 0,
                        total_failed: 1,
                        wall_time_ns: 500_000_000,
                        throughput_per_sec: 2.0,
                    },
                },
            )],
            total_evaluated: 1,
            total_verified: 0,
            total_wall_time_ns: 500_000_000,
        };
        let report = DiscoveryReport::from_results(&results);
        let md = report.to_markdown();

        assert!(!md.contains("## Best Results"));
    }

    #[test]
    fn test_to_json_is_valid_json() {
        let results = sample_results();
        let report = DiscoveryReport::from_results(&results);
        let json_str = report.to_json();

        let parsed: Result<serde_json::Value, _> = serde_json::from_str(&json_str);
        assert!(parsed.is_ok(), "to_json should produce valid JSON");
    }

    #[test]
    fn test_to_json_roundtrip() {
        let results = sample_results();
        let report = DiscoveryReport::from_results(&results);
        let json_str = report.to_json();

        let deserialized: DiscoveryReport =
            serde_json::from_str(&json_str).expect("should deserialize");
        assert_eq!(deserialized.total_candidates, report.total_candidates);
        assert_eq!(deserialized.total_verified, report.total_verified);
        assert_eq!(deserialized.family_stats.len(), report.family_stats.len());
    }
}
