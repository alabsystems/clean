// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Similarity search engine for the Mathverse Library.
//!
//! Finds theorems similar to a given one by name edit distance, shared
//! content domain, or cross-system name normalization. Used by `mathverse find`
//! for `--similar` and `--cross-system` queries.

use crate::equivalence::normalize_name;
use crate::library::MathverseLibrary;
#[cfg(test)]
use crate::types::ContentDomain;
use crate::types::SourceSystem;

/// The reason a result was considered similar.
#[derive(Clone, Debug, PartialEq)]
pub enum SimilarityReason {
    /// Name tokens overlap (edit distance / LCS-based).
    NameSimilarity,
    /// Same source system and content domain.
    SameDomain,
    /// Cross-system normalized name match.
    CrossSystem,
}

/// A single similarity search result.
#[derive(Clone, Debug)]
pub struct SimilarResult {
    pub constant_idx: u32,
    pub name: String,
    pub score: f64,
    pub reason: SimilarityReason,
}

/// Engine for finding similar theorems in an MathverseLibrary.
pub struct SimilarityEngine<'a> {
    library: &'a MathverseLibrary,
}

impl<'a> SimilarityEngine<'a> {
    /// Create a similarity engine over the given library.
    pub fn new(library: &'a MathverseLibrary) -> Self {
        Self { library }
    }

    /// Find theorems with similar names using token overlap and edit distance.
    ///
    /// Tokenizes both the query and each constant name on `.` and `_`,
    /// then scores by Jaccard coefficient of shared tokens combined with
    /// a normalized Levenshtein distance on the full lowercased name.
    pub fn similar_by_name(&self, name: &str, max_results: usize) -> Vec<SimilarResult> {
        let query_lower = name.to_lowercase();
        let query_tokens = tokenize(&query_lower);
        let count = self.library.constant_count();
        let mut scored = Vec::new();
        // Reused Levenshtein DP rows — refilled per call, so the full-corpus scan
        // below allocates them once instead of twice per constant.
        let mut ed_prev = Vec::new();
        let mut ed_curr = Vec::new();

        for idx in 0..count as u32 {
            let cname = match self.library.get_name(idx) {
                Some(n) => n,
                None => continue,
            };
            let cname_lower = cname.to_lowercase();
            if cname_lower == query_lower {
                continue; // Skip exact match.
            }

            let cname_tokens = tokenize(&cname_lower);
            let jaccard = jaccard_similarity(&query_tokens, &cname_tokens);
            let edit_score = 1.0
                - (edit_distance_into(&query_lower, &cname_lower, &mut ed_prev, &mut ed_curr)
                    as f64
                    / query_lower.len().max(cname_lower.len()).max(1) as f64);
            let combined = jaccard * 0.6 + edit_score * 0.4;

            if combined > 0.2 {
                scored.push(SimilarResult {
                    constant_idx: idx,
                    name: cname.to_owned(),
                    score: combined,
                    reason: SimilarityReason::NameSimilarity,
                });
            }
        }

        scored.sort_by(|a, b| {
            b.score
                .partial_cmp(&a.score)
                .unwrap_or(std::cmp::Ordering::Equal)
        });
        scored.truncate(max_results);
        scored
    }

    /// Find theorems from the same source system and content domain.
    pub fn related_in_domain(&self, constant_idx: u32, max_results: usize) -> Vec<SimilarResult> {
        let header = match self.library.get_constant(constant_idx) {
            Some(h) => *h,
            None => return Vec::new(),
        };
        let target_system = header.source_system;
        let target_domain = header.content_domain;
        let target_name = self
            .library
            .get_name(constant_idx)
            .unwrap_or("")
            .to_lowercase();
        let target_tokens = tokenize(&target_name);

        let count = self.library.constant_count();
        let mut results = Vec::new();

        for idx in 0..count as u32 {
            if idx == constant_idx {
                continue;
            }
            let h = match self.library.get_constant(idx) {
                Some(h) => *h,
                None => continue,
            };
            if h.source_system != target_system || h.content_domain != target_domain {
                continue;
            }
            let cname = self.library.get_name(idx).unwrap_or("").to_lowercase();
            let cname_tokens = tokenize(&cname);
            let jaccard = jaccard_similarity(&target_tokens, &cname_tokens);

            results.push(SimilarResult {
                constant_idx: idx,
                name: self.library.get_name(idx).unwrap_or("").to_owned(),
                score: jaccard,
                reason: SimilarityReason::SameDomain,
            });
        }

        results.sort_by(|a, b| {
            b.score
                .partial_cmp(&a.score)
                .unwrap_or(std::cmp::Ordering::Equal)
        });
        results.truncate(max_results);
        results
    }

    /// Find cross-system equivalents by normalized name matching.
    ///
    /// Normalizes the query name for each known source system and then scans
    /// the library for constants whose normalized name matches.
    pub fn cross_system_matches(&self, name: &str, max_results: usize) -> Vec<SimilarResult> {
        // Compute canonical forms of the query under each source system.
        let canonical_forms: Vec<String> = [
            SourceSystem::Lean4,
            SourceSystem::Coq,
            SourceSystem::Isabelle,
            SourceSystem::HolLight,
            SourceSystem::Hol4,
            SourceSystem::Metamath,
            SourceSystem::Mizar,
            SourceSystem::CleanNative,
        ]
        .iter()
        .map(|sys| normalize_name(name, *sys))
        .collect();

        let count = self.library.constant_count();
        let mut results = Vec::new();

        for idx in 0..count as u32 {
            let cname = match self.library.get_name(idx) {
                Some(n) => n,
                None => continue,
            };
            let header = match self.library.get_constant(idx) {
                Some(h) => *h,
                None => continue,
            };
            let source = match SourceSystem::try_from(header.source_system) {
                Ok(s) => s,
                Err(_) => continue,
            };

            let cname_canonical = normalize_name(cname, source);

            // Check if any canonical form of the query matches.
            for canonical in &canonical_forms {
                if cname_canonical == *canonical {
                    // Score: exact normalized match gets 1.0, partial gets less.
                    results.push(SimilarResult {
                        constant_idx: idx,
                        name: cname.to_owned(),
                        score: 1.0,
                        reason: SimilarityReason::CrossSystem,
                    });
                    break;
                }
            }

            if results.len() >= max_results {
                break;
            }
        }

        results.truncate(max_results);
        results
    }
}

/// Tokenize a name on `.` and `_` separators. Returns lowercase tokens.
fn tokenize(name: &str) -> Vec<String> {
    name.split(['.', '_'])
        .filter(|s| !s.is_empty())
        .map(|s| s.to_lowercase())
        .collect()
}

/// Jaccard similarity between two token sets.
fn jaccard_similarity(a: &[String], b: &[String]) -> f64 {
    if a.is_empty() && b.is_empty() {
        return 1.0;
    }
    let set_a: hashbrown::HashSet<&str> = a.iter().map(|s| s.as_str()).collect();
    let set_b: hashbrown::HashSet<&str> = b.iter().map(|s| s.as_str()).collect();
    let intersection = set_a.intersection(&set_b).count();
    let union = set_a.union(&set_b).count();
    if union == 0 {
        0.0
    } else {
        intersection as f64 / union as f64
    }
}

/// Levenshtein edit distance between two strings.
#[cfg(test)]
fn edit_distance(a: &str, b: &str) -> usize {
    let mut prev = Vec::new();
    let mut curr = Vec::new();
    edit_distance_into(a, b, &mut prev, &mut curr)
}

/// Levenshtein edit distance using caller-provided scratch rows, reused across
/// calls in the full-corpus `similar_by_name` scan to avoid two heap allocations
/// per constant. `prev`/`curr` are `clear()`ed and refilled, so their prior
/// contents and capacity are irrelevant; the result is the exact same distance.
fn edit_distance_into(a: &str, b: &str, prev: &mut Vec<usize>, curr: &mut Vec<usize>) -> usize {
    let (ab, bb) = (a.as_bytes(), b.as_bytes());
    let (m, n) = (ab.len(), bb.len());
    prev.clear();
    prev.extend(0..=n);
    curr.clear();
    curr.resize(n + 1, 0);

    for i in 1..=m {
        curr[0] = i;
        for j in 1..=n {
            let cost = if ab[i - 1] == bb[j - 1] { 0 } else { 1 };
            curr[j] = (prev[j] + 1).min(curr[j - 1] + 1).min(prev[j - 1] + cost);
        }
        std::mem::swap(prev, curr);
    }
    prev[n]
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::library::MathverseLibrary;
    use crate::shard::ShardWriter;
    use crate::trust::policy::TrustPolicy;
    use crate::types::{AxiomProfile, ImportConfidence, MathverseConstantHeader, SourceSystem};
    use clean_kernel::flat::{FlatExpr, FlatLevel};

    fn build_test_library(names: &[(&str, SourceSystem)]) -> MathverseLibrary {
        let mut writer = ShardWriter::new();
        let l0 = writer.add_level(FlatLevel::zero());
        let e0 = writer.add_expr(FlatExpr::sort(l0));

        for &(name, source) in names {
            let ni = writer.add_string(name);
            writer.add_constant(MathverseConstantHeader {
                name_idx: ni,
                type_idx: e0,
                value_idx: e0,
                source_system: source as u8,
                import_confidence: ImportConfidence::KernelVerified as u8,
                content_domain: ContentDomain::PureMath as u8,
                decl_kind: 0,
                axiom_profile: AxiomProfile::NONE,
                sidecar_digest: 0,
                provenance_idx: 0,
                level_params_start: 0,
                level_params_count: 0,
                _pad2: [0u8; 26],
            });
        }

        let mut buf = Vec::new();
        writer.write(&mut buf).unwrap();
        let shard = crate::shard::ShardReader::from_bytes(&buf).unwrap();
        let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
        lib.load_shard(&shard).unwrap();
        lib
    }

    #[test]
    fn test_similar_by_name() {
        let lib = build_test_library(&[
            ("Nat.add_comm", SourceSystem::Lean4),
            ("Nat.add_assoc", SourceSystem::Lean4),
            ("Nat.mul_comm", SourceSystem::Lean4),
            ("List.map", SourceSystem::Lean4),
            ("Bool.not_not", SourceSystem::Lean4),
        ]);

        let engine = SimilarityEngine::new(&lib);
        let results = engine.similar_by_name("Nat.add_comm", 5);

        // Nat.add_assoc and Nat.mul_comm should score higher than List.map.
        assert!(!results.is_empty());
        let top_names: Vec<&str> = results.iter().map(|r| r.name.as_str()).collect();
        assert!(
            top_names.contains(&"Nat.add_assoc"),
            "Nat.add_assoc should be similar to Nat.add_comm"
        );
        // All results should have NameSimilarity reason.
        for r in &results {
            assert_eq!(r.reason, SimilarityReason::NameSimilarity);
            assert!(r.score > 0.0);
        }
    }

    #[test]
    fn test_related_in_domain() {
        let lib = build_test_library(&[
            ("Nat.add_comm", SourceSystem::Lean4),
            ("Nat.mul_comm", SourceSystem::Lean4),
            ("PeanoNat.Nat.add_comm", SourceSystem::Coq),
            ("Bool.true", SourceSystem::Lean4),
        ]);

        let engine = SimilarityEngine::new(&lib);
        let results = engine.related_in_domain(0, 10);

        // Should return Nat.mul_comm and Bool.true (same system+domain) but not Coq constant.
        let names: Vec<&str> = results.iter().map(|r| r.name.as_str()).collect();
        assert!(names.contains(&"Nat.mul_comm"));
        assert!(names.contains(&"Bool.true"));
        assert!(
            !names.contains(&"PeanoNat.Nat.add_comm"),
            "Cross-system constants should not appear in same-domain results"
        );
        for r in &results {
            assert_eq!(r.reason, SimilarityReason::SameDomain);
        }
    }

    #[test]
    fn test_cross_system_matches() {
        let lib = build_test_library(&[
            ("Nat.add_comm", SourceSystem::Lean4),
            ("PeanoNat.Nat.add_comm", SourceSystem::Coq),
            ("Mathlib.Nat.add_comm", SourceSystem::Lean4),
            ("List.map", SourceSystem::Lean4),
        ]);

        let engine = SimilarityEngine::new(&lib);
        let results = engine.cross_system_matches("Nat.add_comm", 10);

        // All three add_comm variants should appear (they normalize to "nat_add_comm").
        assert!(results.len() >= 2);
        let names: Vec<&str> = results.iter().map(|r| r.name.as_str()).collect();
        assert!(
            names.contains(&"Nat.add_comm"),
            "Lean4 add_comm should appear"
        );
        assert!(
            names.contains(&"PeanoNat.Nat.add_comm"),
            "Coq add_comm should appear"
        );
        assert!(
            !names.contains(&"List.map"),
            "Unrelated constant should not appear"
        );
        for r in &results {
            assert_eq!(r.reason, SimilarityReason::CrossSystem);
            assert!((r.score - 1.0).abs() < f64::EPSILON);
        }
    }

    #[test]
    fn test_tokenize() {
        assert_eq!(tokenize("Nat.add_comm"), vec!["nat", "add", "comm"]);
        assert_eq!(
            tokenize("PeanoNat.Nat.add_comm"),
            vec!["peanonat", "nat", "add", "comm"]
        );
        assert_eq!(tokenize(""), Vec::<String>::new());
        assert_eq!(tokenize("single"), vec!["single"]);
    }

    #[test]
    fn test_jaccard_similarity() {
        let a = tokenize("nat.add.comm");
        let b = tokenize("nat.add.assoc");
        let sim = jaccard_similarity(&a, &b);
        // Shared: {nat, add}. Union: {nat, add, comm, assoc}. Jaccard = 2/4 = 0.5.
        assert!((sim - 0.5).abs() < f64::EPSILON);

        let identical = tokenize("nat.add");
        assert!((jaccard_similarity(&identical, &identical) - 1.0).abs() < f64::EPSILON);

        assert!((jaccard_similarity(&[], &[]) - 1.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_edit_distance() {
        assert_eq!(edit_distance("kitten", "sitting"), 3);
        assert_eq!(edit_distance("abc", "abc"), 0);
        assert_eq!(edit_distance("", "abc"), 3);
        assert_eq!(edit_distance("abc", ""), 3);
    }

    #[test]
    fn test_similar_empty_library() {
        let lib = MathverseLibrary::new(TrustPolicy::permissive());
        let engine = SimilarityEngine::new(&lib);
        assert!(engine.similar_by_name("anything", 10).is_empty());
        assert!(engine.cross_system_matches("anything", 10).is_empty());
    }
}
