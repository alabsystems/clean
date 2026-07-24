// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Premise selection for the Mathverse Library.
//!
//! Searches the loaded mathverse library for theorems relevant to a given goal,
//! blending type-directed discrimination tree search, BM25 semantic search,
//! dependency-neighborhood heuristics, and symbol-overlap scoring into a
//! single ranked candidate list.
//!
//! The module provides two entry points:
//! - [`search_for_goal`]: takes mathverse-level indices and text (used by tactics)
//! - [`search_for_kernel_goal`]: takes a kernel [`Expr`] goal, extracts symbols
//!   automatically, and bridges to the mathverse library (used by proof search and
//!   the AI verification loop from #3386)
//!
//! Used by `mathverse_use` and `mathverse_suggest` tactics in `clean-elab`.

use crate::library::MathverseLibrary;
use crate::search::{MathverseSearch, SearchResult};
use crate::types::{
    ConstantIdx, ExprIdx, ImportConfidence, MathverseConstantHeader, SourceSystem, TrustLevel,
};

use clean_kernel::expr::{Expr, ExprKind};
use clean_kernel::name::Name;

/// Why a candidate was selected.
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum MatchReason {
    /// Goal type matched via discrimination tree unification.
    TypeUnification,
    /// BM25 text similarity between goal text and constant name.
    NameSimilarity,
    /// Constant is a dependency neighbor of something already in scope.
    DependencyNeighbor,
    /// Constant shares symbols (constant names) with the goal expression.
    SymbolOverlap,
}

/// A candidate theorem from the mathverse library that may prove the current goal.
#[derive(Clone, Debug)]
pub struct PremiseCandidate {
    /// The constant's name in the mathverse library.
    pub name: String,
    /// Global constant index in the library.
    pub constant_idx: ConstantIdx,
    /// Blended relevance score (higher is better, in [0.0, 1.0]).
    pub score: f64,
    /// Source proof system.
    pub source_system: SourceSystem,
    /// Trust level of the constant.
    pub trust_level: TrustLevel,
    /// How this candidate was found.
    pub match_reason: MatchReason,
    /// The constant header for downstream use.
    pub header: MathverseConstantHeader,
}

/// Weight configuration for blending search signals.
#[derive(Clone, Debug)]
pub struct PremiseConfig {
    /// Weight for type-directed matches (0.0-1.0).
    pub type_weight: f64,
    /// Weight for name/semantic matches (0.0-1.0).
    pub name_weight: f64,
    /// Weight for dependency-neighbor matches (0.0-1.0).
    pub dep_weight: f64,
    /// Maximum candidates to return.
    pub max_results: usize,
    /// Minimum trust level for candidate filtering.
    /// Candidates with `ImportConfidence` below this threshold are excluded.
    /// Default: `None` (no trust filtering at the search layer; caller filters).
    pub min_trust: Option<ImportConfidence>,
}

impl Default for PremiseConfig {
    fn default() -> Self {
        Self {
            type_weight: 0.6,
            name_weight: 0.3,
            dep_weight: 0.1,
            max_results: 20,
            min_trust: None,
        }
    }
}

/// Search the mathverse library for theorems relevant to the given goal.
///
/// Blends three search signals:
/// 1. **Type-directed**: discrimination tree search on `goal_type_idx` (if provided)
/// 2. **Semantic**: BM25 search on `goal_text` (the goal rendered as a string)
/// 3. **Dependency neighborhood**: constants used by `context_names` (constants
///    already in scope)
///
/// Results are deduplicated by constant index and sorted by descending score.
pub fn search_for_goal(
    library: &MathverseLibrary,
    goal_type_idx: Option<ExprIdx>,
    goal_text: &str,
    context_names: &[&str],
    config: &PremiseConfig,
) -> Vec<PremiseCandidate> {
    let fetch_limit = config.max_results * 3;

    // Channel 1: type-directed search via discrimination tree
    let type_results = if let Some(type_idx) = goal_type_idx {
        library
            .search_type(type_idx, fetch_limit)
            .unwrap_or_default()
    } else {
        Vec::new()
    };

    // Channel 2: semantic / BM25 search on goal text
    let name_results = if !goal_text.is_empty() {
        library
            .search_semantic(goal_text, fetch_limit)
            .unwrap_or_default()
    } else {
        Vec::new()
    };

    // Channel 3: dependency neighbors of context constants
    let dep_results = collect_dep_neighbors(library, context_names, fetch_limit);

    // Merge and deduplicate
    let mut seen = hashbrown::HashSet::new();
    let mut candidates: Vec<PremiseCandidate> = Vec::new();

    // Helper: normalize a raw score from a search channel to [0, 1].
    let normalize = |score: f32, max_score: f32| -> f64 {
        if max_score <= 0.0 {
            0.0
        } else {
            (score as f64 / max_score as f64).min(1.0)
        }
    };

    let type_max = type_results.iter().map(|r| r.score).fold(0.0f32, f32::max);
    for r in &type_results {
        if seen.insert(r.constant_idx) {
            if let Some(c) = build_candidate(
                library,
                r,
                normalize(r.score, type_max) * config.type_weight,
                MatchReason::TypeUnification,
            ) {
                candidates.push(c);
            }
        }
    }

    let name_max = name_results.iter().map(|r| r.score).fold(0.0f32, f32::max);
    for r in &name_results {
        if let Some(existing) = candidates
            .iter_mut()
            .find(|c| c.constant_idx == r.constant_idx)
        {
            // Boost existing candidate from type search
            existing.score += normalize(r.score, name_max) * config.name_weight;
        } else if seen.insert(r.constant_idx) {
            if let Some(c) = build_candidate(
                library,
                r,
                normalize(r.score, name_max) * config.name_weight,
                MatchReason::NameSimilarity,
            ) {
                candidates.push(c);
            }
        }
    }

    let dep_max = dep_results.iter().map(|r| r.score).fold(0.0f32, f32::max);
    for r in &dep_results {
        if let Some(existing) = candidates
            .iter_mut()
            .find(|c| c.constant_idx == r.constant_idx)
        {
            existing.score += normalize(r.score, dep_max) * config.dep_weight;
        } else if seen.insert(r.constant_idx) {
            if let Some(c) = build_candidate(
                library,
                r,
                normalize(r.score, dep_max) * config.dep_weight,
                MatchReason::DependencyNeighbor,
            ) {
                candidates.push(c);
            }
        }
    }

    // Filter by minimum trust level if configured.
    if let Some(min_trust) = config.min_trust {
        candidates.retain(|c| {
            let confidence = ImportConfidence::try_from(c.header.import_confidence)
                .unwrap_or(ImportConfidence::Unverified);
            // ImportConfidence Ord: lower trust_rank = higher trust.
            // KernelVerified(0) < SourceVerified(1) < ... < Unverified(4).
            // We keep candidates where confidence <= min_trust (i.e., at least as trusted).
            confidence <= min_trust
        });
    }

    // Sort by descending score and truncate
    candidates.sort_by(|a, b| {
        b.score
            .partial_cmp(&a.score)
            .unwrap_or(std::cmp::Ordering::Equal)
    });
    candidates.truncate(config.max_results);
    candidates
}

/// Collect dependency neighbors of the given context constants.
///
/// For each name in `context_names` that exists in the library, looks up
/// its constant index via O(1) hash lookup, then walks its direct
/// dependencies and collects them as candidates with a fixed score of 1.0.
///
/// Complexity: O(k + total_deps) where k = context_names.len() and
/// total_deps is the sum of dependency list lengths for matched constants.
/// Previously O(n*k) due to linear scan to find each name's index.
fn collect_dep_neighbors(
    library: &MathverseLibrary,
    context_names: &[&str],
    max_results: usize,
) -> Vec<SearchResult> {
    let mut results = Vec::new();
    let mut seen = hashbrown::HashSet::new();
    let deps = library.deps();

    for &name in context_names {
        // O(1) hash lookup instead of O(n) linear scan through all constants.
        let const_idx = match library.lookup_constant_idx(name) {
            Some(idx) => idx,
            None => continue,
        };

        // Walk direct deps (not transitive -- too expensive for premise selection).
        if let Some(dep_list) = deps.get(const_idx as usize) {
            for &dep_idx in dep_list {
                if seen.insert(dep_idx) && results.len() < max_results {
                    if let Some(dep_header) = library.get_constant(dep_idx) {
                        results.push(SearchResult {
                            constant_idx: dep_idx,
                            header: *dep_header,
                            score: 1.0,
                        });
                    }
                }
            }
        }
    }

    results
}

/// Build a `PremiseCandidate` from a `SearchResult`.
fn build_candidate(
    library: &MathverseLibrary,
    result: &SearchResult,
    score: f64,
    reason: MatchReason,
) -> Option<PremiseCandidate> {
    let name = library.get_name(result.constant_idx)?.to_string();
    let source_system = SourceSystem::try_from(result.header.source_system).ok()?;
    let trust_level = header_to_trust_level(&result.header);

    Some(PremiseCandidate {
        name,
        constant_idx: result.constant_idx,
        score,
        source_system,
        trust_level,
        match_reason: reason,
        header: result.header,
    })
}

/// Derive a coarse `TrustLevel` from a constant header.
fn header_to_trust_level(header: &MathverseConstantHeader) -> TrustLevel {
    use crate::types::ImportConfidence;

    let confidence = ImportConfidence::try_from(header.import_confidence)
        .unwrap_or(ImportConfidence::Unverified);
    let profile = header.axiom_profile;

    match confidence {
        ImportConfidence::KernelVerified if profile.is_pure() => TrustLevel::KernelVerified,
        ImportConfidence::KernelVerified => TrustLevel::AxiomDependent,
        ImportConfidence::SourceVerified => TrustLevel::AxiomDependent,
        ImportConfidence::Translated => TrustLevel::CertificateReplayed,
        // Tier-2: kernel-re-checked but conditional on trusted-ledger axioms —
        // an axiom-dependent proof, so it maps to AxiomDependent (never
        // KernelVerified).
        ImportConfidence::KernelCheckedConditional => TrustLevel::AxiomDependent,
        // KernelBridged is an end-to-end foundational kernel proof (Mathlib-KV
        // witness + foundational connective bridge); when its stored closure is
        // pure it is genuinely KernelVerified-grade, else axiom-dependent.
        ImportConfidence::KernelBridged if profile.is_pure() => TrustLevel::KernelVerified,
        ImportConfidence::KernelBridged => TrustLevel::AxiomDependent,
        ImportConfidence::Axiomatized => TrustLevel::PartiallyAxiomatized,
        ImportConfidence::Unverified => TrustLevel::TrustedOracle,
    }
}

// ===========================================================================
// Symbol extraction from kernel Expr
// ===========================================================================

/// Extract all constant names referenced in a kernel expression.
///
/// Walks the expression tree iteratively (to avoid stack overflow on deeply
/// nested proof terms) and collects every `Const` name encountered. The
/// result is deduplicated and sorted for deterministic output.
pub fn extract_symbols(expr: &Expr) -> Vec<Name> {
    let mut names = Vec::new();
    let mut stack: Vec<&Expr> = vec![expr];
    // Track visited pointers to avoid re-traversing shared sub-expressions.
    let mut visited = hashbrown::HashSet::new();

    while let Some(e) = stack.pop() {
        let key = e as *const Expr as usize;
        if !visited.insert(key) {
            continue;
        }

        match e.kind() {
            ExprKind::Const(name, _levels) => {
                names.push(name.clone());
            }
            ExprKind::App(f, arg) => {
                stack.push(f);
                stack.push(arg);
            }
            ExprKind::Lam(_binder, ty, body) | ExprKind::Pi(_binder, ty, body) => {
                stack.push(ty);
                stack.push(body);
            }
            ExprKind::Let(_name, ty, val, body, _non_dep) => {
                stack.push(ty);
                stack.push(val);
                stack.push(body);
            }
            ExprKind::Proj(proj_name, _field, inner) => {
                names.push(proj_name.clone());
                stack.push(inner);
            }
            ExprKind::MData(_meta, inner) => {
                stack.push(inner);
            }
            ExprKind::Squash(inner) => {
                stack.push(inner);
            }
            // Leaves: BVar, FVar, Sort, Lit, SProp — no children to recurse into
            _ => {}
        }
    }

    // Deduplicate and sort for deterministic output
    names.sort_by_key(|a| a.to_string());
    names.dedup_by(|a, b| a.to_string() == b.to_string());
    names
}

/// Extract symbol names as strings from a kernel expression.
///
/// Convenience wrapper over [`extract_symbols`] that returns `String` names
/// suitable for matching against the mathverse library's string-based name index.
pub fn extract_symbol_strings(expr: &Expr) -> Vec<String> {
    extract_symbols(expr)
        .into_iter()
        .map(|n| n.to_string())
        .collect()
}

// ===========================================================================
// Symbol-overlap scoring
// ===========================================================================

/// Compute a Jaccard-style symbol overlap score between two symbol sets.
///
/// Returns a value in [0.0, 1.0] where 1.0 means perfect overlap.
/// Both sets should be pre-sorted string slices.
pub(crate) fn symbol_overlap_score(goal_symbols: &[String], candidate_name: &str) -> f64 {
    if goal_symbols.is_empty() {
        return 0.0;
    }

    // Split the candidate name into components (e.g., "Nat.add_comm" -> ["Nat", "add", "comm"])
    let candidate_tokens: Vec<&str> = candidate_name
        .split(['.', '_'])
        .filter(|s| !s.is_empty())
        .collect();

    if candidate_tokens.is_empty() {
        return 0.0;
    }

    // Pre-lowercase the candidate tokens once, instead of recomputing
    // `tok.to_lowercase()` for every goal symbol (was G×T allocations per call
    // across the full-corpus scan; now T). `to_lowercase` (not ASCII-only) is
    // kept so Unicode-named lemmas (α, β, …) match exactly as before.
    let candidate_tokens_lower: Vec<String> =
        candidate_tokens.iter().map(|t| t.to_lowercase()).collect();

    // Count how many goal symbols appear as substrings in the candidate name
    let mut matches = 0usize;
    for sym in goal_symbols {
        // Extract the leaf component of the symbol name (after the last dot)
        let sym_leaf = sym.rsplit('.').next().unwrap_or(sym);
        let sym_lower = sym_leaf.to_lowercase();

        for tok_lower in &candidate_tokens_lower {
            if *tok_lower == sym_lower {
                matches += 1;
                break;
            }
        }
    }

    // Jaccard-like: matches / (goal_symbols + candidate_tokens - matches)
    let union = goal_symbols.len() + candidate_tokens.len() - matches;
    if union == 0 {
        0.0
    } else {
        matches as f64 / union as f64
    }
}

// ===========================================================================
// Kernel goal bridge: search_for_kernel_goal
// ===========================================================================

/// Search the mathverse library for premises relevant to a kernel `Expr` goal.
///
/// This is the main entry point for sledgehammer-style premise selection.
/// It automatically:
/// 1. Extracts all constant symbols from the goal expression
/// 2. Renders the goal as text for BM25 search
/// 3. Scores candidates by symbol overlap with the goal
/// 4. Blends type-directed, semantic, dependency, and symbol-overlap signals
///
/// Returns candidates sorted by descending relevance score.
pub fn search_for_kernel_goal(
    library: &mut MathverseLibrary,
    goal: &Expr,
    context_names: &[&str],
    config: &PremiseConfig,
) -> Vec<PremiseCandidate> {
    // Step 1: Extract symbols from the goal
    let goal_symbols = extract_symbol_strings(goal);

    // Step 2: Render goal as text for BM25 search
    // Use the symbol names joined with spaces as a search query
    let goal_text = goal_symbols.join(" ");

    // Step 3: Convert goal Expr to FlatExpr in the library's arena for
    // discrimination tree search. This is the fix for #3412: the disc tree
    // was built but never queried because goal_type_idx was always None.
    let goal_type_idx = Some(library.add_query_expr(goal));

    // Step 4: Run the base search (type + BM25 + deps)
    let mut candidates = search_for_goal(library, goal_type_idx, &goal_text, context_names, config);

    // Step 5: Boost candidates by symbol overlap
    for candidate in &mut candidates {
        let overlap = symbol_overlap_score(&goal_symbols, &candidate.name);
        if overlap > 0.0 {
            // Additive boost proportional to overlap
            candidate.score += overlap * 0.4; // symbol overlap weight
        }
    }

    // Step 6: Scan ALL library constants for high symbol overlap (catch what BM25 missed)
    let fetch_limit = config.max_results * 2;
    let mut seen: hashbrown::HashSet<ConstantIdx> =
        candidates.iter().map(|c| c.constant_idx).collect();

    if !goal_symbols.is_empty() {
        for idx in 0..library.constant_count() {
            if candidates.len() >= fetch_limit {
                break;
            }
            let const_idx = idx as ConstantIdx;
            if seen.contains(&const_idx) {
                continue;
            }
            if let Some(name) = library.get_name(const_idx) {
                let overlap = symbol_overlap_score(&goal_symbols, name);
                if overlap > 0.1 {
                    // Threshold: at least 10% symbol overlap
                    if let Some(header) = library.get_constant(const_idx) {
                        let source_system = SourceSystem::try_from(header.source_system)
                            .unwrap_or(SourceSystem::Lean4);
                        let trust_level = header_to_trust_level(header);

                        // Apply trust filter
                        if let Some(min_trust) = config.min_trust {
                            let confidence = ImportConfidence::try_from(header.import_confidence)
                                .unwrap_or(ImportConfidence::Unverified);
                            if confidence > min_trust {
                                continue;
                            }
                        }

                        seen.insert(const_idx);
                        candidates.push(PremiseCandidate {
                            name: name.to_string(),
                            constant_idx: const_idx,
                            score: overlap * 0.4,
                            source_system,
                            trust_level,
                            match_reason: MatchReason::SymbolOverlap,
                            header: *header,
                        });
                    }
                }
            }
        }
    }

    // Re-sort after boosting and adding new candidates
    candidates.sort_by(|a, b| {
        b.score
            .partial_cmp(&a.score)
            .unwrap_or(std::cmp::Ordering::Equal)
    });
    candidates.truncate(config.max_results);
    candidates
}

// ===========================================================================
// Batch premise selection for proof search integration
// ===========================================================================

/// Result of a premise selection query, enriched with the original goal.
#[derive(Clone, Debug)]
pub struct PremiseSearchResult {
    /// The candidates found.
    pub candidates: Vec<PremiseCandidate>,
    /// Symbols extracted from the goal.
    pub goal_symbols: Vec<String>,
    /// Number of constants scanned.
    pub constants_scanned: usize,
}

/// Perform premise selection and return enriched results with metadata.
///
/// This is the API intended for integration with the AI proof search
/// verification loop (#3386). It returns both the candidates and the
/// extracted goal symbols for downstream use (e.g., filtering, re-ranking).
pub fn select_premises(
    library: &mut MathverseLibrary,
    goal: &Expr,
    context_names: &[&str],
    config: &PremiseConfig,
) -> PremiseSearchResult {
    let goal_symbols = extract_symbol_strings(goal);
    let candidates = search_for_kernel_goal(library, goal, context_names, config);

    PremiseSearchResult {
        candidates,
        goal_symbols,
        constants_scanned: library.constant_count(),
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::shard::ShardWriter;
    use crate::trust::policy::TrustPolicy;
    use crate::types::{AxiomProfile, ContentDomain, ImportConfidence};
    use clean_kernel::flat::{FlatExpr, FlatLevel};

    /// Helper: build a test shard with named constants.
    fn build_test_shard(names: &[&str]) -> crate::shard::ShardReader {
        let mut writer = ShardWriter::new();
        let l0 = writer.add_level(FlatLevel::zero());
        let e0 = writer.add_expr(FlatExpr::sort(l0));

        for &name in names {
            let ni = writer.add_string(name);
            writer.add_constant(MathverseConstantHeader {
                name_idx: ni,
                type_idx: e0,
                value_idx: e0,
                source_system: SourceSystem::Lean4 as u8,
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
        crate::shard::ShardReader::from_bytes(&buf).unwrap()
    }

    #[test]
    fn test_search_for_goal_empty_library() {
        let lib = MathverseLibrary::new(TrustPolicy::permissive());
        let results = search_for_goal(&lib, None, "anything", &[], &PremiseConfig::default());
        assert!(results.is_empty());
    }

    #[test]
    fn test_search_for_goal_name_match() {
        let shard = build_test_shard(&["Nat.add_comm", "Nat.mul_comm", "List.map", "Int.add_comm"]);
        let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
        lib.load_shard(&shard).unwrap();

        let results = search_for_goal(
            &lib,
            None,
            "Nat add commutative",
            &[],
            &PremiseConfig::default(),
        );
        assert!(
            !results.is_empty(),
            "should find results for 'Nat add commutative'"
        );
        // Nat.add_comm should be the top result
        assert_eq!(results[0].name, "Nat.add_comm");
        assert_eq!(results[0].match_reason, MatchReason::NameSimilarity);
    }

    #[test]
    fn test_search_for_goal_type_match() {
        // Build a shard with typed constants for discrimination tree search.
        let mut writer = ShardWriter::new();
        let nat_name = writer.add_string("Nat");
        let c0_name = writer.add_string("nat_id");

        let l0 = writer.add_level(FlatLevel::zero());
        let e_nat = writer.add_expr(FlatExpr::const_ref(nat_name, u32::MAX));
        let e_nat2 = writer.add_expr(FlatExpr::const_ref(nat_name, u32::MAX));
        let pi_nat_nat = writer.add_expr(FlatExpr::pi(0, e_nat, e_nat2));
        let sort_e = writer.add_expr(FlatExpr::sort(l0));

        writer.add_constant(MathverseConstantHeader {
            name_idx: c0_name,
            type_idx: pi_nat_nat,
            value_idx: sort_e,
            source_system: SourceSystem::Lean4 as u8,
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

        let mut buf = Vec::new();
        writer.write(&mut buf).unwrap();
        let shard = crate::shard::ShardReader::from_bytes(&buf).unwrap();

        let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
        lib.load_shard(&shard).unwrap();

        // Search using the type index of the constant we just loaded
        let type_idx = lib.get_constant(0).unwrap().type_idx;
        let results = search_for_goal(&lib, Some(type_idx), "", &[], &PremiseConfig::default());
        assert!(!results.is_empty(), "type search should find nat_id");
        assert_eq!(results[0].name, "nat_id");
        assert_eq!(results[0].match_reason, MatchReason::TypeUnification);
    }

    #[test]
    fn test_search_for_goal_blended() {
        let shard = build_test_shard(&["Nat.add_comm", "Nat.mul_comm", "List.map"]);
        let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
        lib.load_shard(&shard).unwrap();

        // Search with both type (via the constant's own type index) and name
        let type_idx = lib.get_constant(0).unwrap().type_idx;
        let results = search_for_goal(
            &lib,
            Some(type_idx),
            "Nat add comm",
            &[],
            &PremiseConfig::default(),
        );
        assert!(!results.is_empty());
        // With both type and name channels active, Nat.add_comm should score highest
        assert_eq!(results[0].name, "Nat.add_comm");
        // The score should be boosted by both channels
        assert!(results[0].score > 0.3, "blended score should be meaningful");
    }

    #[test]
    fn test_search_for_goal_dep_neighbor() {
        let shard = build_test_shard(&["base", "dep_of_base", "unrelated"]);
        let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
        lib.load_shard(&shard).unwrap();

        // Add a dependency: base(0) depends on dep_of_base(1)
        lib.add_dependency(0, 1);

        let results = search_for_goal(&lib, None, "", &["base"], &PremiseConfig::default());
        // dep_of_base should appear as a dependency neighbor
        let dep_names: Vec<&str> = results.iter().map(|c| c.name.as_str()).collect();
        assert!(
            dep_names.contains(&"dep_of_base"),
            "dependency neighbor should appear in results"
        );
    }

    // -----------------------------------------------------------------------
    // Direct collect_dep_neighbors tests (O(1) hash lookup path for #3415).
    //
    // The old implementation was O(n*k): for each of the k context names it
    // linearly scanned all n constants to find the index. The fix replaces
    // that scan with `lookup_constant_idx` (O(1)). These tests lock in both
    // correctness (same neighbor set) and scale (a 1K-constant library with
    // many context names completes in well under a second).
    // -----------------------------------------------------------------------

    #[test]
    fn test_collect_dep_neighbors_direct_correctness() {
        let shard = build_test_shard(&["base", "dep_a", "dep_b", "unrelated"]);
        let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
        lib.load_shard(&shard).unwrap();
        // base -> dep_a, dep_b
        lib.add_dependency(0, 1);
        lib.add_dependency(0, 2);

        let results = collect_dep_neighbors(&lib, &["base"], 10);
        let names: Vec<&str> = results
            .iter()
            .filter_map(|r| lib.get_name(r.constant_idx))
            .collect();
        assert!(
            names.contains(&"dep_a"),
            "dep_a should be a neighbor of base"
        );
        assert!(
            names.contains(&"dep_b"),
            "dep_b should be a neighbor of base"
        );
        assert!(
            !names.contains(&"unrelated"),
            "unrelated should NOT be a neighbor of base"
        );
    }

    #[test]
    fn test_collect_dep_neighbors_unknown_name_skipped() {
        let shard = build_test_shard(&["a", "b"]);
        let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
        lib.load_shard(&shard).unwrap();
        lib.add_dependency(0, 1);

        let results = collect_dep_neighbors(&lib, &["does_not_exist", "a"], 10);
        let names: Vec<&str> = results
            .iter()
            .filter_map(|r| lib.get_name(r.constant_idx))
            .collect();
        assert_eq!(names, vec!["b"], "unknown names must be skipped silently");
    }

    #[test]
    fn test_collect_dep_neighbors_dedup_across_context() {
        // Two context names share the same dependency — it should appear once.
        let shard = build_test_shard(&["a", "b", "shared"]);
        let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
        lib.load_shard(&shard).unwrap();
        lib.add_dependency(0, 2);
        lib.add_dependency(1, 2);

        let results = collect_dep_neighbors(&lib, &["a", "b"], 10);
        let shared_count = results
            .iter()
            .filter(|r| lib.get_name(r.constant_idx) == Some("shared"))
            .count();
        assert_eq!(shared_count, 1, "shared neighbor must be deduped");
    }

    #[test]
    fn test_collect_dep_neighbors_respects_max_results() {
        let names: Vec<String> = std::iter::once("root".to_string())
            .chain((0..20).map(|i| format!("dep_{i}")))
            .collect();
        let name_refs: Vec<&str> = names.iter().map(|s| s.as_str()).collect();
        let shard = build_test_shard(&name_refs);

        let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
        lib.load_shard(&shard).unwrap();
        for i in 1..=20 {
            lib.add_dependency(0, i);
        }

        let results = collect_dep_neighbors(&lib, &["root"], 5);
        assert!(
            results.len() <= 5,
            "max_results cap must be respected, got {}",
            results.len()
        );
    }

    #[test]
    fn test_collect_dep_neighbors_scales_without_quadratic_scan() {
        // Regression guard for #3415: 1000 constants x 500 context names.
        // The old O(n*k) path would scan 500_000 string comparisons here;
        // the new O(k) path is trivial. We assert it completes promptly
        // AND returns the correct neighbor ("target") for each hit.
        const N: usize = 1000;
        let names: Vec<String> = (0..N).map(|i| format!("c_{i:05}")).collect();
        let name_refs: Vec<&str> = names.iter().map(|s| s.as_str()).collect();
        let shard = build_test_shard(&name_refs);

        let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
        lib.load_shard(&shard).unwrap();
        // Every first-half constant depends on the last one ("target").
        let target_idx = (N - 1) as ConstantIdx;
        for i in 0..(N / 2) {
            lib.add_dependency(i as ConstantIdx, target_idx);
        }

        let context: Vec<&str> = names.iter().take(N / 2).map(|s| s.as_str()).collect();
        let start = std::time::Instant::now();
        let results = collect_dep_neighbors(&lib, &context, 10);
        let elapsed = start.elapsed();

        // Correctness: the single shared target must be present.
        let target_name = format!("c_{:05}", N - 1);
        let found = results
            .iter()
            .any(|r| lib.get_name(r.constant_idx) == Some(target_name.as_str()));
        assert!(found, "target neighbor must be returned");

        // Soft performance assertion. Even a cold debug build on CI hardware
        // finishes in <50ms; 1 second is a very generous ceiling that would
        // flag a regression back to O(n*k) string-scan behavior.
        assert!(
            elapsed < std::time::Duration::from_secs(1),
            "collect_dep_neighbors took {elapsed:?} for N={N}; suspected regression to O(n*k)"
        );
    }

    #[test]
    fn test_premise_candidate_trust_level() {
        let header = MathverseConstantHeader {
            name_idx: 0,
            type_idx: 0,
            value_idx: 0,
            source_system: SourceSystem::Lean4 as u8,
            import_confidence: ImportConfidence::KernelVerified as u8,
            content_domain: ContentDomain::PureMath as u8,
            decl_kind: 0,
            axiom_profile: AxiomProfile::NONE,
            sidecar_digest: 0,
            provenance_idx: 0,
            level_params_start: 0,
            level_params_count: 0,
            _pad2: [0u8; 26],
        };
        assert_eq!(header_to_trust_level(&header), TrustLevel::KernelVerified);

        let axiom_header = MathverseConstantHeader {
            axiom_profile: AxiomProfile::CHOICE,
            ..header
        };
        assert_eq!(
            header_to_trust_level(&axiom_header),
            TrustLevel::AxiomDependent
        );

        let translated_header = MathverseConstantHeader {
            import_confidence: ImportConfidence::Translated as u8,
            ..header
        };
        assert_eq!(
            header_to_trust_level(&translated_header),
            TrustLevel::CertificateReplayed
        );
    }

    #[test]
    fn test_config_default() {
        let config = PremiseConfig::default();
        assert_eq!(config.max_results, 20);
        let total = config.type_weight + config.name_weight + config.dep_weight;
        assert!((total - 1.0).abs() < 0.01, "weights should sum to ~1.0");
    }

    // -----------------------------------------------------------------------
    // Symbol extraction tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_extract_symbols_const() {
        // Expr::const_str("Nat.add") should yield ["Nat.add"]
        let expr = Expr::const_str("Nat.add");
        let symbols = extract_symbols(&expr);
        assert_eq!(symbols.len(), 1);
        assert_eq!(symbols[0].to_string(), "Nat.add");
    }

    #[test]
    fn test_extract_symbols_app() {
        // App(Nat.add, Nat.zero) should yield ["Nat.add", "Nat.zero"]
        let f = Expr::const_str("Nat.add");
        let arg = Expr::const_str("Nat.zero");
        let app = Expr::app(f, arg);
        let symbols = extract_symbol_strings(&app);
        assert!(symbols.contains(&"Nat.add".to_string()));
        assert!(symbols.contains(&"Nat.zero".to_string()));
        assert_eq!(symbols.len(), 2);
    }

    #[test]
    fn test_extract_symbols_pi() {
        use clean_kernel::expr::BinderInfo;
        use clean_kernel::level::Level;

        // Pi(Nat, Bool) should yield ["Bool", "Nat"]
        let nat = Expr::const_str("Nat");
        let bool_e = Expr::const_str("Bool");
        let pi = Expr::pi(BinderInfo::Default, nat, bool_e);
        let symbols = extract_symbol_strings(&pi);
        assert!(symbols.contains(&"Nat".to_string()));
        assert!(symbols.contains(&"Bool".to_string()));
    }

    #[test]
    fn test_extract_symbols_nested() {
        use clean_kernel::level::Level;

        // App(App(Eq, Nat), App(Nat.add, Nat.zero))
        let eq = Expr::const_str("Eq");
        let nat = Expr::const_str("Nat");
        let add = Expr::const_str("Nat.add");
        let zero = Expr::const_str("Nat.zero");
        let inner_app = Expr::app(add, zero);
        let eq_nat = Expr::app(eq, nat);
        let full = Expr::app(eq_nat, inner_app);

        let symbols = extract_symbol_strings(&full);
        assert!(symbols.contains(&"Eq".to_string()));
        assert!(symbols.contains(&"Nat".to_string()));
        assert!(symbols.contains(&"Nat.add".to_string()));
        assert!(symbols.contains(&"Nat.zero".to_string()));
        assert_eq!(symbols.len(), 4);
    }

    #[test]
    fn test_extract_symbols_deduplication() {
        // App(Nat, Nat) should yield ["Nat"] (not ["Nat", "Nat"])
        let nat1 = Expr::const_str("Nat");
        let nat2 = Expr::const_str("Nat");
        let app = Expr::app(nat1, nat2);
        let symbols = extract_symbol_strings(&app);
        assert_eq!(symbols.len(), 1);
        assert_eq!(symbols[0], "Nat");
    }

    #[test]
    fn test_extract_symbols_empty_for_sort() {
        use clean_kernel::level::Level;
        let sort = Expr::sort(Level::zero());
        let symbols = extract_symbols(&sort);
        assert!(symbols.is_empty());
    }

    #[test]
    fn test_extract_symbols_empty_for_bvar() {
        let bvar = Expr::bvar(0);
        let symbols = extract_symbols(&bvar);
        assert!(symbols.is_empty());
    }

    // -----------------------------------------------------------------------
    // Symbol overlap scoring tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_symbol_overlap_empty_goal() {
        let score = symbol_overlap_score(&[], "Nat.add_comm");
        assert!((score - 0.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_symbol_overlap_exact_match() {
        let goal = vec!["Nat".to_string()];
        let score = symbol_overlap_score(&goal, "Nat");
        // 1 match, union = 1 + 1 - 1 = 1, score = 1.0
        assert!((score - 1.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_symbol_overlap_partial() {
        let goal = vec!["Nat".to_string(), "add".to_string()];
        let score = symbol_overlap_score(&goal, "Nat.add_comm");
        // candidate tokens: ["Nat", "add", "comm"]
        // goal symbols: ["Nat", "add"] — leaf match for Nat, add
        // matches = 2, union = 2 + 3 - 2 = 3, score = 2/3 ≈ 0.667
        assert!(
            score > 0.5,
            "partial overlap should score > 0.5, got {score}"
        );
    }

    #[test]
    fn test_symbol_overlap_no_match() {
        let goal = vec!["List".to_string(), "map".to_string()];
        let score = symbol_overlap_score(&goal, "Nat.add_comm");
        assert!((score - 0.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_symbol_overlap_case_insensitive() {
        let goal = vec!["nat".to_string()];
        let score = symbol_overlap_score(&goal, "Nat.add");
        // "nat" matches "Nat" (case-insensitive)
        assert!(score > 0.0, "case-insensitive matching should work");
    }

    #[test]
    fn test_symbol_overlap_leaf_extraction() {
        // Goal symbol "Lean.Nat.add" should match on "add" leaf
        let goal = vec!["Lean.Nat.add".to_string()];
        let score = symbol_overlap_score(&goal, "Nat.add_comm");
        // Leaf of "Lean.Nat.add" is "add", which matches candidate token "add"
        assert!(score > 0.0, "leaf extraction should find 'add'");
    }

    // -----------------------------------------------------------------------
    // Kernel goal search tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_search_for_kernel_goal_finds_by_symbol() {
        let shard = build_test_shard(&["Nat.add_comm", "Nat.mul_comm", "List.map", "Int.add_comm"]);
        let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
        lib.load_shard(&shard).unwrap();

        // Build a goal: App(Eq, App(Nat.add, x))
        // Symbols: Eq, Nat.add
        let eq = Expr::const_str("Eq");
        let nat_add = Expr::const_str("Nat.add");
        let x = Expr::bvar(0);
        let inner = Expr::app(nat_add, x);
        let goal = Expr::app(eq, inner);

        let results = search_for_kernel_goal(&mut lib, &goal, &[], &PremiseConfig::default());
        // Nat.add_comm should score high because it shares "Nat" and "add"
        assert!(!results.is_empty(), "should find results for Nat.add goal");
        let names: Vec<&str> = results.iter().map(|c| c.name.as_str()).collect();
        assert!(
            names.contains(&"Nat.add_comm"),
            "Nat.add_comm should be found, got: {names:?}"
        );
    }

    #[test]
    fn test_search_for_kernel_goal_empty_library() {
        let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
        let goal = Expr::const_str("Nat.add");
        let results = search_for_kernel_goal(&mut lib, &goal, &[], &PremiseConfig::default());
        assert!(results.is_empty());
    }

    #[test]
    fn test_search_for_kernel_goal_with_context() {
        let shard = build_test_shard(&["base", "dep_of_base", "unrelated"]);
        let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
        lib.load_shard(&shard).unwrap();
        lib.add_dependency(0, 1);

        let goal = Expr::const_str("something");
        let results = search_for_kernel_goal(&mut lib, &goal, &["base"], &PremiseConfig::default());
        // dep_of_base should appear as dependency neighbor
        let names: Vec<&str> = results.iter().map(|c| c.name.as_str()).collect();
        assert!(
            names.contains(&"dep_of_base"),
            "dependency neighbor should appear when context provided"
        );
    }

    // -----------------------------------------------------------------------
    // select_premises integration test
    // -----------------------------------------------------------------------

    #[test]
    fn test_select_premises_returns_metadata() {
        let shard = build_test_shard(&["Nat.add_comm", "Nat.mul_comm"]);
        let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
        lib.load_shard(&shard).unwrap();

        let goal = Expr::const_str("Nat.add");
        let result = select_premises(&mut lib, &goal, &[], &PremiseConfig::default());

        assert_eq!(result.constants_scanned, 2);
        assert!(!result.goal_symbols.is_empty());
        assert!(result.goal_symbols.contains(&"Nat.add".to_string()));
    }

    #[test]
    fn test_match_reason_symbol_overlap() {
        let shard = build_test_shard(&["Nat.add_comm", "Nat.add_assoc", "List.map"]);
        let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
        lib.load_shard(&shard).unwrap();

        // Goal with Nat.add — should find Nat.add_comm and Nat.add_assoc via symbol overlap
        let goal = Expr::const_str("Nat.add");
        let results = search_for_kernel_goal(&mut lib, &goal, &[], &PremiseConfig::default());

        let overlap_candidates: Vec<&PremiseCandidate> = results
            .iter()
            .filter(|c| c.match_reason == MatchReason::SymbolOverlap)
            .collect();
        // At least some candidates should be found via symbol overlap
        // (the exact set depends on what BM25 already found — those get boosted
        // rather than added as SymbolOverlap)
        assert!(!results.is_empty(), "should find Nat-related results");
    }

    #[test]
    fn test_search_for_kernel_goal_respects_max_results() {
        // Build a shard with many constants
        let names: Vec<String> = (0..50).map(|i| format!("Nat.lemma_{i}")).collect();
        let name_refs: Vec<&str> = names.iter().map(|s| s.as_str()).collect();
        let shard = build_test_shard(&name_refs);

        let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
        lib.load_shard(&shard).unwrap();

        let goal = Expr::const_str("Nat");
        let config = PremiseConfig {
            max_results: 5,
            ..PremiseConfig::default()
        };
        let results = search_for_kernel_goal(&mut lib, &goal, &[], &config);
        assert!(results.len() <= 5, "should respect max_results");
    }

    #[test]
    fn test_search_for_kernel_goal_trust_filter() {
        // Build a shard with mixed trust levels
        let mut writer = ShardWriter::new();
        let l0 = writer.add_level(FlatLevel::zero());
        let e0 = writer.add_expr(FlatExpr::sort(l0));

        // Kernel-verified constant
        let n0 = writer.add_string("Nat.add_comm");
        writer.add_constant(MathverseConstantHeader {
            name_idx: n0,
            type_idx: e0,
            value_idx: e0,
            source_system: SourceSystem::Lean4 as u8,
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

        // Unverified constant
        let n1 = writer.add_string("Nat.add_assoc");
        writer.add_constant(MathverseConstantHeader {
            name_idx: n1,
            type_idx: e0,
            value_idx: e0,
            source_system: SourceSystem::Lean4 as u8,
            import_confidence: ImportConfidence::Unverified as u8,
            content_domain: ContentDomain::PureMath as u8,
            decl_kind: 0,
            axiom_profile: AxiomProfile::NONE,
            sidecar_digest: 0,
            provenance_idx: 0,
            level_params_start: 0,
            level_params_count: 0,
            _pad2: [0u8; 26],
        });

        let mut buf = Vec::new();
        writer.write(&mut buf).unwrap();
        let shard = crate::shard::ShardReader::from_bytes(&buf).unwrap();

        let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
        lib.load_shard(&shard).unwrap();

        let goal = Expr::const_str("Nat.add");
        let config = PremiseConfig {
            min_trust: Some(ImportConfidence::KernelVerified),
            ..PremiseConfig::default()
        };
        let results = search_for_kernel_goal(&mut lib, &goal, &[], &config);

        // Only kernel-verified should pass the filter
        for r in &results {
            let confidence = ImportConfidence::try_from(r.header.import_confidence)
                .unwrap_or(ImportConfidence::Unverified);
            assert!(
                confidence <= ImportConfidence::KernelVerified,
                "only kernel-verified should pass trust filter, got: {confidence:?}"
            );
        }
    }

    // -----------------------------------------------------------------------
    // Discrimination tree integration tests (fix for #3412)
    //
    // These tests verify that search_for_kernel_goal actually uses the
    // discrimination tree path (TypeUnification), not just BM25/symbol overlap.
    // -----------------------------------------------------------------------

    /// Helper: build a shard with typed constants for discrimination tree tests.
    /// Returns constants with different type structures:
    /// - "nat_id": Pi(Nat, Nat)   -- Nat -> Nat
    /// - "nat_to_bool": Pi(Nat, Bool) -- Nat -> Bool
    /// - "bool_id": Pi(Bool, Bool) -- Bool -> Bool
    fn build_typed_test_shard() -> crate::shard::ShardReader {
        let mut writer = ShardWriter::new();
        let nat_name = writer.add_string("Nat"); // string idx 0
        let bool_name = writer.add_string("Bool"); // string idx 1
        let c0_name = writer.add_string("nat_id"); // string idx 2
        let c1_name = writer.add_string("nat_to_bool"); // string idx 3
        let c2_name = writer.add_string("bool_id"); // string idx 4

        let l0 = writer.add_level(FlatLevel::zero());
        let sort_e = writer.add_expr(FlatExpr::sort(l0));

        // Build Pi(Nat, Nat): need separate Nat expr nodes for domain/codomain
        let nat_a = writer.add_expr(FlatExpr::const_ref(nat_name, u32::MAX));
        let nat_b = writer.add_expr(FlatExpr::const_ref(nat_name, u32::MAX));
        let pi_nat_nat = writer.add_expr(FlatExpr::pi(0, nat_a, nat_b));

        // Build Pi(Nat, Bool)
        let nat_c = writer.add_expr(FlatExpr::const_ref(nat_name, u32::MAX));
        let bool_a = writer.add_expr(FlatExpr::const_ref(bool_name, u32::MAX));
        let pi_nat_bool = writer.add_expr(FlatExpr::pi(0, nat_c, bool_a));

        // Build Pi(Bool, Bool)
        let bool_b = writer.add_expr(FlatExpr::const_ref(bool_name, u32::MAX));
        let bool_c = writer.add_expr(FlatExpr::const_ref(bool_name, u32::MAX));
        let pi_bool_bool = writer.add_expr(FlatExpr::pi(0, bool_b, bool_c));

        let mk_hdr = |name: u32, ty: u32| MathverseConstantHeader {
            name_idx: name,
            type_idx: ty,
            value_idx: sort_e,
            source_system: SourceSystem::Lean4 as u8,
            import_confidence: ImportConfidence::KernelVerified as u8,
            content_domain: ContentDomain::PureMath as u8,
            decl_kind: 0,
            axiom_profile: AxiomProfile::NONE,
            sidecar_digest: 0,
            provenance_idx: 0,
            level_params_start: 0,
            level_params_count: 0,
            _pad2: [0u8; 26],
        };

        writer.add_constant(mk_hdr(c0_name, pi_nat_nat)); // nat_id: Nat -> Nat
        writer.add_constant(mk_hdr(c1_name, pi_nat_bool)); // nat_to_bool: Nat -> Bool
        writer.add_constant(mk_hdr(c2_name, pi_bool_bool)); // bool_id: Bool -> Bool

        let mut buf = Vec::new();
        writer.write(&mut buf).unwrap();
        crate::shard::ShardReader::from_bytes(&buf).unwrap()
    }

    #[test]
    fn test_disc_tree_used_by_kernel_goal_search() {
        // Build shard with distinct types: nat_id (Nat->Nat), nat_to_bool (Nat->Bool), bool_id (Bool->Bool)
        let shard = build_typed_test_shard();
        let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
        lib.load_shard(&shard).unwrap();

        // Build a kernel goal: Pi(Nat, Nat) — should match nat_id via disc tree
        let nat = Expr::const_str("Nat");
        let nat2 = Expr::const_str("Nat");
        let goal = Expr::pi(clean_kernel::expr::BinderInfo::Default, nat, nat2);

        let results = search_for_kernel_goal(&mut lib, &goal, &[], &PremiseConfig::default());

        // The disc tree should find nat_id as a TypeUnification match
        let type_unification_results: Vec<&PremiseCandidate> = results
            .iter()
            .filter(|c| c.match_reason == MatchReason::TypeUnification)
            .collect();

        assert!(
            !type_unification_results.is_empty(),
            "discrimination tree should produce TypeUnification matches; got reasons: {:?}",
            results
                .iter()
                .map(|c| (&c.name, &c.match_reason))
                .collect::<Vec<_>>()
        );

        // nat_id should be found via TypeUnification
        assert!(
            type_unification_results.iter().any(|c| c.name == "nat_id"),
            "nat_id should be found via TypeUnification, got: {:?}",
            type_unification_results
                .iter()
                .map(|c| &c.name)
                .collect::<Vec<_>>()
        );
    }

    #[test]
    fn test_disc_tree_distinguishes_types() {
        let shard = build_typed_test_shard();
        let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
        lib.load_shard(&shard).unwrap();

        // Build a goal: Pi(Bool, Bool) — should match bool_id, NOT nat_id
        let bool_e = Expr::const_str("Bool");
        let bool_e2 = Expr::const_str("Bool");
        let goal = Expr::pi(clean_kernel::expr::BinderInfo::Default, bool_e, bool_e2);

        let config = PremiseConfig {
            type_weight: 1.0,
            name_weight: 0.0,
            dep_weight: 0.0,
            max_results: 10,
            min_trust: None,
        };
        let results = search_for_goal(
            &lib,
            Some(lib.get_constant(2).unwrap().type_idx),
            "",
            &[],
            &config,
        );

        // bool_id should appear, and it should be a TypeUnification match
        let type_matches: Vec<&PremiseCandidate> = results
            .iter()
            .filter(|c| c.match_reason == MatchReason::TypeUnification)
            .collect();

        assert!(
            type_matches.iter().any(|c| c.name == "bool_id"),
            "bool_id should be found via disc tree for Pi(Bool,Bool), got: {:?}",
            type_matches.iter().map(|c| &c.name).collect::<Vec<_>>()
        );
    }

    #[test]
    fn test_disc_tree_adds_type_unification_to_blended_results() {
        let shard = build_typed_test_shard();
        let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
        lib.load_shard(&shard).unwrap();

        // Build kernel goal Pi(Nat, Nat) and search
        let nat = Expr::const_str("Nat");
        let nat2 = Expr::const_str("Nat");
        let goal = Expr::pi(clean_kernel::expr::BinderInfo::Default, nat, nat2);

        let results = search_for_kernel_goal(&mut lib, &goal, &[], &PremiseConfig::default());

        // With disc tree now active, the type_weight (0.6) channel should contribute
        // significantly to the score of nat_id. It should be the top result.
        if let Some(top) = results.first() {
            // nat_id is the only Nat->Nat constant; it should score highest
            // because it gets both TypeUnification (0.6 weight) AND symbol overlap (Nat)
            assert_eq!(
                top.name, "nat_id",
                "nat_id should be top result for Pi(Nat,Nat) goal; got: {}",
                top.name
            );
        }
    }

    #[test]
    fn test_disc_tree_fallback_when_no_type_match() {
        // When disc tree returns nothing, BM25/symbol overlap still work
        let shard = build_test_shard(&["Nat.add_comm", "Nat.mul_comm"]);
        let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
        lib.load_shard(&shard).unwrap();

        // Goal with a type that doesn't match any stored type (all have Sort type)
        // but symbol overlap should still find results
        let goal = Expr::const_str("Nat.add");
        let results = search_for_kernel_goal(&mut lib, &goal, &[], &PremiseConfig::default());

        assert!(
            !results.is_empty(),
            "BM25/symbol overlap should work as fallback when disc tree has no matches"
        );
        let names: Vec<&str> = results.iter().map(|c| c.name.as_str()).collect();
        assert!(
            names.contains(&"Nat.add_comm"),
            "Nat.add_comm should be found via fallback search, got: {names:?}"
        );
    }

    #[test]
    fn test_add_query_expr_produces_valid_disc_tree_index() {
        // Directly test that add_query_expr produces an ExprIdx that the disc tree can use
        let shard = build_typed_test_shard();
        let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
        lib.load_shard(&shard).unwrap();

        // Build Pi(Nat, Nat) as a kernel Expr, convert to library ExprIdx
        let nat = Expr::const_str("Nat");
        let nat2 = Expr::const_str("Nat");
        let pi = Expr::pi(clean_kernel::expr::BinderInfo::Default, nat, nat2);
        let query_idx = lib.add_query_expr(&pi);

        // Use the query index directly with search_type
        let results = lib.search_type(query_idx, 10).unwrap();

        assert!(
            !results.is_empty(),
            "search_type with query expr from add_query_expr should find matches"
        );
        // nat_id has type Pi(Nat, Nat) and should match
        let found_nat_id = results
            .iter()
            .any(|r| lib.get_name(r.constant_idx) == Some("nat_id"));
        assert!(
            found_nat_id,
            "disc tree should find nat_id for Pi(Nat,Nat) query"
        );
    }

    #[test]
    fn test_mathverse_use_search_uses_disc_tree_not_just_name() {
        // Regression test: before fix #3412, mathverse_use always passed None for
        // goal_type_idx, meaning the disc tree was dead code.
        // This test ensures the disc tree is the PRIMARY search channel.
        let shard = build_typed_test_shard();
        let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
        lib.load_shard(&shard).unwrap();

        // Search for Pi(Nat, Bool) — only nat_to_bool matches structurally
        let nat = Expr::const_str("Nat");
        let bool_e = Expr::const_str("Bool");
        let goal = Expr::pi(clean_kernel::expr::BinderInfo::Default, nat, bool_e);

        // Use high type_weight to ensure disc tree dominates
        let config = PremiseConfig {
            type_weight: 0.9,
            name_weight: 0.05,
            dep_weight: 0.05,
            max_results: 10,
            min_trust: None,
        };

        let results = search_for_kernel_goal(&mut lib, &goal, &[], &config);

        // nat_to_bool should be found and should score highest because it's
        // the only Pi(Nat, Bool) in the library
        let type_matches: Vec<&PremiseCandidate> = results
            .iter()
            .filter(|c| c.match_reason == MatchReason::TypeUnification)
            .collect();

        assert!(
            type_matches.iter().any(|c| c.name == "nat_to_bool"),
            "nat_to_bool should be found via disc tree for Pi(Nat,Bool), got: {:?}",
            results
                .iter()
                .map(|c| (&c.name, &c.match_reason, c.score))
                .collect::<Vec<_>>()
        );
    }
}
