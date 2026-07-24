// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Proof forest: per-term parent pointer forest for precise E-graph explanations.
//!
//! Reference: Nieuwenhuis & Oliveras, "Proof-Producing Congruence Closure"
//! (RTA 2005). Also implemented in z3 (`theory_eq.cpp`) and the `egg` crate.

use crate::cdcl::Lit;
use crate::smt::TermId;
use clean_kernel::FVarId;
use std::collections::{HashMap, HashSet};

/// Precise reason why proof-forest explanation failed.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ExplainFailure {
    /// Recursive congruence explanation exceeded the recursion guard.
    RecursionLimit,
    /// Parent-pointer traversal exceeded the forest-depth guard.
    ForestDepthLimit,
    /// The two terms do not share a common ancestor in the forest.
    DisconnectedTerms,
    /// A parent chain terminated before reaching the computed ancestor.
    BrokenAncestorPath,
    /// A congruence edge referenced an argument pair that could not be explained.
    CongruenceArgumentUnexplained,
}

/// Union reason in the E-graph (for proof reconstruction)
#[derive(Debug, Clone, PartialEq)]
pub enum UnionReason {
    /// Direct equality assertion with proof
    Asserted {
        /// The hypothesis providing the equality
        hypothesis: Option<FVarId>,
        /// LHS term
        lhs: TermId,
        /// RHS term
        rhs: TermId,
    },
    /// Congruence: two terms are equal because their arguments are equal
    Congruence {
        /// Function symbol
        func: String,
        /// E-class IDs of the two function applications
        #[cfg_attr(not(test), allow(dead_code))]
        // test-only trace introspection in non-test builds
        app1: u32,
        #[cfg_attr(not(test), allow(dead_code))]
        // test-only trace introspection in non-test builds
        app2: u32,
        /// Proofs that corresponding arguments are equal
        arg_reasons: Vec<u32>, // Indices into the proof trace
    },
}

/// Reason for a parent pointer edge in the proof forest.
///
/// Lighter-weight than `UnionReason` — only stores what's needed for
/// explanation extraction (the SAT literal or congruence arg pairs).
#[derive(Debug, Clone)]
pub enum ForestReason {
    /// Direct equality assertion. Carries the SAT literal that caused it.
    Asserted(Lit),
    /// Congruence: the two terms are equal because corresponding arguments are equal.
    /// Carries the argument term pairs for recursive explanation.
    Congruence(Vec<(TermId, TermId)>),
}

/// Maximum depth for parent pointer traversal per call. Guards against
/// infinite loops from corrupted parent pointer state.
const MAX_FOREST_DEPTH: usize = 10_000;

/// Maximum recursion depth for explain → collect_reasons → explain chain.
/// Guards against stack overflow from deeply nested congruence chains
/// (e.g., f^n(a) = f^n(b) with n levels of nesting).
const MAX_EXPLAIN_RECURSION: usize = 100;

/// Per-term parent pointer forest for precise E-graph explanations.
///
/// Each merge records a directed edge from one term's root to another,
/// enabling NCA-based explanation extraction that is immune to
/// post-merge canonical E-class ID changes.
#[derive(Debug, Clone)]
pub struct ProofForest {
    /// parent[term_id] = (parent_term_id, reason, decision_level)
    /// Root terms have no entry (absence = root).
    parent: HashMap<TermId, (TermId, ForestReason, u32)>,
    /// Journal for backtracking: entries added per decision level.
    /// trail[level] = list of TermIds whose parent pointer was set at that level.
    trail: Vec<Vec<TermId>>,
}

impl ProofForest {
    /// Create a new empty proof forest.
    pub fn new() -> Self {
        ProofForest {
            parent: HashMap::new(),
            trail: vec![Vec::new()], // Level 0 trail
        }
    }

    /// Record a merge between t1 and t2 with the given reason at the given level.
    ///
    /// Sets `parent[root2] = (t1, reason, level)` — linking root of t2's tree
    /// to the original term t1 (NOT root1). This preserves intermediate chain
    /// information so NCA traversal finds all transitive reasoning steps.
    ///
    /// If t1 and t2 are already in the same tree (same root), this is a no-op.
    pub fn record_merge(&mut self, t1: TermId, t2: TermId, reason: ForestReason, level: u32) {
        let root1 = self.find_root(t1);
        let root2 = self.find_root(t2);
        if root1 != root2 {
            // Link root2 → t1 (not root1) to preserve intermediate edges.
            // This ensures explain() traverses through all intermediate terms
            // in transitive chains, collecting all needed SAT literals.
            self.parent.insert(root2, (t1, reason, level));
            self.trail_entry(level, root2);
        }
    }

    /// Extract the precise set of asserted SAT literals explaining
    /// why t1 and t2 are in the same equivalence class.
    ///
    /// Algorithm: Nearest Common Ancestor (NCA) traversal.
    /// 1. Walk from t1 to root, collecting path P1
    /// 2. Walk from t2 to root, find first node also in P1 (= NCA)
    /// 3. Collect reasons along P1[t1..NCA] and P2[t2..NCA]
    /// 4. For Congruence reasons, recursively explain each arg pair
    ///
    /// Returns a typed failure when the forest cannot produce a complete path
    /// so the caller can fall back to a conservative explanation.
    pub fn explain(&self, t1: TermId, t2: TermId) -> Result<Vec<Lit>, ExplainFailure> {
        self.explain_depth(t1, t2, 0)
    }

    /// Internal explain with recursion depth tracking.
    fn explain_depth(
        &self,
        t1: TermId,
        t2: TermId,
        depth: usize,
    ) -> Result<Vec<Lit>, ExplainFailure> {
        if depth > MAX_EXPLAIN_RECURSION {
            return Err(ExplainFailure::RecursionLimit);
        }
        if t1 == t2 {
            return Ok(Vec::new());
        }

        // Walk from t1 to root, collecting the path (with depth protection)
        let mut path1_set: HashSet<TermId> = HashSet::new();
        let mut current = t1;
        path1_set.insert(current);
        let mut steps = 0;
        while let Some(&(parent, _, _)) = self.parent.get(&current) {
            steps += 1;
            if steps > MAX_FOREST_DEPTH {
                return Err(ExplainFailure::ForestDepthLimit);
            }
            current = parent;
            path1_set.insert(current);
        }

        // Walk from t2 toward root, find NCA (first node in path1_set)
        current = t2;
        let nca = if path1_set.contains(&current) {
            current
        } else {
            let mut found = None;
            steps = 0;
            while let Some(&(parent, _, _)) = self.parent.get(&current) {
                steps += 1;
                if steps > MAX_FOREST_DEPTH {
                    return Err(ExplainFailure::ForestDepthLimit);
                }
                current = parent;
                if path1_set.contains(&current) {
                    found = Some(current);
                    break;
                }
            }
            found.ok_or(ExplainFailure::DisconnectedTerms)?
        };

        // Collect reasons from t1 to NCA and t2 to NCA.
        // If either path contains an unexplainable congruence arg pair,
        // return a typed failure so the caller can fall back conservatively.
        let mut lits = Vec::new();
        self.collect_reasons_to_ancestor(t1, nca, &mut lits, depth)?;
        self.collect_reasons_to_ancestor(t2, nca, &mut lits, depth)?;

        // Deduplicate
        let dedup_set: HashSet<Lit> = lits.drain(..).collect();
        lits.extend(dedup_set);

        Ok(lits)
    }

    /// Collect all asserted SAT literals along the path from `term` to `ancestor`.
    /// For Congruence reasons, recursively explains each argument pair.
    ///
    /// Returns a typed failure if any congruence arg pair cannot be explained,
    /// since partial explanations are unsound (missing lits → invalid learned clauses).
    fn collect_reasons_to_ancestor(
        &self,
        term: TermId,
        ancestor: TermId,
        lits: &mut Vec<Lit>,
        depth: usize,
    ) -> Result<(), ExplainFailure> {
        let mut current = term;
        let mut steps = 0;
        while current != ancestor {
            steps += 1;
            if steps > MAX_FOREST_DEPTH {
                return Err(ExplainFailure::ForestDepthLimit);
            }
            if let Some(&(parent, ref reason, _)) = self.parent.get(&current) {
                match reason {
                    ForestReason::Asserted(lit) => {
                        lits.push(*lit);
                    }
                    ForestReason::Congruence(arg_pairs) => {
                        // Recursively explain each argument pair.
                        // ALL pairs must be explainable — partial success produces
                        // incomplete (unsound) explanations.
                        for &(a, b) in arg_pairs {
                            let sub_lits = match self.explain_depth(a, b, depth + 1) {
                                Ok(sub_lits) => sub_lits,
                                Err(
                                    reason @ (ExplainFailure::RecursionLimit
                                    | ExplainFailure::ForestDepthLimit),
                                ) => return Err(reason),
                                Err(_) => {
                                    return Err(ExplainFailure::CongruenceArgumentUnexplained)
                                }
                            };
                            lits.extend(sub_lits);
                        }
                    }
                }
                current = parent;
            } else {
                // current is a root but not the ancestor — NCA may be wrong
                // or forest state inconsistent. Return a typed failure to force
                // fallback to conservative explanation rather than silently
                // returning incomplete (unsound) literals.
                return Err(ExplainFailure::BrokenAncestorPath);
            }
        }
        Ok(())
    }

    /// Backtrack: undo all parent pointer changes beyond target level.
    pub fn backtrack(&mut self, target_level: u32) {
        while self.trail.len() > target_level as usize + 1 {
            if let Some(entries) = self.trail.pop() {
                for term in entries {
                    self.parent.remove(&term);
                }
            }
        }
    }

    /// Find the root of a term in the proof forest.
    /// A term is a root if it has no entry in the parent map.
    /// Returns `term` itself if depth limit is exceeded (treats it as a root).
    fn find_root(&self, term: TermId) -> TermId {
        let mut current = term;
        let mut steps = 0;
        while let Some(&(parent, _, _)) = self.parent.get(&current) {
            steps += 1;
            if steps > MAX_FOREST_DEPTH {
                break; // Depth exceeded — treat current as root
            }
            current = parent;
        }
        current
    }

    /// Record a trail entry for backtracking.
    fn trail_entry(&mut self, level: u32, term: TermId) {
        while self.trail.len() <= level as usize {
            self.trail.push(Vec::new());
        }
        self.trail[level as usize].push(term);
    }
}

impl Default for ProofForest {
    fn default() -> Self {
        Self::new()
    }
}
