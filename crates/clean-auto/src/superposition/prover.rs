// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Superposition prover: given-clause loop, simplification, and inference rules.

use super::{
    match_terms_frozen, Clause, Inference, Literal, SelectionStrategy, Substitution, TermOrdering,
    KBO,
};
use std::cmp::Ordering;
use std::collections::{BinaryHeap, HashMap, HashSet};
use std::ops::ControlFlow;
use std::time::Instant;

/// A wrapper for clause priority queue ordering
pub(super) struct PrioritizedClause {
    pub(super) clause: Clause,
    pub(super) priority: i64,
}

impl PartialEq for PrioritizedClause {
    fn eq(&self, other: &Self) -> bool {
        self.priority == other.priority
    }
}

impl Eq for PrioritizedClause {}

impl PartialOrd for PrioritizedClause {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for PrioritizedClause {
    fn cmp(&self, other: &Self) -> Ordering {
        // Reverse ordering for min-heap behavior
        other.priority.cmp(&self.priority)
    }
}

/// Superposition prover
pub struct SuperpositionProver {
    /// Term ordering
    pub(super) ordering: Box<dyn TermOrdering>,
    /// Processed clauses (active set)
    pub(super) processed: Vec<Clause>,
    /// Index from clause ID to position in `processed` Vec for O(1) lookup.
    /// Maintained on push and swap_remove to stay in sync (#1820).
    pub(super) processed_index: HashMap<u64, usize>,
    /// Unprocessed clauses (passive set)
    pub(super) unprocessed: BinaryHeap<PrioritizedClause>,
    /// Clause ID counter
    pub(super) next_id: u64,
    /// Archive of removed/replaced clauses for proof trace completeness (#2278).
    /// Stores clauses removed by backward_simplify and originals replaced by
    /// forward demodulation, keyed by clause ID.
    pub(super) clause_archive: HashMap<u64, Clause>,
    /// Selection strategy
    strategy: SelectionStrategy,
    /// Maximum clause size (for fair enumeration)
    max_clause_size: usize,
    /// Statistics
    pub stats: ProverStats,
}

/// Prover statistics
#[derive(Clone, Debug, Default)]
pub struct ProverStats {
    /// Number of inferences performed
    pub inferences: u64,
    /// Number of clauses generated
    pub generated: u64,
    /// Number of clauses kept (after simplification)
    pub kept: u64,
    /// Number of clauses deleted by subsumption
    pub subsumed: u64,
    /// Number of tautologies deleted
    pub tautologies: u64,
}

/// Result of the prover
#[derive(Clone, Debug)]
pub enum ProverResult {
    /// Unsatisfiable - found empty clause
    Unsatisfiable(ProofTrace),
    /// Satisfiable - saturated without finding empty clause
    Saturated,
    /// Resource limit reached
    ResourceLimit,
}

/// Proof trace for reconstruction
#[derive(Clone, Debug)]
pub struct ProofTrace {
    /// The empty clause
    pub empty_clause: Clause,
    /// All clauses used in the proof
    pub clauses: Vec<Clause>,
}

impl Default for SuperpositionProver {
    fn default() -> Self {
        Self::new()
    }
}

impl SuperpositionProver {
    /// Create a new prover with default KBO ordering, empty clause sets.
    pub fn new() -> Self {
        SuperpositionProver {
            ordering: Box::new(KBO::new()),
            processed: Vec::new(),
            processed_index: HashMap::new(),
            unprocessed: BinaryHeap::new(),
            next_id: 0,
            clause_archive: HashMap::new(),
            strategy: SelectionStrategy::SizeFirst,
            max_clause_size: 100,
            stats: ProverStats::default(),
        }
    }

    /// Create a new prover with custom ordering
    pub fn with_ordering(ordering: Box<dyn TermOrdering>) -> Self {
        SuperpositionProver {
            ordering,
            processed: Vec::new(),
            processed_index: HashMap::new(),
            unprocessed: BinaryHeap::new(),
            next_id: 0,
            clause_archive: HashMap::new(),
            strategy: SelectionStrategy::SizeFirst,
            max_clause_size: 100,
            stats: ProverStats::default(),
        }
    }

    /// Set the selection strategy
    pub fn set_strategy(&mut self, strategy: SelectionStrategy) {
        self.strategy = strategy;
    }

    /// Add a clause directly to the processed set, maintaining the index.
    pub(super) fn push_processed(&mut self, clause: Clause) {
        let idx = self.processed.len();
        self.processed_index.insert(clause.id, idx);
        self.processed.push(clause);
    }

    /// Add an input clause.
    ///
    /// # Contracts
    ///
    /// **ENSURES:**
    /// - Clause added to unprocessed set (unless tautology)
    /// - Tautologies (containing both `l` and `!l`) are discarded
    /// - `stats.generated` incremented for non-tautologies
    pub fn add_clause(&mut self, literals: Vec<Literal>) {
        let clause = Clause::new(literals, self.next_id);
        self.next_id += 1;

        // Skip tautologies
        if clause.is_tautology() {
            self.stats.tautologies += 1;
            return;
        }

        let priority = self.compute_priority(&clause);
        self.unprocessed
            .push(PrioritizedClause { clause, priority });
        self.stats.generated += 1;
    }

    fn compute_priority(&self, clause: &Clause) -> i64 {
        // The reversed Ord on PrioritizedClause gives min-heap behavior
        // (pops smallest priority first). Use positive values so that:
        // - FIFO: smallest id = oldest clause → breadth-first
        // - SizeFirst: smallest size → lightest clause first
        // - SymbolCount: fewest literals first
        match self.strategy {
            SelectionStrategy::FIFO => clause.id as i64,
            SelectionStrategy::SizeFirst => clause
                .literals
                .iter()
                .map(|l| l.lhs.size() + l.rhs.size())
                .sum::<usize>() as i64,
            SelectionStrategy::SymbolCount => clause.literals.len() as i64,
        }
    }

    /// Run the prover with a given iteration limit.
    ///
    /// # Contracts
    ///
    /// **REQUIRES:** Clauses have been added via `add_clause()`.
    ///
    /// **ENSURES:**
    /// - `Unsatisfiable(trace)` implies the clause set is unsatisfiable (empty clause derived)
    /// - `Saturated` implies no more inferences possible (may be satisfiable or unknown)
    /// - `Unknown` when iteration limit reached without conclusion
    /// - Sound: never claims UNSAT for satisfiable input
    /// - Refutationally complete (in limit): if UNSAT, will eventually find proof
    ///
    /// # Implementation Notes
    ///
    /// Uses ordered resolution, superposition, and equality factoring inference rules.
    pub fn prove(&mut self, max_iterations: u64) -> ProverResult {
        self.prove_until(max_iterations, None)
    }

    /// Like [`Self::prove`], but additionally bails with [`ProverResult::ResourceLimit`]
    /// the moment a wall-clock `deadline` is reached.
    ///
    /// The given-clause loop is the hot search loop: a single saturation run can
    /// generate an exponentially growing clause set, so a fixed `max_iterations`
    /// bound is not a *time* bound (one runaway saturation was observed running
    /// ~29 min). Polling the deadline INSIDE the loop (before every given-clause
    /// step — `Instant::now()` is ~tens of ns) makes the prover return within a
    /// small grace of `deadline` regardless of how explosive the clause set is.
    /// Passing `None` preserves the pure iteration-bounded behavior.
    ///
    /// Soundness is unchanged: a deadline only causes an *earlier* `ResourceLimit`
    /// (no proof claimed), exactly like exhausting `max_iterations`.
    pub fn prove_until(&mut self, max_iterations: u64, deadline: Option<Instant>) -> ProverResult {
        for _ in 0..max_iterations {
            // Poll the wall-clock deadline before each given-clause step. A single
            // iteration can generate/​simplify many clauses, so this is the finest
            // bail point inside the hot loop; `Instant::now()` is ~tens of ns.
            if let Some(deadline) = deadline {
                if Instant::now() >= deadline {
                    return ProverResult::ResourceLimit;
                }
            }
            // Select the next clause to process
            let given = match self.unprocessed.pop() {
                Some(pc) => pc.clause,
                None => return ProverResult::Saturated,
            };

            // Check for empty clause
            if given.is_empty() {
                return ProverResult::Unsatisfiable(self.build_proof_trace(&given));
            }

            // Skip if clause is too large
            if given
                .literals
                .iter()
                .map(|l| l.lhs.size() + l.rhs.size())
                .sum::<usize>()
                > self.max_clause_size
            {
                continue;
            }

            // Forward simplification
            let Some(given) = self.forward_simplify(given) else {
                continue; // Subsumed or trivial
            };

            // Backward simplification
            self.backward_simplify(&given);

            // Generate new clauses
            let new_clauses = self.generate_clauses(&given);

            // Add given to processed
            self.push_processed(given);
            self.stats.kept += 1;

            // Add new clauses to unprocessed
            for clause in new_clauses {
                if clause.is_empty() {
                    return ProverResult::Unsatisfiable(self.build_proof_trace(&clause));
                }

                if clause.is_tautology() {
                    self.stats.tautologies += 1;
                } else {
                    let priority = self.compute_priority(&clause);
                    self.unprocessed
                        .push(PrioritizedClause { clause, priority });
                    self.stats.generated += 1;
                }
            }
        }

        ProverResult::ResourceLimit
    }

    pub(super) fn build_proof_trace(&self, empty_clause: &Clause) -> ProofTrace {
        // Collect all clauses used in the proof.
        // Seed from the empty clause's parents directly — the empty clause
        // itself was just generated and isn't in processed/clause_archive yet.
        let mut used = HashSet::new();
        used.insert(empty_clause.id);
        let mut to_visit: Vec<u64> = Vec::new();
        for &parent_id in &empty_clause.parents {
            if used.insert(parent_id) {
                to_visit.push(parent_id);
            }
        }

        while let Some(id) = to_visit.pop() {
            if let Some(clause) = self.find_clause(id) {
                for parent_id in &clause.parents {
                    if !used.contains(parent_id) {
                        used.insert(*parent_id);
                        to_visit.push(*parent_id);
                    }
                }
            }
        }

        let mut clauses: Vec<Clause> = self
            .processed
            .iter()
            .filter(|c| used.contains(&c.id))
            .cloned()
            .collect();
        // Include archived clauses (removed by backward_simplify or replaced
        // by forward demodulation) that are part of the proof (#2278).
        for (id, clause) in &self.clause_archive {
            if used.contains(id) {
                clauses.push(clause.clone());
            }
        }

        ProofTrace {
            empty_clause: empty_clause.clone(),
            clauses,
        }
    }

    pub(super) fn find_clause(&self, id: u64) -> Option<&Clause> {
        self.processed_index
            .get(&id)
            .map(|&idx| &self.processed[idx])
            .or_else(|| self.clause_archive.get(&id))
    }

    fn forward_simplify(&mut self, mut clause: Clause) -> Option<Clause> {
        // Check subsumption by processed clauses
        for processed in &self.processed {
            if self.subsumes(processed, &clause) {
                self.stats.subsumed += 1;
                return None;
            }
        }

        // Demodulation: simplify using unit equations.
        // Each demodulation step gets its own intermediate clause ID so that
        // proof reconstruction can trace the full rewrite chain (#1164).
        // Collect units first to free the borrow on self.processed.
        let units: Vec<Clause> = self
            .processed
            .iter()
            .filter(|p| p.is_unit() && p.literals[0].positive)
            .cloned()
            .collect();
        for unit in &units {
            let new_clause = self.demodulate(&clause, unit);
            if matches!(new_clause.inference, Inference::Demodulation(_, _)) {
                // Archive pre-step clause and assign fresh ID (#2278, #1164).
                self.clause_archive.insert(clause.id, clause);
                clause = new_clause;
                clause.id = self.next_id;
                self.next_id += 1;
            }
        }

        // Remove duplicate and trivial literals
        clause.literals.retain(|l| !l.is_reflexive());
        clause.literals.sort();
        clause.literals.dedup();

        if clause.is_tautology() {
            self.stats.tautologies += 1;
            return None;
        }

        Some(clause)
    }

    fn backward_simplify(&mut self, given: &Clause) {
        // For simplicity, we only do backward subsumption
        if !given.is_unit() {
            return;
        }

        let mut to_remove = vec![];
        for (i, processed) in self.processed.iter().enumerate() {
            if self.subsumes(given, processed) {
                to_remove.push(i);
                self.stats.subsumed += 1;
            }
        }

        // Archive then remove in reverse order to preserve indices (#2278).
        for i in to_remove.into_iter().rev() {
            let removed = self.processed.swap_remove(i);
            self.processed_index.remove(&removed.id);
            // swap_remove moves the last element to position i; update its index
            if i < self.processed.len() {
                self.processed_index.insert(self.processed[i].id, i);
            }
            self.clause_archive.insert(removed.id, removed);
        }
    }

    /// Check if c1 subsumes c2 (c1 is more general)
    pub(super) fn subsumes(&self, c1: &Clause, c2: &Clause) -> bool {
        if c1.literals.len() > c2.literals.len() {
            return false;
        }

        // Rename c1 apart from c2 before matching. Both clauses draw their
        // variable indices from the same 0-based pool, so a c1 pattern
        // variable could otherwise be bound to a c2 term CONTAINING that same
        // index — a self-referential binding on which the chain-following
        // `apply_subst` diverges (stack overflow). After renaming, matching
        // with every variable below `offset` frozen keeps each binding
        // bipartite (domain: renamed c1 vars; range: c2 terms), which both
        // terminates and is the actual subsumption condition — the matcher may
        // instantiate c1's variables only.
        let c1_max = c1.vars().into_iter().max().unwrap_or(0);
        let c2_max = c2.vars().into_iter().max().unwrap_or(0);
        let Some(offset) = c1_max.max(c2_max).checked_add(1) else {
            return false; // variable space exhausted: conservatively no subsumption
        };
        let c1_renamed = c1.rename_vars(offset);

        // Try to find a substitution that maps c1's literals to a subset of c2's
        self.subsumes_rec(
            &c1_renamed.literals,
            &c2.literals,
            &Substitution::new(),
            offset,
        )
    }

    fn subsumes_rec(
        &self,
        remaining: &[Literal],
        target: &[Literal],
        subst: &Substitution,
        bind_min: u32,
    ) -> bool {
        if remaining.is_empty() {
            return true;
        }

        let lit = &remaining[0];
        let rest = &remaining[1..];

        for target_lit in target {
            if lit.positive != target_lit.positive {
                continue;
            }

            // Try to match lit against target_lit
            let lit_applied = lit.apply_subst(subst);
            if let Some(ext) = match_terms_frozen(&lit_applied.lhs, &target_lit.lhs, bind_min) {
                let combined = subst.compose(&ext);
                if let Some(ext2) = match_terms_frozen(
                    &lit_applied.rhs.apply_subst(&ext),
                    &target_lit.rhs,
                    bind_min,
                ) {
                    let final_subst = combined.compose(&ext2);
                    if self.subsumes_rec(rest, target, &final_subst, bind_min) {
                        return true;
                    }
                }
            }
            // Also try symmetric matching for equations
            if lit.positive {
                if let Some(ext) = match_terms_frozen(&lit_applied.lhs, &target_lit.rhs, bind_min) {
                    let combined = subst.compose(&ext);
                    if let Some(ext2) = match_terms_frozen(
                        &lit_applied.rhs.apply_subst(&ext),
                        &target_lit.lhs,
                        bind_min,
                    ) {
                        let final_subst = combined.compose(&ext2);
                        if self.subsumes_rec(rest, target, &final_subst, bind_min) {
                            return true;
                        }
                    }
                }
            }
        }

        false
    }

    /// Demodulate (simplify) a clause using a unit equation
    pub(super) fn demodulate(&self, clause: &Clause, unit: &Clause) -> Clause {
        debug_assert!(unit.is_unit() && unit.literals[0].positive);

        // Rename the rewrite rule apart from the clause and freeze the
        // clause's variables during matching — same-index collisions can
        // otherwise produce a self-referential matcher (X ↦ f(.. X ..)) whose
        // chain-following `apply_subst` diverges, or an invalid instance that
        // rewrites to a non-entailed clause. KBO orientation is invariant
        // under variable renaming, so orienting after the rename is safe.
        let unit_max = unit.vars().into_iter().max().unwrap_or(0);
        let clause_max = clause.vars().into_iter().max().unwrap_or(0);
        let Some(offset) = unit_max.max(clause_max).checked_add(1) else {
            return clause.clone(); // variable space exhausted: skip rewriting
        };
        let unit_renamed = unit.rename_vars(offset);

        let eq = &unit_renamed.literals[0];
        let (big, small) = if self.ordering.greater(&eq.lhs, &eq.rhs) {
            (&eq.lhs, &eq.rhs)
        } else if self.ordering.greater(&eq.rhs, &eq.lhs) {
            (&eq.rhs, &eq.lhs)
        } else {
            return clause.clone(); // Not oriented
        };

        let mut result = clause.clone();
        let mut changed = false;

        for lit in &mut result.literals {
            for side in [&mut lit.lhs, &mut lit.rhs] {
                // Restart position enumeration after each rewrite (#2307).
                // Each rewrite replaces `big` (strictly greater under KBO)
                // with `small`, so the term strictly decreases — guaranteeing
                // termination of this fixpoint loop.
                loop {
                    let mut rewritten_side = None;
                    let _ = side.try_visit_positions(|path, subterm| {
                        if let Some(subst) = match_terms_frozen(big, subterm, offset) {
                            let replacement = small.apply_subst(&subst);
                            if let Some(new_side) = side.replace_at_path(path, replacement) {
                                rewritten_side = Some(new_side);
                                return ControlFlow::Break(());
                            }
                        }
                        ControlFlow::Continue(())
                    });

                    if let Some(new_side) = rewritten_side {
                        *side = new_side;
                        changed = true;
                    } else {
                        break;
                    }
                }
            }
        }

        if changed {
            result.parents = vec![clause.id, unit.id];
            result.inference = Inference::Demodulation(clause.id, unit.id);
        }

        result
    }
}
