// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! CDCL solver: struct definition, search loop, and public API.
//!
//! Clause database management (add_clause, add_theory_clause) is in `clause_db`.
//! BCP, conflict analysis, and UNSAT core extraction are in `analysis`.

use super::types::{
    usize_to_u32, Clause, ClauseRef, LBool, Lit, SatUnsatCore, SolveResult, SolverStats, Var,
    VarData, WatchList,
};
use super::vsids::VsidsData;

/// Base restart interval in conflicts (multiplied by Luby sequence value).
pub(super) const RESTART_BASE: u64 = 100;
/// Initial threshold: number of active learned clauses before first reduce_db.
pub(super) const REDUCE_DB_INIT: usize = 2000;
/// Increment added to reduce_db threshold after each reduction.
pub(super) const REDUCE_DB_INC: usize = 300;
/// LBD threshold for "core" clauses that are never deleted.
pub(super) const CORE_LBD: u32 = 2;
/// EMA smoothing factor for fast (short-term) LBD average (~33 conflicts).
pub(super) const LBD_EMA_FAST_ALPHA: f64 = 0.03;
/// EMA smoothing factor for slow (long-term) LBD average (~33k conflicts).
pub(super) const LBD_EMA_SLOW_ALPHA: f64 = 0.00003;
/// Restart when fast LBD EMA exceeds slow EMA by this factor (quality degradation).
pub(super) const LBD_RESTART_MARGIN: f64 = 1.25;
/// Minimum conflicts before Glucose-style restarts can trigger.
pub(super) const LBD_RESTART_WARMUP: u64 = 100;

/// Compute the i-th value of the Luby restart sequence (0-indexed).
///
/// Sequence: 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8, ...
/// Used to schedule restarts: restart after `luby(i) * RESTART_BASE` conflicts.
pub(super) fn luby(i: u32) -> u64 {
    let mut size = 1u64;
    let mut seq = 0u32;
    let mut idx = u64::from(i);
    while size < idx + 1 {
        seq += 1;
        size = 2 * size + 1;
    }
    while size - 1 != idx {
        size = (size - 1) / 2;
        seq -= 1;
        if idx >= size {
            idx -= size;
        }
    }
    1u64 << seq
}

/// CDCL SAT Solver
pub struct CdclSolver {
    /// Number of variables
    pub(super) num_vars: usize,
    /// Clause database (original and learned)
    pub(super) clauses: Vec<Clause>,
    /// Variable data (assignment, level, reason)
    pub(super) var_data: Vec<VarData>,
    /// Watch lists indexed by literal
    pub(super) watches: Vec<WatchList>,
    /// VSIDS decision heuristic
    pub(super) vsids: VsidsData,
    /// Trail: sequence of assignments in order
    pub(super) trail: Vec<Lit>,
    /// Trail limits: index in trail where each decision level starts
    pub(super) trail_lim: Vec<usize>,
    /// Propagation queue head (index into trail)
    pub(super) qhead: usize,
    /// Current decision level
    pub(super) decision_level: u32,
    /// Conflict counter (for restarts)
    pub(super) conflicts: u64,
    /// Decisions counter
    pub(super) decisions: u64,
    /// Propagations counter
    pub(super) propagations: u64,
    /// Learned clause activity increment
    pub(super) clause_inc: f64,
    /// Clause activity decay
    pub(super) clause_decay: f64,
    /// Conflict limit for search
    pub(super) conflict_limit: u64,
    /// Seen marks for conflict analysis
    pub(super) seen: Vec<bool>,
    /// Temporary storage for conflict analysis
    pub(super) analyze_stack: Vec<Lit>,
    /// Temporary storage for learned clause
    pub(super) learnt_clause: Vec<Lit>,
    /// Temporary storage for clause origins during conflict analysis
    pub(super) learnt_origins: Vec<u32>,
    /// HashSet for O(1) deduplication of origins during conflict analysis
    pub(super) seen_origins: hashbrown::HashSet<u32>,
    /// Whether the problem is already determined to be UNSAT
    pub(super) is_unsat: bool,
    /// Number of original (non-learned) clauses for unsat core extraction
    pub(super) num_original_clauses: usize,
    /// Original clause indices used in the unsat core (populated during UNSAT)
    pub(super) unsat_core_indices: Vec<u32>,
    /// For unit clauses, map from variable to the clause that set it
    /// Used for unsat core extraction when unit clause conflicts happen
    pub(super) unit_clause_origins: Vec<Option<u32>>,
    /// Number of active (non-deleted) learned clauses
    pub(super) active_learned: usize,
    /// Number of reduce_db operations performed (used to grow threshold)
    pub(super) reduce_db_count: u32,
    /// Saved phase for each variable (phase saving heuristic).
    /// On backtrack, each variable's last assigned polarity is stored here.
    /// The `decide()` method uses this instead of always choosing positive.
    pub(super) phase: Vec<bool>,
    /// Fast (short-term) EMA of learned clause LBD for Glucose-style restarts.
    pub(super) lbd_ema_fast: f64,
    /// Slow (long-term) EMA of learned clause LBD for Glucose-style restarts.
    pub(super) lbd_ema_slow: f64,
}

impl CdclSolver {
    /// Create a new solver with the given number of variables.
    ///
    /// # Contracts
    ///
    /// **REQUIRES:** `num_vars` is the initial capacity hint (more can be added via `new_var()`)
    ///
    /// **ENSURES:**
    /// - Creates solver with pre-allocated variables `Var(0)` through `Var(num_vars-1)`
    /// - All variables initially unassigned
    /// - No clauses registered yet
    pub fn new(num_vars: usize) -> Self {
        let num_lits = num_vars * 2;
        Self {
            num_vars,
            clauses: Vec::new(),
            var_data: vec![VarData::default(); num_vars],
            watches: vec![Vec::new(); num_lits],
            vsids: VsidsData::new(num_vars),
            trail: Vec::with_capacity(num_vars),
            trail_lim: Vec::new(),
            qhead: 0,
            decision_level: 0,
            conflicts: 0,
            decisions: 0,
            propagations: 0,
            clause_inc: 1.0,
            clause_decay: 0.999,
            conflict_limit: u64::MAX,
            seen: vec![false; num_vars],
            analyze_stack: Vec::new(),
            learnt_clause: Vec::new(),
            learnt_origins: Vec::new(),
            seen_origins: hashbrown::HashSet::new(),
            is_unsat: false,
            num_original_clauses: 0,
            unsat_core_indices: Vec::new(),
            unit_clause_origins: vec![None; num_vars],
            active_learned: 0,
            reduce_db_count: 0,
            phase: vec![true; num_vars],
            lbd_ema_fast: 0.0,
            lbd_ema_slow: 0.0,
        }
    }

    /// Create a new variable and return it.
    ///
    /// # Contracts
    ///
    /// **ENSURES:**
    /// - Returns fresh `Var` with index `== old(num_vars())`
    /// - `num_vars() == old(num_vars()) + 1` after call
    /// - New variable is unassigned
    pub(crate) fn new_var(&mut self) -> Var {
        let var = Var::new(usize_to_u32(self.num_vars, "variable count"));
        self.num_vars += 1;
        self.var_data.push(VarData::default());
        self.watches.push(Vec::new()); // positive literal
        self.watches.push(Vec::new()); // negative literal
        self.vsids.activity.push(0.0);
        self.vsids
            .heap_pos
            .push(usize_to_u32(self.vsids.heap.len(), "VSIDS heap length"));
        self.vsids.heap.push(var);
        self.seen.push(false);
        self.unit_clause_origins.push(None);
        self.phase.push(true);
        var
    }

    /// Get the current number of variables
    pub(crate) fn num_vars(&self) -> usize {
        self.num_vars
    }

    /// Get the number of clauses
    pub(crate) fn num_clauses(&self) -> usize {
        self.clauses.len()
    }

    /// Get the current value of a literal
    #[inline]
    pub(super) fn lit_value(&self, lit: Lit) -> LBool {
        let val = self.var_data[lit.var().index()].value;
        if lit.is_pos() {
            val
        } else {
            val.not()
        }
    }

    /// Set the value of a literal
    #[inline]
    pub(super) fn set_lit(&mut self, lit: Lit, reason: ClauseRef) {
        let var = lit.var();
        let idx = var.index();
        self.var_data[idx].value = if lit.is_pos() {
            LBool::True
        } else {
            LBool::False
        };
        self.var_data[idx].level = self.decision_level;
        self.var_data[idx].reason = reason;
        self.trail.push(lit);
    }

    /// Backtrack to the given decision level
    fn backtrack(&mut self, level: u32) {
        if self.decision_level <= level {
            return;
        }

        // Unassign all variables assigned after the target level
        while self.trail.len() > self.trail_lim[level as usize] {
            let lit = self
                .trail
                .pop()
                .expect("invariant: trail above trail_lim mark is non-empty during backtrack");
            let var = lit.var();
            let idx = var.index();
            // Phase saving: remember the polarity before unassigning
            self.phase[idx] = self.var_data[idx].value == LBool::True;
            self.var_data[idx].value = LBool::Undef;
            self.var_data[idx].reason = ClauseRef::INVALID;
            self.vsids.insert(var);
        }

        self.trail_lim.truncate(level as usize);
        self.qhead = self.trail.len();
        self.decision_level = level;
    }

    /// Make a decision (pick an unassigned variable and assign it)
    fn decide(&mut self) -> bool {
        // Use VSIDS to pick the next variable
        while let Some(var) = self.vsids.pop() {
            if self.var_data[var.index()].value == LBool::Undef {
                // Create a new decision level
                self.trail_lim.push(self.trail.len());
                self.decision_level += 1;
                self.decisions += 1;

                // Phase saving: reuse the last assigned polarity
                let lit = Lit::new(var, self.phase[var.index()]);
                self.set_lit(lit, ClauseRef::INVALID);
                return true;
            }
        }
        false // No unassigned variables
    }

    /// Seed phase saving for future decisions on `var`.
    ///
    /// This updates only the saved polarity cache. It does not assign the
    /// variable immediately; the next decision on `var` will reuse the hint.
    pub(crate) fn set_phase_hint(&mut self, var: Var, phase: bool) {
        self.phase[var.index()] = phase;
    }

    /// Read the saved polarity for `var`.
    #[cfg(test)]
    pub(crate) fn phase_hint(&self, var: Var) -> bool {
        self.phase[var.index()]
    }

    /// Compute LBD (Literal Block Distance) for a set of literals.
    ///
    /// LBD counts the number of distinct decision levels among the literals.
    /// Lower LBD = higher quality clause (fewer decision levels involved).
    /// Used by reduce_db (core clauses have LBD <= 2) and Glucose-style restarts.
    pub(super) fn compute_lbd(&self, lits: &[Lit]) -> u32 {
        let max_level = lits
            .iter()
            .map(|lit| self.var_data[lit.var().index()].level)
            .max()
            .unwrap_or(0);
        let mut levels_seen = vec![false; (max_level + 1) as usize];
        let mut lbd = 0u32;
        for lit in lits {
            let level = self.var_data[lit.var().index()].level as usize;
            if !levels_seen[level] {
                levels_seen[level] = true;
                lbd += 1;
            }
        }
        lbd
    }

    /// Decay clause activities
    fn decay_clause_activity(&mut self) {
        self.clause_inc /= self.clause_decay;
    }

    /// Main solving loop.
    ///
    /// # Contracts
    ///
    /// **REQUIRES:** All clauses have been added via `add_clause()` before calling.
    ///
    /// **ENSURES:**
    /// - `Sat(model)` implies `model` satisfies all original clauses
    /// - `Unsat(core)` implies the subset of clauses in `core` is unsatisfiable
    /// - `Unknown` only when conflict limit is reached
    /// - Deterministic: same clauses yield same result
    ///
    /// # Implementation Notes
    ///
    /// Uses CDCL with two-watched literals, VSIDS, 1UIP conflict analysis,
    /// phase saving, Luby + Glucose-style EMA restarts, and activity-based
    /// learned clause deletion.
    pub fn solve(&mut self) -> SolveResult {
        // Check if already determined UNSAT during clause addition
        if self.is_unsat {
            if !self.unsat_core_indices.is_empty() {
                let core = SatUnsatCore {
                    clause_indices: std::mem::take(&mut self.unsat_core_indices),
                };
                return SolveResult::Unsat(Some(core));
            }
            return SolveResult::Unsat(None);
        }

        // Initial unit propagation
        if let Some(conflict) = self.propagate() {
            let origins = self.collect_unsat_core_level0(conflict);
            let core = SatUnsatCore {
                clause_indices: origins,
            };
            return SolveResult::Unsat(Some(core));
        }

        // Restart state (local to this solve invocation)
        let mut restart_count = 0u32;
        let mut conflicts_since_restart = 0u64;
        let mut restart_limit = luby(0).saturating_mul(RESTART_BASE);

        // Reduce_db threshold: grows after each reduction
        let mut reduce_threshold = REDUCE_DB_INIT + self.reduce_db_count as usize * REDUCE_DB_INC;

        loop {
            if let Some(conflict) = self.propagate() {
                self.conflicts += 1;
                conflicts_since_restart += 1;

                if self.decision_level == 0 {
                    let origins = self.collect_unsat_core_level0(conflict);
                    let core = SatUnsatCore {
                        clause_indices: origins,
                    };
                    return SolveResult::Unsat(Some(core));
                }

                if self.conflicts >= self.conflict_limit {
                    return SolveResult::Unknown;
                }

                // Analyze conflict and learn
                let (learnt, backtrack_level, origins) = self.analyze(conflict);
                self.backtrack(backtrack_level);
                let cref = self.add_learned_clause(learnt.clone(), origins);
                self.set_lit(learnt[0], cref);

                // Update LBD exponential moving averages (Glucose-style)
                let lbd = f64::from(self.clauses[cref.index()].lbd);
                self.lbd_ema_fast += LBD_EMA_FAST_ALPHA * (lbd - self.lbd_ema_fast);
                self.lbd_ema_slow += LBD_EMA_SLOW_ALPHA * (lbd - self.lbd_ema_slow);

                // Decay activities
                self.vsids.decay();
                self.decay_clause_activity();

                // Restart check: Luby budget OR Glucose-style quality degradation
                let luby_trigger = conflicts_since_restart >= restart_limit;
                let glucose_trigger = self.conflicts > LBD_RESTART_WARMUP
                    && self.lbd_ema_fast > self.lbd_ema_slow * LBD_RESTART_MARGIN;
                if luby_trigger || glucose_trigger {
                    self.backtrack(0);
                    restart_count += 1;
                    conflicts_since_restart = 0;
                    restart_limit = luby(restart_count).saturating_mul(RESTART_BASE);
                }

                // Clause database reduction when learned clauses exceed threshold
                if self.active_learned > reduce_threshold {
                    self.reduce_db();
                    reduce_threshold =
                        REDUCE_DB_INIT + self.reduce_db_count as usize * REDUCE_DB_INC;
                }
            } else if !self.decide() {
                // All variables assigned - SAT!
                let model: Vec<bool> = self
                    .var_data
                    .iter()
                    .map(|vd| vd.value == LBool::True)
                    .collect();
                return SolveResult::Sat(model);
            }
        }
    }

    /// Reset the propagation queue so the next `solve()` re-processes all
    /// trail assignments against newly added clauses.
    ///
    /// This is required for DPLL(T) integration: after adding a theory
    /// learned clause via `add_theory_clause()`, the two-watched-literal scheme
    /// won't detect conflicts with already-assigned variables unless
    /// propagation is re-run from the beginning of the trail.
    pub(crate) fn reset_propagation_queue(&mut self) {
        self.qhead = 0;
    }

    /// Undo all decisions and non-level-0 propagations, returning the
    /// solver to the root decision level.
    ///
    /// Required for DPLL(T): after `solve()` returns SAT and the theory
    /// rejects the model, the solver must backtrack before re-solving.
    /// Without this, `solve()` re-enters with stale decisions and its
    /// initial `propagate()` misclassifies conflicts as level-0 UNSAT.
    pub(crate) fn backtrack_to_root(&mut self) {
        self.backtrack(0);
    }

    /// Set the conflict limit for solving (used by cdcl tests)
    #[cfg(test)]
    pub(crate) fn set_conflict_limit(&mut self, limit: u64) {
        self.conflict_limit = limit;
    }

    /// Get statistics
    pub(crate) fn stats(&self) -> SolverStats {
        SolverStats {
            conflicts: self.conflicts,
            decisions: self.decisions,
            propagations: self.propagations,
            learned_clauses: self.active_learned as u64,
        }
    }
}
