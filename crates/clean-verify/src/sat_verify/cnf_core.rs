// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Solver-native CNF representation with arena-style clause database.
//!
//! Provides [`CnfLiteral`], [`ClauseDb`], and [`CnfFormula`] as the shared
//! foundation for DRAT, LRAT, resolution, and extended resolution proof
//! checkers. The literal encoding uses the standard MiniSat convention:
//! `var * 2 + sign` packed into a `u32`.
//!
//! The [`ClauseDb`] stores clauses in a flat arena for cache-friendly access
//! and O(1) lookup by [`ClauseId`].
//!
//! ## References
//!
//! - Een & Sorensson (2003): MiniSat clause allocator design.
//! - Biere et al. (2021): Handbook of Satisfiability, Ch. 4.

use std::collections::HashMap;
use std::fmt;

use super::types::{CnfError, Lit};

/// A literal in the MiniSat u32 encoding: `var * 2 + sign`.
///
/// Sign bit 0 = positive, sign bit 1 = negative.
/// Variable 0 maps to internal codes 0 and 1.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct CnfLiteral(pub u32);

impl CnfLiteral {
    /// Create a positive literal for the given variable (0-indexed).
    #[must_use]
    pub fn positive(var: u32) -> Self {
        Self(var * 2)
    }

    /// Create a negative literal for the given variable (0-indexed).
    #[must_use]
    pub fn negative(var: u32) -> Self {
        Self(var * 2 + 1)
    }

    /// Create from a DIMACS integer (1-indexed, sign encodes polarity).
    ///
    /// Returns `None` if the input is zero.
    #[must_use]
    pub fn from_dimacs(d: i32) -> Option<Self> {
        if d == 0 {
            return None;
        }
        let var = d.unsigned_abs() - 1; // DIMACS is 1-indexed
        if d > 0 {
            Some(Self::positive(var))
        } else {
            Some(Self::negative(var))
        }
    }

    /// Convert back to a DIMACS integer (1-indexed).
    #[must_use]
    pub fn to_dimacs(self) -> i32 {
        let var = self.var() + 1; // back to 1-indexed
        let var_i32 = var as i32;
        if self.sign() {
            -var_i32
        } else {
            var_i32
        }
    }

    /// Convert from the existing `Lit` type (DIMACS-style i32).
    #[must_use]
    pub fn from_lit(lit: Lit) -> Option<Self> {
        Self::from_dimacs(lit.0)
    }

    /// Convert to the existing `Lit` type.
    #[must_use]
    pub fn to_lit(self) -> Lit {
        Lit(self.to_dimacs())
    }

    /// The variable index (0-indexed).
    #[must_use]
    pub fn var(self) -> u32 {
        self.0 >> 1
    }

    /// The sign bit: `false` = positive, `true` = negative.
    #[must_use]
    pub fn sign(self) -> bool {
        self.0 & 1 != 0
    }

    /// Whether this literal is positive.
    #[must_use]
    pub fn is_positive(self) -> bool {
        !self.sign()
    }

    /// The negation of this literal.
    #[must_use]
    pub fn negate(self) -> Self {
        Self(self.0 ^ 1)
    }

    /// The raw u32 encoding.
    #[must_use]
    pub fn code(self) -> u32 {
        self.0
    }
}

impl fmt::Display for CnfLiteral {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_positive() {
            write!(f, "x{}", self.var())
        } else {
            write!(f, "~x{}", self.var())
        }
    }
}

// ---------------------------------------------------------------------------
// ClauseId
// ---------------------------------------------------------------------------

/// An opaque handle into the [`ClauseDb`] arena.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ClauseId(pub u32);

impl fmt::Display for ClauseId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "c{}", self.0)
    }
}

// ---------------------------------------------------------------------------
// ClauseDb — arena-style clause database
// ---------------------------------------------------------------------------

/// Arena-style clause database with flat storage for cache-friendly access.
///
/// Clauses are stored contiguously in a flat `Vec<CnfLiteral>`. Each clause
/// is referenced by a [`ClauseId`] that maps to its offset and length in
/// the arena. Deleted clauses are marked but their storage is not reclaimed
/// until compaction.
#[derive(Debug, Clone)]
pub struct ClauseDb {
    /// Flat literal arena.
    arena: Vec<CnfLiteral>,
    /// (offset, length) for each clause. `None` means deleted.
    index: Vec<Option<(u32, u32)>>,
}

impl ClauseDb {
    /// Create an empty clause database.
    #[must_use]
    pub fn new() -> Self {
        Self {
            arena: Vec::new(),
            index: Vec::new(),
        }
    }

    /// Create a clause database with pre-allocated capacity.
    #[must_use]
    pub fn with_capacity(clause_capacity: usize, literal_capacity: usize) -> Self {
        Self {
            arena: Vec::with_capacity(literal_capacity),
            index: Vec::with_capacity(clause_capacity),
        }
    }

    /// Add a clause to the database, returning its [`ClauseId`].
    ///
    /// The literals are stored sorted for efficient comparison.
    pub fn add_clause(&mut self, lits: &[CnfLiteral]) -> ClauseId {
        let offset = self.arena.len() as u32;
        let mut sorted = lits.to_vec();
        sorted.sort();
        sorted.dedup();
        self.arena.extend_from_slice(&sorted);
        let len = sorted.len() as u32;
        let id = ClauseId(self.index.len() as u32);
        self.index.push(Some((offset, len)));
        id
    }

    /// Mark a clause as deleted. Returns `true` if the clause existed.
    pub fn delete_clause(&mut self, id: ClauseId) -> bool {
        let idx = id.0 as usize;
        if idx < self.index.len() && self.index[idx].is_some() {
            self.index[idx] = None;
            return true;
        }
        false
    }

    /// Look up a clause by ID. Returns `None` if deleted or out of range.
    #[must_use]
    pub fn get_clause(&self, id: ClauseId) -> Option<&[CnfLiteral]> {
        let idx = id.0 as usize;
        self.index.get(idx).and_then(|entry| {
            entry.map(|(offset, len)| {
                let start = offset as usize;
                let end = start + len as usize;
                &self.arena[start..end]
            })
        })
    }

    /// The total number of clauses ever added (including deleted).
    #[must_use]
    pub fn total_clauses(&self) -> usize {
        self.index.len()
    }

    /// The number of currently active (non-deleted) clauses.
    #[must_use]
    pub fn active_clauses(&self) -> usize {
        self.index.iter().filter(|e| e.is_some()).count()
    }

    /// Whether the given clause ID is active (not deleted).
    #[must_use]
    pub fn is_active(&self, id: ClauseId) -> bool {
        self.get_clause(id).is_some()
    }

    /// Iterate over all active clause IDs and their literals.
    pub fn iter_active(&self) -> impl Iterator<Item = (ClauseId, &[CnfLiteral])> {
        self.index.iter().enumerate().filter_map(|(i, entry)| {
            entry.map(|(offset, len)| {
                let start = offset as usize;
                let end = start + len as usize;
                (ClauseId(i as u32), &self.arena[start..end])
            })
        })
    }
}

impl Default for ClauseDb {
    fn default() -> Self {
        Self::new()
    }
}

// ---------------------------------------------------------------------------
// CnfFormula — complete formula with clause database
// ---------------------------------------------------------------------------

/// A CNF formula backed by an arena-style clause database.
///
/// This is the solver-native representation optimized for proof checking.
/// It wraps a [`ClauseDb`] and tracks variable count and clause-to-id mapping.
#[derive(Debug, Clone)]
pub struct CnfFormula {
    /// The clause database.
    pub db: ClauseDb,
    /// Number of distinct variables (0-indexed: variables 0..num_vars).
    pub num_vars: u32,
    /// IDs of the original clauses in insertion order.
    pub clause_ids: Vec<ClauseId>,
}

impl CnfFormula {
    /// Create an empty formula with the given variable count.
    #[must_use]
    pub fn new(num_vars: u32) -> Self {
        Self {
            db: ClauseDb::new(),
            num_vars,
            clause_ids: Vec::new(),
        }
    }

    /// Add a clause to the formula.
    pub fn add_clause(&mut self, lits: &[CnfLiteral]) -> ClauseId {
        // Update num_vars if any literal exceeds current count.
        for lit in lits {
            let v = lit.var() + 1;
            if v > self.num_vars {
                self.num_vars = v;
            }
        }
        let id = self.db.add_clause(lits);
        self.clause_ids.push(id);
        id
    }

    /// Number of active clauses.
    #[must_use]
    pub fn num_clauses(&self) -> usize {
        self.db.active_clauses()
    }
}

// ---------------------------------------------------------------------------
// DIMACS parser
// ---------------------------------------------------------------------------

/// Parse a CNF formula from DIMACS format into a [`CnfFormula`].
///
/// This creates the solver-native `CnfFormula` (as opposed to the existing
/// `Cnf::from_dimacs` which creates `Vec<SatClause>`).
pub fn parse_dimacs(input: &str) -> Result<CnfFormula, CnfError> {
    let mut num_vars = 0u32;
    let mut expected_clauses = 0usize;
    let mut found_header = false;
    let mut formula = CnfFormula::new(0);
    let mut current_lits: Vec<CnfLiteral> = Vec::new();
    let mut clause_count = 0usize;

    for line in input.lines() {
        let trimmed = line.trim();
        if trimmed.is_empty() || trimmed.starts_with('c') {
            continue;
        }
        if trimmed.starts_with("p cnf") || trimmed.starts_with("p CNF") {
            let parts: Vec<&str> = trimmed.split_whitespace().collect();
            if parts.len() < 4 {
                return Err(CnfError::ParseError(
                    "problem line must have format: p cnf <vars> <clauses>".to_string(),
                ));
            }
            num_vars = parts[2]
                .parse()
                .map_err(|e| CnfError::ParseError(format!("bad num_vars: {e}")))?;
            expected_clauses = parts[3]
                .parse()
                .map_err(|e| CnfError::ParseError(format!("bad num_clauses: {e}")))?;
            formula.num_vars = num_vars;
            found_header = true;
            continue;
        }
        if !found_header {
            return Err(CnfError::ParseError(
                "expected 'p cnf ...' header before clause data".to_string(),
            ));
        }
        for token in trimmed.split_whitespace() {
            let val: i32 = token
                .parse()
                .map_err(|e| CnfError::ParseError(format!("bad literal '{token}': {e}")))?;
            if val == 0 {
                formula.add_clause(&current_lits);
                clause_count += 1;
                current_lits.clear();
            } else {
                let var = val.unsigned_abs();
                if var > num_vars {
                    return Err(CnfError::VariableOutOfRange { var, max: num_vars });
                }
                let lit = CnfLiteral::from_dimacs(val).ok_or(CnfError::ZeroLiteral)?;
                current_lits.push(lit);
            }
        }
    }
    // Handle unterminated final clause.
    if !current_lits.is_empty() {
        formula.add_clause(&current_lits);
        clause_count += 1;
    }

    if clause_count != expected_clauses {
        return Err(CnfError::ParseError(format!(
            "expected {expected_clauses} clauses, found {clause_count}"
        )));
    }

    Ok(formula)
}

/// Write a [`CnfFormula`] back to DIMACS format.
#[must_use]
pub fn write_dimacs(formula: &CnfFormula) -> String {
    let mut out = String::new();
    out.push_str(&format!(
        "p cnf {} {}\n",
        formula.num_vars,
        formula.num_clauses()
    ));
    for &cid in &formula.clause_ids {
        if let Some(lits) = formula.db.get_clause(cid) {
            for lit in lits {
                out.push_str(&format!("{} ", lit.to_dimacs()));
            }
            out.push_str("0\n");
        }
    }
    out
}

/// Convert an existing `Cnf` (types.rs) into a `CnfFormula`.
#[must_use]
pub fn from_cnf(cnf: &super::types::Cnf) -> CnfFormula {
    let mut formula = CnfFormula::new(cnf.num_vars);
    for clause in &cnf.clauses {
        let lits: Vec<CnfLiteral> = clause
            .0
            .iter()
            .filter_map(|lit| CnfLiteral::from_lit(*lit))
            .collect();
        formula.add_clause(&lits);
    }
    formula
}

// ---------------------------------------------------------------------------
// WatchList — two-watched-literal index for unit propagation
// ---------------------------------------------------------------------------

/// Two-watched-literal occurrence list for efficient unit propagation.
///
/// Each literal code maps to the set of clause IDs that watch it.
/// This is the standard MiniSat data structure.
#[derive(Debug, Clone)]
pub struct WatchList {
    watches: HashMap<u32, Vec<ClauseId>>,
}

impl WatchList {
    /// Build a watch list from a clause database.
    ///
    /// For each clause, watches the first two literals (or one for unit
    /// clauses).
    #[must_use]
    pub fn build(db: &ClauseDb) -> Self {
        let mut watches: HashMap<u32, Vec<ClauseId>> = HashMap::new();
        for (cid, lits) in db.iter_active() {
            if let Some(first) = lits.first() {
                watches.entry(first.code()).or_default().push(cid);
            }
            if let Some(second) = lits.get(1) {
                watches.entry(second.code()).or_default().push(cid);
            }
        }
        Self { watches }
    }

    /// Get clause IDs watching the given literal.
    #[must_use]
    pub fn watchers(&self, lit: CnfLiteral) -> &[ClauseId] {
        self.watches
            .get(&lit.code())
            .map(Vec::as_slice)
            .unwrap_or(&[])
    }
}

// ---------------------------------------------------------------------------
// DimacsVarMap — bidirectional ay internal ↔ DIMACS variable mapping
// ---------------------------------------------------------------------------

/// Bidirectional mapping between ay internal variable IDs (0-indexed)
/// and DIMACS variable IDs (1-indexed).
///
/// The ay solver uses compact 0-indexed variable IDs internally, but
/// DIMACS format and external proof logs use 1-indexed IDs. This map
/// handles the translation in both directions, including cases where
/// internal and external IDs are not simply offset by 1 (e.g., when
/// variables have been eliminated or reordered).
#[derive(Debug, Clone)]
pub struct DimacsVarMap {
    /// internal → DIMACS (1-indexed)
    to_dimacs: HashMap<u32, u32>,
    /// DIMACS (1-indexed) → internal
    from_dimacs: HashMap<u32, u32>,
}

impl DimacsVarMap {
    /// Create an empty variable map.
    #[must_use]
    pub fn new() -> Self {
        Self {
            to_dimacs: HashMap::new(),
            from_dimacs: HashMap::new(),
        }
    }

    /// Create an identity map for variables 0..num_vars.
    ///
    /// Internal variable `i` maps to DIMACS variable `i + 1`.
    #[must_use]
    pub fn create_identity(num_vars: u32) -> Self {
        let mut map = Self::new();
        for i in 0..num_vars {
            map.insert(i, i + 1);
        }
        map
    }

    /// Insert a mapping: internal variable ID ↔ DIMACS variable ID.
    ///
    /// Overwrites any existing mapping for either key.
    pub fn insert(&mut self, internal: u32, dimacs: u32) {
        self.to_dimacs.insert(internal, dimacs);
        self.from_dimacs.insert(dimacs, internal);
    }

    /// Map an internal variable ID to its DIMACS ID.
    #[must_use]
    pub fn to_dimacs(&self, internal: u32) -> Option<u32> {
        self.to_dimacs.get(&internal).copied()
    }

    /// Map a DIMACS variable ID to its internal ID.
    #[must_use]
    pub fn from_dimacs(&self, dimacs: u32) -> Option<u32> {
        self.from_dimacs.get(&dimacs).copied()
    }

    /// Map a DIMACS signed literal to an internal signed literal.
    ///
    /// Preserves sign, translates only the variable part.
    /// Returns `None` if the variable is not in the map or literal is zero.
    #[must_use]
    pub fn literal_from_dimacs(&self, dimacs_lit: i32) -> Option<i32> {
        if dimacs_lit == 0 {
            return None;
        }
        let var = dimacs_lit.unsigned_abs();
        let internal = self.from_dimacs.get(&var)?;
        let sign = if dimacs_lit > 0 { 1i32 } else { -1i32 };
        Some(sign * (*internal as i32 + 1))
    }

    /// Map an internal signed literal to a DIMACS signed literal.
    ///
    /// The internal literal uses 1-indexed variable IDs (i.e., sign * (var+1)).
    /// Returns `None` if the variable is not in the map or literal is zero.
    #[must_use]
    pub fn literal_to_dimacs(&self, internal_lit: i32) -> Option<i32> {
        if internal_lit == 0 {
            return None;
        }
        let var = internal_lit.unsigned_abs() - 1;
        let dimacs_var = self.to_dimacs.get(&var)?;
        let sign = if internal_lit > 0 { 1i32 } else { -1i32 };
        Some(sign * (*dimacs_var as i32))
    }

    /// Number of mapped variables.
    #[must_use]
    pub fn len(&self) -> usize {
        self.to_dimacs.len()
    }

    /// Whether the map is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.to_dimacs.is_empty()
    }
}

impl Default for DimacsVarMap {
    fn default() -> Self {
        Self::new()
    }
}

// ---------------------------------------------------------------------------
// ProofLogEntry — structured proof steps for clean replay
// ---------------------------------------------------------------------------

/// A single entry in a structured proof log that clean can replay.
///
/// These entries capture ay's solver operations at a level of detail
/// sufficient for clean to independently verify the solver's reasoning.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum ProofLogEntry {
    /// An original clause from the input formula.
    OriginalClause {
        /// Clause ID in the clause database.
        clause_id: u32,
        /// DIMACS literals.
        literals: Vec<i32>,
    },
    /// A clause learned via conflict analysis.
    LearnedClause {
        /// Clause ID assigned to the learned clause.
        clause_id: u32,
        /// DIMACS literals of the learned clause.
        literals: Vec<i32>,
        /// Clause IDs in the resolution derivation.
        antecedents: Vec<u32>,
    },
    /// A clause was deleted (garbage collected).
    DeleteClause {
        /// ID of the deleted clause.
        clause_id: u32,
    },
    /// A literal was propagated by BCP.
    Propagation {
        /// The propagated DIMACS literal.
        literal: i32,
        /// The clause that forced propagation.
        reason_clause: u32,
    },
    /// A branching decision was made.
    Decision {
        /// The decided DIMACS literal (sign encodes polarity).
        literal: i32,
        /// The decision level after this decision.
        level: u32,
    },
    /// A conflict was detected.
    Conflict {
        /// The conflicting clause ID.
        clause_id: u32,
    },
    /// Backtrack to a given decision level.
    Backtrack {
        /// The target decision level.
        level: u32,
    },
    /// Solver restart (trail cleared to level 0).
    Restart,
    /// Human-readable comment (for debugging only, not verified).
    Comment(String),
}

/// Structured proof logger that records solver operations for clean replay.
///
/// Collects [`ProofLogEntry`] items and tracks active clause IDs for
/// basic consistency checking.
#[derive(Debug, Clone)]
pub struct ProofLogger {
    entries: Vec<ProofLogEntry>,
    active_clauses: std::collections::HashSet<u32>,
}

impl ProofLogger {
    /// Create a new empty proof logger.
    #[must_use]
    pub fn new() -> Self {
        Self {
            entries: Vec::new(),
            active_clauses: std::collections::HashSet::new(),
        }
    }

    /// Log a proof entry.
    ///
    /// For `OriginalClause` and `LearnedClause`, the clause ID is
    /// added to the active set. For `DeleteClause`, it is removed.
    pub fn log(&mut self, entry: ProofLogEntry) {
        match &entry {
            ProofLogEntry::OriginalClause { clause_id, .. }
            | ProofLogEntry::LearnedClause { clause_id, .. } => {
                self.active_clauses.insert(*clause_id);
            }
            ProofLogEntry::DeleteClause { clause_id } => {
                self.active_clauses.remove(clause_id);
            }
            _ => {}
        }
        self.entries.push(entry);
    }

    /// The recorded entries.
    #[must_use]
    pub fn entries(&self) -> &[ProofLogEntry] {
        &self.entries
    }

    /// Number of logged entries.
    #[must_use]
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    /// Whether the log is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// Check whether a clause ID is currently active.
    #[must_use]
    pub fn is_clause_active(&self, clause_id: u32) -> bool {
        self.active_clauses.contains(&clause_id)
    }

    /// Validate that a learned clause's antecedents are all active clauses.
    ///
    /// Returns `true` if every antecedent clause ID is in the active set.
    #[must_use]
    pub fn validate_learned_clause(&self, antecedents: &[u32]) -> bool {
        antecedents
            .iter()
            .all(|id| self.active_clauses.contains(id))
    }
}

impl Default for ProofLogger {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // ---- CnfLiteral encoding tests ----

    #[test]
    fn test_cnfliteral_positive_encoding() {
        let lit = CnfLiteral::positive(5);
        assert_eq!(lit.var(), 5);
        assert!(!lit.sign());
        assert!(lit.is_positive());
        assert_eq!(lit.code(), 10);
    }

    #[test]
    fn test_cnfliteral_negative_encoding() {
        let lit = CnfLiteral::negative(5);
        assert_eq!(lit.var(), 5);
        assert!(lit.sign());
        assert!(!lit.is_positive());
        assert_eq!(lit.code(), 11);
    }

    #[test]
    fn test_cnfliteral_negate_roundtrip() {
        let pos = CnfLiteral::positive(3);
        let neg = pos.negate();
        assert_eq!(neg.var(), 3);
        assert!(neg.sign());
        assert_eq!(neg.negate(), pos);
    }

    #[test]
    fn test_cnfliteral_dimacs_roundtrip() {
        for d in [-7, -1, 1, 42] {
            let lit = CnfLiteral::from_dimacs(d).expect("non-zero DIMACS");
            assert_eq!(lit.to_dimacs(), d);
        }
    }

    #[test]
    fn test_cnfliteral_from_dimacs_zero_is_none() {
        assert!(CnfLiteral::from_dimacs(0).is_none());
    }

    #[test]
    fn test_cnfliteral_lit_conversion() {
        let lit = Lit(3);
        let cnf_lit = CnfLiteral::from_lit(lit).expect("non-zero");
        assert_eq!(cnf_lit.to_lit(), lit);

        let neg_lit = Lit(-5);
        let cnf_neg = CnfLiteral::from_lit(neg_lit).expect("non-zero");
        assert_eq!(cnf_neg.to_lit(), neg_lit);
    }

    // ---- ClauseDb tests ----

    #[test]
    fn test_clausedb_add_and_get() {
        let mut db = ClauseDb::new();
        let lits = vec![CnfLiteral::positive(0), CnfLiteral::negative(1)];
        let id = db.add_clause(&lits);
        let stored = db.get_clause(id).expect("clause should exist");
        // Stored sorted: pos(0)=0, neg(1)=3
        assert_eq!(stored.len(), 2);
        assert_eq!(db.active_clauses(), 1);
        assert_eq!(db.total_clauses(), 1);
    }

    #[test]
    fn test_clausedb_delete() {
        let mut db = ClauseDb::new();
        let id = db.add_clause(&[CnfLiteral::positive(0)]);
        assert!(db.is_active(id));
        assert!(db.delete_clause(id));
        assert!(!db.is_active(id));
        assert!(db.get_clause(id).is_none());
        assert_eq!(db.active_clauses(), 0);
        assert_eq!(db.total_clauses(), 1);
    }

    #[test]
    fn test_clausedb_delete_nonexistent() {
        let mut db = ClauseDb::new();
        assert!(!db.delete_clause(ClauseId(99)));
    }

    #[test]
    fn test_clausedb_dedup_and_sort() {
        let mut db = ClauseDb::new();
        let lits = vec![
            CnfLiteral::negative(2),
            CnfLiteral::positive(0),
            CnfLiteral::negative(2), // duplicate
            CnfLiteral::positive(0), // duplicate
        ];
        let id = db.add_clause(&lits);
        let stored = db.get_clause(id).expect("clause should exist");
        assert_eq!(stored.len(), 2, "duplicates should be removed");
    }

    #[test]
    fn test_clausedb_iter_active() {
        let mut db = ClauseDb::new();
        let id0 = db.add_clause(&[CnfLiteral::positive(0)]);
        let id1 = db.add_clause(&[CnfLiteral::positive(1)]);
        let id2 = db.add_clause(&[CnfLiteral::positive(2)]);
        db.delete_clause(id1);

        let active: Vec<ClauseId> = db.iter_active().map(|(id, _)| id).collect();
        assert_eq!(active, vec![id0, id2]);
    }

    #[test]
    fn test_clausedb_empty_clause() {
        let mut db = ClauseDb::new();
        let id = db.add_clause(&[]);
        let stored = db.get_clause(id).expect("empty clause should exist");
        assert!(stored.is_empty());
    }

    // ---- CnfFormula tests ----

    #[test]
    fn test_cnfformula_add_clause_updates_num_vars() {
        let mut formula = CnfFormula::new(0);
        formula.add_clause(&[CnfLiteral::positive(5), CnfLiteral::negative(10)]);
        assert_eq!(formula.num_vars, 11); // 0-indexed var 10 means 11 vars
    }

    // ---- DIMACS roundtrip ----

    #[test]
    fn test_parse_dimacs_simple() {
        let input = "\
c test comment
p cnf 3 2
1 -2 0
2 3 0
";
        let formula = parse_dimacs(input).expect("should parse");
        assert_eq!(formula.num_vars, 3);
        assert_eq!(formula.num_clauses(), 2);
    }

    #[test]
    fn test_parse_dimacs_variable_out_of_range() {
        let input = "p cnf 2 1\n5 0\n";
        assert!(parse_dimacs(input).is_err());
    }

    #[test]
    fn test_parse_dimacs_clause_count_mismatch() {
        let input = "p cnf 3 2\n1 0\n";
        assert!(parse_dimacs(input).is_err());
    }

    #[test]
    fn test_dimacs_roundtrip() {
        let input = "\
p cnf 3 2
1 -2 0
2 3 0
";
        let formula = parse_dimacs(input).expect("parse");
        let output = write_dimacs(&formula);
        let formula2 = parse_dimacs(&output).expect("reparse");
        assert_eq!(formula2.num_vars, formula.num_vars);
        assert_eq!(formula2.num_clauses(), formula.num_clauses());
    }

    #[test]
    fn test_dimacs_single_unit_clause() {
        let input = "p cnf 1 1\n1 0\n";
        let formula = parse_dimacs(input).expect("parse");
        assert_eq!(formula.num_vars, 1);
        assert_eq!(formula.num_clauses(), 1);
        let lits = formula
            .db
            .get_clause(formula.clause_ids[0])
            .expect("clause");
        assert_eq!(lits.len(), 1);
        assert_eq!(lits[0].to_dimacs(), 1);
    }

    #[test]
    fn test_dimacs_empty_clause() {
        let input = "p cnf 1 1\n0\n";
        let formula = parse_dimacs(input).expect("parse");
        assert_eq!(formula.num_clauses(), 1);
        let lits = formula
            .db
            .get_clause(formula.clause_ids[0])
            .expect("clause");
        assert!(lits.is_empty());
    }

    // ---- from_cnf conversion ----

    #[test]
    fn test_from_cnf_conversion() {
        use super::super::types::{Cnf, SatClause};
        let cnf = Cnf {
            num_vars: 3,
            clauses: vec![
                SatClause(vec![Lit(1), Lit(-2)]),
                SatClause(vec![Lit(2), Lit(3)]),
            ],
        };
        let formula = from_cnf(&cnf);
        assert_eq!(formula.num_vars, 3);
        assert_eq!(formula.num_clauses(), 2);
    }

    // ---- WatchList tests ----

    #[test]
    fn test_watchlist_basic() {
        let mut db = ClauseDb::new();
        let l0 = CnfLiteral::positive(0);
        let l1 = CnfLiteral::negative(1);
        let l2 = CnfLiteral::positive(2);
        let id0 = db.add_clause(&[l0, l1, l2]);
        let id1 = db.add_clause(&[l1, l2]);

        let wl = WatchList::build(&db);
        // id0 watches its first two sorted lits, id1 watches its first two sorted lits
        // After sorting: id0 = [l0(0), l1(3), l2(4)] -> watches l0, l1
        // id1 = [l1(3), l2(4)] -> watches l1, l2
        let w0 = wl.watchers(l0);
        assert!(w0.contains(&id0));
        let w1 = wl.watchers(l1);
        assert!(w1.contains(&id0));
        assert!(w1.contains(&id1));
    }

    #[test]
    fn test_watchlist_unit_clause() {
        let mut db = ClauseDb::new();
        let l0 = CnfLiteral::positive(0);
        let id = db.add_clause(&[l0]);
        let wl = WatchList::build(&db);
        assert!(wl.watchers(l0).contains(&id));
    }

    #[test]
    fn test_watchlist_empty_for_unwatched() {
        let db = ClauseDb::new();
        let wl = WatchList::build(&db);
        assert!(wl.watchers(CnfLiteral::positive(99)).is_empty());
    }

    // ---- DimacsVarMap tests ----

    #[test]
    fn test_dimacs_var_map_identity() {
        let map = DimacsVarMap::create_identity(5);
        assert_eq!(map.len(), 5);
        assert!(!map.is_empty());
        // internal 0 → DIMACS 1, internal 4 → DIMACS 5
        assert_eq!(map.to_dimacs(0), Some(1));
        assert_eq!(map.to_dimacs(4), Some(5));
        assert_eq!(map.from_dimacs(1), Some(0));
        assert_eq!(map.from_dimacs(5), Some(4));
        // Out of range
        assert_eq!(map.to_dimacs(5), None);
        assert_eq!(map.from_dimacs(0), None);
    }

    #[test]
    fn test_dimacs_var_map_custom_mapping() {
        let mut map = DimacsVarMap::new();
        assert!(map.is_empty());
        map.insert(0, 10);
        map.insert(1, 20);
        assert_eq!(map.len(), 2);
        assert_eq!(map.to_dimacs(0), Some(10));
        assert_eq!(map.from_dimacs(20), Some(1));
    }

    #[test]
    fn test_dimacs_var_map_literal_roundtrip() {
        let map = DimacsVarMap::create_identity(10);
        // DIMACS literal 5 → internal, then back
        let internal = map.literal_from_dimacs(5).expect("should map");
        let back = map.literal_to_dimacs(internal).expect("should map back");
        assert_eq!(back, 5);

        // Negative literal
        let internal_neg = map.literal_from_dimacs(-3).expect("should map");
        let back_neg = map
            .literal_to_dimacs(internal_neg)
            .expect("should map back");
        assert_eq!(back_neg, -3);
    }

    #[test]
    fn test_dimacs_var_map_zero_literal_is_none() {
        let map = DimacsVarMap::create_identity(5);
        assert_eq!(map.literal_from_dimacs(0), None);
        assert_eq!(map.literal_to_dimacs(0), None);
    }

    // ---- ProofLogEntry tests ----

    #[test]
    fn test_proof_log_entry_variants() {
        // Verify construction of each variant
        let entries = vec![
            ProofLogEntry::OriginalClause {
                clause_id: 0,
                literals: vec![1, -2],
            },
            ProofLogEntry::LearnedClause {
                clause_id: 1,
                literals: vec![3],
                antecedents: vec![0],
            },
            ProofLogEntry::DeleteClause { clause_id: 0 },
            ProofLogEntry::Propagation {
                literal: -2,
                reason_clause: 1,
            },
            ProofLogEntry::Decision {
                literal: 3,
                level: 1,
            },
            ProofLogEntry::Conflict { clause_id: 2 },
            ProofLogEntry::Backtrack { level: 0 },
            ProofLogEntry::Restart,
            ProofLogEntry::Comment("test".to_owned()),
        ];
        assert_eq!(entries.len(), 9);
    }

    // ---- ProofLogger tests ----

    #[test]
    fn test_proof_logger_basic_logging() {
        let mut logger = ProofLogger::new();
        assert!(logger.is_empty());
        assert_eq!(logger.len(), 0);

        logger.log(ProofLogEntry::OriginalClause {
            clause_id: 0,
            literals: vec![1, -2, 3],
        });
        logger.log(ProofLogEntry::OriginalClause {
            clause_id: 1,
            literals: vec![-1, 4],
        });

        assert_eq!(logger.len(), 2);
        assert!(!logger.is_empty());
        assert!(logger.is_clause_active(0));
        assert!(logger.is_clause_active(1));
    }

    #[test]
    fn test_proof_logger_delete_removes_from_active() {
        let mut logger = ProofLogger::new();
        logger.log(ProofLogEntry::OriginalClause {
            clause_id: 5,
            literals: vec![1],
        });
        assert!(logger.is_clause_active(5));

        logger.log(ProofLogEntry::DeleteClause { clause_id: 5 });
        assert!(!logger.is_clause_active(5));
    }

    #[test]
    fn test_proof_logger_validate_learned_clause() {
        let mut logger = ProofLogger::new();
        logger.log(ProofLogEntry::OriginalClause {
            clause_id: 0,
            literals: vec![1, -2],
        });
        logger.log(ProofLogEntry::OriginalClause {
            clause_id: 1,
            literals: vec![2, 3],
        });

        // Valid: both antecedents are active
        assert!(logger.validate_learned_clause(&[0, 1]));

        // Invalid: clause 99 not active
        assert!(!logger.validate_learned_clause(&[0, 99]));

        // Empty antecedents trivially valid
        assert!(logger.validate_learned_clause(&[]));
    }

    #[test]
    fn test_proof_logger_full_solve_sequence() {
        let mut logger = ProofLogger::new();

        // Original clauses
        logger.log(ProofLogEntry::OriginalClause {
            clause_id: 0,
            literals: vec![1, 2],
        });
        logger.log(ProofLogEntry::OriginalClause {
            clause_id: 1,
            literals: vec![-1, 2],
        });
        logger.log(ProofLogEntry::OriginalClause {
            clause_id: 2,
            literals: vec![1, -2],
        });
        logger.log(ProofLogEntry::OriginalClause {
            clause_id: 3,
            literals: vec![-1, -2],
        });

        // Decision
        logger.log(ProofLogEntry::Decision {
            literal: 1,
            level: 1,
        });

        // Propagation
        logger.log(ProofLogEntry::Propagation {
            literal: 2,
            reason_clause: 0,
        });

        // Conflict
        logger.log(ProofLogEntry::Conflict { clause_id: 3 });

        // Learn
        logger.log(ProofLogEntry::LearnedClause {
            clause_id: 4,
            literals: vec![-1],
            antecedents: vec![0, 3],
        });
        assert!(logger.is_clause_active(4));
        assert!(logger.validate_learned_clause(&[0, 3]));

        // Backtrack
        logger.log(ProofLogEntry::Backtrack { level: 0 });

        assert_eq!(logger.len(), 9);
        assert_eq!(logger.entries().len(), 9);
    }
}
