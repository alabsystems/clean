// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! FRAT (Forward-checking RAT) proof format checker.
//!
//! FRAT is the native proof format emitted by modern top-tier SAT solvers
//! (CaDiCaL, Kissat). Unlike DRAT which requires a backward pass for
//! trimming, FRAT supports forward-only verification with explicit clause
//! IDs, finalization markers, and original/lemma annotations.
//!
//! ## Step Types
//!
//! - `a <id> <literals> 0` -- Add clause with ID
//! - `d <id> <literals> 0` -- Delete clause
//! - `f <id> 0` -- Finalize (mark clause as used in proof)
//! - `o <id> <literals> 0` -- Original clause (from input formula)
//! - `l <id> <literals> 0` -- Lemma (requires RUP/RAT check)
//!
//! ## Forward Checking
//!
//! Steps are processed in order (no backward pass):
//! 1. Original clauses populate the clause database.
//! 2. Lemma additions require RUP or RAT justification against the current
//!    clause database.
//! 3. Deletions remove clauses from the active database.
//! 4. Finalization marks clauses as contributing to the proof.
//! 5. Verification succeeds when the empty clause is derived via a finalized
//!    lemma.
//!
//! ## Binary FRAT
//!
//! Binary FRAT uses single-byte step-type tags followed by ULEB128-encoded
//! clause IDs and signed-LEB128-encoded literals, zero-terminated.
//!
//! ## References
//!
//! - Baek & Carneiro (2021): "A Verified SAT Solver Framework with FRAT
//!   Proofs" (CPP 2021)
//! - CaDiCaL: <https://github.com/arminbiere/cadical>
//! - Kissat: <https://github.com/arminbiere/kissat>

use std::collections::HashMap;

use thiserror::Error;

// ---------------------------------------------------------------------------
// Types
// ---------------------------------------------------------------------------

/// A FRAT clause identifier.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct FratClauseId(pub u64);

impl std::fmt::Display for FratClauseId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

/// A single FRAT proof step.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum FratStep {
    /// `o <id> <literals> 0` -- Original clause from the input formula.
    Original { id: FratClauseId, clause: Vec<i32> },
    /// `a <id> <literals> 0` -- Add a clause (no RUP/RAT check required).
    Add { id: FratClauseId, clause: Vec<i32> },
    /// `l <id> <literals> 0` -- Lemma requiring RUP/RAT justification.
    Lemma { id: FratClauseId, clause: Vec<i32> },
    /// `d <id> <literals> 0` -- Delete a clause from the active database.
    Delete { id: FratClauseId, clause: Vec<i32> },
    /// `f <id> 0` -- Finalize: mark clause as used in the proof.
    Finalize { id: FratClauseId },
}

/// Errors from FRAT parsing or verification.
#[derive(Debug, Clone, PartialEq, Eq, Error)]
#[non_exhaustive]
pub enum FratError {
    /// Text parsing failed.
    #[error("FRAT parse error at line {line}: {message}")]
    ParseError { line: usize, message: String },

    /// Binary parsing failed.
    #[error("FRAT binary parse error at offset {offset}: {message}")]
    BinaryParseError { offset: usize, message: String },

    /// Duplicate clause ID.
    #[error("duplicate clause ID {0}")]
    DuplicateClauseId(FratClauseId),

    /// Referenced clause ID not found in active database.
    #[error("missing clause ID {0}")]
    MissingClauseId(FratClauseId),

    /// RUP check failed for a lemma.
    #[error("RUP check failed for clause {id}: {clause:?}")]
    RupFailed { id: FratClauseId, clause: Vec<i32> },

    /// RAT check failed for a lemma.
    #[error("RAT check failed for clause {id} with pivot {pivot}: {clause:?}")]
    RatFailed {
        id: FratClauseId,
        pivot: i32,
        clause: Vec<i32>,
    },

    /// An `original` step declared a clause that is not present in the input CNF.
    ///
    /// SOUNDNESS: `o` re-declares a clause of the input formula; accepting a clause
    /// not in the formula (e.g. a forged empty clause) would let a satisfiable
    /// formula be falsely certified UNSAT.
    #[error("original clause {clause:?} (id {id}) is not present in the input formula")]
    OriginalNotInFormula { id: FratClauseId, clause: Vec<i32> },

    /// Empty proof (no steps).
    #[error("FRAT proof is empty")]
    EmptyProof,

    /// Proof did not derive the empty clause.
    #[error("proof did not derive the empty clause")]
    NoEmptyClause,

    /// Input data was empty.
    #[error("input data is empty")]
    EmptyInput,

    /// Unknown step type tag.
    #[error("unknown step type '{tag}' at line {line}")]
    UnknownStepType { tag: char, line: usize },
}

/// Result of FRAT proof verification.
#[derive(Debug, Clone)]
pub struct FratResult {
    /// Whether the proof is valid (derives the empty clause).
    pub valid: bool,
    /// Total number of steps processed.
    pub steps_processed: usize,
    /// Number of lemma steps verified via RUP.
    pub rup_checks: usize,
    /// Number of lemma steps verified via RAT.
    pub rat_checks: usize,
    /// Number of finalized clauses.
    pub finalized_count: usize,
    /// Whether the empty clause was finalized (strongest validity).
    pub empty_clause_finalized: bool,
}

// ---------------------------------------------------------------------------
// Text parser
// ---------------------------------------------------------------------------

/// Parse a FRAT proof in text format.
///
/// Each line has the form: `<type> <id> [<literals>] 0`
/// where `<type>` is one of `a`, `d`, `f`, `o`, `l`.
///
/// Comment lines starting with `c` are ignored.
///
/// # Errors
///
/// Returns [`FratError::ParseError`] on malformed lines.
pub fn parse_frat_text(text: &str) -> Result<Vec<FratStep>, FratError> {
    let mut steps = Vec::new();

    for (line_idx, line) in text.lines().enumerate() {
        let line_num = line_idx + 1;
        let trimmed = line.trim();

        if trimmed.is_empty() || trimmed.starts_with('c') {
            continue;
        }

        let mut tokens = trimmed.split_whitespace();

        let tag = tokens.next().ok_or_else(|| FratError::ParseError {
            line: line_num,
            message: "empty line after trim".to_owned(),
        })?;

        let tag_char = match tag.len() {
            1 => tag.chars().next().expect("invariant: single char"),
            _ => {
                return Err(FratError::ParseError {
                    line: line_num,
                    message: format!("expected single-char step type, got '{tag}'"),
                });
            }
        };

        let id_str = tokens.next().ok_or_else(|| FratError::ParseError {
            line: line_num,
            message: "missing clause ID".to_owned(),
        })?;

        let id_val: u64 = id_str.parse().map_err(|_| FratError::ParseError {
            line: line_num,
            message: format!("invalid clause ID '{id_str}'"),
        })?;
        let id = FratClauseId(id_val);

        match tag_char {
            'f' => {
                // Finalize: `f <id> 0` -- consume the trailing 0 if present.
                // Some FRAT files omit the trailing 0 for finalize steps.
                steps.push(FratStep::Finalize { id });
            }
            'o' | 'a' | 'l' | 'd' => {
                let mut clause = Vec::new();
                for tok in tokens {
                    let lit: i32 = tok.parse().map_err(|_| FratError::ParseError {
                        line: line_num,
                        message: format!("invalid literal '{tok}'"),
                    })?;
                    if lit == 0 {
                        break;
                    }
                    clause.push(lit);
                }

                let step = match tag_char {
                    'o' => FratStep::Original { id, clause },
                    'a' => FratStep::Add { id, clause },
                    'l' => FratStep::Lemma { id, clause },
                    'd' => FratStep::Delete { id, clause },
                    _ => unreachable!(),
                };
                steps.push(step);
            }
            other => {
                return Err(FratError::UnknownStepType {
                    tag: other,
                    line: line_num,
                });
            }
        }
    }

    Ok(steps)
}

// ---------------------------------------------------------------------------
// Binary FRAT parser
// ---------------------------------------------------------------------------

/// Binary FRAT step-type tags.
const FRAT_BIN_ORIGINAL: u8 = b'o';
const FRAT_BIN_ADD: u8 = b'a';
const FRAT_BIN_LEMMA: u8 = b'l';
const FRAT_BIN_DELETE: u8 = b'd';
const FRAT_BIN_FINALIZE: u8 = b'f';

/// Parse a FRAT proof in binary format.
///
/// Binary encoding: each step starts with a single-byte tag (`o`/`a`/`l`/`d`/`f`),
/// followed by a ULEB128-encoded clause ID, then (for non-finalize steps)
/// signed-LEB128-encoded literals terminated by 0.
///
/// # Errors
///
/// Returns [`FratError::BinaryParseError`] on truncated or malformed data.
pub fn parse_frat_binary(data: &[u8]) -> Result<Vec<FratStep>, FratError> {
    if data.is_empty() {
        return Err(FratError::EmptyInput);
    }

    let mut steps = Vec::new();
    let mut pos = 0;

    while pos < data.len() {
        // Skip whitespace bytes at boundaries.
        if data[pos].is_ascii_whitespace() {
            pos += 1;
            continue;
        }

        let tag = data[pos];
        let tag_offset = pos;
        pos += 1;

        // Read clause ID (ULEB128).
        let (id_val, bytes_read) =
            read_uleb128(data, pos).map_err(|msg| FratError::BinaryParseError {
                offset: tag_offset,
                message: format!("clause ID: {msg}"),
            })?;
        pos += bytes_read;
        let id = FratClauseId(id_val);

        match tag {
            FRAT_BIN_FINALIZE => {
                // Finalize steps have: tag + id + 0-terminator.
                // Consume the zero terminator if present.
                if pos < data.len() && data[pos] == 0 {
                    pos += 1;
                }
                steps.push(FratStep::Finalize { id });
            }
            FRAT_BIN_ORIGINAL | FRAT_BIN_ADD | FRAT_BIN_LEMMA | FRAT_BIN_DELETE => {
                // Read literals until zero terminator.
                let mut clause = Vec::new();
                loop {
                    if pos >= data.len() {
                        return Err(FratError::BinaryParseError {
                            offset: tag_offset,
                            message: "unexpected EOF reading literals".to_owned(),
                        });
                    }
                    let (lit_val, lit_bytes) =
                        read_sleb128(data, pos).map_err(|msg| FratError::BinaryParseError {
                            offset: pos,
                            message: format!("literal: {msg}"),
                        })?;
                    pos += lit_bytes;
                    if lit_val == 0 {
                        break;
                    }
                    clause.push(lit_val as i32);
                }

                let step = match tag {
                    FRAT_BIN_ORIGINAL => FratStep::Original { id, clause },
                    FRAT_BIN_ADD => FratStep::Add { id, clause },
                    FRAT_BIN_LEMMA => FratStep::Lemma { id, clause },
                    FRAT_BIN_DELETE => FratStep::Delete { id, clause },
                    _ => unreachable!(),
                };
                steps.push(step);
            }
            _ => {
                return Err(FratError::BinaryParseError {
                    offset: tag_offset,
                    message: format!("unknown tag byte 0x{tag:02x}"),
                });
            }
        }
    }

    Ok(steps)
}

/// Read a ULEB128-encoded unsigned integer from `data` starting at `pos`.
///
/// Returns `(value, bytes_consumed)`.
fn read_uleb128(data: &[u8], pos: usize) -> Result<(u64, usize), String> {
    let mut result: u64 = 0;
    let mut shift = 0u32;
    let mut i = pos;

    loop {
        if i >= data.len() {
            return Err("unexpected EOF in ULEB128".to_owned());
        }
        let byte = data[i];
        let low7 = u64::from(byte & 0x7F);
        result |= low7 << shift;
        i += 1;
        if byte & 0x80 == 0 {
            break;
        }
        shift += 7;
        if shift >= 64 {
            return Err("ULEB128 overflow".to_owned());
        }
    }

    Ok((result, i - pos))
}

/// Read a signed LEB128-encoded integer from `data` starting at `pos`.
///
/// Returns `(value, bytes_consumed)`.
fn read_sleb128(data: &[u8], pos: usize) -> Result<(i64, usize), String> {
    let mut result: i64 = 0;
    let mut shift = 0u32;
    let mut i = pos;

    let final_byte = loop {
        if i >= data.len() {
            return Err("unexpected EOF in SLEB128".to_owned());
        }
        let byte = data[i];
        let low7 = i64::from(byte & 0x7F);
        result |= low7 << shift;
        i += 1;
        shift += 7;
        if byte & 0x80 == 0 {
            break byte;
        }
        if shift >= 64 {
            return Err("SLEB128 overflow".to_owned());
        }
    };

    // Sign extend if the high bit of the last byte is set.
    if shift < 64 && (final_byte & 0x40) != 0 {
        result |= -(1i64 << shift);
    }

    Ok((result, i - pos))
}

// ---------------------------------------------------------------------------
// Forward-checking verifier
// ---------------------------------------------------------------------------

/// Clause database entry for forward checking.
#[derive(Debug, Clone)]
struct ClauseEntry {
    clause: Vec<i32>,
    finalized: bool,
}

/// Forward-checking FRAT verifier state.
struct FratVerifier {
    /// Active clause database: clause ID -> clause.
    db: HashMap<u64, ClauseEntry>,
    /// Assignment buffer for unit propagation. Index 0 is unused.
    /// `assignment[var] = Some(polarity)` if assigned.
    assignment: Vec<Option<bool>>,
    /// Variables modified during the current propagation round (for cleanup).
    dirty_vars: Vec<usize>,
    /// Maximum variable index seen.
    max_var: u32,
    /// Whether the empty clause has been derived.
    empty_clause_derived: bool,
    /// Whether the empty clause was finalized.
    empty_clause_finalized: bool,
    /// ID of the empty clause, if derived.
    empty_clause_id: Option<u64>,
    /// Count of finalized clauses.
    finalized_count: usize,
    /// Count of RUP checks performed.
    rup_checks: usize,
    /// Count of RAT checks performed.
    rat_checks: usize,
}

impl FratVerifier {
    fn new(max_var: u32) -> Self {
        let size = max_var as usize + 1;
        Self {
            db: HashMap::new(),
            assignment: vec![None; size],
            dirty_vars: Vec::new(),
            max_var,
            empty_clause_derived: false,
            empty_clause_finalized: false,
            empty_clause_id: None,
            finalized_count: 0,
            rup_checks: 0,
            rat_checks: 0,
        }
    }

    /// Ensure assignment buffer is large enough for `var`.
    fn ensure_capacity(&mut self, var: u32) {
        if var > self.max_var {
            self.max_var = var;
            let new_size = var as usize + 1;
            self.assignment.resize(new_size, None);
        }
    }

    /// Assign a literal in the assignment buffer.
    ///
    /// Returns `true` if the assignment contradicts an existing assignment
    /// (variable already assigned to the opposite polarity), indicating
    /// a conflict was detected.
    fn assign_lit(&mut self, lit: i32) -> bool {
        let var = lit.unsigned_abs() as usize;
        if var >= self.assignment.len() {
            self.ensure_capacity(var as u32);
        }
        let polarity = lit > 0;
        if let Some(existing) = self.assignment[var] {
            // Variable already assigned: conflict if opposite polarity.
            return existing != polarity;
        }
        self.assignment[var] = Some(polarity);
        self.dirty_vars.push(var);
        false
    }

    /// Reset assignment buffer to clean state.
    fn reset_assignment(&mut self) {
        for &var in &self.dirty_vars {
            self.assignment[var] = None;
        }
        self.dirty_vars.clear();
    }

    /// Check if a literal is satisfied under the current assignment.
    fn lit_value(&self, lit: i32) -> Option<bool> {
        let var = lit.unsigned_abs() as usize;
        if var >= self.assignment.len() {
            return None;
        }
        self.assignment[var].map(|polarity| if lit > 0 { polarity } else { !polarity })
    }

    /// Add a clause to the database.
    fn add_clause(&mut self, id: u64, clause: Vec<i32>) -> Result<(), FratError> {
        if self.db.contains_key(&id) {
            return Err(FratError::DuplicateClauseId(FratClauseId(id)));
        }
        if clause.is_empty() {
            self.empty_clause_derived = true;
            self.empty_clause_id = Some(id);
        }
        // Ensure capacity for all variables in the clause.
        for &lit in &clause {
            let var = lit.unsigned_abs();
            if var > self.max_var {
                self.ensure_capacity(var);
            }
        }
        self.db.insert(
            id,
            ClauseEntry {
                clause,
                finalized: false,
            },
        );
        Ok(())
    }

    /// Delete a clause from the database.
    fn delete_clause(&mut self, id: u64) -> Result<(), FratError> {
        if self.db.remove(&id).is_none() {
            return Err(FratError::MissingClauseId(FratClauseId(id)));
        }
        Ok(())
    }

    /// Finalize a clause (mark as used in the proof).
    fn finalize_clause(&mut self, id: u64) -> Result<(), FratError> {
        let entry = self
            .db
            .get_mut(&id)
            .ok_or(FratError::MissingClauseId(FratClauseId(id)))?;
        if !entry.finalized {
            entry.finalized = true;
            self.finalized_count += 1;
            if entry.clause.is_empty() {
                self.empty_clause_finalized = true;
            }
        }
        Ok(())
    }

    /// Perform RUP (Reverse Unit Propagation) check for a clause.
    ///
    /// Negate all literals in the clause, then run unit propagation on
    /// the current database. If propagation derives a conflict, the
    /// clause has the RUP property.
    fn check_rup(&mut self, clause: &[i32]) -> bool {
        self.reset_assignment();

        // Negate each literal in the clause and assign.
        for &lit in clause {
            if self.assign_lit(-lit) {
                // Contradictory assignment from clause itself (e.g., [x, -x]).
                return true;
            }
        }

        // Run unit propagation to fixpoint.
        // Collect unit implications per round to avoid borrow conflict.
        loop {
            let mut found_conflict = false;
            let mut unit_lits = Vec::new();

            for entry in self.db.values() {
                match self.evaluate_clause(&entry.clause) {
                    ClauseEval::Conflict => {
                        found_conflict = true;
                        break;
                    }
                    ClauseEval::Unit(unit_lit) => {
                        unit_lits.push(unit_lit);
                    }
                    ClauseEval::Satisfied | ClauseEval::Unresolved => {}
                }
            }

            if found_conflict {
                return true;
            }

            if unit_lits.is_empty() {
                break;
            }

            for lit in unit_lits {
                if self.assign_lit(lit) {
                    // Contradictory unit propagation: two clauses force
                    // the same variable to opposite polarities.
                    return true;
                }
            }
        }

        false
    }

    /// Perform RAT (Resolution Asymmetric Tautology) check.
    ///
    /// The pivot is the first literal of the clause. For every clause in
    /// the database containing the negation of the pivot, the resolvent
    /// with the lemma must have the RUP property.
    fn check_rat(&mut self, clause: &[i32]) -> bool {
        if clause.is_empty() {
            return false;
        }

        let pivot = clause[0];

        // Collect clause IDs of clauses containing -pivot.
        // We collect first to avoid borrow issues.
        let target_clauses: Vec<Vec<i32>> = self
            .db
            .values()
            .filter(|entry| entry.clause.contains(&(-pivot)))
            .map(|entry| entry.clause.clone())
            .collect();

        // For each such clause, check that the resolvent has RUP.
        for other_clause in &target_clauses {
            // Build resolvent: union of both clauses minus pivot and -pivot.
            let mut resolvent: Vec<i32> = clause.iter().filter(|&&l| l != pivot).copied().collect();
            for &l in other_clause {
                if l != -pivot && !resolvent.contains(&l) {
                    resolvent.push(l);
                }
            }

            // Check if resolvent is a tautology (contains both l and -l).
            let is_tautology = resolvent.iter().any(|&l| resolvent.contains(&(-l)));
            if is_tautology {
                continue;
            }

            if !self.check_rup(&resolvent) {
                return false;
            }
        }

        true
    }

    /// Evaluate a clause under the current assignment.
    fn evaluate_clause(&self, clause: &[i32]) -> ClauseEval {
        let mut unassigned_lit = None;
        let mut unassigned_count = 0;

        for &lit in clause {
            match self.lit_value(lit) {
                Some(true) => return ClauseEval::Satisfied,
                Some(false) => {} // falsified, continue
                None => {
                    unassigned_count += 1;
                    unassigned_lit = Some(lit);
                    if unassigned_count > 1 {
                        return ClauseEval::Unresolved;
                    }
                }
            }
        }

        match unassigned_count {
            0 => ClauseEval::Conflict,
            1 => ClauseEval::Unit(unassigned_lit.expect("invariant: exactly one unassigned")),
            _ => ClauseEval::Unresolved,
        }
    }
}

/// Clause evaluation result during unit propagation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ClauseEval {
    /// All literals are falsified.
    Conflict,
    /// Exactly one literal is unassigned (unit clause).
    Unit(i32),
    /// At least one literal is satisfied.
    Satisfied,
    /// Two or more literals are unassigned.
    Unresolved,
}

// ---------------------------------------------------------------------------
// Public verification API
// ---------------------------------------------------------------------------

/// Verify a FRAT proof against a CNF formula.
///
/// The `cnf` parameter is a slice of clauses, each clause being a slice of
/// DIMACS-format literals (positive = true, negative = negated, 0 is not
/// a valid literal).
///
/// The `proof` parameter is a slice of [`FratStep`]s, typically produced by
/// [`parse_frat_text`] or [`parse_frat_binary`].
///
/// # Errors
///
/// Returns [`FratError`] if the proof is malformed, a RUP/RAT check fails,
/// or the proof does not derive the empty clause.
pub fn verify_frat(cnf: &[Vec<i32>], proof: &[FratStep]) -> Result<FratResult, FratError> {
    if proof.is_empty() {
        return Err(FratError::EmptyProof);
    }

    // Compute max variable from CNF and proof.
    let mut max_var: u32 = 0;
    for clause in cnf {
        for &lit in clause {
            let v = lit.unsigned_abs();
            if v > max_var {
                max_var = v;
            }
        }
    }
    for step in proof {
        let lits = match step {
            FratStep::Original { clause, .. }
            | FratStep::Add { clause, .. }
            | FratStep::Lemma { clause, .. }
            | FratStep::Delete { clause, .. } => clause.as_slice(),
            FratStep::Finalize { .. } => &[],
        };
        for &lit in lits {
            let v = lit.unsigned_abs();
            if v > max_var {
                max_var = v;
            }
        }
    }

    // SOUNDNESS: canonical set of the input CNF clauses (literals sorted+deduped)
    // so that `original` steps can be validated against the actual formula rather
    // than trusted. Without this, a forged `o` clause fabricates a refutation.
    let cnf_set: std::collections::HashSet<Vec<i32>> = cnf
        .iter()
        .map(|c| {
            let mut s = c.clone();
            s.sort_unstable();
            s.dedup();
            s
        })
        .collect();

    let mut verifier = FratVerifier::new(max_var);
    let mut steps_processed = 0;

    // Process each proof step.
    for step in proof {
        steps_processed += 1;

        match step {
            FratStep::Original { id, clause } => {
                // SOUNDNESS: an `original` step re-declares a clause of the input
                // formula; require it to actually be present, else a forged clause
                // (e.g. the empty clause, or foreign contradictory units) could
                // fabricate a refutation of a satisfiable formula.
                let mut canon = clause.clone();
                canon.sort_unstable();
                canon.dedup();
                if !cnf_set.contains(&canon) {
                    return Err(FratError::OriginalNotInFormula {
                        id: *id,
                        clause: clause.clone(),
                    });
                }
                verifier.add_clause(id.0, clause.clone())?;
            }
            FratStep::Add { id, clause } => {
                // SOUNDNESS: an added clause is a lemma and must be RUP/RAT-justified
                // against the current database exactly like `Lemma`; an unjustified
                // add (e.g. of the empty clause) must never be accepted.
                verifier.rup_checks += 1;
                if !verifier.check_rup(clause) {
                    verifier.rat_checks += 1;
                    verifier.rup_checks -= 1; // It was a RAT check, not RUP.
                    if !verifier.check_rat(clause) {
                        return Err(FratError::RupFailed {
                            id: *id,
                            clause: clause.clone(),
                        });
                    }
                }
                verifier.add_clause(id.0, clause.clone())?;
            }
            FratStep::Lemma { id, clause } => {
                // Lemmas require RUP or RAT justification.
                verifier.rup_checks += 1;
                if !verifier.check_rup(clause) {
                    // Try RAT with the first literal as pivot.
                    verifier.rat_checks += 1;
                    verifier.rup_checks -= 1; // It was a RAT check, not RUP.
                    if !verifier.check_rat(clause) {
                        return Err(FratError::RupFailed {
                            id: *id,
                            clause: clause.clone(),
                        });
                    }
                }
                verifier.add_clause(id.0, clause.clone())?;
            }
            FratStep::Delete { id, .. } => {
                verifier.delete_clause(id.0)?;
            }
            FratStep::Finalize { id } => {
                verifier.finalize_clause(id.0)?;
            }
        }
    }

    let valid = verifier.empty_clause_derived;

    Ok(FratResult {
        valid,
        steps_processed,
        rup_checks: verifier.rup_checks,
        rat_checks: verifier.rat_checks,
        finalized_count: verifier.finalized_count,
        empty_clause_finalized: verifier.empty_clause_finalized,
    })
}

// ---------------------------------------------------------------------------
// Format detection helper
// ---------------------------------------------------------------------------

/// Check if data looks like a FRAT text proof.
///
/// FRAT text lines start with one of `a`, `d`, `f`, `o`, `l` followed by a
/// clause ID. This distinguishes it from DRAT (which has no IDs or type
/// prefixes beyond `d`).
#[must_use]
pub fn looks_like_frat_text(text: &str) -> bool {
    let mut frat_lines = 0;
    let mut total_lines = 0;

    for line in text.lines().take(10) {
        let trimmed = line.trim();
        if trimmed.is_empty() || trimmed.starts_with('c') {
            continue;
        }
        total_lines += 1;

        let mut tokens = trimmed.split_whitespace();
        let Some(tag) = tokens.next() else { continue };

        // FRAT tags are single characters from {a, d, f, o, l}.
        if tag.len() == 1 && matches!(tag.as_bytes()[0], b'a' | b'd' | b'f' | b'o' | b'l') {
            // Must be followed by a positive integer (clause ID).
            if let Some(id_tok) = tokens.next() {
                if id_tok.parse::<u64>().is_ok() {
                    frat_lines += 1;
                }
            }
        }
    }

    // FRAT if the majority of non-comment lines match the pattern,
    // and we have distinctive FRAT tags (o, l, f -- not just a/d which
    // overlap with DRAT).
    if total_lines == 0 {
        return false;
    }

    // Need at least one line with a FRAT-specific tag (o, l, or f).
    let has_frat_specific = text.lines().take(20).any(|line| {
        let trimmed = line.trim();
        trimmed.starts_with('o') || trimmed.starts_with('l') || trimmed.starts_with('f')
    });

    frat_lines > 0 && has_frat_specific
}

/// Check if data looks like binary FRAT.
///
/// Binary FRAT starts with a step-type tag byte from {`a`, `d`, `f`, `o`, `l`}
/// followed by ULEB128-encoded data.
#[must_use]
pub fn looks_like_frat_binary(data: &[u8]) -> bool {
    if data.is_empty() {
        return false;
    }

    // Skip leading whitespace.
    let start = data.iter().position(|b| !b.is_ascii_whitespace());
    let Some(start) = start else { return false };

    let tag = data[start];

    // Must start with a FRAT-specific tag (o, l, or f distinguish from DRAT).
    matches!(tag, b'o' | b'l' | b'f')
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    // --- Text parsing ---

    #[test]
    fn test_parse_frat_text_simple() {
        let text = "\
o 1 1 2 0
o 2 -1 2 0
o 3 -2 0
l 4 1 0
l 5 0
f 5 0
";
        let steps = parse_frat_text(text).expect("parse should succeed");
        assert_eq!(steps.len(), 6);

        assert_eq!(
            steps[0],
            FratStep::Original {
                id: FratClauseId(1),
                clause: vec![1, 2],
            }
        );
        assert_eq!(
            steps[1],
            FratStep::Original {
                id: FratClauseId(2),
                clause: vec![-1, 2],
            }
        );
        assert_eq!(
            steps[2],
            FratStep::Original {
                id: FratClauseId(3),
                clause: vec![-2],
            }
        );
        assert_eq!(
            steps[3],
            FratStep::Lemma {
                id: FratClauseId(4),
                clause: vec![1],
            }
        );
        assert_eq!(
            steps[4],
            FratStep::Lemma {
                id: FratClauseId(5),
                clause: vec![],
            }
        );
        assert_eq!(
            steps[5],
            FratStep::Finalize {
                id: FratClauseId(5),
            }
        );
    }

    #[test]
    fn test_parse_frat_text_with_comments() {
        let text = "\
c This is a FRAT proof
o 1 1 0
c Another comment
d 1 1 0
";
        let steps = parse_frat_text(text).expect("parse should succeed");
        assert_eq!(steps.len(), 2);
    }

    #[test]
    fn test_parse_frat_text_add_step() {
        let text = "a 10 3 -4 5 0\n";
        let steps = parse_frat_text(text).expect("parse should succeed");
        assert_eq!(
            steps[0],
            FratStep::Add {
                id: FratClauseId(10),
                clause: vec![3, -4, 5],
            }
        );
    }

    #[test]
    fn test_parse_frat_text_unknown_tag() {
        let text = "x 1 2 0\n";
        let result = parse_frat_text(text);
        assert!(result.is_err());
        match result.unwrap_err() {
            FratError::UnknownStepType { tag, line } => {
                assert_eq!(tag, 'x');
                assert_eq!(line, 1);
            }
            e => panic!("expected UnknownStepType, got {e:?}"),
        }
    }

    #[test]
    fn test_parse_frat_text_empty() {
        let steps = parse_frat_text("").expect("parse empty should succeed");
        assert!(steps.is_empty());
    }

    // --- Verification: simple UNSAT ---

    #[test]
    fn test_verify_frat_simple_unsat() {
        // Formula: (x1) AND (-x1) -- trivially UNSAT.
        let cnf = vec![vec![1], vec![-1]];

        let proof = vec![
            FratStep::Original {
                id: FratClauseId(1),
                clause: vec![1],
            },
            FratStep::Original {
                id: FratClauseId(2),
                clause: vec![-1],
            },
            FratStep::Lemma {
                id: FratClauseId(3),
                clause: vec![],
            },
            FratStep::Finalize {
                id: FratClauseId(3),
            },
        ];

        let result = verify_frat(&cnf, &proof).expect("verification should succeed");
        assert!(result.valid, "proof should be valid");
        assert_eq!(result.steps_processed, 4);
        assert_eq!(result.finalized_count, 1);
        assert!(result.empty_clause_finalized);
    }

    #[test]
    fn test_verify_frat_rup_chain() {
        // Formula: (1 2) AND (-1 2) AND (-2)
        // Derivation: lemma (2) by RUP, then lemma () by RUP.
        let cnf = vec![vec![1, 2], vec![-1, 2], vec![-2]];

        let proof = vec![
            FratStep::Original {
                id: FratClauseId(1),
                clause: vec![1, 2],
            },
            FratStep::Original {
                id: FratClauseId(2),
                clause: vec![-1, 2],
            },
            FratStep::Original {
                id: FratClauseId(3),
                clause: vec![-2],
            },
            FratStep::Lemma {
                id: FratClauseId(4),
                clause: vec![2],
            },
            FratStep::Lemma {
                id: FratClauseId(5),
                clause: vec![],
            },
        ];

        let result = verify_frat(&cnf, &proof).expect("verification should succeed");
        assert!(result.valid, "proof should be valid");
        assert!(result.rup_checks >= 2, "should have at least 2 RUP checks");
    }

    #[test]
    fn test_verify_frat_clause_deletion() {
        // Formula: (1) AND (-1) AND (2) -- UNSAT (x1 must be both T and F).
        // Delete redundant clause (2), then derive empty from (1) and (-1).
        let cnf = vec![vec![1], vec![-1], vec![2]];

        let proof = vec![
            FratStep::Original {
                id: FratClauseId(1),
                clause: vec![1],
            },
            FratStep::Original {
                id: FratClauseId(2),
                clause: vec![-1],
            },
            FratStep::Original {
                id: FratClauseId(3),
                clause: vec![2],
            },
            // Delete the redundant clause (2) -- not needed for the proof.
            FratStep::Delete {
                id: FratClauseId(3),
                clause: vec![2],
            },
            // Derive empty from (1) and (-1) via RUP:
            // Negate nothing => propagate: (1) forces x1=T, (-1) conflict.
            FratStep::Lemma {
                id: FratClauseId(4),
                clause: vec![],
            },
        ];

        let result = verify_frat(&cnf, &proof).expect("verification should succeed");
        assert!(result.valid, "proof should be valid after deletion");
    }

    #[test]
    fn test_verify_frat_finalization_tracking() {
        let cnf = vec![vec![1], vec![-1]];

        let proof = vec![
            FratStep::Original {
                id: FratClauseId(1),
                clause: vec![1],
            },
            FratStep::Original {
                id: FratClauseId(2),
                clause: vec![-1],
            },
            FratStep::Lemma {
                id: FratClauseId(3),
                clause: vec![],
            },
            // Finalize multiple clauses.
            FratStep::Finalize {
                id: FratClauseId(1),
            },
            FratStep::Finalize {
                id: FratClauseId(2),
            },
            FratStep::Finalize {
                id: FratClauseId(3),
            },
        ];

        let result = verify_frat(&cnf, &proof).expect("verification should succeed");
        assert!(result.valid);
        assert_eq!(result.finalized_count, 3);
        assert!(result.empty_clause_finalized);
    }

    // --- SOUNDNESS falsification: forged FRAT proofs MUST be rejected ---
    //
    // Regression for a critical false-proof hole: `original` steps were not bound
    // to the input CNF and `add` steps skipped RUP/RAT justification, so a
    // SATISFIABLE formula could be certified UNSAT. Each proof below refutes the
    // satisfiable formula {(x1)} (model x1=true); verify_frat MUST reject them
    // (Err, or a non-valid result), never report valid=true.

    fn assert_frat_rejected(cnf: &[Vec<i32>], proof: &[FratStep], what: &str) {
        let result = verify_frat(cnf, proof);
        let accepted = matches!(&result, Ok(r) if r.valid);
        assert!(
            !accepted,
            "SOUNDNESS: {what} must NOT certify a satisfiable formula UNSAT; got {result:?}"
        );
    }

    #[test]
    fn test_verify_frat_soundness_forged_original_empty_clause_rejected() {
        // Forgery A: declare the EMPTY clause as an `original` of the CNF (it is not).
        assert_frat_rejected(
            &[vec![1]],
            &[
                FratStep::Original {
                    id: FratClauseId(1),
                    clause: vec![],
                },
                FratStep::Finalize {
                    id: FratClauseId(1),
                },
            ],
            "a forged Original empty clause (not in the CNF)",
        );
    }

    #[test]
    fn test_verify_frat_soundness_forged_unjustified_add_rejected() {
        // Forgery B: add the empty clause with no RUP/RAT justification.
        assert_frat_rejected(
            &[vec![1]],
            &[
                FratStep::Original {
                    id: FratClauseId(2),
                    clause: vec![1],
                },
                FratStep::Add {
                    id: FratClauseId(1),
                    clause: vec![],
                },
                FratStep::Finalize {
                    id: FratClauseId(1),
                },
            ],
            "an unjustified Add of the empty clause",
        );
    }

    #[test]
    fn test_verify_frat_soundness_forged_foreign_originals_rejected() {
        // Forgery C: introduce foreign contradictory `originals` (2) and (-2) that
        // are not in the CNF, then RUP the empty clause from them.
        assert_frat_rejected(
            &[vec![1]],
            &[
                FratStep::Original {
                    id: FratClauseId(1),
                    clause: vec![1],
                },
                FratStep::Original {
                    id: FratClauseId(10),
                    clause: vec![2],
                },
                FratStep::Original {
                    id: FratClauseId(11),
                    clause: vec![-2],
                },
                FratStep::Lemma {
                    id: FratClauseId(12),
                    clause: vec![],
                },
                FratStep::Finalize {
                    id: FratClauseId(12),
                },
            ],
            "forged foreign originals not in the CNF",
        );
    }

    // --- RAT verification ---

    #[test]
    fn test_verify_frat_rat_step() {
        // RAT example: formula (1 2) AND (-2). This is UNSAT (forces x2=F,
        // then (1,2) forces x1=T, but that's satisfiable... wait).
        // Actually (1,2) AND (-2) forces x1=T. That's SAT with x1=T, x2=F.
        //
        // Instead: formula (1 2), (-1). Forces x1=F, then (1,2) forces x2=T.
        // SAT with x1=F, x2=T.
        //
        // For RAT: we need a clause where RUP fails but RAT succeeds.
        // Use: (1, 2), (-2, 3), (-3). Adding (1): negate => x1=F.
        // (1,2): unit(2) => x2=T. (-2,3): -2=F, unit(3) => x3=T. (-3): conflict.
        // That's RUP! Small formulas tend to have RUP.
        //
        // Proper RAT example: formula (1, 2) only. Lemma (1) is NOT RUP
        // (no conflict reachable from x1=F) but IS RAT with pivot 1
        // (no clause contains -1, so RAT is vacuously true).
        // After adding (1), then add (-1) and derive empty.
        let cnf = vec![vec![1, 2]];

        let proof = vec![
            FratStep::Original {
                id: FratClauseId(1),
                clause: vec![1, 2],
            },
            // Lemma (1): NOT RUP (x1=F, (1,2) gives unit(2), x2=T, no conflict).
            // RAT with pivot 1: no clause contains -1 => vacuously true.
            FratStep::Lemma {
                id: FratClauseId(2),
                clause: vec![1],
            },
            // Now add (-1) as a lemma. RUP: x1=T, clause (1) satisfied, clause
            // (1,2) satisfied. NOT RUP. RAT with pivot -1: clauses containing 1:
            // (1,2) and (1). Resolvent of (-1) with (1,2) = (2). RUP of (2):
            // x2=F, clause (1,2): unit(1) => x1=T. Clause (1): satisfied. No
            // conflict. Not RUP for (2).
            // Actually, this won't work for deriving UNSAT from a SAT formula.
            //
            // Let's just verify the RAT step alone works and the proof is not
            // expected to derive empty (since the formula IS satisfiable).
        ];

        let result = verify_frat(&cnf, &proof).expect("verification should succeed");
        // Formula is SAT, so the proof won't derive empty (no valid UNSAT proof).
        // But the RAT step should have been accepted.
        assert!(
            !result.valid,
            "SAT formula should not have valid UNSAT proof"
        );
        assert!(result.rat_checks >= 1, "should have at least 1 RAT check");
    }

    #[test]
    fn test_verify_frat_rat_step_non_vacuous() {
        // Non-vacuous RAT: formula (-1, 2), (-1, -2). This is satisfiable
        // (x1=F). Adding (1, 3) with pivot 1:
        // RUP: negate => x1=F, x3=F. (-1,2) satisfied. (-1,-2) satisfied.
        //   No conflict => NOT RUP.
        // RAT with pivot 1: clauses containing -1: (-1,2) and (-1,-2).
        //   Resolvent of (1,3) with (-1,2) = (3, 2). Tautology? No.
        //     RUP of (3,2): negate => x3=F, x2=F. (-1,2): -1 unassigned,
        //     2=F => unit(-1) => x1=F. (-1,-2): -1=T => satisfied. All
        //     satisfied, no conflict. NOT RUP for resolvent (3,2).
        //
        // Hmm, still failing. The issue is that the base formula is SAT.
        // For a non-vacuous RAT that works, we need resolvents that ARE RUP.
        //
        // Formula: (1, 2), (-1, 2), (-2). UNSAT. Adding (1):
        // RUP: x1=F. (1,2): unit(2) => x2=T. (-2): -2=F => conflict. RUP!
        //
        // For a true RAT-only case, use: (1, 2), (-2, 3), (-3, -1).
        // Adding (-1) with pivot -1:
        // RUP: negate => x1=T. (1,2): 1=T => satisfied. (-2,3): unresolved.
        //   (-3,-1): -1=F, unit(-3) => x3=F. (-2,3): -2 unassigned, 3=F =>
        //   unit(-2) => x2=F. (1,2): 1=T => satisfied. All satisfied, no
        //   conflict. NOT RUP.
        // RAT with pivot -1: clauses containing 1: (1, 2).
        //   Resolvent of (-1) with (1, 2) = (2). RUP of (2):
        //   negate => x2=F. (-2,3): -2=T => satisfied. (-3,-1): unresolved.
        //   (1,2): 1 unassigned, 2=F => unit(1) => x1=T. (-3,-1): -1=F,
        //   unit(-3) => x3=F. (-2,3): satisfied. All satisfied, no conflict.
        //   NOT RUP for (2) either.
        //
        // Getting a working non-trivial RAT example is hard in small formulas.
        // Use the standard DRAT benchmark: blocked clause addition.
        //
        // Formula: (1, 2), (1, -2). Adding (-1):
        // RUP: negate => x1=T. (1,2) satisfied. (1,-2) satisfied. NOT RUP.
        // RAT with pivot -1: clauses containing 1: (1,2) and (1,-2).
        //   Resolvent of (-1) with (1,2) = (2).
        //   Resolvent of (-1) with (1,-2) = (-2).
        //   RUP of (2): x2=F. (1,2): unit(1) => x1=T. (1,-2): satisfied.
        //     All satisfied, no conflict. NOT RUP.
        //   So RAT also fails here.
        //
        // The key insight: RAT succeeds when resolvents are tautologies.
        // A "blocked clause" has all resolvents being tautologies.
        //
        // Formula: (1, 2), (-1, 2). Adding (1, -2):
        // RUP: x1=F, x2=T. (1,2): 1=F, 2=T => satisfied. (-1,2): -1=T =>
        //   satisfied. No conflict. NOT RUP.
        // RAT with pivot 1: clauses containing -1: (-1, 2).
        //   Resolvent of (1, -2) with (-1, 2) = (-2, 2) = tautology.
        //   All resolvents are tautologies => RAT succeeds.
        let cnf = vec![vec![1, 2], vec![-1, 2]];

        let proof = vec![
            FratStep::Original {
                id: FratClauseId(1),
                clause: vec![1, 2],
            },
            FratStep::Original {
                id: FratClauseId(2),
                clause: vec![-1, 2],
            },
            // Lemma (1, -2): NOT RUP, but RAT with pivot 1.
            // The only clause containing -1 is (-1, 2).
            // Resolvent = (-2, 2) = tautology => RAT holds.
            FratStep::Lemma {
                id: FratClauseId(3),
                clause: vec![1, -2],
            },
        ];

        let result = verify_frat(&cnf, &proof).expect("RAT step should be accepted");
        assert!(result.rat_checks >= 1, "should have at least 1 RAT check");
    }

    // --- Invalid proof rejection ---

    #[test]
    fn test_verify_frat_no_empty_clause() {
        let cnf = vec![vec![1], vec![-1]];

        let proof = vec![
            FratStep::Original {
                id: FratClauseId(1),
                clause: vec![1],
            },
            FratStep::Original {
                id: FratClauseId(2),
                clause: vec![-1],
            },
            // No lemma deriving the empty clause.
        ];

        let result = verify_frat(&cnf, &proof).expect("verification should complete");
        assert!(
            !result.valid,
            "proof without empty clause should be invalid"
        );
    }

    #[test]
    fn test_verify_frat_bad_rup() {
        // Formula: (1 2) AND (-1 2)
        // Attempting to add lemma (-2) which is NOT RUP or RAT.
        let cnf = vec![vec![1, 2], vec![-1, 2]];

        let proof = vec![
            FratStep::Original {
                id: FratClauseId(1),
                clause: vec![1, 2],
            },
            FratStep::Original {
                id: FratClauseId(2),
                clause: vec![-1, 2],
            },
            FratStep::Lemma {
                id: FratClauseId(3),
                clause: vec![-2],
            },
        ];

        let result = verify_frat(&cnf, &proof);
        assert!(result.is_err(), "bad RUP should produce error");
        match result.unwrap_err() {
            FratError::RupFailed { id, .. } => {
                assert_eq!(id, FratClauseId(3));
            }
            e => panic!("expected RupFailed, got {e:?}"),
        }
    }

    #[test]
    fn test_verify_frat_duplicate_id() {
        // Both originals are in the CNF (so the CNF-membership check passes and the
        // duplicate-id check is what fires).
        let cnf = vec![vec![1], vec![2]];

        let proof = vec![
            FratStep::Original {
                id: FratClauseId(1),
                clause: vec![1],
            },
            FratStep::Original {
                id: FratClauseId(1),
                clause: vec![2],
            },
        ];

        let result = verify_frat(&cnf, &proof);
        assert!(result.is_err());
        match result.unwrap_err() {
            FratError::DuplicateClauseId(id) => assert_eq!(id, FratClauseId(1)),
            e => panic!("expected DuplicateClauseId, got {e:?}"),
        }
    }

    #[test]
    fn test_verify_frat_empty_proof() {
        let cnf = vec![vec![1]];
        let result = verify_frat(&cnf, &[]);
        assert!(result.is_err());
        match result.unwrap_err() {
            FratError::EmptyProof => {}
            e => panic!("expected EmptyProof, got {e:?}"),
        }
    }

    // --- Round-trip: parse then verify ---

    #[test]
    fn test_frat_roundtrip_parse_verify() {
        let text = "\
o 1 1 2 0
o 2 -1 2 0
o 3 -2 0
l 4 2 0
l 5 0
f 5 0
";
        let cnf = vec![vec![1, 2], vec![-1, 2], vec![-2]];

        let steps = parse_frat_text(text).expect("parse should succeed");
        let result = verify_frat(&cnf, &steps).expect("verification should succeed");
        assert!(result.valid, "round-trip proof should be valid");
        assert!(result.empty_clause_finalized);
    }

    // --- Binary parsing ---

    #[test]
    fn test_parse_frat_binary_simple() {
        // Build a binary FRAT with:
        //   o 1 3 0   (original clause {3})
        //   f 1 0     (finalize clause 1)
        let data = vec![
            // Step 1: o 1 3 0
            b'o', 1, // ULEB128 for 1
            // Literal 3 as SLEB128 = 3 (0x03)
            3, 0, // terminator
            // Step 2: f 1 0
            b'f', 1, // ULEB128 for 1
            0, // terminator
        ];

        let steps = parse_frat_binary(&data).expect("parse should succeed");
        assert_eq!(steps.len(), 2);
        assert_eq!(
            steps[0],
            FratStep::Original {
                id: FratClauseId(1),
                clause: vec![3],
            }
        );
        assert_eq!(
            steps[1],
            FratStep::Finalize {
                id: FratClauseId(1)
            }
        );
    }

    #[test]
    fn test_parse_frat_binary_negative_literal() {
        // Build: l 2 -1 5 0  (lemma clause {-1, 5})
        let data = vec![
            b'l', 2, // ULEB128 for 2
            // SLEB128 for -1: 0x7F (127 unsigned = -1 signed in 7-bit)
            0x7F, // SLEB128 for 5: 0x05
            0x05, // terminator
            0,
        ];

        let steps = parse_frat_binary(&data).expect("parse should succeed");
        assert_eq!(steps.len(), 1);
        assert_eq!(
            steps[0],
            FratStep::Lemma {
                id: FratClauseId(2),
                clause: vec![-1, 5],
            }
        );
    }

    #[test]
    fn test_parse_frat_binary_empty() {
        let result = parse_frat_binary(&[]);
        assert!(result.is_err());
    }

    // --- Format detection ---

    #[test]
    fn test_looks_like_frat_text_positive() {
        let text = "o 1 1 2 0\nl 2 0\nf 2 0\n";
        assert!(looks_like_frat_text(text));
    }

    #[test]
    fn test_looks_like_frat_text_negative_drat() {
        // Pure DRAT: no o/l/f tags.
        let text = "1 2 0\nd 1 2 0\n-1 0\n";
        assert!(!looks_like_frat_text(text));
    }

    #[test]
    fn test_looks_like_frat_binary_positive() {
        let data = [b'o', 1, 3, 0];
        assert!(looks_like_frat_binary(&data));
    }

    #[test]
    fn test_looks_like_frat_binary_negative() {
        // Starts with 'a' which is shared with DRAT.
        let data = [b'a', 1, 0];
        assert!(!looks_like_frat_binary(&data));
    }

    // --- Delete of missing clause ---

    #[test]
    fn test_verify_frat_delete_missing() {
        let cnf = vec![vec![1]];
        let proof = vec![
            FratStep::Original {
                id: FratClauseId(1),
                clause: vec![1],
            },
            FratStep::Delete {
                id: FratClauseId(99),
                clause: vec![1],
            },
        ];

        let result = verify_frat(&cnf, &proof);
        assert!(result.is_err());
        match result.unwrap_err() {
            FratError::MissingClauseId(id) => assert_eq!(id, FratClauseId(99)),
            e => panic!("expected MissingClauseId, got {e:?}"),
        }
    }

    // --- Finalize of missing clause ---

    #[test]
    fn test_verify_frat_finalize_missing() {
        let cnf = vec![vec![1]];
        let proof = vec![
            FratStep::Original {
                id: FratClauseId(1),
                clause: vec![1],
            },
            FratStep::Finalize {
                id: FratClauseId(99),
            },
        ];

        let result = verify_frat(&cnf, &proof);
        assert!(result.is_err());
        match result.unwrap_err() {
            FratError::MissingClauseId(id) => assert_eq!(id, FratClauseId(99)),
            e => panic!("expected MissingClauseId, got {e:?}"),
        }
    }

    // --- Add step (non-lemma, no check required) ---

    #[test]
    fn test_verify_frat_add_step_rup_checked() {
        // Formula (x1) AND (-x1) is UNSAT, so the empty clause is genuinely
        // RUP-derivable. SOUNDNESS: `add` steps are now RUP/RAT-justified like
        // lemmas (previously they skipped the check, which was unsound — see the
        // `..._forged_unjustified_add_rejected` falsification test).
        let cnf = vec![vec![1], vec![-1]];

        let proof = vec![
            FratStep::Original {
                id: FratClauseId(1),
                clause: vec![1],
            },
            FratStep::Original {
                id: FratClauseId(2),
                clause: vec![-1],
            },
            FratStep::Add {
                id: FratClauseId(3),
                clause: vec![],
            },
        ];

        let result = verify_frat(&cnf, &proof).expect("justified add should succeed");
        assert!(result.valid);
        assert!(
            result.rup_checks >= 1,
            "add steps are now RUP-checked, not skipped"
        );
    }

    // ---- Bug #3327: Contradictory unit propagation detection ----

    #[test]
    fn test_verify_frat_contradictory_unit_propagation() {
        // Formula: (x1) AND (-x1) AND (x2) AND (-x2)
        // The empty clause is RUP: negating nothing, then propagating:
        // clause (x1) forces x1=T, clause (-x1) conflicts immediately.
        // This tests that the RUP check detects the conflict properly.
        let cnf = vec![vec![1], vec![-1], vec![2], vec![-2]];

        let proof = vec![
            FratStep::Original {
                id: FratClauseId(1),
                clause: vec![1],
            },
            FratStep::Original {
                id: FratClauseId(2),
                clause: vec![-1],
            },
            FratStep::Original {
                id: FratClauseId(3),
                clause: vec![2],
            },
            FratStep::Original {
                id: FratClauseId(4),
                clause: vec![-2],
            },
            FratStep::Lemma {
                id: FratClauseId(5),
                clause: vec![],
            },
        ];

        let result = verify_frat(&cnf, &proof).expect("verification should succeed");
        assert!(
            result.valid,
            "empty clause should be RUP from contradictory unit clauses"
        );
    }

    #[test]
    fn test_verify_frat_rup_via_contradictory_assignments() {
        // Formula: (x1 v x2) AND (-x1 v x3) AND (-x2 v -x3)
        // Lemma: (x1). Negate to get x1=F.
        // Propagate: (x1 v x2) forces x2=T.
        //            (-x1 v x3) is satisfied (x1=F means -x1=T).
        //            (-x2 v -x3): x2=T, so need to check -x3.
        //            But we don't have x3 assigned... unless (-x1 v x3) propagated.
        //            Wait, (-x1 v x3): -x1=T => satisfied, no propagation.
        //            (-x2 v -x3): x2=T, -x3 unassigned => unit(-x3), assign x3=F.
        //            No further conflict. So (x1) is NOT RUP.
        //
        // Better: (x1 v x2) AND (-x2 v x3) AND (x1 v -x3)
        // Lemma: (x1). Negate: x1=F.
        // (x1 v x2): x1=F => unit(x2), assign x2=T.
        // (-x2 v x3): x2=T => -x2=F => unit(x3), assign x3=T.
        // (x1 v -x3): x1=F, -x3=F => conflict! RUP succeeds.
        let cnf = vec![vec![1, 2], vec![-2, 3], vec![1, -3]];

        let proof = vec![
            FratStep::Original {
                id: FratClauseId(1),
                clause: vec![1, 2],
            },
            FratStep::Original {
                id: FratClauseId(2),
                clause: vec![-2, 3],
            },
            FratStep::Original {
                id: FratClauseId(3),
                clause: vec![1, -3],
            },
            FratStep::Lemma {
                id: FratClauseId(4),
                clause: vec![1],
            },
        ];

        let result = verify_frat(&cnf, &proof).expect("verification should succeed");
        // The lemma (x1) is RUP via chain propagation.
        assert!(result.rup_checks >= 1, "should have performed RUP check");
    }

    #[test]
    fn test_verify_frat_self_contradictory_clause_rup() {
        // A tautological clause like (x1 v -x1) is trivially satisfied.
        // But a clause that, when negated, immediately contradicts itself
        // (like the empty clause from a contradictory formula) is RUP.
        //
        // Formula: (x1) AND (-x1). Lemma: (x1 v -x1).
        // Negate: x1=F, x1=T => immediate contradiction => RUP.
        // Then derive empty clause.
        let cnf = vec![vec![1], vec![-1]];

        let proof = vec![
            FratStep::Original {
                id: FratClauseId(1),
                clause: vec![1],
            },
            FratStep::Original {
                id: FratClauseId(2),
                clause: vec![-1],
            },
            // Lemma (x1, -x1): negating gives x1=F AND x1=T => contradiction.
            FratStep::Lemma {
                id: FratClauseId(3),
                clause: vec![1, -1],
            },
            // Now derive empty clause.
            FratStep::Lemma {
                id: FratClauseId(4),
                clause: vec![],
            },
        ];

        let result = verify_frat(&cnf, &proof).expect("verification should succeed");
        assert!(result.valid, "proof should derive the empty clause");
    }
}
