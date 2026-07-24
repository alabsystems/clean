// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! DRAT-to-LRAT proof converter with hint extraction.
//!
//! Converts DRAT (Deletion Resolution Asymmetric Tautology) proofs into
//! LRAT (Linear Resolution Asymmetric Tautology) proofs by adding clause-ID
//! hints that enable linear-time verification. This bridges ay's DRAT output
//! to clean's competition-standard LRAT checker.
//!
//! ## Algorithm
//!
//! Uses a forward-pass approach with tracked unit propagation:
//! 1. Load original CNF clauses into a clause database with sequential IDs.
//! 2. For each DRAT addition step, negate the clause's literals and propagate.
//! 3. During propagation, record which clause IDs caused each unit implication.
//! 4. On conflict, collect the antecedent clause IDs as LRAT hints.
//! 5. Assign a new clause ID and emit an LRAT `Add` step with hints.
//! 6. For deletion steps, emit LRAT `Delete` steps with matching IDs.
//!
//! ## References
//!
//! - Heule et al. (2017): "Trimming while Checking Clausal Proofs"
//! - Cruz-Filipe et al. (2017): "Efficient Certified RAT Verification"
//! - drat-trim: <https://github.com/marijnheule/drat-trim>

use std::io;

use super::cdcl::proof_logging::{parse_drat_proof, ProofStep};
use super::lrat::{ClauseId, LratChecker, LratResult, LratStep};
use super::types::Lit;
use thiserror::Error;

/// Errors from the DRAT-to-LRAT conversion process.
#[derive(Debug, Clone, PartialEq, Eq, Error)]
#[non_exhaustive]
pub enum ConvertError {
    /// DRAT proof parsing failed.
    #[error("DRAT parse error: {0}")]
    DratParse(String),

    /// RUP check failed: could not derive conflict from clause negation.
    #[error("RUP check failed at step {step}: clause {clause:?} is not implied")]
    RupFailed {
        /// Zero-based step index in the DRAT proof.
        step: usize,
        /// The clause that failed RUP.
        clause: Vec<i32>,
    },

    /// RAT check failed (not yet supported in the converter).
    #[error("RAT conversion not supported at step {step}: clause {clause:?}")]
    RatNotSupported {
        /// Zero-based step index.
        step: usize,
        /// The clause that requires RAT.
        clause: Vec<i32>,
    },

    /// A deletion step referenced a clause not in the database.
    #[error("deletion of unknown clause at step {step}: {clause:?}")]
    DeletionNotFound {
        /// Zero-based step index.
        step: usize,
        /// The clause attempted to be deleted.
        clause: Vec<i32>,
    },

    /// The proof did not derive the empty clause (required for UNSAT).
    #[error("proof did not derive the empty clause")]
    NoEmptyClause,

    /// I/O error during streaming parse.
    #[error("I/O error: {0}")]
    IoError(String),

    /// LRAT verification failed during streaming DRAT-to-LRAT conversion.
    #[error("LRAT verification error: {0}")]
    LratError(String),
}

/// Result of evaluating a clause under a partial assignment during propagation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ClauseEval {
    /// All literals falsified.
    Conflict,
    /// Exactly one literal unassigned (returns the literal).
    Unit(i32),
    /// At least one literal satisfied.
    Satisfied,
    /// Two or more literals unassigned.
    Unresolved,
}

/// An entry in the clause database, pairing a clause with its ID.
#[derive(Debug, Clone)]
struct DbEntry {
    id: u64,
    clause: Vec<i32>,
}

/// Clause database with assignment tracking for unit propagation.
///
/// Supports efficient clause lookup and propagation with antecedent tracking.
struct ClauseDatabase {
    /// All active clauses (original + derived).
    entries: Vec<DbEntry>,
    /// Next clause ID to assign.
    next_id: u64,
    /// Assignment buffer: `assignment[var] = Some(polarity)` if assigned.
    /// Index 0 is unused; variables are 1-indexed.
    assignment: Vec<Option<bool>>,
    /// Variables that were dirtied in the current propagation, for cleanup.
    dirty_vars: Vec<usize>,
    /// Antecedent clause ID for each assigned variable.
    /// `antecedent[var] = Some(clause_id)` if the variable was forced by
    /// unit propagation from that clause.
    antecedent: Vec<Option<u64>>,
}

impl ClauseDatabase {
    /// Create a new clause database for formulas over `num_vars` variables.
    fn new(num_vars: u32) -> Self {
        let size = num_vars as usize + 1;
        Self {
            entries: Vec::new(),
            next_id: 1,
            assignment: vec![None; size],
            dirty_vars: Vec::new(),
            antecedent: vec![None; size],
        }
    }

    /// Add a clause and return its assigned ID.
    fn add_clause(&mut self, clause: Vec<i32>) -> u64 {
        let id = self.next_id;
        self.next_id += 1;
        self.entries.push(DbEntry { id, clause });
        id
    }

    /// Add a clause with a specific ID (used for derived clauses).
    fn add_clause_with_id(&mut self, id: u64, clause: Vec<i32>) {
        self.entries.push(DbEntry { id, clause });
        if id >= self.next_id {
            self.next_id = id + 1;
        }
    }

    /// Remove the first clause matching `target` (set-equality) and return its ID.
    fn remove_clause(&mut self, target: &[i32]) -> Option<u64> {
        let mut sorted_target = target.to_vec();
        sorted_target.sort_unstable();
        if let Some(pos) = self.entries.iter().position(|e| {
            let mut sorted = e.clause.clone();
            sorted.sort_unstable();
            sorted == sorted_target
        }) {
            let removed = self.entries.remove(pos);
            Some(removed.id)
        } else {
            None
        }
    }

    /// Attempt RUP verification for `clause` and collect hint clause IDs.
    ///
    /// Returns `Ok(hints)` with the ordered list of antecedent clause IDs
    /// if propagation derives a conflict, or `Err(())` if RUP fails.
    fn rup_check(&mut self, clause: &[i32]) -> Result<Vec<i64>, ()> {
        self.clear_assignment();

        // Negate each literal in the clause and assign.
        for &lit in clause {
            let var = lit.unsigned_abs() as usize;
            let polarity = lit > 0;
            // Assign negation.
            let neg_polarity = !polarity;

            if let Some(existing) = self.assignment.get(var).copied().flatten() {
                if existing != neg_polarity {
                    // Contradictory assignment from clause itself: trivial RUP.
                    // Collect hints from the trail so far.
                    let hints = self.collect_conflict_hints();
                    self.clear_assignment();
                    return Ok(hints);
                }
                // Already assigned to the same value, skip.
            } else {
                self.set_var(var, neg_polarity, None);
            }
        }

        // Propagate until conflict or fixpoint.
        loop {
            let mut progress = false;
            for idx in 0..self.entries.len() {
                let entry_id = self.entries[idx].id;
                match self.eval_clause_at(idx) {
                    ClauseEval::Conflict => {
                        let mut hints = self.collect_conflict_hints();
                        // Add the conflicting clause itself as the final hint.
                        hints.push(entry_id as i64);
                        self.clear_assignment();
                        return Ok(hints);
                    }
                    ClauseEval::Unit(unit_lit) => {
                        let var = unit_lit.unsigned_abs() as usize;
                        let polarity = unit_lit > 0;
                        if let Some(existing) = self.assignment.get(var).copied().flatten() {
                            if existing != polarity {
                                // Contradiction: this unit propagation conflicts.
                                let mut hints = self.collect_conflict_hints();
                                hints.push(entry_id as i64);
                                self.clear_assignment();
                                return Ok(hints);
                            }
                            // Already assigned same value, no conflict.
                        } else {
                            self.set_var(var, polarity, Some(entry_id));
                            progress = true;
                        }
                    }
                    ClauseEval::Satisfied | ClauseEval::Unresolved => {}
                }
            }
            if !progress {
                self.clear_assignment();
                return Err(());
            }
        }
    }

    /// Evaluate clause at `entries[idx]` under current assignment.
    fn eval_clause_at(&self, idx: usize) -> ClauseEval {
        let clause = &self.entries[idx].clause;
        let mut unassigned: Option<i32> = None;
        for &lit in clause {
            let var = lit.unsigned_abs() as usize;
            let polarity = lit > 0;
            match self.assignment.get(var).copied().flatten() {
                Some(val) if val == polarity => return ClauseEval::Satisfied,
                Some(_) => {} // Falsified.
                None => match unassigned {
                    None => unassigned = Some(lit),
                    Some(_) => return ClauseEval::Unresolved,
                },
            }
        }
        match unassigned {
            Some(lit) => ClauseEval::Unit(lit),
            None => ClauseEval::Conflict,
        }
    }

    /// Collect antecedent clause IDs from the current propagation trail.
    fn collect_conflict_hints(&self) -> Vec<i64> {
        let mut hints = Vec::new();
        for &var_idx in &self.dirty_vars {
            if let Some(Some(ante_id)) = self.antecedent.get(var_idx) {
                if !hints.contains(&(*ante_id as i64)) {
                    hints.push(*ante_id as i64);
                }
            }
        }
        hints
    }

    /// Assign a variable and track it for cleanup.
    fn set_var(&mut self, var: usize, polarity: bool, ante: Option<u64>) {
        if var < self.assignment.len() {
            self.assignment[var] = Some(polarity);
            self.antecedent[var] = ante;
            self.dirty_vars.push(var);
        }
    }

    /// Clear all assignments made during the current propagation.
    fn clear_assignment(&mut self) {
        for &idx in &self.dirty_vars {
            self.assignment[idx] = None;
            self.antecedent[idx] = None;
        }
        self.dirty_vars.clear();
    }

    /// Grow internal buffers if a variable exceeds the current capacity.
    fn ensure_var_capacity(&mut self, var: u32) {
        let needed = var as usize + 1;
        if needed > self.assignment.len() {
            self.assignment.resize(needed, None);
            self.antecedent.resize(needed, None);
        }
    }
}

/// Convert a DRAT proof to LRAT by extracting propagation hints.
///
/// Takes the original CNF formula as a slice of clauses (each clause is a
/// `Vec<i32>` of DIMACS literals) and the parsed DRAT proof steps, and
/// returns the equivalent LRAT proof steps with clause-ID hints.
///
/// # Errors
///
/// Returns [`ConvertError`] if a DRAT step cannot be converted (e.g.,
/// RUP check fails and RAT is required but not supported).
pub fn convert_drat_to_lrat(
    cnf: &[Vec<i32>],
    drat_steps: &[ProofStep],
) -> Result<Vec<LratStep>, ConvertError> {
    // Determine num_vars from the formula.
    let mut num_vars = 0u32;
    for clause in cnf {
        for &lit in clause {
            let var = lit.unsigned_abs();
            if var > num_vars {
                num_vars = var;
            }
        }
    }
    // Also scan the proof steps for variables.
    for step in drat_steps {
        let lits = match step {
            ProofStep::Add(c) | ProofStep::Delete(c) => c,
        };
        for &lit in lits {
            let var = lit.unsigned_abs();
            if var > num_vars {
                num_vars = var;
            }
        }
    }

    let mut db = ClauseDatabase::new(num_vars);

    // Load original clauses.
    for clause in cnf {
        db.add_clause(clause.clone());
    }

    let mut lrat_steps = Vec::new();

    for (step_idx, step) in drat_steps.iter().enumerate() {
        match step {
            ProofStep::Add(clause) => {
                // Ensure capacity for any new variables.
                for &lit in clause.iter() {
                    db.ensure_var_capacity(lit.unsigned_abs());
                }

                // Try RUP verification with hint extraction.
                let hints = db.rup_check(clause).map_err(|()| ConvertError::RupFailed {
                    step: step_idx,
                    clause: clause.clone(),
                })?;

                // Assign a new ID and add to database.
                let new_id = db.next_id;
                db.add_clause_with_id(new_id, clause.clone());

                // Convert to LRAT literals.
                let lrat_clause: Vec<Lit> = clause.iter().map(|&l| Lit(l)).collect();

                lrat_steps.push(LratStep::Add {
                    id: ClauseId(new_id),
                    clause: lrat_clause,
                    hints,
                });
            }
            ProofStep::Delete(clause) => {
                if let Some(removed_id) = db.remove_clause(clause) {
                    lrat_steps.push(LratStep::Delete {
                        clause_ids: vec![ClauseId(removed_id)],
                    });
                } else {
                    return Err(ConvertError::DeletionNotFound {
                        step: step_idx,
                        clause: clause.clone(),
                    });
                }
            }
        }
    }

    // A valid UNSAT proof MUST derive the empty clause.
    let has_empty_clause = lrat_steps
        .iter()
        .any(|step| matches!(step, LratStep::Add { clause, .. } if clause.is_empty()));
    if !has_empty_clause {
        return Err(ConvertError::NoEmptyClause);
    }

    Ok(lrat_steps)
}

/// Convert DRAT and CNF text to LRAT text format.
///
/// Parses DIMACS CNF and DRAT text, performs conversion, and returns the
/// LRAT proof as formatted text lines.
///
/// # Errors
///
/// Returns [`ConvertError`] on parse failure or conversion failure.
pub fn convert_drat_to_lrat_text(cnf_text: &str, drat_text: &str) -> Result<String, ConvertError> {
    // Parse the CNF formula from DIMACS.
    let cnf_clauses = parse_dimacs_clauses(cnf_text)?;

    // Parse the DRAT proof.
    let drat_steps =
        parse_drat_proof(drat_text).map_err(|e| ConvertError::DratParse(e.to_string()))?;

    // Convert.
    let lrat_steps = convert_drat_to_lrat(&cnf_clauses, &drat_steps)?;

    // Format as LRAT text.
    let mut output = String::new();
    for step in &lrat_steps {
        match step {
            LratStep::Add { id, clause, hints } => {
                output.push_str(&id.0.to_string());
                for lit in clause {
                    output.push(' ');
                    output.push_str(&lit.0.to_string());
                }
                output.push_str(" 0");
                for hint in hints {
                    output.push(' ');
                    output.push_str(&hint.to_string());
                }
                output.push_str(" 0\n");
            }
            LratStep::Delete { clause_ids } => {
                if let Some(first_id) = clause_ids.first() {
                    output.push_str(&first_id.0.to_string());
                    output.push_str(" d");
                    for cid in clause_ids.iter().skip(1) {
                        output.push(' ');
                        output.push_str(&cid.0.to_string());
                    }
                    output.push_str(" 0\n");
                }
            }
        }
    }

    Ok(output)
}

/// Parse DIMACS CNF clauses from text, returning just the clause vectors.
fn parse_dimacs_clauses(input: &str) -> Result<Vec<Vec<i32>>, ConvertError> {
    let mut clauses = Vec::new();
    let mut current = Vec::new();
    let mut found_header = false;

    for line in input.lines() {
        let trimmed = line.trim();
        if trimmed.is_empty() || trimmed.starts_with('c') {
            continue;
        }
        if trimmed.starts_with("p cnf") || trimmed.starts_with("p CNF") {
            found_header = true;
            continue;
        }
        if !found_header {
            return Err(ConvertError::DratParse(
                "expected 'p cnf ...' header".to_string(),
            ));
        }
        for token in trimmed.split_whitespace() {
            let val: i32 = token
                .parse()
                .map_err(|e| ConvertError::DratParse(format!("bad literal '{token}': {e}")))?;
            if val == 0 {
                clauses.push(current.clone());
                current.clear();
            } else {
                current.push(val);
            }
        }
    }
    if !current.is_empty() {
        clauses.push(current);
    }

    Ok(clauses)
}

// ---------------------------------------------------------------------------
// Binary DRAT parsing
// ---------------------------------------------------------------------------

/// Read a single unsigned LEB128 value from binary DRAT data.
fn read_drat_uleb128(data: &[u8], offset: &mut usize) -> Result<u32, ConvertError> {
    let mut value = 0u64;
    let mut shift = 0u32;

    loop {
        if *offset >= data.len() {
            return Err(ConvertError::DratParse(format!(
                "unexpected end of binary DRAT data at offset {}",
                *offset
            )));
        }

        let byte = data[*offset];
        *offset += 1;

        value |= u64::from(byte & 0x7f) << shift;

        if byte & 0x80 == 0 {
            return u32::try_from(value).map_err(|_| {
                ConvertError::DratParse(format!("LEB128 value {value} exceeds u32 range"))
            });
        }

        shift += 7;
        if shift >= 35 {
            return Err(ConvertError::DratParse(
                "binary DRAT LEB128 sequence too long".to_string(),
            ));
        }
    }
}

/// Parse a binary DRAT proof into `ProofStep` values.
///
/// Binary DRAT format: each step starts with `b'a'` (add) or `b'd'` (delete),
/// followed by unsigned LEB128-encoded literals (mapping: positive `var*2`,
/// negative `var*2+1`) terminated by a zero byte.
///
/// # Errors
///
/// Returns [`ConvertError::DratParse`] on malformed data.
pub fn parse_drat_binary(data: &[u8]) -> Result<Vec<ProofStep>, ConvertError> {
    let mut steps = Vec::new();
    let mut offset = 0;

    while offset < data.len() {
        // Skip whitespace.
        while offset < data.len() && data[offset].is_ascii_whitespace() {
            offset += 1;
        }
        if offset >= data.len() {
            break;
        }

        let marker = data[offset];
        offset += 1;

        let is_delete = match marker {
            b'a' => false,
            b'd' => true,
            _ => {
                return Err(ConvertError::DratParse(format!(
                    "unexpected binary DRAT marker 0x{marker:02x} at offset {}",
                    offset - 1
                )));
            }
        };

        let mut clause = Vec::new();
        loop {
            let encoded = read_drat_uleb128(data, &mut offset)?;
            if encoded == 0 {
                break;
            }

            let abs_lit = i32::try_from(encoded >> 1).map_err(|_| {
                ConvertError::DratParse(format!("binary DRAT literal {encoded} exceeds i32 range"))
            })?;
            if abs_lit == 0 {
                return Err(ConvertError::DratParse(format!(
                    "invalid binary DRAT literal encoding {encoded}"
                )));
            }

            let literal = if encoded & 1 == 0 { abs_lit } else { -abs_lit };
            clause.push(literal);
        }

        if is_delete {
            steps.push(ProofStep::Delete(clause));
        } else {
            steps.push(ProofStep::Add(clause));
        }
    }

    Ok(steps)
}

/// Convert a binary DRAT proof to LRAT format.
///
/// Parses the binary DRAT data, then delegates to [`convert_drat_to_lrat`]
/// for hint extraction and LRAT step construction.
///
/// # Errors
///
/// Returns [`ConvertError`] on parse or conversion failure.
pub fn convert_drat_binary_to_lrat(
    cnf: &[Vec<i32>],
    drat_data: &[u8],
) -> Result<Vec<LratStep>, ConvertError> {
    let drat_steps = parse_drat_binary(drat_data)?;
    convert_drat_to_lrat(cnf, &drat_steps)
}

/// Encode a DRAT literal as binary DRAT's unsigned literal mapping.
///
/// Positive literal `v` maps to `2*v`, negative literal `-v` maps to `2*v + 1`.
#[cfg(test)]
fn encode_drat_binary_literal(lit: i32) -> u32 {
    let abs = lit.unsigned_abs();
    if lit > 0 {
        abs * 2
    } else {
        abs * 2 + 1
    }
}

/// Encode a u32 as LEB128 for test construction.
#[cfg(test)]
fn write_drat_leb128(mut value: u32) -> Vec<u8> {
    let mut out = Vec::new();
    loop {
        let mut byte = (value & 0x7f) as u8;
        value >>= 7;
        if value != 0 {
            byte |= 0x80;
        }
        out.push(byte);
        if value == 0 {
            return out;
        }
    }
}

// ---------------------------------------------------------------------------
// Streaming DRAT parsing and verification
// ---------------------------------------------------------------------------

/// Read a single unsigned LEB128 value from a reader, one byte at a time.
///
/// Returns `Ok(value)` on success, or `Err` on EOF / overflow.
fn read_drat_uleb128_from_reader<R: io::Read>(reader: &mut R) -> Result<u32, ConvertError> {
    let mut value = 0u64;
    let mut shift = 0u32;
    let mut buf = [0u8; 1];

    loop {
        match reader.read_exact(&mut buf) {
            Ok(()) => {}
            Err(e) if e.kind() == io::ErrorKind::UnexpectedEof => {
                return Err(ConvertError::IoError(
                    "unexpected end of binary DRAT data".to_string(),
                ));
            }
            Err(e) => return Err(ConvertError::IoError(e.to_string())),
        }

        let byte = buf[0];
        value |= u64::from(byte & 0x7f) << shift;

        if byte & 0x80 == 0 {
            return u32::try_from(value).map_err(|_| {
                ConvertError::DratParse(format!("LEB128 value {value} exceeds u32 range"))
            });
        }

        shift += 7;
        if shift >= 35 {
            return Err(ConvertError::DratParse(
                "binary DRAT LEB128 sequence too long".to_string(),
            ));
        }
    }
}

/// Parse one binary DRAT step from a `BufRead` source.
///
/// Returns `Ok(Some(step))` for each decoded step, or `Ok(None)` at EOF.
/// Binary DRAT format: `b'a'` (add) or `b'd'` (delete), followed by
/// unsigned LEB128-encoded literals terminated by a zero byte.
///
/// # Errors
///
/// Returns [`ConvertError`] on malformed data or I/O failure.
pub fn parse_drat_binary_streaming<R: io::BufRead>(
    reader: &mut R,
) -> Result<Option<ProofStep>, ConvertError> {
    // Skip whitespace and detect EOF.
    let marker = loop {
        let mut tag_buf = [0u8; 1];
        match reader.read_exact(&mut tag_buf) {
            Ok(()) => {
                if !tag_buf[0].is_ascii_whitespace() {
                    break tag_buf[0];
                }
            }
            Err(e) if e.kind() == io::ErrorKind::UnexpectedEof => return Ok(None),
            Err(e) => return Err(ConvertError::IoError(e.to_string())),
        }
    };

    let is_delete = match marker {
        b'a' => false,
        b'd' => true,
        _ => {
            return Err(ConvertError::DratParse(format!(
                "unexpected binary DRAT marker 0x{marker:02x}"
            )));
        }
    };

    let mut clause = Vec::new();
    loop {
        let encoded = read_drat_uleb128_from_reader(reader)?;
        if encoded == 0 {
            break;
        }

        let abs_lit = i32::try_from(encoded >> 1).map_err(|_| {
            ConvertError::DratParse(format!("binary DRAT literal {encoded} exceeds i32 range"))
        })?;
        if abs_lit == 0 {
            return Err(ConvertError::DratParse(format!(
                "invalid binary DRAT literal encoding {encoded}"
            )));
        }

        let literal = if encoded & 1 == 0 { abs_lit } else { -abs_lit };
        clause.push(literal);
    }

    if is_delete {
        Ok(Some(ProofStep::Delete(clause)))
    } else {
        Ok(Some(ProofStep::Add(clause)))
    }
}

/// Parse one text DRAT step from a `BufRead` source.
///
/// Returns `Ok(Some(step))` for each decoded line, or `Ok(None)` at EOF.
/// Text DRAT format: optional `d ` prefix (delete), then literals separated
/// by whitespace, terminated by `0`.
///
/// # Errors
///
/// Returns [`ConvertError`] on malformed data or I/O failure.
pub fn parse_drat_text_streaming<R: io::BufRead>(
    reader: &mut R,
) -> Result<Option<ProofStep>, ConvertError> {
    let mut line = String::new();
    loop {
        line.clear();
        let bytes_read = reader
            .read_line(&mut line)
            .map_err(|e| ConvertError::IoError(e.to_string()))?;
        if bytes_read == 0 {
            return Ok(None);
        }

        let trimmed = line.trim();
        if trimmed.is_empty() || trimmed.starts_with('c') {
            continue;
        }

        let is_delete = trimmed.starts_with('d');
        let content = if is_delete {
            trimmed[1..].trim_start()
        } else {
            trimmed
        };

        let mut clause = Vec::new();
        for token in content.split_whitespace() {
            let val: i32 = token
                .parse()
                .map_err(|e| ConvertError::DratParse(format!("bad DRAT literal '{token}': {e}")))?;
            if val == 0 {
                break;
            }
            clause.push(val);
        }

        if is_delete {
            return Ok(Some(ProofStep::Delete(clause)));
        } else {
            return Ok(Some(ProofStep::Add(clause)));
        }
    }
}

/// Streaming DRAT-to-LRAT conversion result.
#[derive(Debug, Clone)]
pub struct StreamingConvertResult {
    /// The converted LRAT steps.
    pub lrat_steps: Vec<LratStep>,
    /// Number of DRAT steps processed.
    pub steps_processed: usize,
    /// Whether the proof derived the empty clause.
    pub derived_empty_clause: bool,
}

/// Convert a streaming DRAT proof to LRAT, maintaining only the active clause database.
///
/// Reads DRAT steps one at a time from a `BufRead` source, performs RUP hint
/// extraction for each step, and accumulates the resulting LRAT steps. The
/// clause database grows and shrinks as clauses are added and deleted, keeping
/// memory proportional to the active clause set rather than the full proof.
///
/// Set `binary` to `true` for binary DRAT format, `false` for text.
///
/// # Errors
///
/// Returns [`ConvertError`] on parse failure, RUP check failure, or I/O error.
pub fn convert_drat_to_lrat_streaming<R: io::BufRead>(
    cnf: &[Vec<i32>],
    mut reader: R,
    binary: bool,
) -> Result<StreamingConvertResult, ConvertError> {
    let mut num_vars = 0u32;
    for clause in cnf {
        for &lit in clause {
            let var = lit.unsigned_abs();
            if var > num_vars {
                num_vars = var;
            }
        }
    }

    let mut db = ClauseDatabase::new(num_vars);
    for clause in cnf {
        db.add_clause(clause.clone());
    }

    let mut lrat_steps = Vec::new();
    let mut step_idx = 0usize;
    let mut derived_empty_clause = false;

    loop {
        let step = if binary {
            parse_drat_binary_streaming(&mut reader)?
        } else {
            parse_drat_text_streaming(&mut reader)?
        };

        let Some(step) = step else {
            break;
        };

        match step {
            ProofStep::Add(clause) => {
                for &lit in &clause {
                    db.ensure_var_capacity(lit.unsigned_abs());
                }

                let hints = db
                    .rup_check(&clause)
                    .map_err(|()| ConvertError::RupFailed {
                        step: step_idx,
                        clause: clause.clone(),
                    })?;

                let new_id = db.next_id;
                db.add_clause_with_id(new_id, clause.clone());

                let lrat_clause: Vec<Lit> = clause.iter().map(|&l| Lit(l)).collect();

                if lrat_clause.is_empty() {
                    derived_empty_clause = true;
                }

                lrat_steps.push(LratStep::Add {
                    id: ClauseId(new_id),
                    clause: lrat_clause,
                    hints,
                });
            }
            ProofStep::Delete(clause) => {
                if let Some(removed_id) = db.remove_clause(&clause) {
                    lrat_steps.push(LratStep::Delete {
                        clause_ids: vec![ClauseId(removed_id)],
                    });
                } else {
                    return Err(ConvertError::DeletionNotFound {
                        step: step_idx,
                        clause,
                    });
                }
            }
        }

        step_idx += 1;
    }

    if !derived_empty_clause {
        return Err(ConvertError::NoEmptyClause);
    }

    Ok(StreamingConvertResult {
        lrat_steps,
        steps_processed: step_idx,
        derived_empty_clause,
    })
}

/// Streaming DRAT verification result.
#[derive(Debug, Clone)]
pub struct StreamingVerifyResult {
    /// Whether the DRAT proof verified successfully (LRAT verified + empty clause).
    pub valid: bool,
    /// Number of DRAT steps processed.
    pub drat_steps_processed: usize,
    /// Number of LRAT steps verified.
    pub lrat_steps_verified: usize,
    /// Whether the proof derived the empty clause.
    pub derived_empty_clause: bool,
}

/// Convert and verify a DRAT proof in a single streaming pass.
///
/// This is the combined convert + verify pipeline: reads DRAT steps from a
/// streaming source, converts each to LRAT with hint extraction, and immediately
/// verifies each LRAT step against the LRAT checker. The LRAT proof is never
/// fully materialized in memory.
///
/// Set `binary` to `true` for binary DRAT format, `false` for text.
///
/// # Errors
///
/// Returns [`ConvertError`] on parse failure, RUP check failure, LRAT
/// verification failure, or I/O error.
pub fn verify_drat_streaming<R: io::BufRead>(
    cnf: &[Vec<i32>],
    mut reader: R,
    binary: bool,
) -> Result<StreamingVerifyResult, ConvertError> {
    // Determine num_vars from CNF.
    let mut num_vars = 0u32;
    for clause in cnf {
        for &lit in clause {
            let var = lit.unsigned_abs();
            if var > num_vars {
                num_vars = var;
            }
        }
    }

    let mut db = ClauseDatabase::new(num_vars);
    let mut checker = LratChecker::new(num_vars);

    // Load original clauses into both the DRAT clause database and the LRAT checker.
    for (idx, clause) in cnf.iter().enumerate() {
        let id = (idx as u64) + 1;
        db.add_clause_with_id(id, clause.clone());
        let lrat_lits: Vec<Lit> = clause.iter().map(|&l| Lit(l)).collect();
        checker
            .add_original(ClauseId(id), &lrat_lits)
            .map_err(|e| ConvertError::LratError(e.to_string()))?;
    }

    // Ensure next_id is past the originals.
    if !cnf.is_empty() {
        let max_original_id = cnf.len() as u64;
        if db.next_id <= max_original_id {
            db.next_id = max_original_id + 1;
        }
    }

    let mut step_idx = 0usize;
    let mut lrat_steps_verified = 0usize;
    let mut derived_empty_clause = false;

    loop {
        let step = if binary {
            parse_drat_binary_streaming(&mut reader)?
        } else {
            parse_drat_text_streaming(&mut reader)?
        };

        let Some(step) = step else {
            break;
        };

        match step {
            ProofStep::Add(clause) => {
                for &lit in &clause {
                    let var = lit.unsigned_abs();
                    db.ensure_var_capacity(var);
                    // Grow LRAT checker capacity if needed.
                    if var > num_vars {
                        num_vars = var;
                    }
                }

                let hints = db
                    .rup_check(&clause)
                    .map_err(|()| ConvertError::RupFailed {
                        step: step_idx,
                        clause: clause.clone(),
                    })?;

                let new_id = db.next_id;
                db.add_clause_with_id(new_id, clause.clone());

                let lrat_lits: Vec<Lit> = clause.iter().map(|&l| Lit(l)).collect();

                if lrat_lits.is_empty() {
                    derived_empty_clause = true;
                }

                // Verify immediately.
                checker
                    .add_derived(ClauseId(new_id), &lrat_lits, &hints)
                    .map_err(|e| ConvertError::LratError(e.to_string()))?;

                lrat_steps_verified += 1;
            }
            ProofStep::Delete(clause) => {
                if let Some(removed_id) = db.remove_clause(&clause) {
                    checker
                        .delete(ClauseId(removed_id))
                        .map_err(|e| ConvertError::LratError(e.to_string()))?;
                    lrat_steps_verified += 1;
                } else {
                    return Err(ConvertError::DeletionNotFound {
                        step: step_idx,
                        clause,
                    });
                }
            }
        }

        step_idx += 1;
    }

    if !derived_empty_clause {
        return Err(ConvertError::NoEmptyClause);
    }

    Ok(StreamingVerifyResult {
        valid: derived_empty_clause,
        drat_steps_processed: step_idx,
        lrat_steps_verified,
        derived_empty_clause,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sat_verify::lrat::LratChecker;

    // ---- Basic conversion tests ----

    #[test]
    fn test_convert_simple_unsat_two_clauses() {
        // CNF: (x1) AND (-x1) — trivially UNSAT.
        // DRAT proof: add empty clause.
        let cnf = vec![vec![1], vec![-1]];
        let drat_steps = vec![ProofStep::Add(vec![])];

        let lrat_steps =
            convert_drat_to_lrat(&cnf, &drat_steps).expect("conversion should succeed");

        assert_eq!(lrat_steps.len(), 1);
        match &lrat_steps[0] {
            LratStep::Add { id, clause, hints } => {
                assert_eq!(id.0, 3); // Clauses 1,2 are original; derived is 3.
                assert!(clause.is_empty());
                assert!(!hints.is_empty(), "empty clause derivation needs hints");
            }
            _ => panic!("expected Add step"),
        }
    }

    #[test]
    fn test_convert_three_clause_unsat() {
        // CNF: (x1 v x2) AND (-x1) AND (-x2) — UNSAT.
        // DRAT proof: add {x2} (RUP from 1,2), then add {} (RUP from 4,3).
        let cnf = vec![vec![1, 2], vec![-1], vec![-2]];
        let drat_steps = vec![
            ProofStep::Add(vec![2]), // Should be RUP
            ProofStep::Add(vec![]),  // Empty clause
        ];

        let lrat_steps =
            convert_drat_to_lrat(&cnf, &drat_steps).expect("conversion should succeed");

        assert_eq!(lrat_steps.len(), 2);

        // First step: derive {2} with hints.
        match &lrat_steps[0] {
            LratStep::Add { id, clause, hints } => {
                assert_eq!(id.0, 4);
                assert_eq!(clause, &[Lit(2)]);
                assert!(!hints.is_empty());
            }
            _ => panic!("expected Add step"),
        }

        // Second step: derive {} (empty clause).
        match &lrat_steps[1] {
            LratStep::Add { id, clause, hints } => {
                assert_eq!(id.0, 5);
                assert!(clause.is_empty());
                assert!(!hints.is_empty());
            }
            _ => panic!("expected Add step"),
        }
    }

    #[test]
    fn test_convert_with_deletion() {
        // CNF: (x1) AND (-x1) AND (x1 v x2) — UNSAT.
        // DRAT proof: derive empty clause (RUP from clauses 1+2), then delete
        // clause 3, which has no effect on the proof but exercises the path.
        let cnf = vec![vec![1], vec![-1], vec![1, 2]];
        let drat_steps = vec![
            ProofStep::Delete(vec![1, 2]), // Delete clause {x1 v x2}
            ProofStep::Add(vec![]),        // Empty clause, still RUP from {x1},{-x1}
        ];

        let lrat_steps =
            convert_drat_to_lrat(&cnf, &drat_steps).expect("conversion should succeed");

        // Should have a Delete step and an Add step.
        assert_eq!(lrat_steps.len(), 2);
        assert!(matches!(&lrat_steps[0], LratStep::Delete { .. }));
        assert!(matches!(&lrat_steps[1], LratStep::Add { .. }));
    }

    #[test]
    fn test_convert_rup_failure_returns_error() {
        // CNF: (x1 v x2) — SAT, no UNSAT proof possible.
        let cnf = vec![vec![1, 2]];
        let drat_steps = vec![ProofStep::Add(vec![])]; // Empty clause cannot be RUP.

        let result = convert_drat_to_lrat(&cnf, &drat_steps);
        assert!(result.is_err());
        match result.unwrap_err() {
            ConvertError::RupFailed { step, .. } => assert_eq!(step, 0),
            other => panic!("expected RupFailed, got {other:?}"),
        }
    }

    // ---- Round-trip verification tests ----

    #[test]
    fn test_roundtrip_lrat_verify_simple() {
        // Convert DRAT to LRAT, then verify the LRAT with the checker.
        let cnf = vec![vec![1], vec![-1]];
        let drat_steps = vec![ProofStep::Add(vec![])];

        let lrat_steps =
            convert_drat_to_lrat(&cnf, &drat_steps).expect("conversion should succeed");

        // Now verify with LRAT checker.
        let mut checker = LratChecker::new(1);
        checker
            .add_original(ClauseId(1), &[Lit(1)])
            .expect("original clause");
        checker
            .add_original(ClauseId(2), &[Lit(-1)])
            .expect("original clause");

        let result = checker
            .verify_proof(&lrat_steps)
            .expect("LRAT proof should verify");

        assert!(result.refuted, "proof should derive empty clause");
        assert!(result.valid);
    }

    #[test]
    fn test_roundtrip_lrat_verify_three_clause() {
        // (x1 v x2) AND (-x1) AND (-x2) — UNSAT.
        let cnf = vec![vec![1, 2], vec![-1], vec![-2]];
        let drat_steps = vec![ProofStep::Add(vec![2]), ProofStep::Add(vec![])];

        let lrat_steps =
            convert_drat_to_lrat(&cnf, &drat_steps).expect("conversion should succeed");

        let mut checker = LratChecker::new(2);
        checker
            .add_original(ClauseId(1), &[Lit(1), Lit(2)])
            .expect("ok");
        checker.add_original(ClauseId(2), &[Lit(-1)]).expect("ok");
        checker.add_original(ClauseId(3), &[Lit(-2)]).expect("ok");

        let result = checker
            .verify_proof(&lrat_steps)
            .expect("LRAT proof should verify");

        assert!(result.refuted);
        assert!(result.valid);
    }

    #[test]
    fn test_roundtrip_pigeonhole_php21() {
        // Pigeonhole PHP(2,1): 2 pigeons, 1 hole.
        // Variables: p_{i,j} where i=pigeon, j=hole.
        // p_{1,1} = var 1, p_{2,1} = var 2.
        // At-least-one for pigeon 1: (x1)
        // At-least-one for pigeon 2: (x2)
        // At-most-one for hole 1: (-x1 v -x2)
        let cnf = vec![
            vec![1],      // pigeon 1 in hole 1
            vec![2],      // pigeon 2 in hole 1
            vec![-1, -2], // hole 1 has at most one pigeon
        ];

        // DRAT proof: derive {-x2} by RUP (from {-x1,-x2} and {x1}),
        // then derive {} by RUP (from {-x2} and {x2}).
        let drat_steps = vec![ProofStep::Add(vec![-2]), ProofStep::Add(vec![])];

        let lrat_steps =
            convert_drat_to_lrat(&cnf, &drat_steps).expect("PHP conversion should succeed");

        let mut checker = LratChecker::new(2);
        checker.add_original(ClauseId(1), &[Lit(1)]).expect("ok");
        checker.add_original(ClauseId(2), &[Lit(2)]).expect("ok");
        checker
            .add_original(ClauseId(3), &[Lit(-1), Lit(-2)])
            .expect("ok");

        let result = checker
            .verify_proof(&lrat_steps)
            .expect("PHP LRAT proof should verify");

        assert!(result.refuted);
        assert!(result.valid);
    }

    // ---- Text format tests ----

    #[test]
    fn test_convert_text_simple() {
        let cnf_text = "p cnf 1 2\n1 0\n-1 0\n";
        let drat_text = "0\n";

        let lrat_text =
            convert_drat_to_lrat_text(cnf_text, drat_text).expect("text conversion should succeed");

        // Should contain a single line with clause ID and hints.
        assert!(!lrat_text.is_empty());
        // Parse it back as LRAT to verify it is well-formed.
        let steps = crate::sat_verify::lrat::parse_text_lrat(&lrat_text)
            .expect("converted LRAT should parse");
        assert_eq!(steps.len(), 1);
        assert!(matches!(&steps[0], LratStep::Add { clause, .. } if clause.is_empty()));
    }

    #[test]
    fn test_convert_text_three_clause() {
        let cnf_text = "p cnf 2 3\n1 2 0\n-1 0\n-2 0\n";
        let drat_text = "2 0\n0\n";

        let lrat_text =
            convert_drat_to_lrat_text(cnf_text, drat_text).expect("text conversion should succeed");

        let steps = crate::sat_verify::lrat::parse_text_lrat(&lrat_text)
            .expect("converted LRAT should parse");
        assert_eq!(steps.len(), 2);
    }

    #[test]
    fn test_convert_text_invalid_drat() {
        let cnf_text = "p cnf 1 1\n1 0\n";
        let drat_text = "abc 0\n"; // Invalid token.

        let result = convert_drat_to_lrat_text(cnf_text, drat_text);
        assert!(result.is_err());
    }

    // ---- Four-variable UNSAT chain ----

    #[test]
    fn test_roundtrip_four_variable_chain() {
        // (x1 v x2) AND (-x1) AND (-x2 v x3) AND (-x3)
        // DRAT: derive {x2}, derive {x3}, derive {}.
        let cnf = vec![vec![1, 2], vec![-1], vec![-2, 3], vec![-3]];
        let drat_steps = vec![
            ProofStep::Add(vec![2]),
            ProofStep::Add(vec![3]),
            ProofStep::Add(vec![]),
        ];

        let lrat_steps =
            convert_drat_to_lrat(&cnf, &drat_steps).expect("conversion should succeed");

        let mut checker = LratChecker::new(3);
        checker
            .add_original(ClauseId(1), &[Lit(1), Lit(2)])
            .expect("ok");
        checker.add_original(ClauseId(2), &[Lit(-1)]).expect("ok");
        checker
            .add_original(ClauseId(3), &[Lit(-2), Lit(3)])
            .expect("ok");
        checker.add_original(ClauseId(4), &[Lit(-3)]).expect("ok");

        let result = checker
            .verify_proof(&lrat_steps)
            .expect("LRAT proof should verify");

        assert!(result.refuted);
        assert!(result.valid);
    }

    // ---- Bug #3321: Empty clause derivation check ----

    #[test]
    fn test_convert_no_empty_clause_fails() {
        // CNF: (x1 v x2) AND (-x1) AND (-x2) — UNSAT.
        // DRAT proof: derive {x2} but never derive the empty clause.
        let cnf = vec![vec![1, 2], vec![-1], vec![-2]];
        let drat_steps = vec![ProofStep::Add(vec![2])];

        let result = convert_drat_to_lrat(&cnf, &drat_steps);
        assert!(result.is_err());
        match result.unwrap_err() {
            ConvertError::NoEmptyClause => {}
            other => panic!("expected NoEmptyClause, got {other:?}"),
        }
    }

    #[test]
    fn test_convert_text_no_empty_clause_fails() {
        let cnf_text = "p cnf 2 3\n1 2 0\n-1 0\n-2 0\n";
        let drat_text = "2 0\n"; // Derives {2} but not the empty clause.

        let result = convert_drat_to_lrat_text(cnf_text, drat_text);
        assert!(result.is_err());
        match result.unwrap_err() {
            ConvertError::NoEmptyClause => {}
            other => panic!("expected NoEmptyClause, got {other:?}"),
        }
    }

    // ---- Bug #3324: Delete of missing clause ----

    #[test]
    fn test_convert_delete_missing_clause_fails() {
        // CNF: (x1) AND (-x1) — UNSAT.
        // DRAT proof: delete a clause that doesn't exist, then derive empty.
        let cnf = vec![vec![1], vec![-1]];
        let drat_steps = vec![
            ProofStep::Delete(vec![99, 100]), // Does not exist.
            ProofStep::Add(vec![]),
        ];

        let result = convert_drat_to_lrat(&cnf, &drat_steps);
        assert!(result.is_err());
        match result.unwrap_err() {
            ConvertError::DeletionNotFound { step, .. } => {
                assert_eq!(step, 0);
            }
            other => panic!("expected DeletionNotFound, got {other:?}"),
        }
    }

    // ---- Binary DRAT parsing tests ----

    #[test]
    fn test_parse_drat_binary_add_step() {
        let mut data = Vec::new();
        data.push(b'a');
        // Literal 1 positive = 2, literal -2 = 5
        data.extend(write_drat_leb128(encode_drat_binary_literal(1)));
        data.extend(write_drat_leb128(encode_drat_binary_literal(-2)));
        data.push(0); // terminator

        let steps = parse_drat_binary(&data).expect("binary DRAT should parse");
        assert_eq!(steps.len(), 1);
        assert_eq!(steps[0], ProofStep::Add(vec![1, -2]));
    }

    #[test]
    fn test_parse_drat_binary_delete_step() {
        let mut data = Vec::new();
        data.push(b'd');
        data.extend(write_drat_leb128(encode_drat_binary_literal(3)));
        data.push(0);

        let steps = parse_drat_binary(&data).expect("binary DRAT should parse");
        assert_eq!(steps.len(), 1);
        assert_eq!(steps[0], ProofStep::Delete(vec![3]));
    }

    #[test]
    fn test_parse_drat_binary_empty_clause() {
        let data = vec![b'a', 0]; // 'a' marker + empty clause

        let steps = parse_drat_binary(&data).expect("binary DRAT should parse");
        assert_eq!(steps.len(), 1);
        assert_eq!(steps[0], ProofStep::Add(vec![]));
    }

    #[test]
    fn test_parse_drat_binary_multiple_steps() {
        let mut data = Vec::new();
        // Add {1, 2}
        data.push(b'a');
        data.extend(write_drat_leb128(encode_drat_binary_literal(1)));
        data.extend(write_drat_leb128(encode_drat_binary_literal(2)));
        data.push(0);
        // Delete {1, 2}
        data.push(b'd');
        data.extend(write_drat_leb128(encode_drat_binary_literal(1)));
        data.extend(write_drat_leb128(encode_drat_binary_literal(2)));
        data.push(0);
        // Add {} (empty clause)
        data.push(b'a');
        data.push(0);

        let steps = parse_drat_binary(&data).expect("binary DRAT should parse");
        assert_eq!(steps.len(), 3);
        assert_eq!(steps[0], ProofStep::Add(vec![1, 2]));
        assert_eq!(steps[1], ProofStep::Delete(vec![1, 2]));
        assert_eq!(steps[2], ProofStep::Add(vec![]));
    }

    #[test]
    fn test_parse_drat_binary_invalid_marker() {
        let data = [b'x', 0];
        let result = parse_drat_binary(&data);
        assert!(result.is_err());
    }

    // ---- Binary DRAT to LRAT conversion tests ----

    #[test]
    fn test_convert_drat_binary_simple_unsat() {
        // CNF: (x1) AND (-x1) -- trivially UNSAT.
        let cnf = vec![vec![1], vec![-1]];

        // Binary DRAT: add empty clause.
        let drat_data = vec![b'a', 0]; // 'a' marker + empty clause

        let lrat_steps =
            convert_drat_binary_to_lrat(&cnf, &drat_data).expect("conversion should succeed");

        assert_eq!(lrat_steps.len(), 1);
        match &lrat_steps[0] {
            LratStep::Add { clause, hints, .. } => {
                assert!(clause.is_empty());
                assert!(!hints.is_empty());
            }
            _ => panic!("expected Add step"),
        }

        // Verify with LRAT checker.
        let mut checker = LratChecker::new(1);
        checker.add_original(ClauseId(1), &[Lit(1)]).expect("ok");
        checker.add_original(ClauseId(2), &[Lit(-1)]).expect("ok");
        let result = checker.verify_proof(&lrat_steps).expect("verify");
        assert!(result.refuted);
    }

    #[test]
    fn test_convert_drat_binary_three_clause() {
        // CNF: (x1 v x2) AND (-x1) AND (-x2) -- UNSAT.
        let cnf = vec![vec![1, 2], vec![-1], vec![-2]];

        // Binary DRAT: derive {x2}, then derive {}.
        let mut drat_data = Vec::new();
        // Add {2}
        drat_data.push(b'a');
        drat_data.extend(write_drat_leb128(encode_drat_binary_literal(2)));
        drat_data.push(0);
        // Add {} (empty)
        drat_data.push(b'a');
        drat_data.push(0);

        let lrat_steps =
            convert_drat_binary_to_lrat(&cnf, &drat_data).expect("conversion should succeed");
        assert_eq!(lrat_steps.len(), 2);

        // Round-trip verify.
        let mut checker = LratChecker::new(2);
        checker
            .add_original(ClauseId(1), &[Lit(1), Lit(2)])
            .expect("ok");
        checker.add_original(ClauseId(2), &[Lit(-1)]).expect("ok");
        checker.add_original(ClauseId(3), &[Lit(-2)]).expect("ok");
        let result = checker.verify_proof(&lrat_steps).expect("verify");
        assert!(result.refuted);
    }

    #[test]
    fn test_convert_drat_binary_with_deletion() {
        // CNF: (x1) AND (-x1) AND (x1 v x2) -- UNSAT.
        let cnf = vec![vec![1], vec![-1], vec![1, 2]];

        let mut drat_data = Vec::new();
        // Delete {1, 2}
        drat_data.push(b'd');
        drat_data.extend(write_drat_leb128(encode_drat_binary_literal(1)));
        drat_data.extend(write_drat_leb128(encode_drat_binary_literal(2)));
        drat_data.push(0);
        // Add {} (empty)
        drat_data.push(b'a');
        drat_data.push(0);

        let lrat_steps =
            convert_drat_binary_to_lrat(&cnf, &drat_data).expect("conversion should succeed");
        assert!(lrat_steps.len() >= 2);
    }

    // ---- Larger-scale binary DRAT test (20+ variables) ----

    #[test]
    fn test_convert_drat_binary_large_chain() {
        // Build a chain UNSAT with 25 variables.
        // Formula: (x1 v x2) AND (-x1) AND (-x2 v x3) AND (-x3) AND ... AND (-x25)
        let num_vars = 25;
        let mut cnf: Vec<Vec<i32>> = Vec::new();

        // (x1 v x2)
        cnf.push(vec![1, 2]);
        // (-x1)
        cnf.push(vec![-1]);
        // Chain: (-x_i v x_{i+1})
        for i in 2..num_vars {
            cnf.push(vec![-i, (i + 1)]);
        }
        // (-x_num_vars)
        cnf.push(vec![-num_vars]);

        // Build binary DRAT proof: derive x2, x3, ..., x_num_vars, then {}.
        let mut drat_data = Vec::new();
        for i in 2..=num_vars {
            drat_data.push(b'a');
            drat_data.extend(write_drat_leb128(encode_drat_binary_literal(i)));
            drat_data.push(0);
        }
        // Add empty clause.
        drat_data.push(b'a');
        drat_data.push(0);

        let lrat_steps = convert_drat_binary_to_lrat(&cnf, &drat_data)
            .expect("large binary DRAT conversion should succeed");

        // Verify the LRAT output.
        let mut checker = LratChecker::new(num_vars as u32);
        for (idx, clause) in cnf.iter().enumerate() {
            let id = ClauseId((idx as u64) + 1);
            let lits: Vec<Lit> = clause.iter().map(|&l| Lit(l)).collect();
            checker.add_original(id, &lits).expect("ok");
        }
        let result = checker.verify_proof(&lrat_steps).expect("verify");
        assert!(
            result.refuted,
            "large chain proof should derive empty clause"
        );
        assert!(
            lrat_steps.len() >= 20,
            "expected 20+ LRAT steps, got {}",
            lrat_steps.len()
        );
    }

    // ---- Streaming DRAT parser tests ----

    #[test]
    fn test_parse_drat_text_streaming_simple() {
        let input = b"1 -2 0\nd 1 -2 0\n0\n";
        let mut reader = std::io::BufReader::new(&input[..]);

        let step1 = parse_drat_text_streaming(&mut reader)
            .expect("should parse")
            .expect("should have step");
        assert_eq!(step1, ProofStep::Add(vec![1, -2]));

        let step2 = parse_drat_text_streaming(&mut reader)
            .expect("should parse")
            .expect("should have step");
        assert_eq!(step2, ProofStep::Delete(vec![1, -2]));

        let step3 = parse_drat_text_streaming(&mut reader)
            .expect("should parse")
            .expect("should have step");
        assert_eq!(step3, ProofStep::Add(vec![]));

        let eof = parse_drat_text_streaming(&mut reader).expect("should parse");
        assert!(eof.is_none());
    }

    #[test]
    fn test_parse_drat_text_streaming_comments() {
        let input = b"c comment line\n1 2 0\nc another\n0\n";
        let mut reader = std::io::BufReader::new(&input[..]);

        let step1 = parse_drat_text_streaming(&mut reader)
            .expect("should parse")
            .expect("should have step");
        assert_eq!(step1, ProofStep::Add(vec![1, 2]));

        let step2 = parse_drat_text_streaming(&mut reader)
            .expect("should parse")
            .expect("should have step");
        assert_eq!(step2, ProofStep::Add(vec![]));
    }

    #[test]
    fn test_parse_drat_binary_streaming_simple() {
        let mut data = Vec::new();
        // Add {1, -2}
        data.push(b'a');
        data.extend(write_drat_leb128(encode_drat_binary_literal(1)));
        data.extend(write_drat_leb128(encode_drat_binary_literal(-2)));
        data.push(0);
        // Delete {3}
        data.push(b'd');
        data.extend(write_drat_leb128(encode_drat_binary_literal(3)));
        data.push(0);
        // Add {} (empty clause)
        data.push(b'a');
        data.push(0);

        let mut reader = std::io::BufReader::new(&data[..]);

        let step1 = parse_drat_binary_streaming(&mut reader)
            .expect("should parse")
            .expect("should have step");
        assert_eq!(step1, ProofStep::Add(vec![1, -2]));

        let step2 = parse_drat_binary_streaming(&mut reader)
            .expect("should parse")
            .expect("should have step");
        assert_eq!(step2, ProofStep::Delete(vec![3]));

        let step3 = parse_drat_binary_streaming(&mut reader)
            .expect("should parse")
            .expect("should have step");
        assert_eq!(step3, ProofStep::Add(vec![]));

        let eof = parse_drat_binary_streaming(&mut reader).expect("should parse");
        assert!(eof.is_none());
    }

    #[test]
    fn test_parse_drat_binary_streaming_vs_batch() {
        // Build a multi-step binary DRAT proof.
        let mut data = Vec::new();
        data.push(b'a');
        data.extend(write_drat_leb128(encode_drat_binary_literal(1)));
        data.extend(write_drat_leb128(encode_drat_binary_literal(2)));
        data.push(0);
        data.push(b'd');
        data.extend(write_drat_leb128(encode_drat_binary_literal(1)));
        data.extend(write_drat_leb128(encode_drat_binary_literal(2)));
        data.push(0);
        data.push(b'a');
        data.push(0);

        // Batch parse.
        let batch_steps = parse_drat_binary(&data).expect("batch should parse");

        // Streaming parse.
        let mut reader = std::io::BufReader::new(&data[..]);
        let mut streaming_steps = Vec::new();
        while let Some(step) = parse_drat_binary_streaming(&mut reader).expect("should parse") {
            streaming_steps.push(step);
        }

        assert_eq!(batch_steps, streaming_steps);
    }

    // ---- Streaming DRAT-to-LRAT conversion tests ----

    #[test]
    fn test_convert_drat_to_lrat_streaming_text_simple() {
        let cnf = vec![vec![1], vec![-1]];
        let drat_text = b"0\n";
        let reader = std::io::BufReader::new(&drat_text[..]);

        let result = convert_drat_to_lrat_streaming(&cnf, reader, false)
            .expect("streaming conversion should succeed");

        assert!(result.derived_empty_clause);
        assert_eq!(result.steps_processed, 1);
        assert_eq!(result.lrat_steps.len(), 1);
        assert!(matches!(
            &result.lrat_steps[0],
            LratStep::Add { clause, .. } if clause.is_empty()
        ));
    }

    #[test]
    fn test_convert_drat_to_lrat_streaming_text_three_clause() {
        let cnf = vec![vec![1, 2], vec![-1], vec![-2]];
        let drat_text = b"2 0\n0\n";
        let reader = std::io::BufReader::new(&drat_text[..]);

        let result = convert_drat_to_lrat_streaming(&cnf, reader, false)
            .expect("streaming conversion should succeed");

        assert!(result.derived_empty_clause);
        assert_eq!(result.steps_processed, 2);
        assert_eq!(result.lrat_steps.len(), 2);
    }

    #[test]
    fn test_convert_drat_to_lrat_streaming_binary() {
        let cnf = vec![vec![1], vec![-1]];

        let drat_data = [b'a', 0]; // 'a' marker + empty clause

        let reader = std::io::BufReader::new(&drat_data[..]);
        let result = convert_drat_to_lrat_streaming(&cnf, reader, true)
            .expect("streaming binary conversion should succeed");

        assert!(result.derived_empty_clause);
        assert_eq!(result.steps_processed, 1);
    }

    #[test]
    fn test_convert_drat_to_lrat_streaming_no_empty_clause() {
        let cnf = vec![vec![1, 2], vec![-1], vec![-2]];
        let drat_text = b"2 0\n"; // Derives {2} but not empty clause.
        let reader = std::io::BufReader::new(&drat_text[..]);

        let result = convert_drat_to_lrat_streaming(&cnf, reader, false);
        assert!(result.is_err());
        match result.unwrap_err() {
            ConvertError::NoEmptyClause => {}
            other => panic!("expected NoEmptyClause, got {other:?}"),
        }
    }

    #[test]
    fn test_convert_streaming_vs_batch_equivalence() {
        let cnf = vec![vec![1, 2], vec![-1], vec![-2]];
        let drat_steps = vec![ProofStep::Add(vec![2]), ProofStep::Add(vec![])];

        // Batch conversion.
        let batch_lrat =
            convert_drat_to_lrat(&cnf, &drat_steps).expect("batch conversion should succeed");

        // Streaming text conversion.
        let drat_text = b"2 0\n0\n";
        let reader = std::io::BufReader::new(&drat_text[..]);
        let streaming_result = convert_drat_to_lrat_streaming(&cnf, reader, false)
            .expect("streaming conversion should succeed");

        assert_eq!(batch_lrat.len(), streaming_result.lrat_steps.len());
        // Both should have the same clause content (IDs may differ due to
        // starting state, but structure should be the same).
        for (batch_step, stream_step) in batch_lrat.iter().zip(&streaming_result.lrat_steps) {
            match (batch_step, stream_step) {
                (LratStep::Add { clause: bc, .. }, LratStep::Add { clause: sc, .. }) => {
                    assert_eq!(bc, sc);
                }
                (
                    LratStep::Delete { clause_ids: b_ids },
                    LratStep::Delete { clause_ids: s_ids },
                ) => {
                    assert_eq!(b_ids.len(), s_ids.len());
                }
                _ => panic!("step type mismatch between batch and streaming"),
            }
        }
    }

    // ---- Streaming DRAT verify tests ----

    #[test]
    fn test_verify_drat_streaming_text_simple() {
        let cnf = vec![vec![1], vec![-1]];
        let drat_text = b"0\n";
        let reader = std::io::BufReader::new(&drat_text[..]);

        let result = verify_drat_streaming(&cnf, reader, false)
            .expect("streaming verification should succeed");

        assert!(result.valid);
        assert!(result.derived_empty_clause);
        assert_eq!(result.drat_steps_processed, 1);
        assert_eq!(result.lrat_steps_verified, 1);
    }

    #[test]
    fn test_verify_drat_streaming_text_three_clause() {
        let cnf = vec![vec![1, 2], vec![-1], vec![-2]];
        let drat_text = b"2 0\n0\n";
        let reader = std::io::BufReader::new(&drat_text[..]);

        let result = verify_drat_streaming(&cnf, reader, false)
            .expect("streaming verification should succeed");

        assert!(result.valid);
        assert_eq!(result.drat_steps_processed, 2);
        assert_eq!(result.lrat_steps_verified, 2);
    }

    #[test]
    fn test_verify_drat_streaming_binary_simple() {
        let cnf = vec![vec![1], vec![-1]];

        let drat_data = [b'a', 0]; // 'a' marker + empty clause

        let reader = std::io::BufReader::new(&drat_data[..]);
        let result = verify_drat_streaming(&cnf, reader, true)
            .expect("streaming binary verification should succeed");

        assert!(result.valid);
        assert!(result.derived_empty_clause);
    }

    #[test]
    fn test_verify_drat_streaming_with_deletion() {
        let cnf = vec![vec![1], vec![-1], vec![1, 2]];
        let drat_text = b"d 1 2 0\n0\n";
        let reader = std::io::BufReader::new(&drat_text[..]);

        let result = verify_drat_streaming(&cnf, reader, false)
            .expect("streaming verification with deletion should succeed");

        assert!(result.valid);
        assert_eq!(result.drat_steps_processed, 2);
    }

    #[test]
    fn test_verify_drat_streaming_rup_failure() {
        let cnf = vec![vec![1, 2]]; // SAT formula.
        let drat_text = b"0\n"; // Empty clause cannot be RUP.
        let reader = std::io::BufReader::new(&drat_text[..]);

        let result = verify_drat_streaming(&cnf, reader, false);
        assert!(result.is_err());
        match result.unwrap_err() {
            ConvertError::RupFailed { step, .. } => assert_eq!(step, 0),
            other => panic!("expected RupFailed, got {other:?}"),
        }
    }

    #[test]
    fn test_verify_drat_streaming_large_chain() {
        // Chain UNSAT with 30 variables.
        let num_vars = 30usize;
        let mut cnf: Vec<Vec<i32>> = Vec::new();
        cnf.push(vec![1, 2]);
        cnf.push(vec![-1]);
        for i in 2..num_vars {
            cnf.push(vec![-(i as i32), (i + 1) as i32]);
        }
        cnf.push(vec![-(num_vars as i32)]);

        // DRAT text proof: derive x2, x3, ..., x_num_vars, then {}.
        let mut drat_text = String::new();
        for i in 2..=num_vars {
            drat_text.push_str(&format!("{i} 0\n"));
        }
        drat_text.push_str("0\n");

        let reader = std::io::BufReader::new(drat_text.as_bytes());
        let result = verify_drat_streaming(&cnf, reader, false)
            .expect("large chain streaming verification should succeed");

        assert!(result.valid);
        assert!(result.derived_empty_clause);
        assert_eq!(result.drat_steps_processed, num_vars); // num_vars-1 unit clauses + 1 empty
    }
}
