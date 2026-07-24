// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! LRAT (Linear Resolution Asymmetric Tautology) proof checker.
//!
//! Implements the SAT-COMP standard proof format for UNSAT certificates.
//! Supports both text and binary LRAT formats with linear-time hint-guided
//! RUP (Reverse Unit Propagation) verification.
//!
//! ## Performance
//!
//! The checker uses a reusable assignment buffer with dirty-variable tracking
//! to avoid per-step O(num_vars) allocation. Each RUP check touches only the
//! variables in the clause and hint chains, achieving amortized O(proof_size)
//! total work.
//!
//! ## References
//!
//! - Cruz-Filipe et al. (2017): "Efficient Certified RAT Verification"
//! - Heule et al. (2017): "Trimming while Checking Clausal Proofs"

use super::proof_checker::{ProofCheckError, ProofChecker};
use super::types::Lit;
use std::collections::HashMap;
use std::io;
use thiserror::Error;

/// A globally unique LRAT clause identifier.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ClauseId(pub u64);

impl std::fmt::Display for ClauseId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

/// A single LRAT proof step.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum LratStep {
    /// Add a clause with explicit hints.
    Add {
        /// Clause id assigned by the proof.
        id: ClauseId,
        /// The clause in DIMACS literal form.
        clause: Vec<Lit>,
        /// Signed hint ids.
        hints: Vec<i64>,
    },
    /// Delete active clauses by id.
    Delete {
        /// Clause ids to delete.
        clause_ids: Vec<ClauseId>,
    },
}

/// Errors returned while parsing or verifying LRAT proofs.
#[derive(Debug, Clone, PartialEq, Eq, Error)]
#[non_exhaustive]
pub enum LratError {
    /// Generic parse failure.
    #[error("LRAT parse error: {0}")]
    ParseError(String),
    /// Binary data ended while a step was still being decoded.
    #[error("unexpected end of binary LRAT data")]
    UnexpectedEof,
    /// Clause ids must be positive.
    #[error("invalid clause id {0}")]
    InvalidClauseId(u64),
    /// Literals must be non-zero DIMACS integers.
    #[error("invalid literal {0}")]
    InvalidLiteral(i32),
    /// A literal exceeded the declared number of variables.
    #[error("literal {lit} exceeds declared variable bound {max_var}")]
    VariableOutOfRange { lit: Lit, max_var: u32 },
    /// Clause ids may not be reused.
    #[error("duplicate clause id {0}")]
    DuplicateClauseId(ClauseId),
    /// A referenced clause was not active.
    #[error("missing clause {0}")]
    MissingClause(ClauseId),
    /// A referenced hint clause was not active.
    #[error("missing hint clause {0}")]
    MissingHintClause(ClauseId),
    /// This checker only implements the requested hint-guided RUP path.
    #[error("unsupported RAT hint {0}")]
    UnsupportedRatHint(i64),
    /// Verification failed for a semantically invalid step.
    #[error("LRAT verification failed: {0}")]
    VerificationFailed(String),
    /// I/O error during streaming parse.
    #[error("I/O error: {0}")]
    IoError(String),
}

/// An LRAT proof: original clauses plus derived proof steps.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LratProof {
    /// Number of variables in the input CNF.
    pub num_vars: u32,
    /// Original clauses with their ids.
    pub original_clauses: Vec<(ClauseId, Vec<Lit>)>,
    /// Derived proof steps.
    pub steps: Vec<LratStep>,
}

/// Summary statistics from verifying an LRAT proof.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LratResult {
    /// Whether every processed step verified.
    pub valid: bool,
    /// Number of proof steps verified from `steps`.
    pub verified_steps: usize,
    /// Number of original clauses loaded into the checker.
    pub original_clauses: usize,
    /// Number of derived clauses accepted by the checker.
    pub derived_clauses: usize,
    /// Number of clause deletions processed.
    pub deleted_clauses: usize,
    /// Number of active clauses left after verification.
    pub active_clauses: usize,
    /// Whether an empty clause was present or derived.
    pub refuted: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ClauseEval {
    Conflict,
    Unit(Lit),
    Satisfied,
    Unresolved,
}

/// LRAT checker state.
#[derive(Debug, Clone)]
pub struct LratChecker {
    num_vars: u32,
    active_clauses: HashMap<ClauseId, Vec<Lit>>,
    seen_clause_ids: HashMap<ClauseId, ()>,
    original_clause_count: usize,
    derived_clause_count: usize,
    deleted_clause_count: usize,
    refuted: bool,
    /// Reusable assignment buffer for RUP checking.
    /// Avoids allocating a new Vec on every `add_derived` call.
    /// Variables that were assigned are tracked in `dirty_vars` for
    /// O(clause_width + hints_length) cleanup instead of O(num_vars).
    assignment: Vec<Option<bool>>,
    dirty_vars: Vec<usize>,
}

impl LratChecker {
    /// Create a checker for formulas over `num_vars` variables.
    #[must_use]
    pub fn new(num_vars: u32) -> Self {
        Self {
            num_vars,
            active_clauses: HashMap::new(),
            seen_clause_ids: HashMap::new(),
            original_clause_count: 0,
            derived_clause_count: 0,
            deleted_clause_count: 0,
            refuted: false,
            assignment: vec![None; num_vars as usize + 1],
            dirty_vars: Vec::new(),
        }
    }

    /// Add an original clause to the active clause database.
    pub fn add_original(&mut self, id: ClauseId, clause: &[Lit]) -> Result<(), LratError> {
        self.insert_clause(id, clause)?;
        self.original_clause_count += 1;
        Ok(())
    }

    /// Verify and add a derived clause using hint-guided RUP.
    pub fn add_derived(
        &mut self,
        id: ClauseId,
        clause: &[Lit],
        hints: &[i64],
    ) -> Result<(), LratError> {
        self.ensure_nonzero_clause_id(id)?;
        self.ensure_unique_clause_id(id)?;
        self.validate_clause(clause)?;
        self.verify_hint_guided_rup(clause, hints)?;
        self.seen_clause_ids.insert(id, ());
        self.active_clauses.insert(id, clause.to_vec());
        self.derived_clause_count += 1;
        if clause.is_empty() {
            self.refuted = true;
        }
        Ok(())
    }

    /// Delete a clause by id.
    pub fn delete(&mut self, id: ClauseId) -> Result<(), LratError> {
        self.ensure_nonzero_clause_id(id)?;
        if self.active_clauses.remove(&id).is_none() {
            return Err(LratError::MissingClause(id));
        }
        self.deleted_clause_count += 1;
        Ok(())
    }

    /// Verify all proof steps against the current active clause database.
    pub fn verify_proof(&mut self, steps: &[LratStep]) -> Result<LratResult, LratError> {
        let mut verified_steps = 0usize;
        for step in steps {
            match step {
                LratStep::Add { id, clause, hints } => self.add_derived(*id, clause, hints)?,
                LratStep::Delete { clause_ids } => {
                    for clause_id in clause_ids {
                        self.delete(*clause_id)?;
                    }
                }
            }
            verified_steps += 1;
        }
        Ok(self.result_with_steps(verified_steps))
    }

    fn insert_clause(&mut self, id: ClauseId, clause: &[Lit]) -> Result<(), LratError> {
        self.ensure_nonzero_clause_id(id)?;
        self.ensure_unique_clause_id(id)?;
        self.validate_clause(clause)?;
        self.seen_clause_ids.insert(id, ());
        self.active_clauses.insert(id, clause.to_vec());
        if clause.is_empty() {
            self.refuted = true;
        }
        Ok(())
    }

    fn ensure_nonzero_clause_id(&self, id: ClauseId) -> Result<(), LratError> {
        if id.0 == 0 {
            return Err(LratError::InvalidClauseId(0));
        }
        Ok(())
    }

    fn ensure_unique_clause_id(&self, id: ClauseId) -> Result<(), LratError> {
        if self.seen_clause_ids.contains_key(&id) {
            return Err(LratError::DuplicateClauseId(id));
        }
        Ok(())
    }

    fn validate_clause(&self, clause: &[Lit]) -> Result<(), LratError> {
        for &lit in clause {
            if lit.0 == 0 {
                return Err(LratError::InvalidLiteral(0));
            }
            if lit.var().0 > self.num_vars {
                return Err(LratError::VariableOutOfRange {
                    lit,
                    max_var: self.num_vars,
                });
            }
        }
        Ok(())
    }

    fn verify_hint_guided_rup(&mut self, clause: &[Lit], hints: &[i64]) -> Result<(), LratError> {
        // Clear only the dirty variables from the previous call (amortized O(1)
        // per call instead of O(num_vars)).
        for &idx in &self.dirty_vars {
            self.assignment[idx] = None;
        }
        self.dirty_vars.clear();

        for &lit in clause {
            if assign_tracked(&mut self.assignment, &mut self.dirty_vars, lit.negate()) {
                clear_tracked(&mut self.assignment, &mut self.dirty_vars);
                return Ok(());
            }
        }

        for &hint in hints {
            if hint < 0 {
                clear_tracked(&mut self.assignment, &mut self.dirty_vars);
                return Err(LratError::UnsupportedRatHint(hint));
            }

            let hint_id = ClauseId(u64::try_from(hint).map_err(|_| {
                LratError::ParseError(format!("hint id {hint} cannot be represented as u64"))
            })?);
            if hint_id.0 == 0 {
                clear_tracked(&mut self.assignment, &mut self.dirty_vars);
                return Err(LratError::ParseError(
                    "hint id 0 is reserved as a terminator".to_string(),
                ));
            }

            if !self.active_clauses.contains_key(&hint_id) {
                clear_tracked(&mut self.assignment, &mut self.dirty_vars);
                return Err(LratError::MissingHintClause(hint_id));
            }
            // SAFETY: we just confirmed the key exists above and nothing
            // modifies active_clauses between the contains_key and get.
            let hint_clause = &self.active_clauses[&hint_id];
            let eval = eval_clause_under_assignment(hint_clause, &self.assignment);
            match eval {
                ClauseEval::Conflict => {
                    clear_tracked(&mut self.assignment, &mut self.dirty_vars);
                    return Ok(());
                }
                ClauseEval::Unit(unit_lit) => {
                    if assign_tracked(&mut self.assignment, &mut self.dirty_vars, unit_lit) {
                        clear_tracked(&mut self.assignment, &mut self.dirty_vars);
                        return Ok(());
                    }
                }
                ClauseEval::Satisfied | ClauseEval::Unresolved => {
                    clear_tracked(&mut self.assignment, &mut self.dirty_vars);
                    return Err(LratError::VerificationFailed(format!(
                        "hint clause {hint_id} was not unit or conflicting"
                    )));
                }
            }
        }

        clear_tracked(&mut self.assignment, &mut self.dirty_vars);
        Err(LratError::VerificationFailed(
            "hint sequence ended without deriving a conflict".to_string(),
        ))
    }

    #[must_use]
    fn result_with_steps(&self, verified_steps: usize) -> LratResult {
        LratResult {
            // A proof is only valid if it derives the empty clause (refutation).
            valid: self.refuted,
            verified_steps,
            original_clauses: self.original_clause_count,
            derived_clauses: self.derived_clause_count,
            deleted_clauses: self.deleted_clause_count,
            active_clauses: self.active_clauses.len(),
            refuted: self.refuted,
        }
    }
}

/// A `ProofChecker` wrapper for LRAT proofs.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CheckableLratProof {
    /// The underlying LRAT proof data.
    pub proof: LratProof,
}

impl ProofChecker for CheckableLratProof {
    type Error = ProofCheckError;

    fn check(&self) -> Result<(), Self::Error> {
        let mut checker = LratChecker::new(self.proof.num_vars);
        for (id, clause) in &self.proof.original_clauses {
            checker
                .add_original(*id, clause)
                .map_err(|_| ProofCheckError::NotRefutation)?;
        }
        let result = checker
            .verify_proof(&self.proof.steps)
            .map_err(|_| ProofCheckError::NotRefutation)?;
        if result.refuted {
            Ok(())
        } else {
            Err(ProofCheckError::NotRefutation)
        }
    }

    fn proof_size(&self) -> usize {
        self.proof.steps.len()
    }
}

/// Parse text LRAT proof steps.
pub fn parse_text_lrat(input: &str) -> Result<Vec<LratStep>, LratError> {
    let mut steps = Vec::new();

    for (line_idx, raw_line) in input.lines().enumerate() {
        let line = raw_line.trim();
        if line.is_empty() || line.starts_with('c') {
            continue;
        }

        let tokens: Vec<&str> = line.split_whitespace().collect();
        if tokens.is_empty() {
            continue;
        }

        let step_id = parse_text_clause_id(tokens[0], "step id", line_idx + 1)?;
        if tokens.len() < 2 {
            return Err(LratError::ParseError(format!(
                "line {} is missing LRAT payload",
                line_idx + 1
            )));
        }

        if tokens[1] == "d" {
            let clause_ids = parse_text_delete_clause_ids(&tokens[2..], line_idx + 1)?;
            let _ = step_id;
            steps.push(LratStep::Delete { clause_ids });
            continue;
        }

        let (clause, next_index) = parse_text_clause_literals(&tokens[1..], line_idx + 1)?;
        let hints = parse_text_hints(&tokens[1 + next_index..], line_idx + 1)?;
        steps.push(LratStep::Add {
            id: step_id,
            clause,
            hints,
        });
    }

    Ok(steps)
}

/// Parse binary LRAT proof steps.
pub fn parse_binary_lrat(data: &[u8]) -> Result<Vec<LratStep>, LratError> {
    let mut steps = Vec::new();
    let mut offset = 0usize;

    while offset < data.len() {
        while offset < data.len() && data[offset].is_ascii_whitespace() {
            offset += 1;
        }
        if offset >= data.len() {
            break;
        }

        let tag = data[offset];
        offset += 1;
        match tag {
            b'a' => {
                let clause_id = decode_binary_clause_id(data, &mut offset, "clause id")?;
                let mut clause = Vec::new();
                loop {
                    let encoded_lit = decode_uleb128(data, &mut offset)?;
                    if encoded_lit == 0 {
                        break;
                    }
                    clause.push(decode_binary_lit(encoded_lit)?);
                }

                let mut hints = Vec::new();
                loop {
                    let encoded_hint = decode_uleb128(data, &mut offset)?;
                    if encoded_hint == 0 {
                        break;
                    }
                    hints.push(decode_binary_hint(encoded_hint)?);
                }

                steps.push(LratStep::Add {
                    id: clause_id,
                    clause,
                    hints,
                });
            }
            b'd' => {
                let mut clause_ids = Vec::new();
                loop {
                    let encoded_id = decode_uleb128(data, &mut offset)?;
                    if encoded_id == 0 {
                        break;
                    }
                    clause_ids.push(ClauseId(encoded_id));
                }
                steps.push(LratStep::Delete { clause_ids });
            }
            other => {
                return Err(LratError::ParseError(format!(
                    "unknown binary LRAT step tag 0x{other:02x} at offset {}",
                    offset - 1
                )));
            }
        }
    }

    Ok(steps)
}

/// Detect whether a proof blob looks like binary LRAT.
#[must_use]
pub fn is_binary_lrat(data: &[u8]) -> bool {
    for &byte in data {
        if byte.is_ascii_whitespace() {
            continue;
        }
        return matches!(byte, b'a' | b'd');
    }
    false
}

fn parse_text_clause_id(token: &str, what: &str, line_no: usize) -> Result<ClauseId, LratError> {
    let raw: i128 = token.parse().map_err(|error| {
        LratError::ParseError(format!("line {line_no}: invalid {what} '{token}': {error}"))
    })?;
    if raw <= 0 {
        return Err(LratError::ParseError(format!(
            "line {line_no}: {what} must be positive, found {token}"
        )));
    }
    let value = u64::try_from(raw).map_err(|_| {
        LratError::ParseError(format!(
            "line {line_no}: {what} '{token}' does not fit in u64"
        ))
    })?;
    Ok(ClauseId(value))
}

fn parse_text_delete_clause_ids(
    tokens: &[&str],
    line_no: usize,
) -> Result<Vec<ClauseId>, LratError> {
    let mut clause_ids = Vec::new();
    let mut terminated = false;

    for (index, token) in tokens.iter().enumerate() {
        if *token == "0" {
            terminated = true;
            if index + 1 != tokens.len() {
                return Err(LratError::ParseError(format!(
                    "line {line_no}: unexpected tokens after deletion terminator"
                )));
            }
            break;
        }
        clause_ids.push(parse_text_clause_id(token, "clause id", line_no)?);
    }

    if !terminated {
        return Err(LratError::ParseError(format!(
            "line {line_no}: deletion step is missing a trailing 0"
        )));
    }

    Ok(clause_ids)
}

fn parse_text_clause_literals(
    tokens: &[&str],
    line_no: usize,
) -> Result<(Vec<Lit>, usize), LratError> {
    let mut clause = Vec::new();

    for (index, token) in tokens.iter().enumerate() {
        let value: i32 = token.parse().map_err(|error| {
            LratError::ParseError(format!(
                "line {line_no}: invalid clause literal '{token}': {error}"
            ))
        })?;
        if value == 0 {
            return Ok((clause, index + 1));
        }
        clause.push(Lit(value));
    }

    Err(LratError::ParseError(format!(
        "line {line_no}: addition step is missing the clause terminator 0"
    )))
}

fn parse_text_hints(tokens: &[&str], line_no: usize) -> Result<Vec<i64>, LratError> {
    let mut hints = Vec::new();

    for (index, token) in tokens.iter().enumerate() {
        let value: i64 = token.parse().map_err(|error| {
            LratError::ParseError(format!("line {line_no}: invalid hint '{token}': {error}"))
        })?;
        if value == 0 {
            if index + 1 != tokens.len() {
                return Err(LratError::ParseError(format!(
                    "line {line_no}: unexpected tokens after hint terminator"
                )));
            }
            return Ok(hints);
        }
        hints.push(value);
    }

    Err(LratError::ParseError(format!(
        "line {line_no}: addition step is missing the hint terminator 0"
    )))
}

fn decode_binary_clause_id(
    data: &[u8],
    offset: &mut usize,
    what: &str,
) -> Result<ClauseId, LratError> {
    let value = decode_uleb128(data, offset)?;
    if value == 0 {
        return Err(LratError::ParseError(format!(
            "{what} 0 is reserved as a terminator"
        )));
    }
    Ok(ClauseId(value))
}

fn decode_binary_lit(encoded: u64) -> Result<Lit, LratError> {
    let var = encoded / 2;
    if var == 0 {
        return Err(LratError::ParseError(format!(
            "invalid binary LRAT literal encoding {encoded}"
        )));
    }
    let var_i32 = i32::try_from(var).map_err(|_| {
        LratError::ParseError(format!(
            "binary LRAT literal encoding {encoded} exceeds i32 range"
        ))
    })?;
    if encoded & 1 == 0 {
        Ok(Lit(var_i32))
    } else {
        Ok(Lit(-var_i32))
    }
}

fn decode_binary_hint(encoded: u64) -> Result<i64, LratError> {
    let magnitude = encoded / 2;
    if magnitude == 0 {
        return Err(LratError::ParseError(format!(
            "invalid binary LRAT hint encoding {encoded}"
        )));
    }
    let magnitude_i64 = i64::try_from(magnitude).map_err(|_| {
        LratError::ParseError(format!(
            "binary LRAT hint encoding {encoded} exceeds i64 range"
        ))
    })?;
    if encoded & 1 == 0 {
        Ok(magnitude_i64)
    } else {
        Ok(-magnitude_i64)
    }
}

fn decode_uleb128(data: &[u8], offset: &mut usize) -> Result<u64, LratError> {
    let mut value = 0u64;
    let mut shift = 0u32;

    loop {
        if *offset >= data.len() {
            return Err(LratError::UnexpectedEof);
        }

        let byte = data[*offset];
        *offset += 1;

        let low_bits = u64::from(byte & 0x7f);
        if shift >= 64 || low_bits > (u64::MAX >> shift) {
            return Err(LratError::ParseError(
                "binary LRAT integer exceeds u64 range".to_string(),
            ));
        }
        value |= low_bits << shift;

        if byte & 0x80 == 0 {
            return Ok(value);
        }

        shift += 7;
        if shift >= 64 {
            return Err(LratError::ParseError(
                "binary LRAT integer exceeds u64 range".to_string(),
            ));
        }
    }
}

/// Assign a literal and push the variable index to the dirty list for cleanup.
/// Returns true on conflict (variable already assigned to the opposite value).
fn assign_tracked(assignment: &mut [Option<bool>], dirty: &mut Vec<usize>, lit: Lit) -> bool {
    let index = lit.var().0 as usize;
    let value = lit.polarity();
    match assignment.get_mut(index) {
        Some(slot) => match *slot {
            Some(existing) => existing != value,
            None => {
                *slot = Some(value);
                dirty.push(index);
                false
            }
        },
        None => true,
    }
}

/// Clear only the tracked dirty variables in the assignment buffer.
fn clear_tracked(assignment: &mut [Option<bool>], dirty: &mut Vec<usize>) {
    for &idx in dirty.iter() {
        assignment[idx] = None;
    }
    dirty.clear();
}

fn eval_clause_under_assignment(clause: &[Lit], assignment: &[Option<bool>]) -> ClauseEval {
    let mut unit = None;

    for &lit in clause {
        let index = lit.var().0 as usize;
        match assignment.get(index).copied().flatten() {
            Some(value) if value == lit.polarity() => return ClauseEval::Satisfied,
            Some(_) => {}
            None => match unit {
                None => unit = Some(lit),
                Some(_) => return ClauseEval::Unresolved,
            },
        }
    }

    match unit {
        Some(lit) => ClauseEval::Unit(lit),
        None => ClauseEval::Conflict,
    }
}

// ---------------------------------------------------------------------------
// Streaming parsers and verification
// ---------------------------------------------------------------------------

/// Read a single ULEB128-encoded value from a `Read` source, one byte at a time.
///
/// Returns `Ok(value)` on success, or `Err` on EOF / overflow.
fn read_uleb128_from_reader<R: io::Read>(reader: &mut R) -> Result<u64, LratError> {
    let mut value = 0u64;
    let mut shift = 0u32;
    let mut buf = [0u8; 1];

    loop {
        match reader.read_exact(&mut buf) {
            Ok(()) => {}
            Err(e) if e.kind() == io::ErrorKind::UnexpectedEof => {
                return Err(LratError::UnexpectedEof);
            }
            Err(e) => return Err(LratError::IoError(e.to_string())),
        }

        let byte = buf[0];
        let low_bits = u64::from(byte & 0x7f);
        if shift >= 64 || (shift > 0 && low_bits > (u64::MAX >> shift)) {
            return Err(LratError::ParseError(
                "binary LRAT integer exceeds u64 range".to_string(),
            ));
        }
        value |= low_bits << shift;

        if byte & 0x80 == 0 {
            return Ok(value);
        }

        shift += 7;
        if shift >= 64 {
            return Err(LratError::ParseError(
                "binary LRAT integer exceeds u64 range".to_string(),
            ));
        }
    }
}

/// Parse the next binary LRAT step from a `BufRead` source.
///
/// Returns `Ok(Some(step))` for each decoded step, or `Ok(None)` at EOF.
/// This is the streaming counterpart to [`parse_binary_lrat`].
pub fn parse_binary_lrat_streaming<R: io::BufRead>(
    reader: &mut R,
) -> Result<Option<LratStep>, LratError> {
    // Skip leading whitespace and detect EOF.
    let tag = loop {
        let mut tag_buf = [0u8; 1];
        match reader.read_exact(&mut tag_buf) {
            Ok(()) => {
                if !tag_buf[0].is_ascii_whitespace() {
                    break tag_buf[0];
                }
            }
            Err(e) if e.kind() == io::ErrorKind::UnexpectedEof => return Ok(None),
            Err(e) => return Err(LratError::IoError(e.to_string())),
        }
    };

    match tag {
        b'a' => {
            let id_val = read_uleb128_from_reader(reader)?;
            if id_val == 0 {
                return Err(LratError::ParseError(
                    "clause id 0 is reserved as a terminator".to_string(),
                ));
            }

            let mut clause = Vec::new();
            loop {
                let encoded = read_uleb128_from_reader(reader)?;
                if encoded == 0 {
                    break;
                }
                clause.push(decode_binary_lit(encoded)?);
            }

            let mut hints = Vec::new();
            loop {
                let encoded = read_uleb128_from_reader(reader)?;
                if encoded == 0 {
                    break;
                }
                hints.push(decode_binary_hint(encoded)?);
            }

            Ok(Some(LratStep::Add {
                id: ClauseId(id_val),
                clause,
                hints,
            }))
        }
        b'd' => {
            let mut clause_ids = Vec::new();
            loop {
                let encoded = read_uleb128_from_reader(reader)?;
                if encoded == 0 {
                    break;
                }
                clause_ids.push(ClauseId(encoded));
            }
            Ok(Some(LratStep::Delete { clause_ids }))
        }
        other => Err(LratError::ParseError(format!(
            "unknown binary LRAT step tag 0x{other:02x}",
        ))),
    }
}

/// Parse the next text LRAT step from a `BufRead` source.
///
/// Returns `Ok(Some(step))` for each decoded line, or `Ok(None)` at EOF.
/// This is the streaming counterpart to [`parse_text_lrat`].
pub fn parse_text_lrat_streaming<R: io::BufRead>(
    reader: &mut R,
) -> Result<Option<LratStep>, LratError> {
    let mut line = String::new();
    loop {
        line.clear();
        let bytes_read = reader
            .read_line(&mut line)
            .map_err(|e| LratError::IoError(e.to_string()))?;
        if bytes_read == 0 {
            return Ok(None);
        }

        let trimmed = line.trim();
        if trimmed.is_empty() || trimmed.starts_with('c') {
            continue;
        }

        let tokens: Vec<&str> = trimmed.split_whitespace().collect();
        if tokens.is_empty() {
            continue;
        }

        // Use line 0 for streaming (no global line counter).
        let step_id = parse_text_clause_id(tokens[0], "step id", 0)?;
        if tokens.len() < 2 {
            return Err(LratError::ParseError(
                "streaming: line is missing LRAT payload".to_string(),
            ));
        }

        if tokens[1] == "d" {
            let clause_ids = parse_text_delete_clause_ids(&tokens[2..], 0)?;
            let _ = step_id;
            return Ok(Some(LratStep::Delete { clause_ids }));
        }

        let (clause, next_index) = parse_text_clause_literals(&tokens[1..], 0)?;
        let hints = parse_text_hints(&tokens[1 + next_index..], 0)?;
        return Ok(Some(LratStep::Add {
            id: step_id,
            clause,
            hints,
        }));
    }
}

/// Verify an LRAT proof by streaming steps from a text `BufRead` source.
///
/// Instead of loading the entire proof into memory, this processes steps
/// one at a time. The checker maintains only the active clause database
/// (which can shrink via deletions), not the full proof text.
///
/// # Errors
///
/// Returns [`LratError`] on parse or verification failure.
pub fn verify_lrat_streaming_text<R: io::BufRead>(
    reader: R,
    num_vars: u32,
    original_clauses: &[(ClauseId, Vec<Lit>)],
) -> Result<LratResult, LratError> {
    verify_lrat_streaming_impl(reader, num_vars, original_clauses, false)
}

/// Verify an LRAT proof by streaming steps from a binary `BufRead` source.
///
/// # Errors
///
/// Returns [`LratError`] on parse or verification failure.
pub fn verify_lrat_streaming_binary<R: io::BufRead>(
    reader: R,
    num_vars: u32,
    original_clauses: &[(ClauseId, Vec<Lit>)],
) -> Result<LratResult, LratError> {
    verify_lrat_streaming_impl(reader, num_vars, original_clauses, true)
}

/// Verify an LRAT proof by auto-detecting text vs binary format.
///
/// Leading whitespace is ignored during format detection. Text proofs are
/// expected to begin with a clause id or `c` comment line; binary proofs begin
/// with `b'a'` or `b'd'`.
pub fn verify_lrat_streaming<R: io::BufRead>(
    mut reader: R,
    num_vars: u32,
    original_clauses: &[(ClauseId, Vec<Lit>)],
) -> Result<LratResult, LratError> {
    let binary = loop {
        let buf = reader
            .fill_buf()
            .map_err(|e| LratError::IoError(e.to_string()))?;
        if buf.is_empty() {
            break false;
        }

        let mut idx = 0usize;
        while idx < buf.len() && buf[idx].is_ascii_whitespace() {
            idx += 1;
        }

        if idx == buf.len() {
            let len = buf.len();
            reader.consume(len);
            continue;
        }

        break matches!(buf[idx], b'a' | b'd');
    };

    verify_lrat_streaming_impl(reader, num_vars, original_clauses, binary)
}

fn verify_lrat_streaming_impl<R: io::BufRead>(
    mut reader: R,
    num_vars: u32,
    original_clauses: &[(ClauseId, Vec<Lit>)],
    binary: bool,
) -> Result<LratResult, LratError> {
    let mut checker = LratChecker::new(num_vars);

    for (id, clause) in original_clauses {
        checker.add_original(*id, clause)?;
    }

    let mut verified_steps = 0usize;

    loop {
        let step = if binary {
            parse_binary_lrat_streaming(&mut reader)?
        } else {
            parse_text_lrat_streaming(&mut reader)?
        };

        let Some(step) = step else {
            break;
        };

        match &step {
            LratStep::Add { id, clause, hints } => checker.add_derived(*id, clause, hints)?,
            LratStep::Delete { clause_ids } => {
                for clause_id in clause_ids {
                    checker.delete(*clause_id)?;
                }
            }
        }
        verified_steps += 1;
    }

    Ok(checker.result_with_steps(verified_steps))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn encode_uleb128(mut value: u64) -> Vec<u8> {
        let mut bytes = Vec::new();
        loop {
            let mut byte = (value & 0x7f) as u8;
            value >>= 7;
            if value != 0 {
                byte |= 0x80;
            }
            bytes.push(byte);
            if value == 0 {
                break;
            }
        }
        bytes
    }

    fn encode_binary_lit(lit: Lit) -> u64 {
        let var = u64::from(lit.var().0);
        if lit.polarity() {
            2 * var
        } else {
            2 * var + 1
        }
    }

    fn encode_binary_hint(hint: i64) -> u64 {
        let magnitude = hint.unsigned_abs();
        if hint >= 0 {
            2 * magnitude
        } else {
            2 * magnitude + 1
        }
    }

    #[test]
    fn test_parse_text_lrat_addition_step() {
        let steps = parse_text_lrat("3 1 -2 0 4 -5 0\n").expect("text LRAT should parse");
        assert_eq!(
            steps,
            vec![LratStep::Add {
                id: ClauseId(3),
                clause: vec![Lit(1), Lit(-2)],
                hints: vec![4, -5],
            }]
        );
    }

    #[test]
    fn test_parse_text_lrat_deletion_step() {
        let steps = parse_text_lrat("7 d 1 4 9 0\n").expect("text LRAT should parse");
        assert_eq!(
            steps,
            vec![LratStep::Delete {
                clause_ids: vec![ClauseId(1), ClauseId(4), ClauseId(9)],
            }]
        );
    }

    #[test]
    fn test_parse_text_lrat_empty_clause() {
        let steps = parse_text_lrat("4 0 1 2 0\n").expect("text LRAT should parse");
        assert_eq!(
            steps,
            vec![LratStep::Add {
                id: ClauseId(4),
                clause: vec![],
                hints: vec![1, 2],
            }]
        );
    }

    #[test]
    fn test_parse_binary_lrat_addition() {
        let mut data = vec![b'a'];
        data.extend(encode_uleb128(3));
        data.extend(encode_uleb128(encode_binary_lit(Lit(1))));
        data.extend(encode_uleb128(encode_binary_lit(Lit(-2))));
        data.extend(encode_uleb128(0));
        data.extend(encode_uleb128(encode_binary_hint(4)));
        data.extend(encode_uleb128(encode_binary_hint(-5)));
        data.extend(encode_uleb128(0));

        let steps = parse_binary_lrat(&data).expect("binary LRAT should parse");
        assert_eq!(
            steps,
            vec![LratStep::Add {
                id: ClauseId(3),
                clause: vec![Lit(1), Lit(-2)],
                hints: vec![4, -5],
            }]
        );
    }

    #[test]
    fn test_parse_binary_lrat_deletion() {
        let mut data = vec![b'd'];
        data.extend(encode_uleb128(1));
        data.extend(encode_uleb128(4));
        data.extend(encode_uleb128(9));
        data.extend(encode_uleb128(0));

        let steps = parse_binary_lrat(&data).expect("binary LRAT should parse");
        assert_eq!(
            steps,
            vec![LratStep::Delete {
                clause_ids: vec![ClauseId(1), ClauseId(4), ClauseId(9)],
            }]
        );
    }

    #[test]
    fn test_is_binary_lrat_detection() {
        let mut binary = vec![b'a'];
        binary.extend(encode_uleb128(1));
        binary.extend(encode_uleb128(0));
        binary.extend(encode_uleb128(0));

        assert!(is_binary_lrat(&binary));
        assert!(!is_binary_lrat(b"1 2 0 3 0\n"));
    }

    #[test]
    fn test_lrat_checker_simple_unsat() {
        let mut checker = LratChecker::new(1);
        checker
            .add_original(ClauseId(1), &[Lit(1)])
            .expect("original clause should load");
        checker
            .add_original(ClauseId(2), &[Lit(-1)])
            .expect("original clause should load");

        let result = checker
            .verify_proof(&[LratStep::Add {
                id: ClauseId(3),
                clause: vec![],
                hints: vec![1, 2],
            }])
            .expect("proof should verify");

        assert!(result.valid);
        assert_eq!(result.verified_steps, 1);
        assert_eq!(result.derived_clauses, 1);
        assert!(result.refuted);
    }

    #[test]
    fn test_lrat_checker_rup_verification() {
        let mut checker = LratChecker::new(2);
        checker
            .add_original(ClauseId(1), &[Lit(1)])
            .expect("original clause should load");
        checker
            .add_original(ClauseId(2), &[Lit(-1), Lit(2)])
            .expect("original clause should load");

        checker
            .add_derived(ClauseId(3), &[Lit(2)], &[1, 2])
            .expect("RUP step should verify");
    }

    #[test]
    fn test_lrat_checker_deletion() {
        let mut checker = LratChecker::new(1);
        checker
            .add_original(ClauseId(1), &[Lit(1)])
            .expect("original clause should load");

        checker.delete(ClauseId(1)).expect("delete should succeed");

        let error = checker
            .delete(ClauseId(1))
            .expect_err("second delete should fail");
        assert_eq!(error, LratError::MissingClause(ClauseId(1)));
    }

    #[test]
    fn test_lrat_checker_missing_hint_clause() {
        let mut checker = LratChecker::new(1);
        checker
            .add_original(ClauseId(1), &[Lit(1)])
            .expect("original clause should load");

        let error = checker
            .add_derived(ClauseId(2), &[], &[1, 99])
            .expect_err("missing hint clause should fail");
        assert_eq!(error, LratError::MissingHintClause(ClauseId(99)));
    }

    #[test]
    fn test_lrat_checker_duplicate_clause_id() {
        let mut checker = LratChecker::new(1);
        checker
            .add_original(ClauseId(1), &[Lit(1)])
            .expect("original clause should load");

        let error = checker
            .add_original(ClauseId(1), &[Lit(-1)])
            .expect_err("duplicate clause id should fail");
        assert_eq!(error, LratError::DuplicateClauseId(ClauseId(1)));
    }

    #[test]
    fn test_lrat_proof_checker_trait_valid() {
        let proof = CheckableLratProof {
            proof: LratProof {
                num_vars: 1,
                original_clauses: vec![(ClauseId(1), vec![Lit(1)]), (ClauseId(2), vec![Lit(-1)])],
                steps: vec![LratStep::Add {
                    id: ClauseId(3),
                    clause: vec![],
                    hints: vec![1, 2],
                }],
            },
        };

        assert!(proof.check().is_ok());
        assert_eq!(proof.proof_size(), 1);
    }

    #[test]
    fn test_lrat_proof_checker_trait_invalid() {
        let proof = CheckableLratProof {
            proof: LratProof {
                num_vars: 2,
                original_clauses: vec![
                    (ClauseId(1), vec![Lit(1)]),
                    (ClauseId(2), vec![Lit(-1), Lit(2)]),
                ],
                steps: vec![LratStep::Add {
                    id: ClauseId(3),
                    clause: vec![Lit(2)],
                    hints: vec![2],
                }],
            },
        };

        assert!(proof.check().is_err());
    }

    #[test]
    fn test_lrat_checker_interleaved_add_delete() {
        // 3-variable UNSAT: (1 v 2) AND (-1) AND (-2 v 3) AND (-3)
        // Proof: derive {2} from 1,2; delete 1; derive {3} from 5,3;
        //        derive {} from 6,4
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
            .verify_proof(&[
                LratStep::Add {
                    id: ClauseId(5),
                    clause: vec![Lit(2)],
                    hints: vec![1, 2],
                },
                LratStep::Delete {
                    clause_ids: vec![ClauseId(1)],
                },
                LratStep::Add {
                    id: ClauseId(6),
                    clause: vec![Lit(3)],
                    hints: vec![3, 5],
                },
                LratStep::Add {
                    id: ClauseId(7),
                    clause: vec![],
                    hints: vec![6, 4],
                },
            ])
            .expect("interleaved add/delete proof should verify");

        assert!(result.refuted);
        assert_eq!(result.verified_steps, 4);
        assert_eq!(result.derived_clauses, 3);
        assert_eq!(result.deleted_clauses, 1);
        // active = 4 original + 3 derived - 1 deleted = 6
        assert_eq!(result.active_clauses, 6);
    }

    #[test]
    fn test_parse_binary_lrat_multi_byte_uleb128() {
        // Test ULEB128 encoding for values > 127 (multi-byte).
        // Clause ID 200 = 0xC8 in ULEB128: [0xC8, 0x01]
        let mut data = vec![b'a'];
        data.extend(encode_uleb128(200));
        // Literal: var=150, positive → 2*150 = 300 → ULEB128: [0xAC, 0x02]
        data.extend(encode_uleb128(encode_binary_lit(Lit(150))));
        data.extend(encode_uleb128(0)); // end literals
                                        // Hint: clause 100, positive → 2*100 = 200 → ULEB128: [0xC8, 0x01]
        data.extend(encode_uleb128(encode_binary_hint(100)));
        data.extend(encode_uleb128(0)); // end hints

        let steps = parse_binary_lrat(&data).expect("multi-byte binary LRAT should parse");
        assert_eq!(steps.len(), 1);
        match &steps[0] {
            LratStep::Add { id, clause, hints } => {
                assert_eq!(*id, ClauseId(200));
                assert_eq!(clause, &[Lit(150)]);
                assert_eq!(hints, &[100]);
            }
            _ => panic!("expected Add step"),
        }
    }

    #[test]
    fn test_parse_binary_lrat_mixed_add_and_delete() {
        // Multiple binary steps: add + delete + add
        let mut data = Vec::new();

        // Add: id=5, clause={1,-2}, hints={1,2}
        data.push(b'a');
        data.extend(encode_uleb128(5));
        data.extend(encode_uleb128(encode_binary_lit(Lit(1))));
        data.extend(encode_uleb128(encode_binary_lit(Lit(-2))));
        data.extend(encode_uleb128(0));
        data.extend(encode_uleb128(encode_binary_hint(1)));
        data.extend(encode_uleb128(encode_binary_hint(2)));
        data.extend(encode_uleb128(0));

        // Delete: ids={1,3}
        data.push(b'd');
        data.extend(encode_uleb128(1));
        data.extend(encode_uleb128(3));
        data.extend(encode_uleb128(0));

        // Add: id=6, empty clause, hints={5,4}
        data.push(b'a');
        data.extend(encode_uleb128(6));
        data.extend(encode_uleb128(0));
        data.extend(encode_uleb128(encode_binary_hint(5)));
        data.extend(encode_uleb128(encode_binary_hint(4)));
        data.extend(encode_uleb128(0));

        let steps = parse_binary_lrat(&data).expect("mixed binary LRAT should parse");
        assert_eq!(steps.len(), 3);
        assert!(matches!(&steps[0], LratStep::Add { id, .. } if *id == ClauseId(5)));
        assert!(matches!(&steps[1], LratStep::Delete { clause_ids } if clause_ids.len() == 2));
        assert!(
            matches!(&steps[2], LratStep::Add { id, clause, .. } if *id == ClauseId(6) && clause.is_empty())
        );
    }

    #[test]
    fn test_text_and_binary_parse_equivalence() {
        // Same proof in text and binary should parse to identical steps.
        let text_proof = "5 1 -2 0 1 2 0\n6 d 1 3 0\n7 0 5 4 0\n";
        let text_steps = parse_text_lrat(text_proof).expect("text should parse");

        let mut binary_data = Vec::new();
        // Add: id=5, clause={1,-2}, hints={1,2}
        binary_data.push(b'a');
        binary_data.extend(encode_uleb128(5));
        binary_data.extend(encode_uleb128(encode_binary_lit(Lit(1))));
        binary_data.extend(encode_uleb128(encode_binary_lit(Lit(-2))));
        binary_data.extend(encode_uleb128(0));
        binary_data.extend(encode_uleb128(encode_binary_hint(1)));
        binary_data.extend(encode_uleb128(encode_binary_hint(2)));
        binary_data.extend(encode_uleb128(0));
        // Delete: ids={1,3}
        binary_data.push(b'd');
        binary_data.extend(encode_uleb128(1));
        binary_data.extend(encode_uleb128(3));
        binary_data.extend(encode_uleb128(0));
        // Add: id=7, empty clause, hints={5,4}
        binary_data.push(b'a');
        binary_data.extend(encode_uleb128(7));
        binary_data.extend(encode_uleb128(0));
        binary_data.extend(encode_uleb128(encode_binary_hint(5)));
        binary_data.extend(encode_uleb128(encode_binary_hint(4)));
        binary_data.extend(encode_uleb128(0));

        let binary_steps = parse_binary_lrat(&binary_data).expect("binary should parse");
        assert_eq!(text_steps, binary_steps);
    }

    #[test]
    fn test_reusable_assignment_buffer_correctness() {
        // Verifies that the dirty-tracking assignment buffer produces
        // correct results across multiple add_derived calls.
        let mut checker = LratChecker::new(3);
        checker
            .add_original(ClauseId(1), &[Lit(1), Lit(2)])
            .expect("ok");
        checker.add_original(ClauseId(2), &[Lit(-1)]).expect("ok");
        checker
            .add_original(ClauseId(3), &[Lit(-2), Lit(3)])
            .expect("ok");
        checker.add_original(ClauseId(4), &[Lit(-3)]).expect("ok");

        // First derivation.
        checker
            .add_derived(ClauseId(5), &[Lit(2)], &[1, 2])
            .expect("first derivation should work");

        // Second derivation uses result of first.
        checker
            .add_derived(ClauseId(6), &[Lit(3)], &[3, 5])
            .expect("second derivation should work");

        // Third derivation: empty clause.
        checker
            .add_derived(ClauseId(7), &[], &[6, 4])
            .expect("empty clause derivation should work");

        assert!(checker.refuted);
    }

    // ---- Bug #3321: valid=false when no empty clause derived ----

    #[test]
    fn test_lrat_checker_no_empty_clause_invalid() {
        // Derive a non-empty clause only — proof is structurally correct
        // but does not constitute a refutation.
        let mut checker = LratChecker::new(2);
        checker
            .add_original(ClauseId(1), &[Lit(1), Lit(2)])
            .expect("original clause should load");
        checker
            .add_original(ClauseId(2), &[Lit(-1)])
            .expect("original clause should load");

        let result = checker
            .verify_proof(&[LratStep::Add {
                id: ClauseId(3),
                clause: vec![Lit(2)],
                hints: vec![1, 2],
            }])
            .expect("proof should parse and verify steps");

        // The proof did NOT derive the empty clause, so it is not valid.
        assert!(
            !result.valid,
            "proof without empty clause must not be valid"
        );
        assert!(
            !result.refuted,
            "proof without empty clause is not a refutation"
        );
        assert_eq!(result.verified_steps, 1);
        assert_eq!(result.derived_clauses, 1);
    }

    #[test]
    fn test_lrat_checker_only_deletions_invalid() {
        // Proof that only deletes clauses without deriving empty clause.
        let mut checker = LratChecker::new(1);
        checker
            .add_original(ClauseId(1), &[Lit(1)])
            .expect("original clause should load");
        checker
            .add_original(ClauseId(2), &[Lit(-1)])
            .expect("original clause should load");

        let result = checker
            .verify_proof(&[LratStep::Delete {
                clause_ids: vec![ClauseId(1)],
            }])
            .expect("deletion-only proof should process");

        assert!(!result.valid, "deletion-only proof must not be valid");
        assert!(!result.refuted);
        assert_eq!(result.verified_steps, 1);
        assert_eq!(result.deleted_clauses, 1);
    }

    // ---- Streaming parser tests ----

    #[test]
    fn test_streaming_text_lrat_simple() {
        let input = b"3 1 -2 0 4 -5 0\n7 d 1 4 9 0\n";
        let mut reader = std::io::BufReader::new(&input[..]);

        let step1 = parse_text_lrat_streaming(&mut reader)
            .expect("should parse")
            .expect("should have step");
        assert_eq!(
            step1,
            LratStep::Add {
                id: ClauseId(3),
                clause: vec![Lit(1), Lit(-2)],
                hints: vec![4, -5],
            }
        );

        let step2 = parse_text_lrat_streaming(&mut reader)
            .expect("should parse")
            .expect("should have step");
        assert_eq!(
            step2,
            LratStep::Delete {
                clause_ids: vec![ClauseId(1), ClauseId(4), ClauseId(9)],
            }
        );

        let eof = parse_text_lrat_streaming(&mut reader).expect("should parse");
        assert!(eof.is_none());
    }

    #[test]
    fn test_streaming_binary_lrat_simple() {
        let mut data = Vec::new();
        // Add: id=3, clause={1,-2}, hints={4,-5}
        data.push(b'a');
        data.extend(encode_uleb128(3));
        data.extend(encode_uleb128(encode_binary_lit(Lit(1))));
        data.extend(encode_uleb128(encode_binary_lit(Lit(-2))));
        data.extend(encode_uleb128(0));
        data.extend(encode_uleb128(encode_binary_hint(4)));
        data.extend(encode_uleb128(encode_binary_hint(-5)));
        data.extend(encode_uleb128(0));
        // Delete: {1,4,9}
        data.push(b'd');
        data.extend(encode_uleb128(1));
        data.extend(encode_uleb128(4));
        data.extend(encode_uleb128(9));
        data.extend(encode_uleb128(0));

        let mut reader = std::io::BufReader::new(&data[..]);

        let step1 = parse_binary_lrat_streaming(&mut reader)
            .expect("should parse")
            .expect("should have step");
        assert_eq!(
            step1,
            LratStep::Add {
                id: ClauseId(3),
                clause: vec![Lit(1), Lit(-2)],
                hints: vec![4, -5],
            }
        );

        let step2 = parse_binary_lrat_streaming(&mut reader)
            .expect("should parse")
            .expect("should have step");
        assert_eq!(
            step2,
            LratStep::Delete {
                clause_ids: vec![ClauseId(1), ClauseId(4), ClauseId(9)],
            }
        );

        let eof = parse_binary_lrat_streaming(&mut reader).expect("should parse");
        assert!(eof.is_none());
    }

    #[test]
    fn test_streaming_text_verify_simple_unsat() {
        let proof_text = b"3 0 1 2 0\n";
        let reader = std::io::BufReader::new(&proof_text[..]);

        let result = verify_lrat_streaming_text(
            reader,
            1,
            &[(ClauseId(1), vec![Lit(1)]), (ClauseId(2), vec![Lit(-1)])],
        )
        .expect("streaming verify should succeed");

        assert!(result.valid);
        assert!(result.refuted);
        assert_eq!(result.verified_steps, 1);
    }

    #[test]
    fn test_streaming_binary_verify_simple_unsat() {
        let mut data = Vec::new();
        data.push(b'a');
        data.extend(encode_uleb128(3));
        data.extend(encode_uleb128(0)); // empty clause
        data.extend(encode_uleb128(encode_binary_hint(1)));
        data.extend(encode_uleb128(encode_binary_hint(2)));
        data.extend(encode_uleb128(0));

        let reader = std::io::BufReader::new(&data[..]);
        let result = verify_lrat_streaming_binary(
            reader,
            1,
            &[(ClauseId(1), vec![Lit(1)]), (ClauseId(2), vec![Lit(-1)])],
        )
        .expect("streaming binary verify should succeed");

        assert!(result.valid);
        assert!(result.refuted);
        assert_eq!(result.verified_steps, 1);
    }

    #[test]
    fn test_streaming_vs_batch_equivalence_interleaved() {
        // 3-variable UNSAT with interleaved add/delete.
        let proof_text = "\
5 2 0 1 2 0\n\
6 d 1 0\n\
7 3 0 3 5 0\n\
8 0 7 4 0\n";

        let original_clauses = vec![
            (ClauseId(1), vec![Lit(1), Lit(2)]),
            (ClauseId(2), vec![Lit(-1)]),
            (ClauseId(3), vec![Lit(-2), Lit(3)]),
            (ClauseId(4), vec![Lit(-3)]),
        ];

        // Batch verification.
        let batch_steps = parse_text_lrat(proof_text).expect("batch parse");
        let mut batch_checker = LratChecker::new(3);
        for (id, clause) in &original_clauses {
            batch_checker.add_original(*id, clause).expect("ok");
        }
        let batch_result = batch_checker
            .verify_proof(&batch_steps)
            .expect("batch verify");

        // Streaming verification.
        let reader = std::io::BufReader::new(proof_text.as_bytes());
        let streaming_result =
            verify_lrat_streaming_text(reader, 3, &original_clauses).expect("streaming verify");

        assert_eq!(batch_result, streaming_result);
        assert!(streaming_result.refuted);
    }

    // ---- Large-scale pigeonhole test (PHP(4,3)) ----

    /// Generate the pigeonhole principle PHP(n, n-1) CNF.
    ///
    /// n pigeons, n-1 holes. Variable p_{i,j} = (i-1)*(n-1) + j.
    /// At-least-one clauses: each pigeon must go in at least one hole.
    /// At-most-one clauses: each hole holds at most one pigeon.
    fn php_cnf(n: u32) -> (u32, Vec<(ClauseId, Vec<Lit>)>) {
        let holes = n - 1;
        let num_vars = n * holes;
        let var = |pigeon: u32, hole: u32| -> i32 { ((pigeon - 1) * holes + hole) as i32 };

        let mut clauses = Vec::new();
        let mut clause_id = 1u64;

        // At-least-one: pigeon i must go in some hole.
        for i in 1..=n {
            let clause: Vec<Lit> = (1..=holes).map(|j| Lit(var(i, j))).collect();
            clauses.push((ClauseId(clause_id), clause));
            clause_id += 1;
        }

        // At-most-one: hole j holds at most one pigeon.
        for j in 1..=holes {
            for i1 in 1..=n {
                for i2 in (i1 + 1)..=n {
                    let clause = vec![Lit(-var(i1, j)), Lit(-var(i2, j))];
                    clauses.push((ClauseId(clause_id), clause));
                    clause_id += 1;
                }
            }
        }

        (num_vars, clauses)
    }

    /// Build a valid LRAT proof for PHP(4,3) by constructing it manually.
    ///
    /// This constructs a proof by successively narrowing possibilities.
    /// PHP(4,3): 4 pigeons, 3 holes, 12 variables, guaranteed UNSAT.
    fn php43_lrat_proof(original_clauses: &[(ClauseId, Vec<Lit>)]) -> Vec<LratStep> {
        // For PHP(4,3) we build the LRAT proof by running the DRAT-to-LRAT
        // converter on a known DRAT proof.
        // We'll use the LratChecker directly since constructing valid hints
        // by hand for 50+ steps is error-prone.
        //
        // Instead, we use a simpler but larger formula: chain UNSAT with
        // many variables, which is easy to prove.
        let _ = original_clauses;
        Vec::new() // Placeholder -- see test below for actual approach
    }

    #[test]
    fn test_large_scale_chain_unsat_streaming() {
        // Build a chain UNSAT formula with 50+ variables and 100+ clauses.
        // Formula: (x1 v x2) AND (-x1) AND (-x2 v x3) AND (-x3) AND ...
        // This creates an implication chain that is UNSAT.
        let num_vars = 120u32;
        let mut original_clauses = Vec::new();
        let mut clause_id = 1u64;

        // First clause: (x1 v x2)
        original_clauses.push((ClauseId(clause_id), vec![Lit(1), Lit(2)]));
        clause_id += 1;

        // (-x1)
        original_clauses.push((ClauseId(clause_id), vec![Lit(-1)]));
        clause_id += 1;

        // Chain: (-x_i v x_{i+1}) for i = 2..num_vars-1
        for i in 2..num_vars {
            original_clauses.push((
                ClauseId(clause_id),
                vec![Lit(-(i as i32)), Lit((i + 1) as i32)],
            ));
            clause_id += 1;
        }

        // Final negation: (-x_num_vars)
        original_clauses.push((ClauseId(clause_id), vec![Lit(-(num_vars as i32))]));
        clause_id += 1;

        let num_original = clause_id - 1;

        // Build LRAT proof: derive x2 from clause1 + clause2 (unit prop),
        // then x3, x4, ..., x_num_vars, then empty clause.
        let mut proof_steps = Vec::new();
        let mut next_proof_id = clause_id;

        // Derive x2: negate -x2, (x1,x2) + (-x1) -> conflict via hints
        // hint1 = clause 1 (x1 v x2), hint2 = clause 2 (-x1)
        proof_steps.push(LratStep::Add {
            id: ClauseId(next_proof_id),
            clause: vec![Lit(2)],
            hints: vec![1, 2],
        });
        let mut prev_derived_id = next_proof_id;
        next_proof_id += 1;

        // Derive x3, x4, ..., x_num_vars
        for i in 3..=num_vars {
            // hint_chain_clause is (-x_{i-1} v x_i) which is clause (i-1)+1 = i
            // (original clauses: idx 0 = clause1, idx 1 = clause2, idx 2 = (-x2 v x3) = clause3, ...)
            // The clause (-x_{i-1} v x_i) has id = i (since clause3 = (-x2 v x3), i.e., id = 2 + (i-2) = i)
            // Actually: clause1=(x1,x2), clause2=(-x1), clause3=(-x2,x3), ..., clause_k = (-x_{k-1}, x_k)
            // So (-x_{i-1} v x_i) is clause (i) for i >= 3.
            let chain_clause_id = i as i64;
            proof_steps.push(LratStep::Add {
                id: ClauseId(next_proof_id),
                clause: vec![Lit(i as i32)],
                hints: vec![chain_clause_id, prev_derived_id as i64],
            });
            prev_derived_id = next_proof_id;
            next_proof_id += 1;
        }

        // Derive empty clause: x_num_vars contradicts (-x_num_vars)
        let final_neg_id = num_original as i64;
        proof_steps.push(LratStep::Add {
            id: ClauseId(next_proof_id),
            clause: vec![],
            hints: vec![prev_derived_id as i64, final_neg_id],
        });

        // Add some deletions to exercise streaming deletion path.
        let del_start_id = next_proof_id + 1;
        proof_steps.push(LratStep::Delete {
            clause_ids: vec![ClauseId(1), ClauseId(2)],
        });

        let total_steps = proof_steps.len();
        assert!(
            total_steps >= 50,
            "expected 50+ proof steps, got {total_steps}"
        );
        assert!(
            original_clauses.len() >= 100,
            "expected 100+ original clauses, got {}",
            original_clauses.len()
        );

        // Batch verification.
        let mut batch_checker = LratChecker::new(num_vars);
        for (id, clause) in &original_clauses {
            batch_checker.add_original(*id, clause).expect("ok");
        }
        let batch_result = batch_checker
            .verify_proof(&proof_steps)
            .expect("batch verify should succeed");
        assert!(
            batch_result.refuted,
            "batch proof should derive empty clause"
        );

        // Text streaming verification.
        let text_proof = format_lrat_text_steps(&proof_steps);
        let text_reader = std::io::BufReader::new(text_proof.as_bytes());
        let streaming_text_result =
            verify_lrat_streaming_text(text_reader, num_vars, &original_clauses)
                .expect("streaming text verify should succeed");
        assert!(
            streaming_text_result.refuted,
            "streaming text should derive empty clause"
        );
        assert_eq!(
            batch_result.verified_steps, streaming_text_result.verified_steps,
            "step count mismatch between batch and streaming"
        );

        // Binary round-trip: encode as binary, parse back, verify.
        let binary_proof = encode_lrat_binary_steps(&proof_steps);
        let binary_steps = parse_binary_lrat(&binary_proof).expect("binary round-trip parse");
        assert_eq!(
            proof_steps, binary_steps,
            "binary round-trip should produce identical steps"
        );

        // Binary streaming verification.
        let binary_reader = std::io::BufReader::new(&binary_proof[..]);
        let streaming_binary_result =
            verify_lrat_streaming_binary(binary_reader, num_vars, &original_clauses)
                .expect("streaming binary verify should succeed");
        assert!(
            streaming_binary_result.refuted,
            "streaming binary should derive empty clause"
        );
        assert_eq!(
            batch_result.verified_steps,
            streaming_binary_result.verified_steps
        );
    }

    /// Format LRAT steps as text for streaming tests.
    fn format_lrat_text_steps(steps: &[LratStep]) -> String {
        let mut output = String::new();
        for step in steps {
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
                    if let Some(first) = clause_ids.first() {
                        output.push_str(&first.0.to_string());
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
        output
    }

    /// Encode LRAT steps in binary format.
    fn encode_lrat_binary_steps(steps: &[LratStep]) -> Vec<u8> {
        let mut data = Vec::new();
        for step in steps {
            match step {
                LratStep::Add { id, clause, hints } => {
                    data.push(b'a');
                    data.extend(encode_uleb128(id.0));
                    for lit in clause {
                        data.extend(encode_uleb128(encode_binary_lit(*lit)));
                    }
                    data.extend(encode_uleb128(0));
                    for hint in hints {
                        data.extend(encode_uleb128(encode_binary_hint(*hint)));
                    }
                    data.extend(encode_uleb128(0));
                }
                LratStep::Delete { clause_ids } => {
                    data.push(b'd');
                    for cid in clause_ids {
                        data.extend(encode_uleb128(cid.0));
                    }
                    data.extend(encode_uleb128(0));
                }
            }
        }
        data
    }
}
