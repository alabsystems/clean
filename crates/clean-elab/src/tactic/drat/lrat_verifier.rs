// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! LRAT (Linear RAT) proof verifier and checkpoint/resume support.

use std::collections::HashMap;

use super::types::{CnfFormula, DratError, LratOp, LratProof};

/// LRAT proof verifier (more efficient than DRAT)
pub struct LratVerifier {
    /// Active clauses indexed by ID
    clauses: HashMap<u64, Vec<i32>>,
    /// Next automatic clause ID
    next_id: u64,
    /// Number of variables
    num_vars: usize,
}

impl LratVerifier {
    /// Create a new LRAT verifier
    pub fn new() -> Self {
        Self {
            clauses: HashMap::new(),
            next_id: 1,
            num_vars: 0,
        }
    }

    /// Initialize with a CNF formula
    pub fn init_formula(&mut self, formula: &CnfFormula) {
        self.num_vars = formula.num_vars;
        self.clauses.clear();
        self.next_id = 1;

        for clause in &formula.clauses {
            self.clauses.insert(self.next_id, clause.clone());
            self.next_id += 1;
        }
    }

    /// Check RUP (Reverse Unit Propagation) with specific hints.
    ///
    /// REQUIRES: `clause` contains valid DIMACS-format literals (nonzero i32).
    ///   `hints` are clause IDs that must exist in `self.clauses`.
    ///   `self.num_vars` correctly bounds all variable indices.
    /// ENSURES: Returns Ok(true) if unit propagation using hint clauses derives
    ///   a conflict (proving the clause is RUP). Returns Ok(false) if no conflict
    ///   found. Returns Err(InvalidHint) if a hint ID is not in the clause database.
    fn is_rup_with_hints(&self, clause: &[i32], hints: &[u64]) -> Result<bool, DratError> {
        let mut assignment: Vec<Option<bool>> = vec![None; self.num_vars + 1];

        // Set all literals in clause to false
        for &lit in clause {
            let var = lit.unsigned_abs() as usize;
            if var < assignment.len() {
                assignment[var] = Some(lit < 0);
            }
        }

        // Propagate using only the hint clauses
        for &hint_id in hints {
            let hint_clause = self.clauses.get(&hint_id).ok_or(DratError::InvalidHint {
                hint_id,
                step: 0, // Will be filled in by caller
            })?;

            // Check if clause becomes unit or conflict
            let mut unassigned_lit = None;
            let mut num_false = 0;
            let mut satisfied = false;

            for &lit in hint_clause {
                let var = lit.unsigned_abs() as usize;
                if var >= assignment.len() {
                    unassigned_lit = Some(lit);
                    continue;
                }

                match assignment[var] {
                    Some(val) => {
                        let lit_true = (lit > 0) == val;
                        if lit_true {
                            satisfied = true;
                            break;
                        } else {
                            num_false += 1;
                        }
                    }
                    None => {
                        if unassigned_lit.is_some() {
                            // Not a unit clause with current assignment
                            break;
                        }
                        unassigned_lit = Some(lit);
                    }
                }
            }

            if satisfied {
                continue;
            }

            // Conflict found!
            if num_false == hint_clause.len() {
                return Ok(true);
            }

            // Unit propagation
            if num_false == hint_clause.len() - 1 {
                if let Some(lit) = unassigned_lit {
                    let var = lit.unsigned_abs() as usize;
                    if var < assignment.len() && assignment[var].is_none() {
                        assignment[var] = Some(lit > 0);
                    }
                }
            }
        }

        // Check if we have a conflict with any clause
        for clause in self.clauses.values() {
            let all_false = clause.iter().all(|&lit| {
                let var = lit.unsigned_abs() as usize;
                if var >= assignment.len() {
                    return false;
                }
                match assignment[var] {
                    Some(val) => (lit > 0) != val,
                    None => false,
                }
            });
            if all_false {
                return Ok(true);
            }
        }

        Ok(false)
    }

    /// Verify an LRAT proof.
    ///
    /// REQUIRES: `formula` is a valid CNF formula. `proof` contains well-formed
    ///   LRAT operations where Add clause IDs are unique and hint IDs reference
    ///   existing clauses.
    /// ENSURES: Returns Ok(true) iff the proof successfully derives the empty
    ///   clause (certifying UNSAT). Returns Err(RupCheckFailed) if a clause
    ///   addition fails RUP. Returns Err(NoEmptyClause) if proof ends without
    ///   deriving contradiction.
    pub fn verify(formula: &CnfFormula, proof: &LratProof) -> Result<bool, DratError> {
        let mut verifier = LratVerifier::new();
        verifier.init_formula(formula);

        let mut derived_empty = false;

        for (step, op) in proof.operations.iter().enumerate() {
            match op {
                LratOp::Add { id, clause, hints } => {
                    // Verify RUP with hints (including empty clause — must
                    // be derivable from hint chain, not accepted blindly)
                    match verifier.is_rup_with_hints(clause, hints) {
                        Ok(true) => {
                            if clause.is_empty() {
                                derived_empty = true;
                                break;
                            }
                            verifier.clauses.insert(*id, clause.clone());
                        }
                        Ok(false) => {
                            return Err(DratError::RupCheckFailed {
                                clause: clause.clone(),
                                step,
                            });
                        }
                        Err(mut e) => {
                            if let DratError::InvalidHint { step: s, .. } = &mut e {
                                *s = step;
                            }
                            return Err(e);
                        }
                    }
                }
                LratOp::Delete { clause_ids, .. } => {
                    for &del_id in clause_ids {
                        verifier.clauses.remove(&del_id);
                    }
                }
            }
        }

        if !derived_empty {
            return Err(DratError::NoEmptyClause);
        }

        Ok(true)
    }
}

impl Default for LratVerifier {
    fn default() -> Self {
        Self::new()
    }
}

// ============================================================================
// Streaming/Incremental Verification API
// ============================================================================
//
// Per Ay Integration Requirements (CLEAN_FEATURE_REQUESTS.md):
// - Provide incremental proof certificate verification
// - Support checkpoint/resume for long-running AI proof searches
// - LRAT preferred for incremental mode (linear-time checking with hints)
//
// Design: designs/2026-01-28-incremental-certificate-verification.md

/// Checkpoint of an LRAT verifier state for incremental verification.
///
/// Enables save/restore for long-running proof searches per Ay's
/// interactive mode requirements.
#[derive(Debug, Clone)]
pub struct LratCheckpoint {
    /// Active clauses indexed by ID
    pub(crate) clauses: HashMap<u64, Vec<i32>>,
    /// Next automatic clause ID
    pub(crate) next_id: u64,
    /// Number of variables
    pub(crate) num_vars: usize,
    /// Number of proof steps processed
    pub(crate) steps_processed: usize,
    /// Whether empty clause has been derived
    pub(crate) derived_empty: bool,
}

impl LratCheckpoint {
    /// Serialize checkpoint to bytes for persistence.
    ///
    /// ENSURES: Output is a valid input to `from_bytes()`. Roundtrip:
    ///   `from_bytes(&checkpoint.to_bytes()) == Ok(equivalent_checkpoint)`.
    pub fn to_bytes(&self) -> Vec<u8> {
        // Simple binary format: num_vars (8), next_id (8), steps (8), derived (1),
        // clause_count (8), then for each: id (8), len (4), literals...
        let mut bytes = Vec::new();
        bytes.extend_from_slice(&(self.num_vars as u64).to_le_bytes());
        bytes.extend_from_slice(&self.next_id.to_le_bytes());
        bytes.extend_from_slice(&(self.steps_processed as u64).to_le_bytes());
        bytes.push(if self.derived_empty { 1 } else { 0 });
        bytes.extend_from_slice(&(self.clauses.len() as u64).to_le_bytes());

        for (&id, clause) in &self.clauses {
            bytes.extend_from_slice(&id.to_le_bytes());
            bytes.extend_from_slice(&(clause.len() as u32).to_le_bytes());
            for &lit in clause {
                bytes.extend_from_slice(&lit.to_le_bytes());
            }
        }
        bytes
    }

    /// Deserialize checkpoint from bytes.
    ///
    /// REQUIRES: `bytes` was produced by `to_bytes()` or follows the same binary
    ///   format: header (num_vars:u64, next_id:u64, steps:u64, derived:u8,
    ///   clause_count:u64), then clause_count entries of (id:u64, len:u32, lits:i32*len).
    /// ENSURES: On Ok, returns a valid LratCheckpoint equivalent to the original.
    ///   On Err(ParseError), the input was truncated or malformed. Validates all
    ///   lengths before allocation to prevent OOM from corrupt clause_count values.
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, DratError> {
        if bytes.len() < 33 {
            return Err(DratError::ParseError("Checkpoint too short".to_string()));
        }

        fn read_u64(bytes: &[u8], pos: &mut usize, context: &str) -> Result<u64, DratError> {
            if *pos + 8 > bytes.len() {
                return Err(DratError::ParseError(context.to_string()));
            }
            let value = u64::from_le_bytes(
                bytes[*pos..*pos + 8]
                    .try_into()
                    .map_err(|_| DratError::ParseError(context.to_string()))?,
            );
            *pos += 8;
            Ok(value)
        }

        fn read_u32(bytes: &[u8], pos: &mut usize, context: &str) -> Result<u32, DratError> {
            if *pos + 4 > bytes.len() {
                return Err(DratError::ParseError(context.to_string()));
            }
            let value = u32::from_le_bytes(
                bytes[*pos..*pos + 4]
                    .try_into()
                    .map_err(|_| DratError::ParseError(context.to_string()))?,
            );
            *pos += 4;
            Ok(value)
        }

        fn read_i32(bytes: &[u8], pos: &mut usize, context: &str) -> Result<i32, DratError> {
            if *pos + 4 > bytes.len() {
                return Err(DratError::ParseError(context.to_string()));
            }
            let value = i32::from_le_bytes(
                bytes[*pos..*pos + 4]
                    .try_into()
                    .map_err(|_| DratError::ParseError(context.to_string()))?,
            );
            *pos += 4;
            Ok(value)
        }

        fn read_byte(bytes: &[u8], pos: &mut usize, context: &str) -> Result<u8, DratError> {
            if *pos >= bytes.len() {
                return Err(DratError::ParseError(context.to_string()));
            }
            let value = bytes[*pos];
            *pos += 1;
            Ok(value)
        }

        let mut pos = 0;
        let num_vars = usize::try_from(read_u64(bytes, &mut pos, "Checkpoint too short")?)
            .map_err(|_| DratError::ParseError("Checkpoint too short".to_string()))?;
        let next_id = read_u64(bytes, &mut pos, "Checkpoint too short")?;
        let steps_processed =
            usize::try_from(read_u64(bytes, &mut pos, "Checkpoint too short")?)
                .map_err(|_| DratError::ParseError("Checkpoint too short".to_string()))?;
        let derived_empty = read_byte(bytes, &mut pos, "Checkpoint too short")? != 0;
        let clause_count = usize::try_from(read_u64(bytes, &mut pos, "Checkpoint too short")?)
            .map_err(|_| DratError::ParseError("Checkpoint too short".to_string()))?;

        let remaining = bytes.len().saturating_sub(pos);
        let max_clauses = remaining / 12;
        if clause_count > max_clauses {
            return Err(DratError::ParseError("Truncated checkpoint".to_string()));
        }
        let mut clauses = HashMap::with_capacity(clause_count);
        for _ in 0..clause_count {
            if pos + 12 > bytes.len() {
                return Err(DratError::ParseError("Truncated checkpoint".to_string()));
            }
            let id = read_u64(bytes, &mut pos, "Truncated checkpoint")?;
            let len = read_u32(bytes, &mut pos, "Truncated checkpoint")? as usize;

            let needed = len
                .checked_mul(4)
                .and_then(|bytes_len| pos.checked_add(bytes_len))
                .ok_or_else(|| DratError::ParseError("Truncated clause".to_string()))?;
            if needed > bytes.len() {
                return Err(DratError::ParseError("Truncated clause".to_string()));
            }
            let mut clause = Vec::with_capacity(len);
            for _ in 0..len {
                clause.push(read_i32(bytes, &mut pos, "Truncated clause")?);
            }
            clauses.insert(id, clause);
        }

        Ok(LratCheckpoint {
            clauses,
            next_id,
            num_vars,
            steps_processed,
            derived_empty,
        })
    }
}
