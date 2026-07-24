// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Data types for DRAT/LRAT proof certificate verification.

// ============================================================================
// Data Structures
// ============================================================================

/// A CNF formula represented as a list of clauses.
#[derive(Debug, Clone, Default)]
pub struct CnfFormula {
    /// The clauses in the formula
    pub clauses: Vec<Vec<i32>>,
    /// Number of variables
    pub num_vars: usize,
}

impl CnfFormula {
    /// Create a new empty CNF formula
    ///
    /// ENSURES: `clauses` is empty and `num_vars` is 0.
    pub fn new() -> Self {
        Self::default()
    }

    /// Add a clause to the formula
    ///
    /// REQUIRES: Literals in `clause` are non-zero (0 is the DIMACS terminator).
    /// ENSURES: `num_vars` is updated to the maximum variable index across all clauses.
    /// ENSURES: `clause` is appended to `self.clauses`.
    pub fn add_clause(&mut self, clause: Vec<i32>) {
        for &lit in &clause {
            let var = lit.unsigned_abs() as usize;
            if var > self.num_vars {
                self.num_vars = var;
            }
        }
        self.clauses.push(clause);
    }

    /// Parse a CNF formula from DIMACS format
    ///
    /// REQUIRES: `input` is valid DIMACS CNF text (comment lines start with 'c',
    ///   header is `p cnf <vars> <clauses>`, clauses terminated by 0).
    /// ENSURES: On `Ok`, `num_vars` reflects the header or actual maximum variable.
    /// ENSURES: Trailing clauses without a `0` terminator are still captured.
    pub fn parse_dimacs(input: &str) -> Result<Self, DratError> {
        let mut formula = CnfFormula::new();
        let mut current_clause = Vec::new();

        for line in input.lines() {
            let line = line.trim();

            // Skip comments and empty lines
            if line.is_empty() || line.starts_with('c') {
                continue;
            }

            // Parse header
            if line.starts_with("p cnf") {
                let parts: Vec<&str> = line.split_whitespace().collect();
                if parts.len() >= 4 {
                    if let Ok(vars) = parts[2].parse::<usize>() {
                        formula.num_vars = vars;
                    }
                }
                continue;
            }

            // Parse clause literals
            for token in line.split_whitespace() {
                match token.parse::<i32>() {
                    Ok(0) => {
                        if !current_clause.is_empty() {
                            formula.add_clause(current_clause.clone());
                            current_clause.clear();
                        }
                    }
                    Ok(lit) => current_clause.push(lit),
                    Err(_) => {} // Skip non-numeric tokens
                }
            }
        }

        // Handle final clause without trailing 0
        if !current_clause.is_empty() {
            formula.add_clause(current_clause);
        }

        Ok(formula)
    }
}

/// A DRAT proof operation
#[derive(Debug, Clone)]
pub enum DratOp {
    /// Add a clause (RUP or RAT)
    Add(Vec<i32>),
    /// Delete a clause
    Delete(Vec<i32>),
}

/// A DRAT proof certificate
#[derive(Debug, Clone, Default)]
pub struct DratProof {
    /// The proof operations
    pub operations: Vec<DratOp>,
}

impl DratProof {
    /// Create a new empty DRAT proof
    ///
    /// ENSURES: `operations` is empty.
    pub fn new() -> Self {
        Self::default()
    }

    /// Parse a DRAT proof from text format
    ///
    /// REQUIRES: `input` is DRAT-format text (delete lines prefixed with 'd',
    ///   clause literals terminated by 0, empty lines skipped).
    /// ENSURES: Each non-empty line becomes an `Add` or `Delete` operation.
    /// ENSURES: Empty clauses (line "0") are preserved as valid operations.
    pub fn parse(input: &str) -> Result<Self, DratError> {
        let mut proof = DratProof::new();

        for line in input.lines() {
            let line = line.trim();
            if line.is_empty() {
                continue;
            }

            // Check for delete line
            let is_delete = line.starts_with('d') || line.starts_with("d ");
            let line = if is_delete {
                line.trim_start_matches('d').trim()
            } else {
                line
            };

            // Parse literals
            let mut clause = Vec::new();
            for token in line.split_whitespace() {
                match token.parse::<i32>() {
                    Ok(0) => break,
                    Ok(lit) => clause.push(lit),
                    Err(_) => {}
                }
            }

            // Empty clauses (line "0") are valid — they represent the
            // derivation of ⊥ (the conclusion of every UNSAT proof).
            if is_delete {
                proof.operations.push(DratOp::Delete(clause));
            } else {
                proof.operations.push(DratOp::Add(clause));
            }
        }

        Ok(proof)
    }
}

/// An LRAT proof operation
#[derive(Debug, Clone)]
pub enum LratOp {
    /// Add a clause with ID and RUP hints
    Add {
        /// Clause ID (unique identifier)
        id: u64,
        /// The clause literals
        clause: Vec<i32>,
        /// Hint clause IDs for RUP derivation
        hints: Vec<u64>,
    },
    /// Delete clauses by ID
    Delete {
        /// The deleting clause ID
        id: u64,
        /// IDs of clauses to delete
        clause_ids: Vec<u64>,
    },
}

/// An LRAT proof certificate
#[derive(Debug, Clone, Default)]
pub struct LratProof {
    /// The proof operations
    pub operations: Vec<LratOp>,
}

impl LratProof {
    /// Create a new empty LRAT proof
    ///
    /// ENSURES: `operations` is empty.
    pub fn new() -> Self {
        Self::default()
    }

    /// Parse an LRAT proof from text format
    ///
    /// REQUIRES: `input` is LRAT-format text (each line: `id [d id1 ...] | [lit ... 0 hint ... 0]`).
    /// ENSURES: On `Ok`, each non-empty/non-comment line becomes an `Add` or `Delete` operation.
    /// ENSURES: On `Err(ParseError)`, the first token could not be parsed as a clause ID.
    pub fn parse(input: &str) -> Result<Self, DratError> {
        let mut proof = LratProof::new();

        for line in input.lines() {
            let line = line.trim();
            if line.is_empty() || line.starts_with('c') {
                continue;
            }

            let tokens: Vec<&str> = line.split_whitespace().collect();
            if tokens.is_empty() {
                continue;
            }

            // First token is always the clause ID
            let id = tokens[0]
                .parse::<u64>()
                .map_err(|_| DratError::ParseError("Invalid clause ID".to_string()))?;

            // Check if this is a delete operation
            if tokens.len() > 1 && tokens[1] == "d" {
                let clause_ids: Vec<u64> = tokens[2..]
                    .iter()
                    .filter(|&&t| t != "0")
                    .filter_map(|t| t.parse().ok())
                    .collect();
                proof.operations.push(LratOp::Delete { id, clause_ids });
            } else {
                // Add operation: id lit1 lit2 ... 0 hint1 hint2 ... 0
                let mut clause = Vec::new();
                let mut hints = Vec::new();
                let mut parsing_hints = false;

                for &token in &tokens[1..] {
                    if token == "0" {
                        parsing_hints = true;
                        continue;
                    }

                    if parsing_hints {
                        // Hints are clause IDs (positive integers)
                        if let Ok(hint) = token.parse::<u64>() {
                            hints.push(hint);
                        }
                    } else {
                        // Literals can be positive or negative
                        if let Ok(lit) = token.parse::<i32>() {
                            clause.push(lit);
                        }
                    }
                }

                proof.operations.push(LratOp::Add { id, clause, hints });
            }
        }

        Ok(proof)
    }
}

/// Errors that can occur during DRAT/LRAT verification
#[derive(Debug, Clone, thiserror::Error)]
#[non_exhaustive]
pub enum DratError {
    /// Parse error
    #[error("Parse error: {0}")]
    ParseError(String),
    /// RUP check failed
    #[error("RUP check failed at step {step}: {clause:?}")]
    RupCheckFailed { clause: Vec<i32>, step: usize },
    /// RAT check failed
    #[error("RAT check failed at step {step} (pivot {pivot}): {clause:?}")]
    RatCheckFailed {
        clause: Vec<i32>,
        pivot: i32,
        step: usize,
    },
    /// Invalid hint in LRAT proof
    #[error("Invalid hint {hint_id} at step {step}")]
    InvalidHint { hint_id: u64, step: usize },
    /// Missing clause ID
    #[error("Missing clause ID {id} at step {step}")]
    MissingClauseId { id: u64, step: usize },
    /// Empty clause not derived
    #[error("Empty clause not derived")]
    NoEmptyClause,
}

/// Result of processing a single proof step
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StepResult {
    /// Step valid, continue processing
    Continue,
    /// Proof complete (empty clause derived)
    Complete,
}

/// Result of proof reconstruction
#[derive(Debug)]
pub struct DratProofResult {
    /// The proof term (if reconstruction succeeded)
    pub proof_term: Option<clean_kernel::Expr>,
    /// Whether the DRAT/LRAT verification succeeded
    pub verified: bool,
    /// Error message if reconstruction failed
    pub error: Option<String>,
}
