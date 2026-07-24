// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! DRAT/DRUP proof logging and verification.
//!
//! Implements Reverse Unit Propagation (RUP) and Resolution Asymmetric
//! Tautology (RAT) checking for CDCL unsatisfiability proofs.
//!
//! References:
//! - Wetzler, Heule, Hunt: "DRAT-trim: Efficient Checking and Trimming
//!   Using Expressive Clausal Proofs" (SAT 2014)
//! - Heule, Hunt, Wetzler: "Trimming while Checking Clausal Proofs"
//!   (FMCAD 2013)

use super::{negate, CdclError, Clause, Literal};
use crate::spec::ProofStatus;

/// S09: RUP verification is sound — if `verify_rup` returns true, the
/// new clause is an asymmetric tautology implied by the current clause set.
pub const S09_RUP_SOUNDNESS: ProofStatus = ProofStatus::DerivedPending;

/// S10: RAT verification is sound — if `verify_rat` returns true, the
/// new clause is a resolution asymmetric tautology w.r.t. the pivot.
pub const S10_RAT_SOUNDNESS: ProofStatus = ProofStatus::DerivedPending;

/// A single step in a DRAT/DRUP proof.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum ProofStep {
    /// Add a clause (must be RUP or RAT w.r.t. current clause set).
    Add(Clause),
    /// Delete a clause from the active set.
    Delete(Clause),
}

/// Result of verifying a complete proof log.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProofLogResult {
    /// Whether the entire proof log verified successfully.
    pub valid: bool,
    /// Number of steps that were successfully verified.
    pub steps_verified: usize,
    /// Index of the first step that failed verification, if any.
    pub first_error: Option<usize>,
    /// Indices of deletion steps that targeted non-existent clauses.
    ///
    /// A well-formed DRAT proof should only delete clauses that exist in the
    /// active clause set. Deletions of non-existent clauses indicate a
    /// corrupted or malformed proof, even if the proof is otherwise valid.
    pub phantom_deletions: Vec<usize>,
}

/// A complete proof log: original clauses plus proof steps.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProofLog {
    /// Proof steps (additions and deletions).
    pub steps: Vec<ProofStep>,
    /// The original clause set from the CNF formula.
    pub original_clauses: Vec<Clause>,
}

/// Verify a clause by Reverse Unit Propagation.
///
/// Returns `true` if unit propagation of the negation of `new_clause`
/// on `clauses` derives a conflict, proving `new_clause` is implied.
///
/// SOUNDNESS FIX (#3327): During unit propagation, if the same variable
/// would be assigned both true and false, that is a contradiction and
/// the clause is RUP. Previously this case was not detected, which could
/// cause incorrect verification results when the trail became inconsistent.
#[must_use]
pub fn verify_rup(clauses: &[Clause], new_clause: &[Literal]) -> bool {
    // Build assignment: negate every literal in new_clause.
    let mut assignment = Vec::new();
    for &lit in new_clause {
        // Check if the negated literal contradicts an existing assignment.
        let neg = negate(lit);
        if assignment.contains(&negate(neg)) {
            // Variable assigned both polarities: contradiction => RUP.
            return true;
        }
        assignment.push(neg);
    }

    // Iteratively propagate until fixpoint or conflict.
    loop {
        let mut progress = false;
        for clause in clauses {
            match eval_clause_under(clause, &assignment) {
                ClauseEval::Conflict => return true,
                ClauseEval::Unit(unit_lit) => {
                    // SOUNDNESS FIX (#3327): Check for contradictory
                    // assignment before adding the unit literal.
                    let neg_unit = negate(unit_lit);
                    if assignment.contains(&neg_unit) {
                        // Contradictory assignment: variable would be
                        // both true and false. This is a conflict.
                        return true;
                    }
                    if !assignment.contains(&unit_lit) {
                        assignment.push(unit_lit);
                        progress = true;
                    }
                }
                ClauseEval::Satisfied | ClauseEval::Unresolved => {}
            }
        }
        if !progress {
            return false;
        }
    }
}

/// Verify a clause by Resolution Asymmetric Tautology w.r.t. a pivot.
///
/// A clause C with pivot literal p is RAT w.r.t. clause set F if for
/// every clause D in F containing ~p, RUP(F, C | (D \ {~p})) holds.
#[must_use]
pub fn verify_rat(clauses: &[Clause], new_clause: &[Literal], pivot: Literal) -> bool {
    // The pivot must be in new_clause.
    if !new_clause.contains(&pivot) {
        return false;
    }

    let neg_pivot = negate(pivot);

    // For every clause containing the negation of the pivot...
    for clause in clauses {
        if !clause.contains(&neg_pivot) {
            continue;
        }
        // Build resolvent: new_clause union (clause \ {neg_pivot})
        let mut resolvent: Vec<Literal> = new_clause.to_vec();
        for &lit in clause {
            if lit != neg_pivot && !resolvent.contains(&lit) {
                resolvent.push(lit);
            }
        }
        // The resolvent must be RUP w.r.t. the clause set.
        if !verify_rup(clauses, &resolvent) {
            return false;
        }
    }
    true
}

/// Verify a complete proof log step by step.
///
/// Processes each step in order, maintaining the active clause set.
/// Addition steps must be verifiable by RUP (or RAT with first literal
/// as pivot). Deletion steps remove clauses from the active set.
///
/// A valid DRAT refutation proof must derive the empty clause at some
/// point during the proof. If all steps are individually valid but the
/// empty clause is never derived, the proof does not establish
/// unsatisfiability and is rejected.
#[must_use]
pub fn verify_proof_log(log: &ProofLog) -> ProofLogResult {
    let mut active_clauses: Vec<Clause> = log.original_clauses.clone();
    let mut empty_clause_derived = false;
    let mut phantom_deletions = Vec::new();

    for (i, step) in log.steps.iter().enumerate() {
        match step {
            ProofStep::Add(clause) => {
                if !verify_addition(&active_clauses, clause) {
                    return ProofLogResult {
                        valid: false,
                        steps_verified: i,
                        first_error: Some(i),
                        phantom_deletions,
                    };
                }
                if clause.is_empty() {
                    empty_clause_derived = true;
                }
                active_clauses.push(clause.clone());
            }
            ProofStep::Delete(clause) => {
                if !remove_clause(&mut active_clauses, clause) {
                    phantom_deletions.push(i);
                }
            }
        }
    }

    // A valid refutation proof must derive the empty clause (contradiction).
    // Without it, the proof does not establish unsatisfiability.
    ProofLogResult {
        valid: empty_clause_derived,
        steps_verified: log.steps.len(),
        first_error: if empty_clause_derived {
            None
        } else {
            Some(log.steps.len())
        },
        phantom_deletions,
    }
}

/// Parse a DRAT proof from text format.
///
/// Format: one clause per line, `0`-terminated. Lines starting with `d`
/// are deletion steps; others are addition steps.
///
/// ```text
/// 1 2 0          // add clause {1, 2}
/// d -1 3 0       // delete clause {-1, 3}
/// 0              // add empty clause (refutation)
/// ```
pub fn parse_drat_proof(input: &str) -> Result<Vec<ProofStep>, CdclError> {
    let mut steps = Vec::new();
    for line in input.lines() {
        let line = line.trim();
        if line.is_empty() || line.starts_with('c') {
            continue;
        }
        let step = parse_single_step(line)?;
        steps.push(step);
    }
    Ok(steps)
}

/// Format a single proof step as DRAT text.
#[must_use]
pub fn format_drat_step(step: &ProofStep) -> String {
    match step {
        ProofStep::Add(clause) => format_clause_line(clause),
        ProofStep::Delete(clause) => {
            let mut s = String::from("d ");
            s.push_str(&format_clause_line(clause));
            s
        }
    }
}

// ---- internal helpers ----

/// Result of evaluating a clause under a partial assignment.
enum ClauseEval {
    /// All literals are falsified.
    Conflict,
    /// Exactly one literal is unassigned; all others are falsified.
    Unit(Literal),
    /// At least one literal is satisfied.
    Satisfied,
    /// Two or more literals are unassigned.
    Unresolved,
}

/// Evaluate a clause under a partial assignment (list of true literals).
fn eval_clause_under(clause: &[Literal], assignment: &[Literal]) -> ClauseEval {
    let mut unassigned: Option<Literal> = None;
    for &lit in clause {
        if assignment.contains(&lit) {
            return ClauseEval::Satisfied;
        }
        let neg = negate(lit);
        if assignment.contains(&neg) {
            // This literal is falsified; continue.
            continue;
        }
        // Literal is unassigned.
        match unassigned {
            None => unassigned = Some(lit),
            Some(_) => return ClauseEval::Unresolved,
        }
    }
    match unassigned {
        None => ClauseEval::Conflict,
        Some(u) => ClauseEval::Unit(u),
    }
}

/// Verify an addition step: try RUP first, then RAT with first literal as pivot.
fn verify_addition(clauses: &[Clause], new_clause: &Clause) -> bool {
    if verify_rup(clauses, new_clause) {
        return true;
    }
    // Try RAT with the first literal as pivot (DRAT convention).
    if let Some(&pivot) = new_clause.first() {
        return verify_rat(clauses, new_clause, pivot);
    }
    // Empty clause addition: RUP must have caught it (conflict from no assumptions).
    false
}

/// Remove the first occurrence of `target` from `clauses` (set-equality match).
///
/// Returns `true` if the clause was found and removed, `false` if no matching
/// clause exists in the active set (phantom deletion).
fn remove_clause(clauses: &mut Vec<Clause>, target: &Clause) -> bool {
    let mut sorted_target = target.clone();
    sorted_target.sort_unstable();
    if let Some(pos) = clauses.iter().position(|c| {
        let mut sorted = c.clone();
        sorted.sort_unstable();
        sorted == sorted_target
    }) {
        clauses.remove(pos);
        true
    } else {
        false
    }
}

/// Parse a single DRAT line into a `ProofStep`.
fn parse_single_step(line: &str) -> Result<ProofStep, CdclError> {
    let is_delete = line.starts_with('d');
    let tokens = if is_delete { line[1..].trim() } else { line };

    let mut lits = Vec::new();
    for tok in tokens.split_whitespace() {
        let val: i32 = tok
            .parse()
            .map_err(|_| CdclError::ParseError(format!("bad DRAT literal: {tok}")))?;
        if val == 0 {
            break;
        }
        lits.push(val);
    }

    if is_delete {
        Ok(ProofStep::Delete(lits))
    } else {
        Ok(ProofStep::Add(lits))
    }
}

/// Format a clause as a space-separated line ending with `0`.
fn format_clause_line(clause: &[Literal]) -> String {
    let mut parts: Vec<String> = clause.iter().map(|l| l.to_string()).collect();
    parts.push("0".to_string());
    parts.join(" ")
}
