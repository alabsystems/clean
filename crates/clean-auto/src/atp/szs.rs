// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! SZS (SUMO-TPTP-TSTP) status ontology for ATP results.

use std::fmt;

/// SZS status codes per the TPTP ontology.
///
/// Reference: <http://www.tptp.org/TPTP/SZSOntology>
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum SzsStatus {
    /// FOF conjecture proved (negated conjecture + axioms is unsatisfiable).
    Theorem,
    /// CNF clause set is unsatisfiable (no conjecture present).
    Unsatisfiable,
    /// Negated conjecture + axioms is satisfiable (conjecture is false).
    CounterSatisfiable,
    /// CNF clause set is satisfiable (no conjecture present).
    Satisfiable,
    /// Resource limit (time or iterations) exhausted.
    ResourceOut,
    /// Prover gave up without a conclusive result.
    GaveUp,
    /// Input error (parse failure, etc.).
    InputError,
}

impl fmt::Display for SzsStatus {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let name = match self {
            SzsStatus::Theorem => "Theorem",
            SzsStatus::Unsatisfiable => "Unsatisfiable",
            SzsStatus::CounterSatisfiable => "CounterSatisfiable",
            SzsStatus::Satisfiable => "Satisfiable",
            SzsStatus::ResourceOut => "ResourceOut",
            SzsStatus::GaveUp => "GaveUp",
            SzsStatus::InputError => "InputError",
        };
        write!(f, "{name}")
    }
}

/// Format an SZS status line for TPTP output.
///
/// Example: `% SZS status Theorem for PUZ001+1`
pub(crate) fn format_szs_status(status: SzsStatus, problem_name: &str) -> String {
    format!("% SZS status {status} for {problem_name}")
}

/// Format the start of an SZS proof output block.
pub(crate) fn format_szs_proof_start(problem_name: &str) -> String {
    format!("% SZS output start Proof for {problem_name}")
}

/// Format the end of an SZS proof output block.
pub(crate) fn format_szs_proof_end(problem_name: &str) -> String {
    format!("% SZS output end Proof for {problem_name}")
}
