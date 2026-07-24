// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! ATP runner: orchestrates parsing, clausification, proving, and output.

use super::cnf_transform::{clausify_problem, ClausificationResult, SymbolTable};
use super::szs::{format_szs_proof_end, format_szs_proof_start, format_szs_status};
use super::tptp_parser::{parse_tptp, TptpParseError};
use crate::superposition::{Clause, Inference, ProverResult, SuperpositionProver, Term};

use super::szs::SzsStatus;
use thiserror::Error;

/// ATP error.
#[derive(Debug, Error)]
#[non_exhaustive]
pub enum AtpError {
    #[error("TPTP parse error: {0}")]
    Parse(#[from] TptpParseError),
}

/// Configuration for the ATP runner.
#[derive(Clone, Debug)]
pub struct AtpConfig {
    /// Maximum iterations for the prover.
    pub max_iterations: u64,
    /// Maximum clause size.
    pub max_clause_size: usize,
    /// Problem name (used in SZS output).
    pub problem_name: String,
}

impl Default for AtpConfig {
    fn default() -> Self {
        AtpConfig {
            max_iterations: 100_000,
            max_clause_size: 100,
            problem_name: "unknown".to_string(),
        }
    }
}

/// Result of an ATP run.
#[derive(Clone, Debug)]
pub struct AtpResult {
    /// SZS status.
    pub status: SzsStatus,
    /// Formatted output (SZS status line + optional proof).
    pub output: String,
}

/// ATP runner: parse TPTP, clausify, prove, and format output.
pub struct AtpRunner {
    config: AtpConfig,
}

impl Default for AtpRunner {
    fn default() -> Self {
        AtpRunner::new(AtpConfig::default())
    }
}

impl AtpRunner {
    pub fn new(config: AtpConfig) -> Self {
        AtpRunner { config }
    }

    /// Run the ATP on a TPTP problem string.
    pub fn run(&self, input: &str) -> Result<AtpResult, AtpError> {
        // Parse
        let problem = parse_tptp(input)?;
        let has_conjecture = problem.has_conjecture();

        // Clausify
        let ClausificationResult { clauses, table } = clausify_problem(&problem.formulas);

        // Create prover and add clauses
        let mut prover = SuperpositionProver::new();
        for clause in &clauses {
            prover.add_clause(clause.literals.clone());
        }

        // Prove
        let result = prover.prove(self.config.max_iterations);

        // Determine SZS status
        let (status, proof_trace) = match result {
            ProverResult::Unsatisfiable(trace) => {
                let status = if has_conjecture {
                    SzsStatus::Theorem
                } else {
                    SzsStatus::Unsatisfiable
                };
                (status, Some(trace))
            }
            ProverResult::Saturated => {
                let status = if has_conjecture {
                    SzsStatus::CounterSatisfiable
                } else {
                    SzsStatus::Satisfiable
                };
                (status, None)
            }
            ProverResult::ResourceLimit => (SzsStatus::ResourceOut, None),
        };

        // Format output
        let mut output = format_szs_status(status, &self.config.problem_name);
        output.push('\n');

        if let Some(trace) = proof_trace {
            output.push_str(&format_szs_proof_start(&self.config.problem_name));
            output.push('\n');
            output.push_str(&format_proof(&trace.clauses, &trace.empty_clause, &table));
            output.push_str(&format_szs_proof_end(&self.config.problem_name));
            output.push('\n');
        }

        Ok(AtpResult { status, output })
    }
}

/// Format a proof trace in TSTP-like format.
fn format_proof(clauses: &[Clause], empty_clause: &Clause, table: &SymbolTable) -> String {
    let mut out = String::new();

    for clause in clauses {
        out.push_str(&format_clause_step(clause, table));
        out.push('\n');
    }
    out.push_str(&format_clause_step(empty_clause, table));
    out.push('\n');

    out
}

fn format_clause_step(clause: &Clause, table: &SymbolTable) -> String {
    let inference_str = match &clause.inference {
        Inference::Input => "input".to_string(),
        Inference::Superposition(c1, c2, _pos) => format!("superposition({c1},{c2})"),
        Inference::EqualityResolution(c) => format!("equality_resolution({c})"),
        Inference::EqualityFactoring(c) => format!("equality_factoring({c})"),
        Inference::Demodulation(c1, c2) => format!("demodulation({c1},{c2})"),
        Inference::Subsumption(c) => format!("subsumption({c})"),
    };

    let clause_str = format_clause_literals(clause, table);
    format!("cnf({}, plain, {clause_str}, {inference_str}).", clause.id)
}

fn format_clause_literals(clause: &Clause, table: &SymbolTable) -> String {
    if clause.literals.is_empty() {
        return "$false".to_string();
    }

    let lits: Vec<String> = clause
        .literals
        .iter()
        .map(|l| format_literal(l, table))
        .collect();

    if lits.len() == 1 {
        lits[0].clone()
    } else {
        format!("({})", lits.join(" | "))
    }
}

fn format_literal(lit: &crate::superposition::Literal, table: &SymbolTable) -> String {
    let lhs = format_term(&lit.lhs, table);
    let rhs = format_term(&lit.rhs, table);

    // Check if this is a predicate encoding (P = $true or P != $true)
    if is_true_constant(&lit.rhs, table) {
        if lit.positive {
            return lhs; // P = $true -> P
        }
        return format!("~{lhs}"); // P != $true -> ~P
    }

    if lit.positive {
        format!("{lhs} = {rhs}")
    } else {
        format!("{lhs} != {rhs}")
    }
}

fn is_true_constant(term: &Term, table: &SymbolTable) -> bool {
    match term {
        Term::Const(sym) => table.symbol_name(*sym) == Some("$true"),
        _ => false,
    }
}

fn format_term(term: &Term, table: &SymbolTable) -> String {
    match term {
        Term::Var(v) => format!("X{v}"),
        Term::Const(sym) => table.symbol_name(*sym).unwrap_or("?").to_string(),
        Term::App(sym, args) => {
            let name = table.symbol_name(*sym).unwrap_or("?");
            let args_str: Vec<String> = args.iter().map(|a| format_term(a, table)).collect();
            format!("{name}({})", args_str.join(","))
        }
    }
}
