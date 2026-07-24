// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! SMT solver core combining SAT + theory solvers (DPLL(T))

mod phase_hints;
mod propagation;
mod solver;
mod theory;
mod types;

pub(crate) use solver::SmtSolver;
pub(crate) use theory::{
    LeveledTheoryState, TheoryCheckResult, TheoryLemmaRequest, TheoryLiteral, TheorySolver,
};
pub(crate) use types::{
    ProofTrailEntry, SmtInt, SmtModel, SmtResult, SmtStats, SmtTerm, TermId, UnsatCore,
};

#[cfg(test)]
mod tests;
#[cfg(test)]
mod tests_api_tail;
#[cfg(test)]
mod tests_array_integration;
#[cfg(test)]
mod tests_dpll_t;
#[cfg(test)]
mod tests_extensionality;
#[cfg(test)]
mod tests_fast_path_measurement;
#[cfg(test)]
mod tests_literal_semantics;
#[cfg(test)]
mod tests_nelson_oppen;
#[cfg(test)]
mod tests_nelson_oppen_disequality_forwarding;
#[cfg(test)]
mod tests_nelson_oppen_fixpoint;
#[cfg(test)]
mod tests_nelson_oppen_forwarding_unknown;
#[cfg(test)]
mod tests_nelson_oppen_isolation;
#[cfg(test)]
mod tests_nelson_oppen_propagation;
#[cfg(test)]
mod tests_nelson_oppen_unknown;
#[cfg(test)]
mod tests_phase_hints;
#[cfg(test)]
mod tests_proof_trail;
#[cfg(test)]
mod tests_proof_trail_determinism;
#[cfg(test)]
mod tests_reset_hooks;
#[cfg(test)]
mod tests_runtime_stats;
#[cfg(test)]
mod tests_theory_literal_lookup;
