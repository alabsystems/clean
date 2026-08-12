// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

// The automation crate keeps staged solver bridge APIs compiled before every
// downstream call path is wired; keep consumer builds quiet while narrower
// hygiene lints remain active.
//! clean Native Automation Engine
//!
//! Provides automatic theorem proving without external process calls:
//!
//! # Components (ported from other systems)
//!
//! ## From Z3
//! - CDCL SAT solver (`cdcl.rs`)
//! - E-graph congruence closure (`egraph.rs`)
//! - SMT solver with DPLL(T) (`smt.rs`)
//! - Theory solvers (`theories/`)
//!   - Equality with uninterpreted functions (EUF)
//!   - Linear rational arithmetic (LRA) via Simplex
//!   - Arrays with select/store (read-over-write axioms)
//!
//! ## SMT-Kernel Bridge (`bridge.rs`)
//! - Translation between kernel Expr and SMT solver terms / queries
//! - Typed bridge outcomes via `SmtVerificationResult`
//! - Public bridge/classifier coverage for propositional forms, comparisons,
//!   arithmetic heads, and quantified forms
//!
//! # Import Styles
//!
//! The primary bridge entry point is re-exported at the crate root:
//!
//! ```text
//! use clean_auto::SmtBridge;
//! ```
//!
//! Module-path imports remain available when you want a grouped namespace:
//!
//! ```text
//! use clean_auto::bridge::SmtBridge;
//! use clean_auto::oracle::OracleRequest;
//! use clean_auto::premise::PremiseDatabase;
//! ```
//!
//! # API Boundary
//!
//! External callers go through [`SmtBridge`]. Native SMT control-plane types and
//! trail-inspection helpers remain crate-private so the DPLL(T) internals can
//! evolve without becoming a cross-crate contract.
//!
//! ```compile_fail
//! use clean_auto::{ProofTrailEntry, SmtInt, SmtModel, SmtStats, SmtTerm, TermId};
//! ```
//!
//! ```compile_fail
//! use clean_auto::{
//!     TheoryCheckResult, TheoryLemmaRequest, TheoryLiteral, TheorySolver, UnsatCore,
//! };
//! ```
//!
//! ```compile_fail
//! use clean_auto::SmtBridge;
//!
//! fn external_stats<'env>(bridge: &SmtBridge<'env>) {
//!     let _ = bridge.stats();
//! }
//! ```
//!
//! ```compile_fail
//! use clean_auto::SmtBridge;
//!
//! fn external_trail<'env>(bridge: &SmtBridge<'env>) {
//!     let _ = bridge.proof_trail();
//! }
//! ```
//!
//! ## From E Prover
//! - Superposition calculus (`superposition.rs`)
//! - Term orderings (KBO, LPO)
//!
//! ## From Isabelle
//! - Premise selection (`premise.rs`)
//!   - MePo (Meng-Paulson): symbol-based relevance filtering
//!   - MaSh: k-NN and Naive Bayes feature-based learning
//!   - Hybrid selector combining both approaches
//! - Proof reconstruction
//!
//! # GPU Acceleration
//!
//! Clause processing can be offloaded to GPU for large problems.
//!
//! # Example: Using the Native SMT Solver (crate-internal)
//!
//! The native `SmtSolver` is a crate-internal type used by `SmtBridge`.
//! External consumers should use `SmtBridge` directly (#2386).
//!
//! ```text
//! use crate::smt::{SmtResult, SmtSolver};
//! use crate::theories::equality::EqualityTheory;
//!
//! let mut smt = SmtSolver::new();
//! let a = smt.const_term("a");
//! let b = smt.const_term("b");
//! smt.add_theory(Box::new(EqualityTheory::new()));
//! let _ = smt.assert_eq(a, b);
//! match smt.solve() {
//!     SmtResult::Sat(_) => { /* satisfiable */ }
//!     SmtResult::Unsat(_) => { /* unsatisfiable */ }
//!     SmtResult::Unknown => { /* unknown */ }
//! }
//! ```
//!
//! # Example: Using the detailed automation API
//!
//! New call sites should use [`AutomationQuery`] for forward-compatible access
//! to future automation options:
//!
//! ```text
//! use clean_auto::{AutomationEngine, AutomationOutcome, AutomationQuery};
//!
//! let engine = AutomationEngine::new();
//! let query = AutomationQuery::new(&goal, timeout)
//!     .with_hypotheses(&hypotheses)
//!     .with_local_ctx(&local_ctx);
//! match engine.auto_prove_with_query(&env, query) {
//!     AutomationOutcome::Verified(proof) => {
//!         let _proof_text = proof.proof_text();
//!     }
//!     AutomationOutcome::Unverified { source, reason, .. } => {
//!         // SMT found an UNSAT core but proof reconstruction hit a trust boundary.
//!     }
//!     AutomationOutcome::Refuted { source, .. } => {
//!         // The solver found a counterexample / refutation.
//!     }
//!     AutomationOutcome::Unknown { source, reason, .. } => {
//!         // The strategy timed out or could not decide.
//!     }
//! }
//! ```
//!
//! [`AutomationRequest`] and `auto_prove_with_request` remain available as
//! compatibility wrappers. `AutomationEngine::auto_prove()` collapses
//! non-proof outcomes to `None` for callers that only care about verified proofs.
//!
//! # Example: Using the SMT-Kernel Bridge
//!
//! The bridge connects SMT solving to Lean kernel expressions:
//!
//! ```text
//! use clean_auto::{SmtBridge, SmtVerificationResult};
//! use clean_kernel::{Environment, Expr};
//!
//! let env = Environment::new();
//! let mut bridge = SmtBridge::new(&env);
//!
//! // Add hypothesis: a = b (as a kernel Expr)
//! bridge.add_hypothesis(&hyp_expr);
//!
//! // Try to prove: b = a (symmetry)
//! if let Ok(result) = bridge.prove(&goal_expr) {
//!     match result {
//!         SmtVerificationResult::Verified(proof) => {
//!             let _description = proof.proof_sketch();
//!         }
//!         SmtVerificationResult::Unverified { .. }
//!         | SmtVerificationResult::Refuted(_)
//!         | SmtVerificationResult::Unknown(_) => {}
//!     }
//! }
//! ```
//!
//! **Note:** `SmtBridge` is single-shot — each instance supports at most one
//! `prove()` call. A second call returns `BridgeError::BridgeReuse`. Create a
//! new bridge for each goal (#2836).
//!
//! See [`bridge::SmtBridge`] for the full API.

pub mod arith_proof;
pub mod atp;
pub mod batch;
mod batch_search;
pub mod bridge;
pub(crate) mod cdcl;
/// CLI surface for `clean auto prove` (Epic #3436 Phase 4, #3454).
///
/// Feature-gated so non-CLI consumers keep a minimal dep graph — clap and
/// `clean-features` are pulled in only when `--features cli` is enabled.
#[cfg(feature = "cli")]
pub mod cli;
#[expect(
    dead_code,
    reason = "issue #2341 narrows the public boundary without renaming unused internal egraph helpers"
)]
pub(crate) mod egraph;
mod engine;
mod engine_api;
mod engine_batch;
mod engine_detailed;
mod engine_induction;
mod engine_induction_assembly;
mod engine_induction_aux;
mod engine_induction_match;
mod engine_induction_rewrite;
pub mod engine_router;
pub mod interval;
pub mod norms;
pub mod oracle;
pub mod premise;
pub(crate) mod proof;
#[cfg(test)]
#[cfg(test)]
mod test_env;
// One wire contract for every bincode-2 kernel proof carrier.  This stays
// outside the ay feature gate so the solver cache cannot grow a second codec.
mod proof_codec;
mod proof_result;
/// Public **[PROVED]-grade** kernel re-check entry point for the Trust M-POS
/// output gate. Gated behind `ay-bv-blast` (it routes an `ay`-exported
/// `BvBlastProof` through the clean CIC kernel via the `bv_blast_reflection`
/// lane). See [`proved_gate::kernel_recheck_proved_grade`].
#[cfg(feature = "ay-bv-blast")]
pub mod proved_gate;
pub(crate) mod smt;
pub mod smtlib_builder;
/// Solver-results cache — Phase 0: obligation key + per-attempt telemetry.
///
/// Pure instrumentation (no hit-serving): a content-addressed obligation key
/// plus a `solver-attempt-record-v1` telemetry sink keyed by
/// `CLEAN_SOLVER_TELEMETRY_DIR`. See
/// `designs/2026-06-24-solver-results-cache-service.md`.
pub(crate) mod solver_cache;
/// Phase-1 solver-cache tooling surface (`VCIDX01` index, telemetry analysis,
/// NN dataset export) driven by the `clean solver` CLI. See
/// [`solver_cache::service`] and
/// `designs/2026-06-24-solver-results-cache-service.md` §5–§7.
pub use solver_cache::service as solver_cache_service;
#[expect(
    dead_code,
    reason = "issue #2341 narrows the public boundary without renaming standard superposition internals"
)]
#[allow(clippy::upper_case_acronyms)]
pub(crate) mod superposition;
#[expect(
    dead_code,
    reason = "#2386 narrows theories to pub(crate); internal types awaiting consolidation"
)]
pub(crate) mod theories;

// Ay SMT solver backend lives under bridge/ay_backend/; the supported
// public cross-crate surface is bridge/ay_contract.

pub use atp::{AtpConfig, AtpResult, AtpRunner, SzsStatus};
pub use batch_search::{
    batch_prove, BatchGoal, BatchGoalResult, BatchGoalStatus, BatchQuery, BatchResult,
    BatchSearchLoop, SearchStrategy,
};
pub use bridge::{SmtBridge, SmtProofResult, SmtVerificationResult};
#[cfg(feature = "fuzz")]
pub use cdcl::{CdclSolver, Lit, SolveResult, Var};
pub use engine::AutomationEngine;
pub use engine_api::{AutomationOutcome, AutomationQuery, AutomationRequest, AutomationSource};
pub use engine_batch::{BatchProveResult, BatchProveStats};
pub use engine_router::{classify_goal, engine_plan, route_goal, GoalClass, RoutedEngine};
pub use proof_result::ProofResult;
pub use smtlib_builder::{
    parse_smtlib2_result, ParseSmtLib2ResultError, SmtLibBuilder, SmtLibCheckSatResult,
    SmtLibCommand, SmtLibConst, SmtLibExpr, SmtLibSort,
};

/// Domain-prefixed alias for [`ProofResult`] to avoid name collisions when
/// importing multiple crates that define their own `ProofResult` types
/// (e.g., `clean_elab::tactic::drat::DratProofResult`).
pub type AutoProofResult = ProofResult;

/// Common imports for automation users.
///
/// # Example
///
/// ```text
/// use clean_auto::prelude::*;
///
/// let engine = AutomationEngine::new();
/// let query = AutomationQuery::new(&goal, timeout)
///     .with_hypotheses(&hypotheses);
/// match engine.auto_prove_with_query(&env, query) {
///     AutomationOutcome::Verified(proof) => { /* ... */ }
///     AutomationOutcome::Unverified { .. }
///     | AutomationOutcome::Refuted { .. }
///     | AutomationOutcome::Unknown { .. } => {}
/// }
/// ```
pub mod prelude {
    pub use crate::bridge::{PremiseOrigin, QuantifierOrigin, SmtBridge};
    pub use crate::oracle::{
        sort_oracle_candidates, sort_proof_term_candidates, OracleCandidate, OracleCandidateRunner,
        OracleConfig, OracleRequest, OracleRunError, ProofOracle, ProofTermCandidate,
    };
    #[cfg(feature = "oracle-http")]
    pub use crate::oracle::{ClaudeOracle, GeminiOracle, HttpOracle, OpenAiOracle};
    pub use crate::premise::{HybridSelector, MePoSelector, PremiseDatabase, PremiseId};
    // SmtSolver and SmtResult are crate-internal since #2386.
    // External consumers use SmtBridge directly.
    pub use crate::{
        batch_prove, AtpConfig, AtpResult, AtpRunner, AutoProofResult, AutomationEngine,
        AutomationOutcome, AutomationQuery, AutomationRequest, AutomationSource, BatchGoal,
        BatchGoalResult, BatchGoalStatus, BatchProveResult, BatchProveStats, BatchQuery,
        BatchResult, BatchSearchLoop, ProofResult, SearchStrategy, SzsStatus,
    };
}

#[cfg(test)]
mod tests;

#[cfg(test)]
#[test]
fn test_add_hypothesis_deep_and_chain_stack_safe() {
    bridge::tests::tests_hypothesis_stack_safety::run_test_add_hypothesis_deep_and_chain_stack_safe(
    );
}

#[cfg(test)]
#[test]
fn test_collect_equality_hypothesis_edges_deep_and_chain_stack_safe() {
    bridge::tests::tests_hypothesis_stack_safety::run_test_collect_equality_hypothesis_edges_deep_and_chain_stack_safe();
}

#[cfg(test)]
#[test]
fn test_collect_arithmetic_hypothesis_edges_deep_and_chain_stack_safe() {
    bridge::tests::tests_hypothesis_stack_safety::run_test_collect_arithmetic_hypothesis_edges_deep_and_chain_stack_safe();
}
