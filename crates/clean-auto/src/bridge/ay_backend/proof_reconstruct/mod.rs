// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Ay proof reconstruction: raw `ay_core::Proof` → kernel `Expr` proof terms.
//!
//! Translates Ay UNSAT proof objects into kernel-checkable proof terms,
//! enabling certified SMT tactics that don't rely on `trustedAy`.
//!
//! # Architecture
//!
//! Works with raw `ay_core::Proof` (not Alethe strings) to preserve structure:
//! - `ProofStep::Assume` → hypothesis lookup from tactic context
//! - `ProofStep::Resolution` → propositional resolution (Phase 3)
//! - `ProofStep::TheoryLemma` → theory-specific proof construction (Phase 2)
//! - `ProofStep::Step` → Alethe-rule-specific construction (Phase 3)
//!
//! # Status
//!
//! Phase 1 (DONE): Infrastructure + term back-translation + fallback.
//! Phase 2 (DONE): EUF theory lemma reconstruction (trans/congr/pred) + LRA Farkas.
//! Phase 3 (IN PROGRESS): Resolution (done), ay-emitted Alethe-step handling
//!   for ThResolution/Or/Trust plus forward-looking OrPos coverage, and
//!   theory lemma handling for 4 kernel-reconstructed kinds (EUF
//!   trans/congr/pred, LRA Farkas) plus trust-carried BvBitBlast /
//!   ArrayAxiom / Generic clauses. Hole remains an error fallback.

// BV bit-blast proof-reconstruction lane — gated behind `ay-bv-blast` (off by
// default). These modules import `ay_proof::bv_blast_export`, which upstream
// `ay` has removed. Preserved (not deleted) so they are recoverable once `ay`
// re-adds the export API. See crates/clean-auto/Cargo.toml.
#[cfg(feature = "ay-bv-blast")]
pub mod bv_blast_reflection;
#[cfg(feature = "ay-bv-blast")]
pub mod bv_lowering_bridge;
pub mod certified_proof;
// Proof-carrying ay, MILESTONE 2: NATIVE kernel certification of a BV
// MULTIPLICATION UNSAT obligation (array-multiplier bit-blast → reflection →
// `Unsat` → exact rooted certification authority). Gated with the BV bit-blast lane.
pub mod clean_cic;
mod context;
#[cfg(feature = "ay-bv-blast")]
pub mod pcay_bvmul;
// Proof-carrying ay, MILESTONE 3: NATIVE kernel certification of a BV SHIFT
// UNSAT obligation (barrel-shifter bit-blast → OP-AGNOSTIC reflection → `Unsat`
// → exact rooted certification authority). Reuses milestone-2's reflection family
// (the sub-quadratic `certify_unsat3_by_reflection`).
#[cfg(feature = "ay-bv-blast")]
pub mod pcay_bvshift;
// Shared fail-closed certifying-verification bridge skeleton (design doc §4).
// NOT feature-gated: it depends only on the always-present `clean_kernel`
// substrate (`Environment::axiom_deps`), so it builds in the default + `ay-smt`
// builds, unlike the `ay-bv-blast`-gated BV lowering bridge.
pub(super) mod em_combinator;
pub(crate) mod expr_builders;
pub(crate) mod expr_builders_arith;
mod expr_builders_real_downcast;
mod farkas_certificate;
mod generic_step;
mod real_downcast_normalize;
mod resolution;
mod resolution_build;
mod resolution_plan;
mod term_translate;
mod theory_lemma;
pub mod unified_cert;
// BV bit-blast lane (gated — see above and Cargo.toml `ay-bv-blast`).
#[cfg(feature = "ay-bv-blast")]
pub mod theory_lemma_bv;
#[cfg(feature = "ay-bv-blast")]
pub mod theory_lemma_bv_compute_blast;
mod theory_lemma_congr;
mod theory_lemma_euf;
mod theory_lemma_lra;
mod theory_lemma_lra_additive;
mod theory_lemma_lra_additive_close;
mod theory_lemma_lra_chain;
mod theory_lemma_lra_chain_close;
mod theory_lemma_lra_chain_expr;
mod theory_lemma_lra_single;
mod theory_lemma_lra_sum_nf;
mod theory_lemma_lra_weighted;
mod theory_lemma_pred;
pub(crate) mod trace;
mod trace_convert;
mod trace_rooting;
mod tseitin;
mod tseitin_equiv;
mod tseitin_xor;
mod types;

#[cfg(test)]
mod tests;
#[cfg(test)]
mod tests_boundary;
#[cfg(test)]
mod tests_contract_gate_support;
#[cfg(test)]
mod tests_e2e;
#[cfg(test)]
mod tests_e2e_arith;
#[cfg(test)]
mod tests_e2e_lra;
#[cfg(test)]
mod tests_e2e_lra_real;
#[cfg(test)]
mod tests_e2e_lra_weighted;
#[cfg(test)]
mod tests_e2e_lra_weighted_constructor;
#[cfg(test)]
mod tests_em_combinator;
#[cfg(test)]
mod tests_farkas_certificate;
#[cfg(test)]
mod tests_or_pos;
#[cfg(test)]
mod tests_replacement_gate;
#[cfg(test)]
mod tests_resolution;
#[cfg(test)]
mod tests_sentinel;
#[cfg(test)]
mod tests_sum_nf_failclose;
#[cfg(test)]
mod tests_support;
#[cfg(test)]
mod tests_th_resolution;
#[cfg(test)]
mod tests_theory_lemma;
#[cfg(test)]
mod tests_trace;
#[cfg(test)]
mod tests_trace_rooting;
#[cfg(test)]
mod tests_trust;
#[cfg(test)]
mod tests_tseitin;
#[cfg(test)]
mod tests_tseitin_equiv;
#[cfg(test)]
mod tests_tseitin_xor;

use ay_core::{Proof, TermStore};
use clean_kernel::Expr;

pub(crate) use context::ReconstructionContext;
pub use types::VariableMapping;
pub(crate) use types::{
    ReconstructResult, ReconstructionError, ReconstructionResult, ReconstructionStats,
};

/// Minimum stack space to reserve before recursive proof-reconstruction calls.
const MIN_STACK_RED_ZONE: usize = 32 * 1024;

/// Stack size to grow to when ay term recursion runs low on stack.
const STACK_GROWTH_SIZE: usize = 1024 * 1024;

/// Stack-safe wrapper for deep ay term recursion.
#[inline(always)]
fn stack_safe<R>(f: impl FnOnce() -> R) -> R {
    #[cfg(kani)]
    {
        f()
    }
    #[cfg(not(kani))]
    {
        stacker::maybe_grow(MIN_STACK_RED_ZONE, STACK_GROWTH_SIZE, f)
    }
}

/// Attempt to reconstruct a kernel proof term from a ay proof.
///
/// Main entry point called from `AyProofBackend` after UNSAT with proof.
pub(crate) fn attempt_reconstruction(
    proof: &Proof,
    terms: &TermStore,
    var_map: &VariableMapping,
    negated_goal: &Expr,
) -> ReconstructionResult {
    let mut ctx = ReconstructionContext::with_proof(proof, terms, var_map);
    if ctx.trace().step_count() == 0 {
        let mut stats = ReconstructionStats::default();
        stats.record_proof_error(ReconstructionError::EmptyProof);
        return ReconstructionResult {
            proof_term: None,
            negated_goal_fvar: None,
            compound_witness_fvars: Vec::new(),
            derives_empty_clause: false,
            trust_subterm_count: 0,
            residual:
                crate::bridge::ay_backend::reconstruction_quality::ResidualTrustSummary::empty(),
            stats,
        };
    }
    ctx.reconstruct(proof, negated_goal)
}
