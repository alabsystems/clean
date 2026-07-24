// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Type definitions for verification handlers.

use serde::{Deserialize, Serialize};

pub use super::fill_sorries_types::{
    ExtractedTheorem, FillSorriesParams, FillSorriesResult, SorryGoal, SorryGoalInfo,
    SorryHypothesis, SorryLocation,
};

// ============================================================================
// Verify-C Types
// ============================================================================

/// Verify C code request parameters
#[derive(Debug, Clone, Deserialize)]
pub struct VerifyCParams {
    /// C source code with ACSL specifications
    pub code: String,
    /// Treat unknown obligations as failures
    #[serde(default)]
    pub fail_unknown: bool,
    /// Include per-VC details in response
    #[serde(default)]
    pub include_details: bool,
    /// Optional timeout in milliseconds
    pub timeout_ms: Option<u64>,
}

/// Result for a single function verification
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct VerifyCFunctionResult {
    /// Function name
    pub name: String,
    /// Total verification conditions
    pub total_vcs: usize,
    /// Number of VCs proved
    pub proved: usize,
    /// Number of VCs failed
    pub failed: usize,
    /// Number of VCs with unknown status
    pub unknown: usize,
    /// Per-VC details (if requested)
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub details: Vec<VerifyCVCDetail>,
}

/// Detail for a single verification condition
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct VerifyCVCDetail {
    /// Description of the VC
    pub description: String,
    /// Status: "proved", "failed", "unknown"
    pub status: String,
    /// Reason for failure (if failed)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub reason: Option<String>,
}

/// Verify C code response
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct VerifyCResult {
    /// Whether verification succeeded (all VCs proved)
    pub success: bool,
    /// Number of functions verified
    pub num_functions: usize,
    /// Total verification conditions
    pub total_vcs: usize,
    /// Total proved VCs (kernel-verified or structurally established)
    pub proved: usize,
    /// Total VCs that were UNSAT to the SMT solver but lack a reconstructed
    /// kernel proof term (sound "valid, but no proof term"). Accepted by the
    /// default success predicate; rejected when `fail_unknown` is set.
    #[serde(default)]
    pub unverified: usize,
    /// Total failed (refuted) VCs
    pub failed: usize,
    /// Total unknown VCs (verification gaps / unsupported constructs)
    pub unknown: usize,
    /// Per-function results
    pub functions: Vec<VerifyCFunctionResult>,
    /// Parse errors (if any)
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub errors: Vec<String>,
    /// Time taken in milliseconds
    pub time_ms: u64,
    /// Time taken in nanoseconds (normalized alias, Part of #2515)
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub time_ns: Option<u64>,
}

// ============================================================================
// LLM Integration API Types
// ============================================================================

/// Verify complete proof request parameters
///
/// This endpoint verifies a complete proof in one call, suitable for
/// verification-guided LLM search where proofs are generated externally.
#[derive(Debug, Clone, Deserialize)]
pub struct VerifyProofParams {
    /// Goal to prove (Lean expression syntax for the type)
    pub goal: String,
    /// Proof to verify (tactic script with semicolons or newlines)
    pub proof: String,
    /// Optional context (imports, opens)
    #[serde(default)]
    pub context: Option<VerifyProofContext>,
    /// Optional timeout in milliseconds
    pub timeout_ms: Option<u64>,
}

/// Optional context for proof verification
#[derive(Debug, Clone, Default, Deserialize)]
pub struct VerifyProofContext {
    /// Imports to load (e.g., ["Mathlib.Data.Nat.Basic"])
    #[serde(default)]
    pub imports: Vec<String>,
    /// Namespaces to open (e.g., ["Nat"])
    #[serde(default)]
    pub opens: Vec<String>,
    /// Additional variable declarations
    #[serde(default)]
    pub variables: Vec<String>,
}

/// Timing breakdown for verification stages
///
/// Reports time spent in each stage of proof verification:
/// - Parse: converting goal string to AST
/// - Elaborate: type checking and inference
/// - Verify: executing tactics and checking proof
///
/// Used for delta measurement per 4/delta bound theorem (arXiv:2512.02080).
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TimingBreakdown {
    /// Time spent parsing goal and proof (nanoseconds)
    pub parse_ns: u64,
    /// Time spent elaborating expressions (nanoseconds)
    pub elaborate_ns: u64,
    /// Time spent in verification/type-checking (nanoseconds)
    pub verify_ns: u64,
    /// Total time (sum of above, nanoseconds)
    pub total_ns: u64,
}

/// Trust summary for axiom usage tracking (#2160 T3, #2198).
///
/// Reports how many times each trusted axiom was used during proof verification.
/// AI agents use this to distinguish fully kernel-verified proofs from those
/// relying on external solvers (trustedAy, trustedArith) or incomplete proofs (sorry).
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct TrustedAyProvenance {
    /// trustedAy sub-terms caused by arithmetic-boundary residual debt.
    pub arithmetic_boundary_steps: u64,
    /// trustedAy sub-terms caused by Alethe `trust` steps.
    pub alethe_trust_steps: u64,
    /// trustedAy sub-terms caused by bitblast theory-lemma residues.
    pub theory_bv_bitblast_steps: u64,
    /// trustedAy sub-terms caused by array-axiom theory-lemma residues.
    pub theory_array_axiom_steps: u64,
    /// trustedAy sub-terms caused by generic theory-lemma residues.
    pub theory_generic_steps: u64,
    /// trustedAy sub-terms caused by local reconstruction gaps.
    pub local_gap_steps: u64,
    /// trustedAy sub-terms whose exact residual source is unavailable.
    pub unclassified_steps: u64,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct SorryProvenance {
    /// Whether the closed proof term contains an explicit/non-synthetic sorry.
    pub has_explicit_sorry: bool,
    /// Whether the closed proof term contains a synthetic sorry.
    pub has_synthetic_sorry: bool,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct TrustedArithProvenance {
    /// `trustedArith` steps recorded directly at a runtime callsite.
    pub direct_steps: u64,
    /// `trustedArith` steps recorded through `close_with_trusted_arith(...)`.
    pub goal_close_helper_steps: u64,
    /// `trustedArith` steps recorded through target-rewrite helper fallbacks.
    pub target_rewrite_helper_steps: u64,
    /// `trustedArith` steps whose exact source class is unavailable.
    pub unclassified_steps: u64,
}

/// Request-local summary of SMT proof candidates that failed kernel validation
/// before a recovery lane produced a clean proof (#2920).
///
/// This is **not** accepted trust debt — it records how many invalid candidates
/// the selector rejected during a single tactic request. A response may show
/// `fully_verified = true` alongside a non-empty `smt_recovery`.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct SmtRecoverySummary {
    /// Direct ay proof candidates that failed kernel validation before selection.
    pub invalid_direct_ay_candidates: u64,
    /// Direct certificate proof candidates that failed kernel validation before selection.
    pub invalid_direct_certificate_candidates: u64,
    /// Bridge-produced proof candidates that failed kernel validation.
    pub invalid_bridge_candidates: u64,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TrustSummary {
    /// Number of sorry axioms used (incomplete proofs)
    pub sorry_count: u64,
    /// Optional typed provenance for sorry debt derived from the closed proof term.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub sorry_provenance: Option<SorryProvenance>,
    /// Number of trustedAy axioms used (SMT-verified, not kernel-checked)
    pub ay_count: u64,
    /// Optional typed provenance for trustedAy debt.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub ay_provenance: Option<TrustedAyProvenance>,
    /// Number of trustedArith axioms used (decision procedure, not kernel-checked)
    pub arith_count: u64,
    /// Optional typed provenance for trustedArith debt.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub arith_provenance: Option<TrustedArithProvenance>,
    /// Declarations that failed kernel type-check (#2198).
    /// Kernel type checking is always on and fail-closed, so this is nonzero
    /// whenever a declaration was rejected by the kernel type check (rejected
    /// declarations are never structurally registered).
    #[serde(default)]
    pub kernel_check_failures: u64,
    /// True only when all counters are 0 AND kernel type-check passes
    pub fully_verified: bool,
    /// Request-local SMT recovery summary. Present when at least one invalid
    /// proof candidate was rejected before a recovery lane closed the goal.
    /// Does not participate in `fully_verified` (#2920).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub smt_recovery: Option<SmtRecoverySummary>,
}

/// Verify complete proof response
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct VerifyProofResult {
    /// Whether the proof was verified successfully
    pub verified: bool,
    /// Proof certificate (if verified and requested)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub certificate: Option<String>,
    /// Time taken in nanoseconds
    pub time_ns: u64,
    /// Timing breakdown per verification stage (parse/elaborate/verify)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub timing: Option<TimingBreakdown>,
    /// Error information (if not verified)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub error: Option<VerifyProofError>,
    /// Axiom usage summary (sorry, trustedAy, trustedArith counts)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub trust_summary: Option<TrustSummary>,
}

/// Error details for failed proof verification
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct VerifyProofError {
    /// Error message
    pub message: String,
    /// Position in proof where error occurred
    #[serde(skip_serializing_if = "Option::is_none")]
    pub position: Option<VerifyProofPosition>,
    /// Expected type at error location
    #[serde(skip_serializing_if = "Option::is_none")]
    pub expected_type: Option<String>,
    /// Remaining goals at failure point
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub actual_goals: Vec<String>,
    /// Suggested fixes
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub suggestions: Vec<String>,
}

/// Position in proof
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct VerifyProofPosition {
    /// Line number (1-indexed)
    pub line: usize,
    /// Column number (1-indexed)
    pub col: usize,
}

// =============================================================================
// Batch Proof Verification Types
// =============================================================================

/// Batch verify proof request parameters
///
/// Enables verification of multiple proofs in parallel using rayon.
/// Critical for FATE-Eval benchmark throughput (28s -> 28ms for 28K proofs).
#[derive(Debug, Clone, Deserialize)]
pub struct VerifyProofBatchParams {
    /// List of proofs to verify
    pub proofs: Vec<VerifyProofBatchItem>,
    /// Number of threads to use (default: all CPUs)
    pub threads: Option<usize>,
    /// Global timeout in milliseconds
    pub timeout_ms: Option<u64>,
}

/// Single item in batch verification
#[derive(Debug, Clone, Deserialize)]
pub struct VerifyProofBatchItem {
    /// Client-assigned identifier (echoed in response)
    pub id: String,
    /// Goal to prove
    pub goal: String,
    /// Proof to verify
    pub proof: String,
    /// Optional context
    #[serde(default)]
    pub context: Option<VerifyProofContext>,
}

/// Batch verification response
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct VerifyProofBatchResult {
    /// Results for each proof (same order as input)
    pub results: Vec<VerifyProofBatchItemResult>,
    /// Total wall-clock time in nanoseconds
    pub total_time_ns: u64,
    /// Throughput in operations per second
    pub throughput_ops_sec: f64,
    /// Aggregate statistics
    pub stats: VerifyProofBatchStats,
}

/// Per-item result in batch verification
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct VerifyProofBatchItemResult {
    /// Client-assigned identifier (echoed from input)
    pub id: String,
    /// Whether proof verified successfully
    pub verified: bool,
    /// Per-item time in nanoseconds
    pub time_ns: u64,
    /// Timing breakdown (if available)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub timing: Option<TimingBreakdown>,
    /// Error details (if !verified)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub error: Option<VerifyProofError>,
    /// Axiom usage summary
    #[serde(skip_serializing_if = "Option::is_none")]
    pub trust_summary: Option<TrustSummary>,
}

/// Aggregate statistics for batch verification
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct VerifyProofBatchStats {
    /// Number of proofs verified successfully
    pub verified_count: usize,
    /// Number of proofs that failed
    pub failed_count: usize,
    /// Average verification time in nanoseconds
    pub avg_time_ns: u64,
    /// Min verification time in nanoseconds
    pub min_time_ns: u64,
    /// Max verification time in nanoseconds
    pub max_time_ns: u64,
}

// =============================================================================
// Full File Verification Types
// =============================================================================

/// Verify a complete Lean file (FATE benchmark format)
///
/// Accepts entire Lean files with imports, opens, and theorem declarations.
/// Extracts theorem + sorry, verifies proof fills the sorry.
///
/// This enables FATE benchmark evaluation without full Mathlib support:
/// - Parses file to extract theorem declaration
/// - Identifies sorry locations
/// - Verifies replacement proof if provided
#[derive(Debug, Clone, Deserialize)]
pub struct VerifyFileParams {
    /// Complete Lean file content
    pub content: String,
    /// Optional replacement proof for the sorry (tactic script)
    #[serde(default)]
    pub proof: Option<String>,
    /// Optional timeout in milliseconds
    pub timeout_ms: Option<u64>,
}

/// Result of file verification
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct VerifyFileResult {
    /// Whether the file/proof was verified successfully
    pub verified: bool,
    /// Extracted theorem information
    #[serde(skip_serializing_if = "Option::is_none")]
    pub theorem: Option<ExtractedTheorem>,
    /// List of sorries found in the file
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub sorries: Vec<SorryLocation>,
    /// Total time in nanoseconds
    pub time_ns: u64,
    /// Timing breakdown
    #[serde(skip_serializing_if = "Option::is_none")]
    pub timing: Option<TimingBreakdown>,
    /// Error if verification failed
    #[serde(skip_serializing_if = "Option::is_none")]
    pub error: Option<VerifyProofError>,
    /// Axiom usage summary
    #[serde(skip_serializing_if = "Option::is_none")]
    pub trust_summary: Option<TrustSummary>,
}
