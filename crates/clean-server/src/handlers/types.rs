// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Shared request/response types for handler endpoints.

use serde::{Deserialize, Serialize};

// ============================================================================
// Timing conversion helpers (Part of #2515)
// ============================================================================

/// Convert milliseconds to nanoseconds (saturating).
pub(crate) const fn ns_from_ms(ms: u64) -> u64 {
    ms.saturating_mul(1_000_000)
}

/// Convert microseconds to nanoseconds (saturating).
pub(crate) const fn ns_from_us(us: u64) -> u64 {
    us.saturating_mul(1_000)
}

// ============================================================================
// Core Request/Response Types
// ============================================================================

/// Check code request parameters
#[derive(Debug, Clone, Deserialize)]
pub struct CheckParams {
    /// Lean code to check
    pub code: String,
    /// Optional timeout in milliseconds
    pub timeout_ms: Option<u64>,
}

/// Check code response
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CheckResult {
    /// Whether the code is valid
    pub valid: bool,
    /// Inferred type (if expression)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub inferred_type: Option<String>,
    /// Errors (if any)
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub errors: Vec<CheckError>,
    /// Time taken in milliseconds
    pub time_ms: u64,
    /// Time taken in nanoseconds (normalized alias, Part of #2515)
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub time_ns: Option<u64>,
}

/// Error from checking
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CheckError {
    /// Error message
    pub message: String,
    /// Line number (1-indexed, if available)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub line: Option<usize>,
    /// Column number (1-indexed, if available)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub column: Option<usize>,
}

/// Prove request parameters
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProveParams {
    /// Goal to prove (Lean expression syntax)
    pub goal: String,
    /// Hypotheses to use (Lean expression syntax)
    #[serde(default)]
    pub hypotheses: Vec<String>,
    /// Optional timeout in milliseconds
    pub timeout_ms: Option<u64>,
    /// Strategy selection: "auto" (default, tries all), "smt", "superposition".
    ///
    /// "auto" chains SMT -> superposition -> oracle. Other values restrict
    /// the engine to a single strategy.
    #[serde(default)]
    pub strategy: Option<String>,
}

/// Machine-readable proof certainty for the `prove` endpoint.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default, Serialize, Deserialize)]
#[non_exhaustive]
#[serde(rename_all = "snake_case")]
pub enum ProveStatus {
    /// A kernel-checkable proof term was produced.
    Verified,
    /// SMT proved UNSAT, but no kernel proof term is available.
    Unverified,
    /// A proof term was produced but the kernel re-check (`check_type`)
    /// REJECTED it against the goal. This is NOT a valid proof; `status` must
    /// never be `Verified` when the re-check failed. The rejected term and a
    /// non-`fully_verified` `trust_summary` are surfaced for inspection.
    KernelRejected,
    /// SMT found a counterexample to the goal.
    Refuted,
    /// The solver could not determine the result.
    #[default]
    Unknown,
}

/// Prove response
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProveResult {
    /// Whether a proof was found
    pub found: bool,
    /// Proof term (Lean syntax)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub proof_term: Option<String>,
    /// Human-readable proof sketch
    #[serde(skip_serializing_if = "Option::is_none")]
    pub proof_sketch: Option<String>,
    /// Method used (smt, superposition, etc.)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub method: Option<String>,
    /// Authoritative proof-certainty status for the result.
    ///
    /// `found` is kept for backwards compatibility; use `status` to
    /// distinguish verified, unverified, refuted, and unknown outcomes.
    #[serde(default)]
    pub status: ProveStatus,
    /// Optional non-proof diagnostic for unverified or unknown solver outcomes.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub reason: Option<String>,
    /// Aggregate trust debt for verified proof terms.
    ///
    /// Present only when `status = verified`, because only that path carries a
    /// closed proof term the server can summarize.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub trust_summary: Option<crate::handlers::TrustSummary>,
    /// Time taken in milliseconds
    pub time_ms: u64,
    /// Time taken in nanoseconds (normalized alias, Part of #2515)
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub time_ns: Option<u64>,
}

/// Get type request parameters
#[derive(Debug, Clone, Deserialize)]
pub struct GetTypeParams {
    /// Expression to get type of
    pub expr: String,
}

/// Get type response
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct GetTypeResult {
    /// The type (Lean syntax)
    #[serde(rename = "type")]
    pub type_: String,
    /// Time taken in milliseconds
    pub time_ms: u64,
    /// Time taken in nanoseconds (normalized alias, Part of #2515)
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub time_ns: Option<u64>,
}

/// Batch check request parameters
#[derive(Debug, Clone, Deserialize)]
pub struct BatchCheckParams {
    /// List of code snippets to check
    pub items: Vec<BatchCheckItem>,
    /// Whether to use GPU acceleration
    #[serde(default)]
    pub use_gpu: bool,
    /// Optional timeout for entire batch in milliseconds
    pub timeout_ms: Option<u64>,
}

/// Single item in batch check
#[derive(Debug, Clone, Deserialize)]
pub struct BatchCheckItem {
    /// Unique identifier for this item
    pub id: String,
    /// Code to check
    pub code: String,
}

/// Batch check response
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BatchCheckResult {
    /// Results for each item (in same order)
    pub results: Vec<BatchCheckItemResult>,
    /// Total time in milliseconds
    pub time_ms: u64,
    /// Total time in nanoseconds (normalized alias, Part of #2515)
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub time_ns: Option<u64>,
    /// Whether GPU was used
    pub gpu_used: bool,
    /// Warnings about request processing (e.g., ignored flags)
    ///
    /// This field is optional for backwards compatibility with existing clients.
    /// When absent or empty, no warnings occurred.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub warnings: Vec<String>,
}

/// Result for single batch item
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BatchCheckItemResult {
    /// Item ID (same as request)
    pub id: String,
    /// Whether valid
    pub valid: bool,
    /// Error message (if invalid)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub error: Option<String>,
}

/// Per-method contract metadata published by `serverInfo` (Part of #2515).
///
/// Tells AI consumers which response field carries the success/failure boolean
/// for each method, without requiring out-of-band hardcoding.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MethodContractInfo {
    /// Canonical method name
    pub name: String,
    /// Top-level outcome boolean field (e.g. `"valid"`, `"found"`, `"success"`)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub outcome_field: Option<String>,
    /// Item-level outcome boolean field for batch methods (e.g. `"valid"`)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub item_outcome_field: Option<String>,
    /// Recommended outcome field for new clients (`"verified"` when applicable)
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub preferred_outcome_field: Option<String>,
}

/// Server info response
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ServerInfo {
    /// Server name
    pub name: String,
    /// Version
    pub version: String,
    /// Resolved Lean toolchain version from `lean-toolchain`, if available.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub lean_toolchain_version: Option<String>,
    /// Available methods
    pub methods: Vec<String>,
    /// GPU acceleration available
    pub gpu_available: bool,
    /// Per-method response contract metadata (Part of #2515).
    ///
    /// Additive field — absent for older server versions.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub method_contracts: Vec<MethodContractInfo>,
}

// ============================================================================
// Metrics Types
// ============================================================================

/// Get server metrics response
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct GetMetricsResult {
    /// Server uptime in seconds
    pub uptime_secs: u64,
    /// Total requests processed
    pub total_requests: u64,
    /// Total successful requests
    pub successful_requests: u64,
    /// Total failed requests
    pub failed_requests: u64,
    /// Success rate (0.0 - 1.0)
    pub success_rate: f64,
    /// Average request latency in microseconds
    pub avg_latency_us: u64,
    /// Average request latency in nanoseconds (normalized alias, Part of #2515)
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub avg_latency_ns: Option<u64>,
    /// Requests per second (based on uptime)
    pub requests_per_second: f64,
    /// Per-method request counts
    pub method_counts: MethodCounts,
    /// Aggregate batch statistics
    pub batch_stats: BatchStats,
    /// Timing breakdown (microseconds)
    pub timing: TimingStats,
    /// Cached names in the global name interner
    pub name_interner_entries: u64,
}

/// Type cache metrics for the kernel type checker
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TypeCacheMetrics {
    /// Number of cache hits
    pub hits: u64,
    /// Number of cache misses
    pub misses: u64,
    /// Number of entries in cache
    pub entries: u64,
    /// Hit rate (0.0 - 100.0)
    pub hit_rate: f64,
}

/// Cache metrics response
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct GetCacheMetricsResult {
    /// Type checker cache stats (if enabled)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub type_cache: Option<TypeCacheMetrics>,
    /// Whether def_eq caching is enabled
    pub def_eq_cache_enabled: bool,
    /// Number of WHNF cache entries (last observed)
    pub whnf_cache_entries: u64,
    /// Number of def_eq cache entries (last observed)
    pub def_eq_cache_entries: u64,
    /// Proof state cache entries (LLM API)
    pub proof_state_cache_entries: u64,
}

/// Per-method request counts
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MethodCounts {
    /// Check requests
    pub check: u64,
    /// Prove requests
    pub prove: u64,
    /// GetType requests
    pub get_type: u64,
    /// BatchCheck requests
    pub batch_check: u64,
    /// VerifyCert requests
    pub verify_cert: u64,
    /// BatchVerifyCert requests
    pub batch_verify_cert: u64,
    /// VerifyCertArchive requests
    pub verify_cert_archive: u64,
    /// BatchVerifyCertArchive requests
    pub batch_verify_cert_archive: u64,
    /// VerifyC requests
    pub verify_c: u64,
}

/// Aggregate batch operation statistics
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BatchStats {
    /// Total items processed in batch operations
    pub items_processed: u64,
    /// Total certificates verified
    pub certificates_verified: u64,
}

/// Timing breakdown statistics (microseconds)
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TimingStats {
    /// Cumulative time in handlers
    pub cumulative_handler_time_us: u64,
    /// Cumulative time in handlers (nanoseconds, normalized alias, Part of #2515)
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub cumulative_handler_time_ns: Option<u64>,
    /// Cumulative time in type checking
    pub type_check_time_us: u64,
    /// Cumulative time in type checking (nanoseconds, normalized alias, Part of #2515)
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub type_check_time_ns: Option<u64>,
    /// Cumulative time in certificate verification
    pub cert_verify_time_us: u64,
    /// Cumulative time in certificate verification (nanoseconds, normalized alias, Part of #2515)
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub cert_verify_time_ns: Option<u64>,
}

// ============================================================================
// Admin Types
// ============================================================================

/// Get configuration request parameters (empty, no params needed)
#[derive(Debug, Clone, Default, Deserialize)]
pub struct GetConfigParams {}

/// Server configuration response
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct GetConfigResult {
    /// GPU acceleration enabled
    pub gpu_enabled: bool,
    /// Default timeout for operations (milliseconds)
    pub default_timeout_ms: u64,
    /// Number of worker threads for batch operations (0 = auto)
    pub worker_threads: usize,
    /// Effective thread count (actual threads used when worker_threads=0)
    pub effective_threads: usize,
    /// Resolved Lean toolchain version from `lean-toolchain`, if available.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub lean_toolchain_version: Option<String>,
}

/// Save environment request parameters
#[derive(Debug, Clone, Deserialize)]
pub struct SaveEnvironmentParams {
    /// File path to save to
    pub path: String,
    /// Format: "bincode" (default) or "json"
    #[serde(default)]
    pub format: Option<String>,
}

/// Save environment response
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SaveEnvironmentResult {
    /// Whether the save succeeded
    pub success: bool,
    /// Number of constants saved
    pub num_constants: usize,
    /// Number of inductives saved
    pub num_inductives: usize,
    /// File size in bytes
    pub file_size: u64,
}

/// Load environment request parameters
#[derive(Debug, Clone, Deserialize)]
pub struct LoadEnvironmentParams {
    /// File path to load from
    pub path: String,
    /// Format: "bincode" (default) or "json"
    #[serde(default)]
    pub format: Option<String>,
    /// Whether to replace or merge with current environment
    #[serde(default)]
    pub replace: bool,
}

/// Load environment response
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LoadEnvironmentResult {
    /// Whether the load succeeded
    pub success: bool,
    /// Number of constants loaded
    pub num_constants: usize,
    /// Number of inductives loaded
    pub num_inductives: usize,
}

/// Import module request parameters
#[derive(Debug, Clone, Deserialize)]
pub struct ImportModuleParams {
    /// Module name in dot-separated form (e.g. "Init", "Init.Core", "Std", "Mathlib")
    pub module: String,
    /// Additional search paths for .olean files (optional)
    #[serde(default)]
    pub search_paths: Vec<String>,
}

/// Import module response
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ImportModuleResult {
    /// Whether the import succeeded
    pub success: bool,
    /// Module(s) loaded (including transitive deps)
    pub modules_loaded: Vec<String>,
    /// Total constants added
    pub constants_added: usize,
    /// Total constants skipped (duplicates)
    pub constants_skipped: usize,
}

/// Get environment request parameters (optional filtering)
#[derive(Debug, Clone, Default, Deserialize)]
pub struct GetEnvironmentParams {
    /// Return JSON representation (default: false returns summary)
    #[serde(default)]
    pub include_json: bool,
}

/// Get environment response
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct GetEnvironmentResult {
    /// Number of constants
    pub num_constants: usize,
    /// Number of inductives
    pub num_inductives: usize,
    /// Constant names (first 100)
    pub constant_names: Vec<String>,
    /// JSON representation (if requested)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub json: Option<String>,
}
