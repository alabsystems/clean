// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Solver-results cache — Phase 0: obligation key + solver-attempt telemetry.
//!
//! See `designs/2026-06-24-solver-results-cache-service.md`. Phase 0 has two
//! parts:
//!
//! - **Telemetry** ([`telemetry`]): captures one [`record::SolverAttemptRecord`]
//!   per solving attempt to a sink keyed by `CLEAN_SOLVER_TELEMETRY_DIR`. Pure
//!   instrumentation; zero-overhead no-op when the env var is unset.
//! - **Proof cache** ([`store`]): a local content-addressed store keyed by the
//!   [`obligation::obligation_digest`] of the goal type, holding re-checkable
//!   proof terms. A cache *hit* short-circuits the solver search and returns the
//!   stored proof term; keyed by `CLEAN_SOLVER_CACHE_DIR`, zero-overhead no-op
//!   when unset.
//!
//! # Soundness (load-bearing)
//!
//! This is a **search-result cache, not a trust cache, and not in the TCB.**
//!
//! - The obligation key is a soundness *bucket* (it reuses the alpha-canonical
//!   de-Bruijn `blake3` digest the novelty gate already trusts). The kernel is
//!   the *arbiter*: a cache hit returns a stored proof term, and the caller
//!   (swarm / graduation) re-checks that term through the kernel via
//!   `recheck_and_classify` exactly as for a freshly-found proof. A stale,
//!   colliding, or deliberately-corrupted entry is therefore *caught* by the
//!   kernel re-check and is never silently trusted.
//! - Only re-checkable, proof-bearing results are cached. Raw solver verdicts
//!   (`Unsat` without a proof, `Unknown`, `Timeout`) are telemetry / hints,
//!   never a verification and never a cache entry.

pub(crate) mod analysis;
pub(crate) mod dataset;
pub(crate) mod index;
pub(crate) mod ingest;
pub(crate) mod obligation;
pub(crate) mod record;
pub(crate) mod serve;
pub mod service;
pub(crate) mod store;
pub(crate) mod telemetry;

#[cfg(test)]
mod tests_e2e;

pub(crate) use obligation::obligation_digest;

use thiserror::Error;

/// Errors raised while building obligation keys or writing telemetry.
///
/// All variants are non-fatal at the call site: telemetry failures are logged
/// and swallowed so instrumentation can never perturb solving.
///
/// Public because [`crate::solver_cache_service::encode_proof_hex`] (a tools /
/// tests helper for building an ingest envelope) returns it; it is re-exported
/// through the `solver_cache_service` facade so external callers can name it.
#[derive(Debug, Error)]
#[non_exhaustive]
pub enum SolverCacheError {
    /// Flattening a goal expression for the obligation digest failed.
    #[error("flatten goal for obligation digest: {0}")]
    Flatten(String),
    /// Serializing an attempt record to JSON failed.
    #[error("serialize solver-attempt-record: {0}")]
    Serialize(String),
    /// Writing to the telemetry sink failed.
    #[error("solver telemetry sink: {0}")]
    Sink(String),
}
