// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! LLM oracle integration for the proof discovery loop.
//!
//! Wraps the commercial LLM backends from `clean-auto` (AI Model, AI Model, AI Provider)
//! to generate candidate theorem statements and proofs for discovery search.
//!
//! Unlike `clean-auto`'s oracle (which generates tactic sequences for known goals),
//! the discovery oracle generates novel theorem-proof pairs that the kernel then
//! verifies at sub-microsecond speed.
//!
//! # Architecture
//!
//! ```text
//! DiscoveryOracleRunner
//!   ├─ builds a discovery-specific prompt (theorem family + context)
//!   ├─ delegates to clean_auto::oracle::ProofOracle (AI Model/AI Model/AI Provider)
//!   ├─ parses LLM response into CandidateTheorem values
//!   └─ feeds candidates to kernel BatchVerifier
//! ```
//!
//! # Feature gate
//!
//! This module requires the `oracle` feature:
//!
//! ```toml
//! clean-discovery = { workspace = true, features = ["oracle"] }
//! ```

mod prompt;
mod runner;

pub use prompt::DiscoveryPrompt;
pub use runner::DiscoveryOracleRunner;

// Re-export core oracle types from clean-auto for convenience.
pub use clean_auto::oracle::{
    ClaudeOracle, GeminiOracle, HttpOracle, OpenAiOracle, OracleCandidate, OracleConfig,
    OracleError, OracleMetrics, OracleRequest, ProofOracle,
};
