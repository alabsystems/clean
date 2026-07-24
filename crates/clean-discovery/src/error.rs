// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Error types for the proof discovery loop.

use clean_kernel::EnvError;

/// Errors that can occur during proof discovery.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum DiscoveryError {
    /// Failed to initialize the kernel environment with required declarations.
    #[error("environment initialization failed: {0}")]
    EnvInit(#[from] EnvError),

    /// No candidates were generated for the search.
    #[error("no candidates generated for family {family}")]
    NoCandidates { family: String },

    /// Search budget exhausted without finding valid theorems.
    #[error("search budget exhausted: evaluated {evaluated} candidates, 0 valid")]
    BudgetExhausted { evaluated: u64 },

    /// Invalid search configuration.
    #[error("invalid configuration: {reason}")]
    InvalidConfig { reason: String },

    /// I/O error during file operations (save/load).
    #[error("I/O error: {0}")]
    Io(#[from] std::io::Error),

    /// Serialization or deserialization error.
    #[error("serialization error: {0}")]
    Serialization(String),
}
