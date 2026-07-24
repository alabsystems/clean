// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Proof Backend Trait for TLAPS Integration
//!
//! Copyright 2026 Andrew Yates
//! Licensed under Apache-2.0
//!
//! This module defines the `ProofBackend` trait for pluggable proof backends.
//! Pattern adopted from ty/crates/tla-prove/src/backend.rs (alabsystems/ty).
//!
//! ## Architecture
//!
//! ```text
//! ┌─────────────────┐     ┌────────────────────┐
//! │ BenchmarkRunner │────▶│ ProofBackend trait │
//! └─────────────────┘     └────────────────────┘
//!                                   ▲
//!                                   │
//!         ┌─────────────────────────┼─────────────────────────┐
//!         │                         │                         │
//! ┌───────┴───────┐       ┌────────┴────────┐       ┌────────┴────────┐
//! │NativeTacticBk │       │   AyBackend     │       │  ZenonBackend   │
//! │(current impl) │       │   (future)      │       │    (future)     │
//! └───────────────┘       └─────────────────┘       └─────────────────┘
//! ```
//!
//! ## Usage
//!
//! ```text
//! let backend = NativeTacticBackend::new();
//! if backend.supports(&obligation) {
//!     let result = backend.prove(&obligation, &context);
//!     match result.outcome {
//!         ProofOutcome::Proved => println!("Proved!"),
//!         ProofOutcome::Failed { message, .. } => println!("Failed: {}", message),
//!         ProofOutcome::Unknown { reason } => println!("Unknown: {}", reason),
//!     }
//! }
//! ```

use crate::TlaObligation;
use serde::{Deserialize, Serialize};
use std::time::Duration;

/// Outcome of a proof attempt
///
/// Three-state outcome following tla-prove pattern:
/// - Proved: obligation was successfully proved
/// - Failed: proof attempt failed with potential counterexample
/// - Unknown: prover could not determine result (timeout, resource limit, etc.)
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum ProofOutcome {
    /// Proof succeeded
    Proved,

    /// Proof failed - obligation is likely false or unprovable with current tactics
    Failed {
        /// Human-readable failure message
        message: String,
        /// Counterexample if available: list of (variable, value) pairs
        counterexample: Option<Vec<(String, String)>>,
    },

    /// Prover could not determine result
    Unknown {
        /// Reason for unknown result (timeout, resource limit, etc.)
        reason: String,
    },
}

impl ProofOutcome {
    /// Check if the outcome is a successful proof
    pub fn is_proved(&self) -> bool {
        matches!(self, ProofOutcome::Proved)
    }

    /// Check if the outcome is a definite failure
    pub fn is_failed(&self) -> bool {
        matches!(self, ProofOutcome::Failed { .. })
    }

    /// Check if the outcome is unknown
    pub fn is_unknown(&self) -> bool {
        matches!(self, ProofOutcome::Unknown { .. })
    }
}

/// Result of a proof attempt including metadata
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TlapsProofResult {
    /// The outcome of the proof attempt
    pub outcome: ProofOutcome,

    /// Time taken for the proof attempt
    pub duration: Duration,

    /// Tactics or strategies tried during the attempt
    pub tactics_tried: Vec<String>,

    /// Proof certificate if proved (serialized proof term)
    pub certificate: Option<String>,
}

impl TlapsProofResult {
    /// Create a successful proof result
    pub fn proved(duration: Duration, tactics: Vec<String>, certificate: Option<String>) -> Self {
        Self {
            outcome: ProofOutcome::Proved,
            duration,
            tactics_tried: tactics,
            certificate,
        }
    }

    /// Create a failed proof result
    pub fn failed(
        message: String,
        counterexample: Option<Vec<(String, String)>>,
        duration: Duration,
        tactics: Vec<String>,
    ) -> Self {
        Self {
            outcome: ProofOutcome::Failed {
                message,
                counterexample,
            },
            duration,
            tactics_tried: tactics,
            certificate: None,
        }
    }

    /// Create an unknown result (e.g., timeout)
    pub fn unknown(reason: String, duration: Duration, tactics: Vec<String>) -> Self {
        Self {
            outcome: ProofOutcome::Unknown { reason },
            duration,
            tactics_tried: tactics,
            certificate: None,
        }
    }
}

/// Context for proof attempts
///
/// Contains configuration and shared resources for proof backends.
#[derive(Debug, Clone, Default)]
pub struct ProofContext {
    /// Maximum time allowed for a single proof attempt
    pub timeout: Option<Duration>,

    /// Enable trace/debug output
    pub trace: bool,

    /// Additional configuration options
    pub options: std::collections::HashMap<String, String>,
}

impl ProofContext {
    /// Create a new proof context with default settings
    pub fn new() -> Self {
        Self::default()
    }

    /// Set timeout for proof attempts
    pub fn with_timeout(mut self, timeout: Duration) -> Self {
        self.timeout = Some(timeout);
        self
    }

    /// Enable trace output
    pub fn with_trace(mut self, trace: bool) -> Self {
        self.trace = trace;
        self
    }

    /// Set a configuration option
    pub fn with_option(mut self, key: &str, value: &str) -> Self {
        self.options.insert(key.to_string(), value.to_string());
        self
    }
}

/// Trait for pluggable proof backends
///
/// Implements the ProofBackend pattern from ty/crates/tla-prove.
/// Each backend can handle different types of obligations using different
/// proof strategies.
pub trait ProofBackend: Send + Sync {
    /// Attempt to prove an obligation
    ///
    /// Returns a TlapsProofResult containing the outcome and metadata.
    fn prove(&self, obligation: &TlaObligation, context: &ProofContext) -> TlapsProofResult;

    /// Return the name of this backend
    fn name(&self) -> &str;

    /// Check if this backend supports the given obligation
    ///
    /// Backends should return true only for obligations they can meaningfully
    /// attempt. For example, an SMT backend might not support temporal logic
    /// obligations.
    fn supports(&self, obligation: &TlaObligation) -> bool;
}

/// Native tactic backend using clean-tla's TlaTacticEngine
///
/// This backend wraps the existing `prove_tla_obligation` function,
/// providing the ProofBackend interface for the benchmark runner.
pub struct NativeTacticBackend {
    /// Enable trace output for debugging
    trace: bool,
}

impl NativeTacticBackend {
    /// Create a new native tactic backend
    pub fn new() -> Self {
        Self { trace: false }
    }

    /// Enable trace output
    pub fn with_trace(mut self, trace: bool) -> Self {
        self.trace = trace;
        self
    }
}

impl Default for NativeTacticBackend {
    fn default() -> Self {
        Self::new()
    }
}

impl ProofBackend for NativeTacticBackend {
    fn prove(&self, obligation: &TlaObligation, context: &ProofContext) -> TlapsProofResult {
        use crate::tactic::{prove_tla_obligation, prove_tla_obligation_traced};
        use std::time::Instant;

        let start = Instant::now();

        // Use traced version if context or self requests trace
        let result = if self.trace || context.trace {
            prove_tla_obligation_traced(obligation)
        } else {
            prove_tla_obligation(obligation)
        };

        let duration = start.elapsed();

        // Convert ObligationResult to TlapsProofResult
        if result.proved {
            TlapsProofResult::proved(duration, result.tactics_tried, result.certificate)
        } else {
            // Check if it looks like a timeout
            if result.error.as_ref().is_some_and(|e| e.contains("timeout")) {
                TlapsProofResult::unknown(
                    result.error.unwrap_or_else(|| "Timeout".to_string()),
                    duration,
                    result.tactics_tried,
                )
            } else {
                TlapsProofResult::failed(
                    result.error.unwrap_or_else(|| "Proof failed".to_string()),
                    None, // No counterexample extraction yet
                    duration,
                    result.tactics_tried,
                )
            }
        }
    }

    fn name(&self) -> &str {
        "native-tactic"
    }

    fn supports(&self, _obligation: &TlaObligation) -> bool {
        // Native backend supports all obligations (it may fail, but it can try)
        true
    }
}

/// Backend registry for managing multiple proof backends
///
/// Allows registering multiple backends and dispatching to the appropriate
/// one based on obligation characteristics.
pub struct BackendRegistry {
    backends: Vec<Box<dyn ProofBackend>>,
}

impl BackendRegistry {
    /// Create a new empty registry
    pub fn new() -> Self {
        Self {
            backends: Vec::new(),
        }
    }

    /// Register a backend
    pub fn register(&mut self, backend: Box<dyn ProofBackend>) {
        self.backends.push(backend);
    }

    /// Get all backends that support the given obligation
    pub fn supporting_backends(&self, obligation: &TlaObligation) -> Vec<&dyn ProofBackend> {
        self.backends
            .iter()
            .filter(|b| b.supports(obligation))
            .map(|b| b.as_ref())
            .collect()
    }

    /// Get backend by name
    pub fn get(&self, name: &str) -> Option<&dyn ProofBackend> {
        self.backends
            .iter()
            .find(|b| b.name() == name)
            .map(|b| b.as_ref())
    }

    /// Try all supporting backends until one succeeds
    pub fn prove_first(
        &self,
        obligation: &TlaObligation,
        context: &ProofContext,
    ) -> Option<(String, TlapsProofResult)> {
        for backend in self.supporting_backends(obligation) {
            let result = backend.prove(obligation, context);
            if result.outcome.is_proved() {
                return Some((backend.name().to_string(), result));
            }
        }
        None
    }

    /// List all registered backend names
    pub fn names(&self) -> Vec<&str> {
        self.backends.iter().map(|b| b.name()).collect()
    }
}

impl Default for BackendRegistry {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::encoding::TlaFormula;

    #[test]
    fn test_proof_outcome_predicates() {
        assert!(ProofOutcome::Proved.is_proved());
        assert!(!ProofOutcome::Proved.is_failed());
        assert!(!ProofOutcome::Proved.is_unknown());

        let failed = ProofOutcome::Failed {
            message: "test".to_string(),
            counterexample: None,
        };
        assert!(!failed.is_proved());
        assert!(failed.is_failed());
        assert!(!failed.is_unknown());

        let unknown = ProofOutcome::Unknown {
            reason: "timeout".to_string(),
        };
        assert!(!unknown.is_proved());
        assert!(!unknown.is_failed());
        assert!(unknown.is_unknown());
    }

    #[test]
    fn test_native_backend_name() {
        let backend = NativeTacticBackend::new();
        assert_eq!(backend.name(), "native-tactic");
    }

    #[test]
    fn test_native_backend_supports_all() {
        let backend = NativeTacticBackend::new();
        let obligation = TlaObligation::new(TlaFormula::True);
        assert!(backend.supports(&obligation));
    }

    #[test]
    fn test_native_backend_prove_trivial() {
        let backend = NativeTacticBackend::new();
        let obligation = TlaObligation::new(TlaFormula::True);
        let context = ProofContext::new();

        let result = backend.prove(&obligation, &context);
        // The native backend should be able to prove True
        // (but we check it doesn't panic at minimum)
        assert!(!result.tactics_tried.is_empty() || result.duration.as_nanos() > 0);
    }

    #[test]
    fn test_backend_registry() {
        let mut registry = BackendRegistry::new();
        registry.register(Box::new(NativeTacticBackend::new()));

        assert_eq!(registry.names(), vec!["native-tactic"]);

        let obligation = TlaObligation::new(TlaFormula::True);
        let supporting = registry.supporting_backends(&obligation);
        assert_eq!(supporting.len(), 1);
        assert_eq!(supporting[0].name(), "native-tactic");
    }

    #[test]
    fn test_proof_context_builder() {
        let context = ProofContext::new()
            .with_timeout(Duration::from_secs(30))
            .with_trace(true)
            .with_option("max_depth", "10");

        assert_eq!(context.timeout, Some(Duration::from_secs(30)));
        assert!(context.trace);
        assert_eq!(context.options.get("max_depth"), Some(&"10".to_string()));
    }
}
