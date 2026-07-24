// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Centralized method registry for JSON-RPC methods.
//!
//! This module provides a single source of truth for method metadata.
//!
//! # History
//!
//! Method dispatch was previously duplicated across `lib.rs` and `websocket.rs`
//! with nearly identical ~180-line match blocks. This caused drift (e.g.,
//! progress list missing batchGetPremises in #611). Dispatch is now centralized
//! in [`crate::dispatch::dispatch_request`] (Part of #1742).
//!
//! # Alias Contract (Part of #1380)
//!
//! Some methods accept alternative names (aliases) in dispatch. The registry is
//! the single source of truth for which aliases exist and which canonical method
//! they map to. Policy:
//! - `serverInfo` advertises canonical names only (via [`all_method_names`]).
//! - Dispatch accepts both canonical and alias names.
//! - [`is_known_method`] returns true for both.
//! - [`resolve_canonical`] maps alias → canonical name.
//!
//! # Usage
//!
//! ```no_run
//! use clean_server::registry::{supports_progress, all_method_names};
//!
//! // Get all method names for serverInfo
//! let methods: Vec<String> = all_method_names();
//! assert!(!methods.is_empty());
//!
//! // Check if a method supports progress streaming
//! if supports_progress("batchCheck") {
//!     // Set up progress channel
//! }
//! ```
//!
//! # Design Note
//!
//! This registry provides method metadata (progress support, batch safety, aliases).
//! Actual dispatch lives in [`crate::dispatch`]. Unit tests verify the registry
//! is internally consistent and that dispatch covers all registered methods.

/// Per-method outcome boolean contract metadata (Part of #2515).
///
/// Tells API consumers which field(s) in the response carry the success/failure
/// signal. Methods with no outcome boolean (e.g. `getType`, `serverInfo`) leave
/// both fields `None`.
#[derive(Debug, Clone, Copy)]
pub struct OutcomeContract {
    /// Top-level boolean field name in the response (e.g. `"valid"`, `"found"`).
    pub top_level_field: Option<&'static str>,
    /// Item-level boolean field name in batch item results (e.g. `"valid"`).
    pub item_field: Option<&'static str>,
}

impl OutcomeContract {
    /// Whether this method exposes any success/failure boolean in its response.
    pub fn has_outcome(self) -> bool {
        self.top_level_field.is_some() || self.item_field.is_some()
    }

    /// Normalized convergence target for clients.
    ///
    /// Existing endpoints keep their legacy field names, but new consumers can
    /// treat any outcome-bearing method as converging on `verified`.
    pub fn preferred_outcome_field(self) -> Option<&'static str> {
        if self.has_outcome() {
            Some("verified")
        } else {
            None
        }
    }
}

/// Metadata for a JSON-RPC method.
#[derive(Debug, Clone, Copy)]
pub struct MethodInfo {
    /// Method name as it appears in JSON-RPC requests
    pub name: &'static str,
    /// Whether this method supports progress streaming over WebSocket
    pub supports_progress: bool,
    /// Whether this method is safe to call in JSON-RPC batch mode
    /// (false = requires single-request framing for correct semantics)
    pub batch_safe: bool,
    /// Alternative names that route to the same handler.
    ///
    /// Aliases are accepted in dispatch but NOT advertised in `serverInfo`.
    /// This is the single source of truth for the canonical-vs-alias contract
    /// (Part of #1380).
    pub aliases: &'static [&'static str],
    /// Which response field carries the success/failure boolean (Part of #2515).
    pub outcome_contract: OutcomeContract,
}

impl MethodInfo {
    /// Whether the method exposes any success/failure boolean in its response.
    pub fn has_outcome(self) -> bool {
        self.outcome_contract.has_outcome()
    }

    /// Normalized convergence target for clients.
    pub fn preferred_outcome_field(self) -> Option<&'static str> {
        self.outcome_contract.preferred_outcome_field()
    }
}

/// Central registry of all JSON-RPC methods.
///
/// This is the single source of truth for method metadata.
/// When adding a new method:
/// 1. Add entry here (with aliases if applicable)
/// 2. Add match arm in dispatch.rs dispatch_request
/// 3. Run tests to verify consistency
pub const METHOD_REGISTRY: &[MethodInfo] = &[
    // Core Type Checking
    MethodInfo {
        name: "check",
        supports_progress: false,
        batch_safe: true,
        aliases: &[],
        outcome_contract: OutcomeContract {
            top_level_field: Some("valid"),
            item_field: None,
        },
    },
    MethodInfo {
        name: "getType",
        supports_progress: false,
        batch_safe: true,
        aliases: &[],
        outcome_contract: OutcomeContract {
            top_level_field: None,
            item_field: None,
        },
    },
    MethodInfo {
        name: "batchCheck",
        supports_progress: true,
        batch_safe: true,
        aliases: &[],
        outcome_contract: OutcomeContract {
            top_level_field: None,
            item_field: Some("valid"),
        },
    },
    // Proof & SMT
    MethodInfo {
        name: "prove",
        supports_progress: true,
        batch_safe: true,
        aliases: &[],
        outcome_contract: OutcomeContract {
            top_level_field: Some("found"),
            item_field: None,
        },
    },
    MethodInfo {
        name: "proveTLA",
        supports_progress: false,
        batch_safe: true,
        aliases: &[],
        outcome_contract: OutcomeContract {
            top_level_field: Some("proved"),
            item_field: None,
        },
    },
    MethodInfo {
        name: "batchProveTLA",
        supports_progress: true,
        batch_safe: true,
        aliases: &[],
        outcome_contract: OutcomeContract {
            top_level_field: None,
            item_field: Some("proved"),
        },
    },
    // Premise Selection
    MethodInfo {
        name: "getPremises",
        supports_progress: false,
        batch_safe: true,
        aliases: &[],
        outcome_contract: OutcomeContract {
            top_level_field: None,
            item_field: None,
        },
    },
    MethodInfo {
        name: "batchGetPremises",
        supports_progress: true,
        batch_safe: true,
        aliases: &[],
        outcome_contract: OutcomeContract {
            top_level_field: None,
            item_field: None,
        },
    },
    // Certificate Operations
    MethodInfo {
        name: "verifyCert",
        supports_progress: false,
        batch_safe: true,
        aliases: &[],
        outcome_contract: OutcomeContract {
            top_level_field: Some("success"),
            item_field: None,
        },
    },
    MethodInfo {
        name: "batchVerifyCert",
        supports_progress: true,
        batch_safe: true,
        aliases: &[],
        outcome_contract: OutcomeContract {
            top_level_field: None,
            item_field: Some("success"),
        },
    },
    MethodInfo {
        name: "verifyCertArchive",
        supports_progress: false,
        batch_safe: true,
        aliases: &[],
        outcome_contract: OutcomeContract {
            top_level_field: Some("success"),
            item_field: None,
        },
    },
    MethodInfo {
        name: "batchVerifyCertArchive",
        supports_progress: true,
        batch_safe: true,
        aliases: &[],
        outcome_contract: OutcomeContract {
            top_level_field: None,
            item_field: Some("success"),
        },
    },
    // External Certificate Verification — snake_case canonical, camelCase aliases (Part of #894)
    MethodInfo {
        name: "verify_alethe_certificate",
        supports_progress: false,
        batch_safe: true,
        aliases: &["verifyAletheCertificate"],
        outcome_contract: OutcomeContract {
            top_level_field: Some("success"),
            item_field: None,
        },
    },
    MethodInfo {
        name: "verify_farkas_certificate",
        supports_progress: false,
        batch_safe: true,
        aliases: &["verifyFarkasCertificate"],
        outcome_contract: OutcomeContract {
            top_level_field: Some("success"),
            item_field: None,
        },
    },
    MethodInfo {
        name: "verify_entailment_certificate",
        supports_progress: false,
        batch_safe: true,
        aliases: &["verifyEntailmentCertificate"],
        outcome_contract: OutcomeContract {
            top_level_field: Some("success"),
            item_field: None,
        },
    },
    MethodInfo {
        name: "verify_certificates_batch",
        supports_progress: false,
        batch_safe: true,
        aliases: &["verifyCertificatesBatch", "batchVerifyExternalCert"],
        outcome_contract: OutcomeContract {
            top_level_field: None,
            item_field: Some("success"),
        },
    },
    MethodInfo {
        name: "compressCert",
        supports_progress: false,
        batch_safe: true,
        aliases: &[],
        outcome_contract: OutcomeContract {
            top_level_field: Some("success"),
            item_field: None,
        },
    },
    MethodInfo {
        name: "decompressCert",
        supports_progress: false,
        batch_safe: true,
        aliases: &[],
        outcome_contract: OutcomeContract {
            top_level_field: Some("success"),
            item_field: None,
        },
    },
    MethodInfo {
        name: "archiveCert",
        supports_progress: false,
        batch_safe: true,
        aliases: &[],
        outcome_contract: OutcomeContract {
            top_level_field: Some("success"),
            item_field: None,
        },
    },
    MethodInfo {
        name: "unarchiveCert",
        supports_progress: false,
        batch_safe: true,
        aliases: &[],
        outcome_contract: OutcomeContract {
            top_level_field: Some("success"),
            item_field: None,
        },
    },
    MethodInfo {
        name: "trainDict",
        supports_progress: false,
        batch_safe: true,
        aliases: &[],
        outcome_contract: OutcomeContract {
            top_level_field: Some("success"),
            item_field: None,
        },
    },
    MethodInfo {
        name: "archiveCertWithDict",
        supports_progress: false,
        batch_safe: true,
        aliases: &[],
        outcome_contract: OutcomeContract {
            top_level_field: Some("success"),
            item_field: None,
        },
    },
    MethodInfo {
        name: "unarchiveCertWithDict",
        supports_progress: false,
        batch_safe: true,
        aliases: &[],
        outcome_contract: OutcomeContract {
            top_level_field: Some("success"),
            item_field: None,
        },
    },
    // C Verification
    MethodInfo {
        name: "verifyC",
        supports_progress: true,
        batch_safe: true,
        aliases: &[],
        outcome_contract: OutcomeContract {
            top_level_field: Some("success"),
            item_field: None,
        },
    },
    // Server Management
    MethodInfo {
        name: "serverInfo",
        supports_progress: false,
        batch_safe: true,
        aliases: &[],
        outcome_contract: OutcomeContract {
            top_level_field: None,
            item_field: None,
        },
    },
    MethodInfo {
        name: "saveEnvironment",
        supports_progress: false,
        batch_safe: true,
        aliases: &[],
        outcome_contract: OutcomeContract {
            top_level_field: Some("success"),
            item_field: None,
        },
    },
    MethodInfo {
        name: "loadEnvironment",
        supports_progress: false,
        batch_safe: true,
        aliases: &[],
        outcome_contract: OutcomeContract {
            top_level_field: Some("success"),
            item_field: None,
        },
    },
    MethodInfo {
        name: "importModule",
        supports_progress: false,
        batch_safe: true,
        aliases: &[],
        outcome_contract: OutcomeContract {
            top_level_field: Some("success"),
            item_field: None,
        },
    },
    // Swarm worker declaration submission (C1 Task C).
    MethodInfo {
        name: "addDecl",
        supports_progress: false,
        batch_safe: true,
        aliases: &[],
        outcome_contract: OutcomeContract {
            top_level_field: Some("accepted"),
            item_field: None,
        },
    },
    MethodInfo {
        name: "getEnvironment",
        supports_progress: false,
        batch_safe: true,
        aliases: &[],
        outcome_contract: OutcomeContract {
            top_level_field: None,
            item_field: None,
        },
    },
    MethodInfo {
        name: "getConfig",
        supports_progress: false,
        batch_safe: true,
        aliases: &[],
        outcome_contract: OutcomeContract {
            top_level_field: None,
            item_field: None,
        },
    },
    MethodInfo {
        name: "getMetrics",
        supports_progress: false,
        batch_safe: true,
        aliases: &[],
        outcome_contract: OutcomeContract {
            top_level_field: None,
            item_field: None,
        },
    },
    MethodInfo {
        name: "getCacheMetrics",
        supports_progress: false,
        batch_safe: true,
        aliases: &[],
        outcome_contract: OutcomeContract {
            top_level_field: None,
            item_field: None,
        },
    },
    // LLM Integration API (Proof State Management)
    MethodInfo {
        name: "initProofState",
        supports_progress: false,
        batch_safe: true,
        aliases: &[],
        outcome_contract: OutcomeContract {
            top_level_field: Some("success"),
            item_field: None,
        },
    },
    MethodInfo {
        name: "proofState.openObligation",
        supports_progress: false,
        batch_safe: true,
        aliases: &[],
        outcome_contract: OutcomeContract {
            top_level_field: None,
            item_field: None,
        },
    },
    MethodInfo {
        name: "applyTactic",
        supports_progress: false,
        batch_safe: true,
        aliases: &[],
        outcome_contract: OutcomeContract {
            top_level_field: Some("success"),
            item_field: None,
        },
    },
    MethodInfo {
        name: "batchApplyTactic",
        supports_progress: false,
        batch_safe: true,
        aliases: &[],
        outcome_contract: OutcomeContract {
            top_level_field: None,
            item_field: Some("success"),
        },
    },
    MethodInfo {
        name: "getProofState",
        supports_progress: false,
        batch_safe: true,
        aliases: &[],
        outcome_contract: OutcomeContract {
            top_level_field: None,
            item_field: None,
        },
    },
    MethodInfo {
        name: "proofState.searchTheorems",
        supports_progress: false,
        batch_safe: true,
        aliases: &[],
        outcome_contract: OutcomeContract {
            top_level_field: None,
            item_field: None,
        },
    },
    MethodInfo {
        name: "proofState.searchTactics",
        supports_progress: false,
        batch_safe: true,
        aliases: &[],
        outcome_contract: OutcomeContract {
            top_level_field: None,
            item_field: None,
        },
    },
    MethodInfo {
        name: "proofState.close",
        supports_progress: false,
        batch_safe: true,
        aliases: &[],
        outcome_contract: OutcomeContract {
            top_level_field: Some("closed"),
            item_field: None,
        },
    },
    MethodInfo {
        name: "proofState.retain",
        supports_progress: false,
        batch_safe: true,
        aliases: &[],
        outcome_contract: OutcomeContract {
            top_level_field: Some("retained"),
            item_field: None,
        },
    },
    MethodInfo {
        name: "proofState.explainFailure",
        supports_progress: false,
        batch_safe: true,
        aliases: &[],
        outcome_contract: OutcomeContract {
            top_level_field: None,
            item_field: None,
        },
    },
    MethodInfo {
        name: "extractProof",
        supports_progress: false,
        batch_safe: true,
        aliases: &[],
        outcome_contract: OutcomeContract {
            top_level_field: Some("success"),
            item_field: None,
        },
    },
    MethodInfo {
        name: "verifyProof",
        supports_progress: false,
        batch_safe: true,
        aliases: &[],
        outcome_contract: OutcomeContract {
            top_level_field: Some("verified"),
            item_field: None,
        },
    },
    MethodInfo {
        name: "verifyProofBatch",
        supports_progress: false,
        batch_safe: true,
        aliases: &[],
        outcome_contract: OutcomeContract {
            top_level_field: None,
            item_field: Some("verified"),
        },
    },
    MethodInfo {
        name: "verifyFile",
        supports_progress: false,
        batch_safe: true,
        aliases: &[],
        outcome_contract: OutcomeContract {
            top_level_field: Some("verified"),
            item_field: None,
        },
    },
    MethodInfo {
        name: "fillSorries",
        supports_progress: false,
        batch_safe: true,
        aliases: &[],
        outcome_contract: OutcomeContract {
            top_level_field: Some("success"),
            item_field: None,
        },
    },
    MethodInfo {
        name: "composeProof",
        supports_progress: false,
        batch_safe: true,
        aliases: &[],
        outcome_contract: OutcomeContract {
            top_level_field: Some("success"),
            item_field: None,
        },
    },
    // LLM Integration API - Full Proof Search (#3177)
    MethodInfo {
        name: "searchProof",
        supports_progress: true,
        batch_safe: true,
        aliases: &[],
        outcome_contract: OutcomeContract {
            top_level_field: Some("found"),
            item_field: None,
        },
    },
    // Widget RPC endpoints for infoview parity (Part of #1193)
    MethodInfo {
        name: "getWidgets",
        supports_progress: false,
        batch_safe: true,
        aliases: &[],
        outcome_contract: OutcomeContract {
            top_level_field: None,
            item_field: None,
        },
    },
    MethodInfo {
        name: "getWidgetSource",
        supports_progress: false,
        batch_safe: true,
        aliases: &[],
        outcome_contract: OutcomeContract {
            top_level_field: None,
            item_field: None,
        },
    },
    MethodInfo {
        name: "Widget_event",
        supports_progress: false,
        batch_safe: true,
        aliases: &[],
        outcome_contract: OutcomeContract {
            top_level_field: None,
            item_field: None,
        },
    },
];

/// Check if a method supports progress streaming.
///
/// Used by WebSocket dispatch to determine if progress channel should be set up.
/// Checks both canonical names and aliases.
#[inline]
pub fn supports_progress(method: &str) -> bool {
    find_method_info(method)
        .map(|m| m.supports_progress)
        .unwrap_or(false)
}

/// Get all canonical method names for serverInfo.
///
/// Returns canonical method names only (no aliases). Aliases are accepted
/// by dispatch but not advertised in discovery (Part of #1380).
pub fn all_method_names() -> Vec<String> {
    METHOD_REGISTRY.iter().map(|m| m.name.to_string()).collect()
}

/// Check if a method is registered as a canonical name.
#[inline]
pub fn is_registered(method: &str) -> bool {
    METHOD_REGISTRY.iter().any(|m| m.name == method)
}

/// Check if a method name is known (canonical or alias).
#[inline]
pub fn is_known_method(method: &str) -> bool {
    find_method_info(method).is_some()
}

/// Resolve an alias to its canonical method name.
///
/// Returns `Some(canonical_name)` if the input is an alias, `None` if it's
/// already canonical or not recognized.
pub fn resolve_canonical(method: &str) -> Option<&'static str> {
    for m in METHOD_REGISTRY {
        if m.aliases.contains(&method) {
            return Some(m.name);
        }
    }
    None
}

/// Get all registered aliases as (alias, canonical) pairs.
pub fn all_aliases() -> Vec<(&'static str, &'static str)> {
    let mut result = Vec::new();
    for m in METHOD_REGISTRY {
        for alias in m.aliases {
            result.push((*alias, m.name));
        }
    }
    result
}

/// Find the `MethodInfo` for a method name (canonical or alias).
fn find_method_info(method: &str) -> Option<&'static MethodInfo> {
    // Check canonical names first (fast path)
    if let Some(m) = METHOD_REGISTRY.iter().find(|m| m.name == method) {
        return Some(m);
    }
    // Check aliases
    METHOD_REGISTRY.iter().find(|m| m.aliases.contains(&method))
}

/// Get methods that support progress streaming.
pub fn progress_methods() -> Vec<&'static str> {
    METHOD_REGISTRY
        .iter()
        .filter(|m| m.supports_progress)
        .map(|m| m.name)
        .collect()
}

/// Get all canonical method outcome contracts for `serverInfo` (Part of #2515).
///
/// Returns `(name, outcome_contract)` for every canonical method.
pub fn all_method_contracts() -> Vec<(&'static str, OutcomeContract)> {
    METHOD_REGISTRY
        .iter()
        .map(|m| (m.name, m.outcome_contract))
        .collect()
}

/// Check if a method is batch-safe (won't lose progress in JSON-RPC batch mode).
///
/// Methods that require single-request framing should be marked non-batch-safe.
/// Checks both canonical names and aliases.
#[inline]
pub fn is_batch_safe(method: &str) -> bool {
    find_method_info(method)
        .map(|m| m.batch_safe)
        .unwrap_or(false) // Unknown methods are treated as non-batch-safe
}

#[cfg(test)]
mod tests {
    use super::*;

    /// All canonical method names that appear in dispatch match arms.
    const DISPATCH_METHODS: &[&str] = &[
        "Widget_event",
        "addDecl",
        "applyTactic",
        "archiveCert",
        "archiveCertWithDict",
        "batchApplyTactic",
        "batchCheck",
        "batchGetPremises",
        "batchProveTLA",
        "batchVerifyCert",
        "batchVerifyCertArchive",
        "check",
        "composeProof",
        "compressCert",
        "decompressCert",
        "extractProof",
        "fillSorries",
        "getCacheMetrics",
        "getConfig",
        "getEnvironment",
        "getMetrics",
        "getPremises",
        "getProofState",
        "getType",
        "getWidgetSource",
        "getWidgets",
        "importModule",
        "initProofState",
        "loadEnvironment",
        "proofState.close",
        "proofState.explainFailure",
        "proofState.openObligation",
        "proofState.retain",
        "proofState.searchTactics",
        "proofState.searchTheorems",
        "prove",
        "proveTLA",
        "saveEnvironment",
        "searchProof",
        "serverInfo",
        "trainDict",
        "unarchiveCert",
        "unarchiveCertWithDict",
        "verifyC",
        "verifyCert",
        "verifyCertArchive",
        "verifyFile",
        "verifyProof",
        "verifyProofBatch",
        "verify_alethe_certificate",
        "verify_certificates_batch",
        "verify_entailment_certificate",
        "verify_farkas_certificate",
    ];

    /// Alias names that appear as additional match arms in dispatch.
    /// Must also be sorted for stable diffs.
    const DISPATCH_ALIASES: &[&str] = &[
        "batchVerifyExternalCert",
        "verifyAletheCertificate",
        "verifyCertificatesBatch",
        "verifyEntailmentCertificate",
        "verifyFarkasCertificate",
    ];

    #[test]
    fn test_registry_has_all_core_methods() {
        let required = [
            "check",
            "prove",
            "getType",
            "batchCheck",
            "serverInfo",
            "getConfig",
            "getMetrics",
            "getCacheMetrics",
        ];
        for method in required {
            assert!(
                is_registered(method),
                "Required method '{}' not in registry",
                method
            );
        }
    }

    #[test]
    fn test_progress_methods_are_batch_methods() {
        for method in METHOD_REGISTRY {
            if method.supports_progress {
                let is_batch_or_long_running = method.name.starts_with("batch")
                    || method.name == "prove"
                    || method.name == "verifyC"
                    || method.name == "searchProof";
                assert!(
                    is_batch_or_long_running,
                    "Method '{}' supports progress but doesn't look like a batch/long-running method",
                    method.name
                );
            }
        }
    }

    #[test]
    fn test_no_duplicate_methods() {
        let mut names: Vec<&str> = METHOD_REGISTRY.iter().map(|m| m.name).collect();
        names.sort();
        let original_len = names.len();
        names.dedup();
        assert_eq!(
            names.len(),
            original_len,
            "Duplicate method names in registry"
        );
    }

    #[test]
    fn test_no_duplicate_aliases() {
        let mut all: Vec<&str> = Vec::new();
        for m in METHOD_REGISTRY {
            all.push(m.name);
            all.extend_from_slice(m.aliases);
        }
        all.sort();
        let original_len = all.len();
        all.dedup();
        assert_eq!(
            all.len(),
            original_len,
            "Duplicate names (canonical or alias) in registry"
        );
    }

    #[test]
    fn test_alias_not_also_canonical() {
        let canonical: std::collections::BTreeSet<&str> =
            METHOD_REGISTRY.iter().map(|m| m.name).collect();
        for m in METHOD_REGISTRY {
            for alias in m.aliases {
                assert!(
                    !canonical.contains(alias),
                    "Alias '{}' is also a canonical method name — aliases must not collide",
                    alias
                );
            }
        }
    }

    #[test]
    fn test_supports_progress_helper() {
        assert!(supports_progress("batchCheck"));
        assert!(supports_progress("batchVerifyCert"));
        assert!(supports_progress("batchGetPremises"));
        assert!(!supports_progress("check"));
        assert!(!supports_progress("serverInfo"));
        assert!(!supports_progress("nonexistent_method"));
    }

    #[test]
    fn test_supports_progress_resolves_aliases() {
        // None of the aliased external-cert methods support progress today,
        // so all should return false. The key property is that the lookup
        // does not panic and correctly resolves through find_method_info().
        for (alias, _canonical) in all_aliases() {
            // Should return a definite answer (not panic), matching canonical behavior
            let alias_result = supports_progress(alias);
            let canonical_result = supports_progress(_canonical);
            assert_eq!(
                alias_result, canonical_result,
                "supports_progress('{}') = {} but supports_progress('{}') = {}",
                alias, alias_result, _canonical, canonical_result
            );
        }
    }

    #[test]
    fn test_all_method_names_returns_all() {
        let names = all_method_names();
        assert_eq!(names.len(), METHOD_REGISTRY.len());
    }

    #[test]
    fn test_all_method_names_excludes_aliases() {
        let names = all_method_names();
        for (alias, _) in all_aliases() {
            assert!(
                !names.contains(&alias.to_string()),
                "all_method_names() should NOT include alias '{}'",
                alias
            );
        }
    }

    #[test]
    fn test_progress_methods_count() {
        let progress = progress_methods();
        assert_eq!(
            progress.len(),
            8,
            "Expected 8 progress-supporting methods, got {}: {:?}",
            progress.len(),
            progress
        );
    }

    #[test]
    fn test_is_batch_safe_helper() {
        assert!(is_batch_safe("batchCheck"));
        assert!(is_batch_safe("prove"));
        assert!(is_batch_safe("verifyC"));
        assert!(is_batch_safe("verify_alethe_certificate"));
        assert!(is_batch_safe("verify_farkas_certificate"));
        assert!(is_batch_safe("verify_entailment_certificate"));
        assert!(is_batch_safe("verify_certificates_batch"));
        assert!(is_batch_safe("check"));
        assert!(is_batch_safe("serverInfo"));
        assert!(is_batch_safe("getType"));
        assert!(!is_batch_safe("nonexistent_method"));
    }

    #[test]
    fn test_is_batch_safe_works_for_aliases() {
        assert!(is_batch_safe("verifyAletheCertificate"));
        assert!(is_batch_safe("verifyFarkasCertificate"));
        assert!(is_batch_safe("verifyEntailmentCertificate"));
        assert!(is_batch_safe("verifyCertificatesBatch"));
        assert!(is_batch_safe("batchVerifyExternalCert"));
    }

    #[test]
    fn test_batch_safe_unknown_method_is_false() {
        assert!(!is_batch_safe("definitelyUnknownMethod"));
    }

    #[test]
    fn test_resolve_canonical() {
        assert_eq!(
            resolve_canonical("verifyAletheCertificate"),
            Some("verify_alethe_certificate")
        );
        assert_eq!(
            resolve_canonical("verifyFarkasCertificate"),
            Some("verify_farkas_certificate")
        );
        assert_eq!(
            resolve_canonical("verifyEntailmentCertificate"),
            Some("verify_entailment_certificate")
        );
        assert_eq!(
            resolve_canonical("verifyCertificatesBatch"),
            Some("verify_certificates_batch")
        );
        assert_eq!(
            resolve_canonical("batchVerifyExternalCert"),
            Some("verify_certificates_batch")
        );
        // Canonical names return None (already canonical)
        assert_eq!(resolve_canonical("verify_farkas_certificate"), None);
        assert_eq!(resolve_canonical("check"), None);
        // Unknown names return None
        assert_eq!(resolve_canonical("unknownMethod"), None);
    }

    #[test]
    fn test_is_known_method() {
        // Canonical names
        assert!(is_known_method("check"));
        assert!(is_known_method("verify_alethe_certificate"));
        assert!(is_known_method("verify_farkas_certificate"));
        // Alias names
        assert!(is_known_method("verifyAletheCertificate"));
        assert!(is_known_method("verifyFarkasCertificate"));
        assert!(is_known_method("batchVerifyExternalCert"));
        // Unknown
        assert!(!is_known_method("unknownMethod"));
    }

    #[test]
    fn test_all_aliases_returns_expected_pairs() {
        let aliases = all_aliases();
        assert_eq!(aliases.len(), 5, "Expected 5 aliases, got: {:?}", aliases);
        assert!(aliases.contains(&("verifyAletheCertificate", "verify_alethe_certificate")));
        assert!(aliases.contains(&("verifyFarkasCertificate", "verify_farkas_certificate")));
        assert!(aliases.contains(&(
            "verifyEntailmentCertificate",
            "verify_entailment_certificate"
        )));
        assert!(aliases.contains(&("verifyCertificatesBatch", "verify_certificates_batch")));
        assert!(aliases.contains(&("batchVerifyExternalCert", "verify_certificates_batch")));
    }

    /// Consistency test: Verify registry contains all expected dispatch methods.
    #[test]
    fn test_registry_dispatch_consistency() {
        for method in DISPATCH_METHODS {
            assert!(
                is_registered(method),
                "Dispatch method '{}' not in registry - add to METHOD_REGISTRY",
                method
            );
        }

        let registry_names: std::collections::BTreeSet<&str> =
            METHOD_REGISTRY.iter().map(|m| m.name).collect();
        let dispatch_set: std::collections::BTreeSet<&str> =
            DISPATCH_METHODS.iter().copied().collect();

        let missing_from_registry: Vec<&str> =
            dispatch_set.difference(&registry_names).copied().collect();
        let extra_in_registry: Vec<&str> =
            registry_names.difference(&dispatch_set).copied().collect();

        assert!(
            missing_from_registry.is_empty(),
            "Dispatch methods missing from registry: {:?}",
            missing_from_registry
        );
        assert!(
            extra_in_registry.is_empty(),
            "Registry methods missing from dispatch list: {:?}",
            extra_in_registry
        );
    }

    /// Verify all DISPATCH_ALIASES are registered as aliases in the registry.
    #[test]
    fn test_registry_alias_dispatch_consistency() {
        let registry_aliases: std::collections::BTreeSet<&str> =
            all_aliases().iter().map(|(alias, _)| *alias).collect();
        let dispatch_alias_set: std::collections::BTreeSet<&str> =
            DISPATCH_ALIASES.iter().copied().collect();

        for alias in DISPATCH_ALIASES {
            assert!(
                is_known_method(alias),
                "Dispatch alias '{}' not recognized by registry - add to aliases in METHOD_REGISTRY",
                alias
            );
        }

        let missing: Vec<&str> = dispatch_alias_set
            .difference(&registry_aliases)
            .copied()
            .collect();
        let extra: Vec<&str> = registry_aliases
            .difference(&dispatch_alias_set)
            .copied()
            .collect();

        assert!(
            missing.is_empty(),
            "Dispatch aliases missing from registry: {:?}",
            missing
        );
        assert!(
            extra.is_empty(),
            "Registry aliases missing from dispatch alias list: {:?}",
            extra
        );
    }

    #[test]
    fn test_dispatch_methods_sorted_unique() {
        let mut sorted = DISPATCH_METHODS.to_vec();
        sorted.sort_unstable();
        assert_eq!(
            DISPATCH_METHODS,
            sorted.as_slice(),
            "DISPATCH_METHODS must be sorted for stable diffs"
        );

        sorted.dedup();
        assert_eq!(
            DISPATCH_METHODS.len(),
            sorted.len(),
            "DISPATCH_METHODS must not contain duplicates"
        );
    }

    #[test]
    fn test_dispatch_aliases_sorted_unique() {
        let mut sorted = DISPATCH_ALIASES.to_vec();
        sorted.sort_unstable();
        assert_eq!(
            DISPATCH_ALIASES,
            sorted.as_slice(),
            "DISPATCH_ALIASES must be sorted for stable diffs"
        );

        sorted.dedup();
        assert_eq!(
            DISPATCH_ALIASES.len(),
            sorted.len(),
            "DISPATCH_ALIASES must not contain duplicates"
        );
    }

    #[test]
    fn test_dispatch_methods_matches_registry_count() {
        assert_eq!(
            DISPATCH_METHODS.len(),
            METHOD_REGISTRY.len(),
            "DISPATCH_METHODS ({}) should match METHOD_REGISTRY ({})",
            DISPATCH_METHODS.len(),
            METHOD_REGISTRY.len()
        );
    }

    #[test]
    fn test_preferred_outcome_field_normalizes_to_verified() {
        let check = METHOD_REGISTRY
            .iter()
            .find(|m| m.name == "check")
            .expect("check method missing");
        assert_eq!(check.preferred_outcome_field(), Some("verified"));
        assert!(check.has_outcome());

        let batch_apply_tactic = METHOD_REGISTRY
            .iter()
            .find(|m| m.name == "batchApplyTactic")
            .expect("batchApplyTactic method missing");
        assert_eq!(
            batch_apply_tactic.preferred_outcome_field(),
            Some("verified")
        );
        assert!(batch_apply_tactic.has_outcome());

        let get_type = METHOD_REGISTRY
            .iter()
            .find(|m| m.name == "getType")
            .expect("getType method missing");
        assert_eq!(get_type.preferred_outcome_field(), None);
        assert!(!get_type.has_outcome());
    }
}
