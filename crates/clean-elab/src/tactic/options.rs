// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Proof options and set_option tactic
//!
//! This module provides configuration types for local proof options
//! and the `set_option` tactic for modifying them.

use crate::tactic::{ProofState, TacticError, TacticResult};

/// Set option value types
#[derive(Debug, Clone)]
pub enum OptionValue {
    Bool(bool),
    Nat(u64),
    String(String),
}

/// Configuration for set_option
#[derive(Debug, Clone, Default)]
#[non_exhaustive]
pub struct SetOptionConfig {
    /// Options to set (key -> value)
    pub options: Vec<(String, OptionValue)>,
}

impl SetOptionConfig {
    /// ENSURES: Returns a config with an empty options list.
    pub fn new() -> Self {
        Self::default()
    }

    /// ENSURES: Appends a `Bool` option entry; returns `self` for chaining.
    #[must_use]
    pub fn set_bool(mut self, key: &str, value: bool) -> Self {
        self.options
            .push((key.to_string(), OptionValue::Bool(value)));
        self
    }

    /// ENSURES: Appends a `Nat` option entry; returns `self` for chaining.
    #[must_use]
    pub fn set_nat(mut self, key: &str, value: u64) -> Self {
        self.options
            .push((key.to_string(), OptionValue::Nat(value)));
        self
    }

    /// ENSURES: Appends a `String` option entry; returns `self` for chaining.
    #[must_use]
    pub fn set_string(mut self, key: &str, value: &str) -> Self {
        self.options
            .push((key.to_string(), OptionValue::String(value.to_string())));
        self
    }
}

/// Local proof state options that can be modified
#[derive(Debug, Clone, Default)]
#[non_exhaustive]
pub struct ProofOptions {
    /// Enable verbose output when explicitly overridden.
    verbose: Option<bool>,
    /// Maximum recursion depth override for tactics that honor `max_depth`.
    max_depth: Option<u64>,
    /// Enable tracing when explicitly overridden.
    trace: Option<bool>,
    /// Timeout override in milliseconds (`Some(0)` = disable timeout).
    timeout_ms: Option<u64>,
    /// Enable profiling when explicitly overridden.
    profile: Option<bool>,
}

impl ProofOptions {
    /// Effective verbose flag for UI/tests.
    #[must_use]
    pub fn is_verbose(&self) -> bool {
        self.verbose_override().unwrap_or(false)
    }

    /// Effective max-depth value after projecting onto tactic search APIs.
    #[must_use]
    pub fn max_depth(&self) -> u64 {
        self.max_depth_override()
            .map(|depth| depth as u64)
            .unwrap_or(100)
    }

    /// Effective trace flag for UI/tests.
    #[must_use]
    pub fn is_trace(&self) -> bool {
        self.trace.unwrap_or(false)
    }

    /// Effective timeout value for UI/tests (`0` = no timeout override).
    #[must_use]
    pub fn timeout_ms(&self) -> u64 {
        self.timeout_ms.unwrap_or(0)
    }

    /// Effective profiling flag for UI/tests.
    #[must_use]
    pub fn is_profile(&self) -> bool {
        self.profile.unwrap_or(false)
    }

    /// Explicit max-depth override for tactics that otherwise keep their defaults.
    #[must_use]
    pub(crate) fn max_depth_override(&self) -> Option<usize> {
        self.max_depth
            .map(|depth| usize::try_from(depth).unwrap_or(usize::MAX))
    }

    /// Explicit verbose override for tactics that support it.
    #[must_use]
    pub(crate) fn verbose_override(&self) -> Option<bool> {
        self.verbose
    }
}

/// Tactic: set_option
///
/// Sets a local option for the current proof. Options affect tactic
/// behavior within the current proof scope.
///
/// Common options:
/// - `verbose`: Enable verbose output from tactics
/// - `max_depth`: Maximum recursion depth for search tactics
/// - `trace`: Enable trace output for debugging
/// - `timeout_ms`: Set timeout for tactics in milliseconds
///
/// # Example
/// ```text
/// set_option verbose true
/// simp  -- Now shows verbose output
/// ```
///
/// Note: This is a "meta" tactic that doesn't change the proof state
/// goals, only the configuration.
///
/// # Errors
/// - `Other` if the option name is not recognized
///
/// REQUIRES: `key` is one of the recognized option names (verbose, max_depth,
///   trace, timeout_ms, profile).
/// ENSURES: On `Ok`, the option is validated (no proof state goals are modified).
/// ENSURES: On `Err(InvalidTarget)`, `key` is not a recognized option name.
pub fn set_option(state: &mut ProofState, key: &str, value: OptionValue) -> TacticResult {
    let opts = state.options_mut();
    match key {
        "verbose" => match value {
            OptionValue::Bool(v) => opts.verbose = Some(v),
            _ => {
                return Err(TacticError::InvalidTarget {
                    tactic: "set_option".into(),
                    detail: "option 'verbose' expects a Bool value".into(),
                })
            }
        },
        "max_depth" => match value {
            OptionValue::Nat(v) => opts.max_depth = Some(v),
            _ => {
                return Err(TacticError::InvalidTarget {
                    tactic: "set_option".into(),
                    detail: "option 'max_depth' expects a Nat value".into(),
                })
            }
        },
        "trace" => match value {
            OptionValue::Bool(v) => opts.trace = Some(v),
            _ => {
                return Err(TacticError::InvalidTarget {
                    tactic: "set_option".into(),
                    detail: "option 'trace' expects a Bool value".into(),
                })
            }
        },
        "timeout_ms" => match value {
            OptionValue::Nat(v) => opts.timeout_ms = Some(v),
            _ => {
                return Err(TacticError::InvalidTarget {
                    tactic: "set_option".into(),
                    detail: "option 'timeout_ms' expects a Nat value".into(),
                })
            }
        },
        "profile" => match value {
            OptionValue::Bool(v) => opts.profile = Some(v),
            _ => {
                return Err(TacticError::InvalidTarget {
                    tactic: "set_option".into(),
                    detail: "option 'profile' expects a Bool value".into(),
                })
            }
        },
        _ => {
            return Err(TacticError::InvalidTarget {
                tactic: "set_option".into(),
                detail: format!(
                    "unknown option '{key}'. Valid options: [\"verbose\", \"max_depth\", \"trace\", \"timeout_ms\", \"profile\"]"
                ),
            })
        }
    }
    Ok(())
}

/// set_option with builder-style config
///
/// REQUIRES: All keys in `config.options` are recognized option names.
/// ENSURES: On `Ok`, all options are applied in order.
/// ENSURES: On `Err`, processing stops at the first unrecognized key.
pub fn set_options(state: &mut ProofState, config: SetOptionConfig) -> TacticResult {
    for (key, value) in config.options {
        set_option(state, &key, value)?;
    }
    Ok(())
}
