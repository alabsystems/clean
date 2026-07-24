// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Boxing pass configuration.

pub(crate) const CLOSURE_MAX_ARGS: usize = 8;

/// Configuration for the explicit boxing pass.
///
/// Controls which optimizations are enabled during boxing transformation.
///
/// # Default Behavior
///
/// `BoxingConfig::default()` and `BoxingConfig::new()` both enable all optimizations.
/// Use `BoxingConfig::minimal()` to disable all optimizations.
#[derive(Debug, Clone)]
pub struct BoxingConfig {
    /// Enable expensive constant boxing optimization.
    ///
    /// When true, constants that would be boxed repeatedly (like large integers)
    /// are boxed once in an auxiliary declaration and referenced thereafter.
    pub optimize_expensive_constants: bool,
    /// Generate boxed wrapper versions of declarations with scalar params/return.
    ///
    /// When true, declarations requiring boxed versions for partial application
    /// will have wrapper declarations generated.
    pub generate_boxed_versions: bool,
}

impl Default for BoxingConfig {
    fn default() -> Self {
        Self::new()
    }
}

impl BoxingConfig {
    /// Create a new config with all optimizations enabled.
    ///
    /// This is the recommended default for production use.
    pub fn new() -> Self {
        Self {
            optimize_expensive_constants: true,
            generate_boxed_versions: true,
        }
    }

    /// Create a minimal config with no optimizations.
    ///
    /// Useful for testing or when you want raw boxing without optimizations.
    pub fn minimal() -> Self {
        Self {
            optimize_expensive_constants: false,
            generate_boxed_versions: false,
        }
    }
}
