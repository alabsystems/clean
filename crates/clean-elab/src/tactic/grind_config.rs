// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Configuration for the `grind` tactic.
//!
//! Extracted from `grind.rs` to respect the 500-line file limit.

/// Configuration for the `grind` tactic.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct GrindConfig {
    /// Maximum recursive depth for case-splitting (default: 8).
    pub max_depth: usize,
    /// Maximum number of case splits allowed (default: 32).
    pub max_splits: usize,
    /// Whether to run `simp` as a preprocessing step (default: true).
    pub use_simp: bool,
    /// Whether to use congruence closure (default: true).
    pub use_cc: bool,
    /// Whether to attempt case splitting on disjunctions (default: true).
    pub split_disjunctions: bool,
    /// Whether to attempt case splitting on if-then-else (default: true).
    pub split_ite: bool,
    /// Whether to try `tauto` as a closer (default: true).
    pub use_tauto: bool,
    /// Maximum iterations for the CC engine per invocation (default: 1000).
    pub cc_max_iterations: usize,
    /// Maximum simp steps per invocation (default: 200).
    pub simp_max_steps: usize,
    /// Depth limit for solve_by_elim within grind (default: 3).
    pub solve_by_elim_depth: usize,
    /// Whether to try the clean-auto automation engine (SMT + superposition)
    /// as a closer before case splitting (default: true).
    pub use_automation: bool,
    /// Whether to try mathverse and decide as arithmetic closers (default: true).
    pub use_arithmetic_closers: bool,
    /// Timeout in milliseconds for the automation engine (default: 100).
    pub automation_timeout_ms: u64,
}

impl Default for GrindConfig {
    fn default() -> Self {
        Self {
            max_depth: 8,
            max_splits: 32,
            use_simp: true,
            use_cc: true,
            split_disjunctions: true,
            split_ite: true,
            use_tauto: true,
            cc_max_iterations: 1000,
            simp_max_steps: 200,
            solve_by_elim_depth: 3,
            use_automation: true,
            use_arithmetic_closers: true,
            automation_timeout_ms: 100,
        }
    }
}

impl GrindConfig {
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    #[must_use]
    pub fn with_max_depth(mut self, depth: usize) -> Self {
        self.max_depth = depth;
        self
    }

    #[must_use]
    pub fn with_max_splits(mut self, splits: usize) -> Self {
        self.max_splits = splits;
        self
    }

    #[must_use]
    pub fn with_use_simp(mut self, enabled: bool) -> Self {
        self.use_simp = enabled;
        self
    }

    #[must_use]
    pub fn with_use_cc(mut self, enabled: bool) -> Self {
        self.use_cc = enabled;
        self
    }

    #[must_use]
    pub fn with_use_tauto(mut self, enabled: bool) -> Self {
        self.use_tauto = enabled;
        self
    }

    #[must_use]
    pub fn with_solve_by_elim_depth(mut self, depth: usize) -> Self {
        self.solve_by_elim_depth = depth;
        self
    }

    #[must_use]
    pub fn with_use_automation(mut self, enabled: bool) -> Self {
        self.use_automation = enabled;
        self
    }

    #[must_use]
    pub fn with_use_arithmetic_closers(mut self, enabled: bool) -> Self {
        self.use_arithmetic_closers = enabled;
        self
    }

    #[must_use]
    pub fn with_automation_timeout_ms(mut self, ms: u64) -> Self {
        self.automation_timeout_ms = ms;
        self
    }
}
