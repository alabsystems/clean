// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Lake CLI command definitions and handlers.
//!
//! Provides the command enum and dispatch logic for Lake CLI operations.
//! The binary crate (clean-cli) wires these to clap; this module provides
//! the portable command types and handler implementations.
//!
//! Phase 2 of Epic #3436 moves the clap subcommand tree and descriptor array
//! for `lake` into this crate. See [`clap_args`] for the clap surface and
//! [`features::FEATURES`] for the `FeatureDescriptor` array consumed by
//! `clean features`, `clean help`, and the coverage gate in
//! `crates/clean-cli/tests/feature_coverage.rs`.
//!
//! Handlers for each [`LakeCommand`] variant live in [`dispatch`]; this file
//! is kept type-and-glue-only so the 500-LoC per-file cap is comfortably met.

mod clap_args;
mod dispatch;
mod features;
mod features_ext;
mod features_refs;
pub(crate) mod toolchain;

pub use clap_args::{CacheCommands, LakeArgs, LakeCommands, ScriptCommands};
pub use dispatch::run_lake;
pub use features::FEATURES;
pub use toolchain::DEFAULT_CLEAN_TOOLCHAIN;

use std::path::PathBuf;

/// Lake CLI subcommands
#[derive(Debug, Clone)]
#[non_exhaustive]
pub enum LakeCommand {
    /// Build the project
    Build(BuildArgs),
    /// Remove build artifacts
    Clean(CleanArgs),
    /// Create a new Lake project
    Init(InitArgs),
    /// Prefetch dependency sources without modifying the manifest
    Fetch(FetchArgs),
    /// Build an executable target and locate the produced binary
    Run(RunArgs),
    /// Locate (without rebuilding) a named executable target's binary
    Exe(ExeArgs),
    /// Build the package test targets and locate the produced test binaries
    Test(TestArgs),
    /// Print the resolved Lake environment as `key=value` lines
    Env(EnvArgs),
    /// Update dependencies to latest revisions
    Update(UpdateArgs),
}

/// Arguments for `lake build`
#[derive(Debug, Clone, Default)]
#[non_exhaustive]
pub struct BuildArgs {
    /// Project directory (defaults to current directory)
    pub dir: Option<PathBuf>,
    /// Number of parallel jobs (0 = auto-detect)
    pub jobs: usize,
    /// Print verbose output
    pub verbose: bool,
    /// Force rebuild all modules
    pub force: bool,
    /// Only type-check, skip code generation
    pub check_only: bool,
    /// Warn and continue when a stdlib/local-dep `.olean` import fails to load
    /// (fail-closed default: such failures fail the module build)
    pub permissive_imports: bool,
}

/// Arguments for `lake clean`
#[derive(Debug, Clone, Default)]
#[non_exhaustive]
pub struct CleanArgs {
    /// Project directory (defaults to current directory)
    pub dir: Option<PathBuf>,
}

/// Arguments for `lake init`
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct InitArgs {
    /// Directory in which to create the project
    pub dir: Option<PathBuf>,
    /// Package name
    pub name: String,
    /// Create a library (true) or executable (false) project
    pub lib: bool,
}

impl InitArgs {
    /// Arguments for initializing a LIBRARY project.
    ///
    /// `InitArgs` is `#[non_exhaustive]`, so callers outside this crate
    /// (including the crate's own integration tests, e.g. the Lake parity
    /// battery in `tests/parity_battery.rs`) have no struct-literal syntax
    /// for it; these named constructors are the supported way in. Two named
    /// constructors instead of one taking `lib: bool`, per the org
    /// bool-parameter rule.
    #[must_use]
    pub fn lib_project(dir: Option<PathBuf>, name: impl Into<String>) -> Self {
        Self {
            dir,
            name: name.into(),
            lib: true,
        }
    }

    /// Arguments for initializing an EXECUTABLE project (root `Main.lean`).
    #[must_use]
    pub fn exe_project(dir: Option<PathBuf>, name: impl Into<String>) -> Self {
        Self {
            dir,
            name: name.into(),
            lib: false,
        }
    }
}

/// Arguments for `lake fetch`
#[derive(Debug, Clone, Default)]
#[non_exhaustive]
pub struct FetchArgs {
    /// Project directory (defaults to current directory)
    pub dir: Option<PathBuf>,
}

/// Arguments for `lake run`
#[derive(Debug, Clone, Default)]
#[non_exhaustive]
pub struct RunArgs {
    /// Project directory (defaults to current directory)
    pub dir: Option<PathBuf>,
    /// Executable target to build and run (defaults to the sole/default target)
    pub target: Option<String>,
    /// Arguments forwarded to the produced executable
    pub args: Vec<String>,
    /// Number of parallel jobs (0 = auto-detect)
    pub jobs: usize,
    /// Print verbose output
    pub verbose: bool,
}

/// Arguments for `lake exe`
#[derive(Debug, Clone, Default)]
#[non_exhaustive]
pub struct ExeArgs {
    /// Project directory (defaults to current directory)
    pub dir: Option<PathBuf>,
    /// Executable target name to locate and run
    pub name: String,
    /// Arguments forwarded to the produced executable
    pub args: Vec<String>,
    /// Print verbose output
    pub verbose: bool,
}

/// Arguments for `lake test`
#[derive(Debug, Clone, Default)]
#[non_exhaustive]
pub struct TestArgs {
    /// Project directory (defaults to current directory)
    pub dir: Option<PathBuf>,
    /// Test target name or substring filter (defaults to all test targets)
    pub target: Option<String>,
    /// Arguments forwarded to the produced test executable(s)
    pub args: Vec<String>,
    /// Number of parallel jobs (0 = auto-detect)
    pub jobs: usize,
    /// Print verbose output
    pub verbose: bool,
}

/// Arguments for `lake env`
#[derive(Debug, Clone, Default)]
#[non_exhaustive]
pub struct EnvArgs {
    /// Project directory (defaults to current directory)
    pub dir: Option<PathBuf>,
}

/// Arguments for `lake update`
#[derive(Debug, Clone, Default)]
#[non_exhaustive]
pub struct UpdateArgs {
    /// Project directory (defaults to current directory)
    pub dir: Option<PathBuf>,
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests;
