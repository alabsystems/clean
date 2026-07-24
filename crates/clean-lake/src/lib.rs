// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Lake build system for clean
//!
//! This crate implements Lake, Lean 4's package manager and build system.
//! It provides:
//!
//! - lakefile.lean parsing
//! - lake-manifest.json parsing
//! - Incremental compilation
//! - Dependency management
//! - Parallel builds

pub mod build;
pub mod cli;
pub mod config;
pub mod error;
pub mod fetch;
pub mod glob;
pub(crate) mod interpolate;
pub mod manifest;
#[cfg(test)]
mod test_env;
pub mod toml_config;
pub mod workspace;

pub use build::{BuildContext, BuildOptions, BuildResult};
pub use config::{LakeConfig, LakeScript, LeanExe, LeanLib, LeanTest, PackageConfig};
pub use error::{LakeError, LakeResult};
pub use fetch::{FetchManager, ResolveResult, ResolvedPackage, UpdateResult, UpdateStatus};
pub use glob::{parse_globs, GlobKind, ModuleGlob};
pub use manifest::{GitPackage, LakeManifest, ManifestPackage, PathPackage};
pub use workspace::Workspace;
