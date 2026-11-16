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

pub mod artifact_binding;
pub mod build;
pub mod build_trace;
pub mod cli;
pub mod config;
pub mod error;
pub mod fetch;
pub mod glob;
pub(crate) mod interpolate;
pub mod manifest;
mod module_options;
mod module_world;
#[cfg(test)]
mod test_env;
pub mod toml_config;
pub mod workspace;

pub use artifact_binding::{ImportAdmissionFindings, ImportAdmitter};
pub use build::{
    BuildContext, BuildOptions, BuildResult, FreshModuleArtifacts, CLEAN_OLEAN_GIT_HASH,
};
pub use cli::DEFAULT_CLEAN_TOOLCHAIN;
pub use config::{
    LakeConfig, LakeScript, LakefileParseMode, LeanExe, LeanLib, LeanOption, LeanOptionValue,
    LeanTest, PackageConfig, SkippedConstruct,
};
pub use error::{LakeError, LakeResult};
pub use fetch::{FetchManager, ResolveResult, ResolvedPackage, UpdateResult, UpdateStatus};
pub use glob::{parse_globs, GlobKind, ModuleGlob};
pub use manifest::{GitPackage, LakeManifest, ManifestPackage, PathPackage};
pub use workspace::Workspace;
