// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Test-only support compiled under `cfg(any(test, feature = "test-support"))`.
//!
//! Integration tests reach it through the crate's self dev-dependency
//! (`clean-olean = { path = ".", features = ["test-support"] }` in
//! `Cargo.toml`), unit tests through `crate::test_support`. Nothing here is
//! part of the library's public contract; a production dependency edge must
//! never enable the feature.
//!
//! `reducer_differential` is the battery behind the Lean kernel-theory
//! profile's reducer allowlist (`crates/clean-olean/tests/lean_profile_reducer_differential.rs`).
//!
//! The surface is exactly what consumers import — derived 2026-09-15 with
//! `grep -rn "test_support::" crates`: `compiled_fixture_dir` (every
//! consumer), `run_oracle` (`runtime_declarations`, `bvar_tests`,
//! `parsed_name_tests`, `instance_metadata_tests`,
//! `companion_extension_tests`, `clean-compiler`'s `runtime_lcnf` tests),
//! `fixture_root` (`typed_import_identity`, reading `typed_names/CONSTANTS`)
//! and `PINNED_LEAN_REQUIRED` (`clean-compiler`'s own `.expect`). The
//! implementing module is private; its internals (order parsing, the cache
//! key, the recipe version) are reachable only from its own tests.

mod pinned_lean;
pub mod reducer_differential;

pub use pinned_lean::{compiled_fixture_dir, fixture_root, run_oracle, PINNED_LEAN_REQUIRED};
