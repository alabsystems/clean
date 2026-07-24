// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! NN verification certificate import for the Mathverse Library.
//!
//! Parses certificates from NN verification tools (gamma-crown, alpha-beta-CROWN)
//! and writes them to `.mathverse` shards with proper trust tagging
//! (`FLOAT_APPROX | NN_ABSTRACTION`).
//!
//! MVP scope: gamma-crown JSON certificate format.

pub mod gamma_crown;
pub mod shard_writer;
pub mod types;
