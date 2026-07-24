// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Incremental Certificate Builder with Fail-Fast Verification
//!
//! This module provides `CertBuilder`, a builder that verifies each certificate
//! node as it's added, enabling early failure detection without building
//! complete certificates for invalid proofs.
//!
//! ## Design Reference
//!
//! See `designs/2026-01-28-incremental-cert-verification.md` for full design.
//! Module split per `designs/2026-03-10-2485-cert-builder-equality-extraction-and-module-split.md`.

pub mod cache;
mod construct;
mod reduction;
mod reify;
mod state;

pub use cache::WhnfCache;
pub(crate) use state::BuildNode;
pub use state::{BuildResult, CertBuilder, NodeId};

#[cfg(test)]
mod tests;
