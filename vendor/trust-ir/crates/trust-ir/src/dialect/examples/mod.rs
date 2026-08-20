// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Example dialect helper modules shipped inside `trust-ir` for documentation,
//! tests, and prototyping.
//!
//! All example dialects are gated behind the `dialect-verif-example` feature
//! (or `cfg(test)`) so they never appear in production builds unless a
//! consumer opts in. The serialized `verif.*` payload contract is broader than
//! this Rust helper module: TrustIr opts in to the helpers directly, while other
//! consumers may rely only on the op names / payload shape.

pub mod verif;

pub use verif::{
    BFS_STEP, FINGERPRINT_BATCH, FRONTIER_DRAIN, VerifDialect, bfs_step, fingerprint_batch,
    frontier_drain,
};
