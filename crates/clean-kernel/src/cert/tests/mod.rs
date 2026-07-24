// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Certificate test modules
//!
//! Tests are split by functionality for maintainability:
//! - core: Basic certificate verification
//! - equality: Definitional and structural equality
//! - compression: LZ4/ZSTD compression and archives
//! - streaming: Streaming certificate I/O
//! - batch: Batch verification
//! - replay: Certificate replay
//! - dict: Dictionary compression
//! - serialization: JSON/bincode serialization
//! - extensions: Cubical, classical, ZFC mode tests

mod batch;
mod batch_build;
mod batch_runner;
mod batch_verify_contracts;
mod builder_core;
mod builder_equality;
mod builder_whnf_cache;
mod classical;
mod compression;
mod core;
mod cross_project;
mod cubical;
mod dict;
mod equality;
mod metadata;
mod replay;
mod serialization;
mod source_hygiene;
mod stack_safe;
mod streaming;
mod verifier;
mod verifier_extended;
mod whnf;
mod zfc;
