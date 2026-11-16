// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! TLAPS benchmark runner (absorbed from the former `clean-tlaps-bench`
//! crate; rearch stage 9 facade consolidation).
//!
//! Runs benchmarks on TLAPS proof obligations.
//!
//! ## Architecture
//!
//! The benchmark library uses a pluggable backend system:
//!
//! ```text
//! ┌─────────────────┐     ┌────────────────────┐
//! │ BenchmarkRunner │────▶│ ProofBackend trait │
//! └─────────────────┘     └────────────────────┘
//! ```
//!
//! Backends implement the `ProofBackend` trait to provide different
//! proof strategies (native tactics, SMT, etc.).

pub mod backend;
pub mod bench_compare;
#[cfg(feature = "cli")]
pub mod cli;
pub mod runner;
pub mod schema;

pub use backend::{
    BackendRegistry, NativeTacticBackend, ProofBackend, ProofContext, ProofOutcome,
    TlapsProofResult,
};
pub use bench_compare::{
    build_benchmark_report, classify_benchmark_ns_maps, classify_benchmarks,
    normalize_benchmark_ns_map, BenchChange, BenchComparison, BenchReport, BenchReportMetadata,
    BenchReportSummary, BenchSample, NewBenchmark,
};
pub use runner::{BenchmarkResult, BenchmarkRunner, BenchmarkSummary, CategoryStats};
pub use schema::BenchmarkObligation;
