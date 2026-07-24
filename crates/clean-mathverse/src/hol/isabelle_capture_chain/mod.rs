// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Self-healing Isabelle capture-chain driver (`clean mathverse
//! isabelle-capture-chain`).
//!
//! Mechanizes the three manual interventions the Lib3 backfill needed, turning
//! a night of hand-babysitting `isabelle build` into one typed, resumable
//! command:
//!
//! 1. **Concurrent `record_proofs` elaboration blows the ~16 GB Poly/ML
//!    arm64_32 store** → retry the segment at `threads=1` (serialize the
//!    per-process RSS).
//! 2. **A single theory blows the store even serialized** (HOL-Library.Interval's
//!    line-567 `by` proof) → isolate it and bake it *proofless*
//!    (`record_proofs=2`: zproof recording OFF, ~48 s heap bake), so the chain
//!    and downstream umbrellas never re-elaborate it under recording.
//! 3. **Heap saves must be `-b` per segment** or successors rebuild predecessors
//!    → every segment builds with `-b`, on the previous segment's saved heap.
//!
//! The [`spec`] is the source of truth: an ordered list of chained segments plus
//! global build options. ROOT files are GENERATED from it (never the reverse).
//! The [`driver`] loop shells `isabelle build` out through the injected
//! [`runner::IsabelleBuildRunner`] (so the whole self-healing state machine is
//! testable without a live toolchain), classifies each outcome, and walks the
//! [`ladder`] response ladder on an out-of-store failure:
//! `retry-threads1 → bisect → proofless`. Durable [`state`] is persisted after
//! every transition so `--resume` continues exactly where a crash or halt left
//! off, and never retries a rung it already exhausted.
//!
//! The process runner is the ONLY impure part — `isabelle build` cannot be pure
//! Rust. Everything else (spec parse/validate, ROOT generation, OOM-line
//! parsing, the bisect split, the ladder state machine, resume) is deterministic
//! and unit-tested.

pub mod collect;
pub mod driver;
pub mod error;
pub mod ladder;
pub mod root_gen;
pub mod runner;
pub mod spec;
pub mod state;

#[cfg(test)]
mod tests_driver;

pub use driver::{run_capture_chain, CaptureSummary, RunOptions};
pub use error::CaptureChainError;
pub use runner::{
    classify, BuildInvocation, BuildOutcome, BuildRun, IsabelleBuildRunner, SystemBuildRunner,
};
pub use spec::{ChainSpec, CollectSpec, Segment};
pub use state::{ChainState, SegStatus, SegmentState};
