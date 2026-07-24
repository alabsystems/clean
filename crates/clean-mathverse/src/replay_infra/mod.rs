// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **Lane-agnostic replay infrastructure** — the reusable cores extracted from
//! the Isabelle/HOL kernel-verification campaign so every import lane (Coq,
//! Lean, …) can share them:
//!
//! - [`targets`] — the blocking-weight *frontier arithmetic* (which rejected
//!   items gate the most downstream cascade), generic over an opaque item id.
//!   The Isabelle targeter (`crate::hol::isabelle_targets`) delegates its inner
//!   loop here with byte-identical results; [`coq_targets`] is the second adapter.
//! - [`ledger`] — the [`VerdictSource`](ledger::VerdictSource) read-side contract
//!   (accepted set + rejection reasons) that both the Isabelle snapshot and the
//!   Coq `kernel-verified.json` manifest satisfy.
//! - [`coq_targets`] — the Coq adapter: builds a reject subgraph from the Coq
//!   lane's `.mathverse` shards + `kernel-verified.json`, and ranks its
//!   gatekeepers. Reads Coq OUTPUT formats only; touches no `coq/**` driver code.
//!
//! See `docs/analysis/replay-infra-lanes.md` for the full adapter contract and
//! the one-function integration step the Coq lane adds when it opts in to
//! incremental retry.

pub mod coq_targets;
pub mod ledger;
pub mod targets;
