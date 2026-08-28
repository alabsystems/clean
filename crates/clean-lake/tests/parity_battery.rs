// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! # Lake parity battery — the Lake pillar's pinned, re-runnable measurement
//!
//! A fixed-denominator scenario matrix for the `clean lake` compatibility
//! surface (Lean 4 drop-in roadmap, Lake pillar; row proposal: pillar audit
//! 2026-08-21, wf_484081ec journal). Every row runs ENTIRELY in-process
//! against micro-fixtures the harness materializes in a per-test tempdir.
//! No network is ever touched: "git dependencies" are local repositories the
//! harness creates and commits itself, cloned over the filesystem.
//!
//! ## Battery contract
//!
//! - **Rows are PINNED.** Each row asserts the EXACT outcome (built/skipped/
//!   failed sets, artifact paths, error variants, message fragments) measured
//!   when the row landed. A row failing means the pinned behavior moved — that
//!   is the battery doing its job, not noise to be silenced.
//! - **Adding rows is always fine.** New capability gets a new pinned row.
//! - **Weakening or deleting a row needs the same justification as changing a
//!   ratchet baseline** (see `data/unchecked_decl_ratchet.json` policy): a
//!   written rationale in the commit that touches the row, naming what
//!   regressed or why the pinned behavior was wrong.
//! - **GAP rows pin today's honest shortfall** (e.g. clean-lake emits no
//!   native executable; the portable `run` verb still requires
//!   `lakefile.lean`). When the capability lands, the gap row FAILS — upgrade
//!   it to assert the new, stronger behavior. Never delete it silently.
//!
//! ## Row families
//!
//! | Row | Scenario |
//! |-----|----------|
//! | 01  | `lakefile.toml` lib build emits the `.olean` triple and round-trips |
//! | 02  | `lakefile.toml` exe builds its root module; portable-run gap pinned |
//! | 03  | `lakefile.lean` lib+exe build; run reports the native gap honestly |
//! | 04  | path require: cross-package `rfl` THROUGH the dep value |
//! | 05  | git require chain A→B→C: manifest v7 pinned, closure loaded |
//! | 06  | scope-only (Reservoir) require normalization + two override rows |
//! | 07  | incremental no-op rebuild: 0 built, N skipped |
//! | 08  | fail-closed missing dep: no manifest / name absent from manifest |
//! | 09  | missing stdlib import fails closed; `--permissive-imports` opt-out |
//! | 10  | `lake init` lib template builds (toolchain + scaffold pinned) |
//! | 11  | `lake init` exe template builds (scaffold content pinned) |
//! | 12  | strict-lakefile rejection of an unmodeled top-level construct |
//! | 13  | `lake test` without test targets errors honestly |
//! | 14  | `lake test` with a target builds and reports the missing driver |
//! | 15  | workspace-owned modules shadow the stdlib name prefixes |
//! | 16  | native module-name build: `.olean` kernel-verified, no toolchain spawn |
//!
//! The rows themselves live in `parity_battery/rows_01_07.rs`,
//! `parity_battery/rows_08_14.rs`, `parity_battery/rows_15.rs` and
//! `parity_battery/rows_16.rs`, over the shared harness in
//! `parity_battery/common.rs`; this file is the target root that binds them
//! into one test binary.

// An integration-test crate ROOT resolves `mod` against `tests/`, not against a
// same-named directory, so each child module names its path explicitly.
#[path = "parity_battery/common.rs"]
mod common;
#[path = "parity_battery/rows_01_07.rs"]
mod rows_01_07;
#[path = "parity_battery/rows_08_14.rs"]
mod rows_08_14;
#[path = "parity_battery/rows_15.rs"]
mod rows_15;
#[path = "parity_battery/rows_16.rs"]
mod rows_16;
