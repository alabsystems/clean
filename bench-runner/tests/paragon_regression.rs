// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

// Compile + run the REAL `#[cfg(test)] #[test]` regression target in the
// worktree. The durable artifact lives at
// `crates/clean-cli/tests/paragon_integration_bench.rs`, where it LINKS for a
// normal (non-worktree) checkout. Here it is `include!`d into a standalone,
// trust-ir-free workspace so the exact same test target is compiled with
// `cfg(test)` active and executed via `cargo test`, even inside a worktree
// (where the full-workspace lockfile collides on `clean-kernel`).
//
// This is what guards against the "agent harness builds can hide a broken test
// target" failure mode: the `#[test] fn paragon_integration_bench_regression`
// in the included file becomes an active test here and must compile + pass.
//
// `#![allow(dead_code)]` because the included file also defines binary-only
// helpers (`run_one`, `Outcome::from_token`/`token`) that the subprocess runner
// uses but this in-process test path does not.
#![allow(dead_code)]

include!("../../crates/clean-cli/tests/paragon_integration_bench.rs");
