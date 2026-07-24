// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

// Compile + run the search-robustness regression tests in the worktree. The
// durable artifact lives at `crates/clean-cli/tests/auto_search_robustness.rs`,
// where it LINKS for a normal (non-worktree) checkout and runs as
// `cargo test -p clean-cli`. Here it is `include!`d into this standalone,
// trust-ir-free workspace so the same `#[test]`s compile + run via `cargo test`
// even inside a worktree (where the full-workspace lockfile collides on
// `clean-kernel`). This guards against the "agent harness builds can hide a
// broken test target" failure mode.

include!("../../crates/clean-cli/tests/auto_search_robustness.rs");
