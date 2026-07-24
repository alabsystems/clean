// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

pub(super) fn run(conjecture: String, allow_empty: bool) -> anyhow::Result<()> {
    clean_kernel::cli::run_verify_constructive_claims(&conjecture, allow_empty)
}
