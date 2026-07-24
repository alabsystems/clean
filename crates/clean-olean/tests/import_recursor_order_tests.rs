// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Regression tests for RecursorArgOrder assignment in the olean loader.
//!
//! Validates that olean-loaded recursors get the same arg_order as the kernel
//! builder (inductive_builder.rs). Requires a Lean 4 installation via elan.
//!
//! Part of #1790

use clean_kernel::env::Environment;
use clean_kernel::inductive::RecursorArgOrder;
use clean_kernel::name::Name;
use clean_olean::{default_search_paths, load_module_with_deps};

fn get_lean_lib_path() -> Option<std::path::PathBuf> {
    default_search_paths()
        .into_iter()
        .find(|p| p.join("Init/Prelude.olean").exists())
}

/// Gate this file's integration tests behind `CLEAN_OLEAN_INTEGRATION=1`.
/// They load real `.olean` files against the installed Lean toolchain; on
/// machines with a non-matching toolchain they surface compiler-name and
/// inductive-flag differences that reflect Lean version drift rather than
/// real bugs in the import pipeline. Opt in via the env var when running
/// the dedicated integration lane.
fn require_olean_lean() -> Option<std::path::PathBuf> {
    if std::env::var_os("CLEAN_OLEAN_INTEGRATION").is_none() {
        eprintln!(
            "TRACE: olean integration test skipped \u{2014} set \
             CLEAN_OLEAN_INTEGRATION=1 to run against the installed \
             Lean toolchain"
        );
        return None;
    }
    get_lean_lib_path()
}

/// Regression test for #1790, updated for the Lean-faithful casesOn layout:
/// a casesOn registered in the recursor table must use MajorAfterMotive
/// (major premise right after the motive, before the minors — same as recOn
/// and the same telescope Lean's own casesOn Definitions spell), while rec
/// keeps MajorAfterMinors.
#[test]
fn test_olean_cases_on_arg_order_matches_builder() {
    let Some(lib_path) = require_olean_lean() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };

    let mut env = Environment::default();
    let _ = load_module_with_deps(&mut env, "Init.Prelude", &[lib_path])
        .expect("Failed to load Init.Prelude");

    // Nat.rec: MajorAfterMinors (params → motives → minors → indices → major)
    let nat_rec = env
        .get_recursor(&Name::from_string("Nat.rec"))
        .expect("Nat.rec not found in olean-loaded env");
    assert_eq!(
        nat_rec.arg_order,
        RecursorArgOrder::MajorAfterMinors,
        "Nat.rec should use MajorAfterMinors"
    );

    // Nat.casesOn: when present in the recursor table, it must carry the
    // Lean-faithful MajorAfterMotive layout (the current loader keeps
    // olean casesOn as a value-bearing Definition, so absence is fine).
    if let Some(nat_cases) = env.get_recursor(&Name::from_string("Nat.casesOn")) {
        assert_eq!(
            nat_cases.arg_order,
            RecursorArgOrder::MajorAfterMotive,
            "Nat.casesOn should use MajorAfterMotive (Lean-faithful layout)"
        );
    }

    // Nat.recOn: MajorAfterMotive (params → motives → indices → major → minors)
    let nat_rec_on = env
        .get_recursor(&Name::from_string("Nat.recOn"))
        .expect("Nat.recOn not found in olean-loaded env");
    assert_eq!(
        nat_rec_on.arg_order,
        RecursorArgOrder::MajorAfterMotive,
        "Nat.recOn should use MajorAfterMotive"
    );

    // Also check Bool.casesOn for a non-recursive inductive (same caveat:
    // present only when the loader registers it as a recursor).
    if let Some(bool_cases) = env.get_recursor(&Name::from_string("Bool.casesOn")) {
        assert_eq!(
            bool_cases.arg_order,
            RecursorArgOrder::MajorAfterMotive,
            "Bool.casesOn should use MajorAfterMotive (Lean-faithful layout)"
        );
    }
}
