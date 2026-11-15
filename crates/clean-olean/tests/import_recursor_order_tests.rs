// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Regression tests for RecursorArgOrder assignment in the olean loader.
//!
//! Validates that olean-loaded recursors get the same arg_order as the kernel
//! builder (inductive_builder.rs). Requires a Lean 4 installation via elan.
//!
//! Part of #1790

use clean_kernel::env::{ConstantKind, Environment};
use clean_kernel::expr::ExprKind;
use clean_kernel::inductive::RecursorArgOrder;
use clean_kernel::name::Name;
use clean_kernel::tc::TypeChecker;
use clean_olean::{load_module_with_deps, pinned_lean_lib_path};

fn get_lean_lib_path() -> Option<std::path::PathBuf> {
    pinned_lean_lib_path()
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

/// Stored recOn/casesOn wrappers are definitions, not necessarily primitive recursors.
/// Require their real telescope and checked body; absence from both tables is an error.
fn assert_major_after_motive(env: &Environment, name: &str, inductive: &str) {
    let name = Name::from_string(name);
    let info = env.get_const(&name).expect("stored eliminator must exist");
    let ExprKind::Pi(_, _, after_motive) = info.type_.kind() else {
        panic!("{name}: motive binder missing");
    };
    let ExprKind::Pi(_, major_ty, _) = after_motive.kind() else {
        panic!("{name}: major binder must follow motive");
    };
    assert!(
        matches!(major_ty.kind(), ExprKind::Const(owner, levels)
        if owner == &Name::from_string(inductive) && levels.is_empty()),
        "{name}: wrong major-premise position or owner: {major_ty:?}"
    );
    let tc = TypeChecker::new(env);
    assert!(matches!(
        tc.infer_type(&info.type_)
            .expect("eliminator type checks")
            .kind(),
        ExprKind::Sort(_)
    ));
    if let Some(recursor) = env.get_recursor(&name) {
        assert_eq!(
            recursor.arg_order,
            RecursorArgOrder::MajorAfterMotive,
            "{name}: stored recursor order must agree with its telescope"
        );
    } else {
        assert_eq!(
            info.kind,
            ConstantKind::Definition,
            "{name}: stored wrapper kind"
        );
        tc.check_type(
            info.value.as_ref().expect("stored wrapper body"),
            &info.type_,
        )
        .unwrap_or_else(|error| panic!("{name}: stored wrapper body does not check: {error:?}"));
    }
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

    // Keep every original eliminator mandatory, including definition wrappers.
    assert_major_after_motive(&env, "Nat.casesOn", "Nat");
    assert_major_after_motive(&env, "Nat.recOn", "Nat");
    assert_major_after_motive(&env, "Bool.casesOn", "Bool");
}
