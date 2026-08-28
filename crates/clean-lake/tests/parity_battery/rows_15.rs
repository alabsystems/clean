// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Parity battery row 15: a module the workspace itself provides is LOCAL,
//! whatever its name. Row semantics are pinned; see `parity_battery.rs`.

use tempfile::TempDir;

use clean_lake::{BuildOptions, Workspace};

use crate::common::*;

// ---------------------------------------------------------------------------
// Row 15 — workspace-owned modules shadow the stdlib name prefixes
// ---------------------------------------------------------------------------

/// `is_stdlib_import` used to be a bare prefix test on
/// `Init|Std|Lean|Lake|Mathlib` that never consulted the workspace's own
/// module index. A package declaring `lean_lib Std` therefore built
/// `Std.Mine`, then FAILED `Std.User` with
/// `failed to load stdlib import 'Std.Mine' … not found in [elan toolchain]` —
/// its own just-built artifact ignored. Worse than the failure: under
/// `--permissive-imports`, or wherever a same-named toolchain `.olean` exists,
/// the project's module is silently replaced by Lean's with no diagnostic.
///
/// This row pins both halves of the predicate:
///  - **positive**: a module the workspace CAN provide routes to the local
///    build, and the `rfl` THROUGH the shadowed module's value kernel-verifies
///    (a name-only or toolchain-sourced import cannot fake that);
///  - **negative control**: a module the workspace CANNOT provide still routes
///    to the toolchain, so the shadowing check did not disable stdlib loading.
///    `Init.NoSuchCleanLakeParityModule` exists in no toolchain's search paths,
///    so the control is machine-independent (same device as row 09).
#[test]
fn row15_workspace_owned_module_shadows_the_stdlib_prefix() {
    let tmp = TempDir::new().expect("tempdir");
    write_file(
        &tmp.path().join("lakefile.toml"),
        "name = \"stdshadow\"\nsrcDir = \"src\"\n\n[[lean_lib]]\nname = \"Std\"\n",
    );
    write_file(
        &tmp.path().join("src/Std/Mine.lean"),
        "def mineVal : Nat := 4\n",
    );
    write_file(
        &tmp.path().join("src/Std/User.lean"),
        "import Std.Mine\ndef userVal : Nat := mineVal\n\
         theorem user_eq : userVal = 4 := rfl\n",
    );

    let result = build_all(tmp.path());
    assert_eq!(
        sorted(result.built),
        vec!["Std.Mine", "Std.User"],
        "a module the workspace provides is LOCAL, whatever its name"
    );
    assert!(
        result.failed.is_empty(),
        "the rfl THROUGH the shadowed module's value must kernel-verify: {:?}",
        result.failed
    );
    let ws = Workspace::load(tmp.path()).expect("workspace reloads");
    for module in ["Std.Mine", "Std.User"] {
        assert_olean_triple(&ws, module);
    }

    // The SILENT face of the same bug: `--permissive-imports` downgrades a
    // failed stdlib load to a warning, so a workspace module misrouted to the
    // toolchain vanishes from the environment with no diagnostic. Routing is
    // decided before the flag is consulted, so a forced permissive rebuild
    // must still build both modules and still kernel-verify the `rfl`.
    let permissive = build_all_with(
        tmp.path(),
        BuildOptions::new()
            .with_permissive_imports(true)
            .with_force(true),
    );
    assert_eq!(
        sorted(permissive.built),
        vec!["Std.Mine", "Std.User"],
        "permissive mode must not silently drop a workspace-owned import"
    );
    assert!(
        permissive.failed.is_empty(),
        "no failures under the opt-out: {:?}",
        permissive.failed
    );

    // Negative control, same workspace: an `Init.*` module the workspace does
    // NOT provide must still route to the toolchain loader and fail closed
    // there. If shadowing had disabled the stdlib route, this would instead
    // report a missing LOCAL module (or, worse, quietly build).
    write_file(
        &tmp.path().join("src/Std/Outside.lean"),
        "import Init.NoSuchCleanLakeParityModule\ndef outsideVal : Type 1 := Type\n",
    );
    let result = build_all(tmp.path());
    assert_eq!(
        result.failed.len(),
        1,
        "exactly the toolchain-routed module fails: {:?}",
        result.failed
    );
    let (module, reason) = &result.failed[0];
    assert_eq!(module, "Std.Outside");
    assert!(
        reason.contains("failed to load stdlib import 'Init.NoSuchCleanLakeParityModule'"),
        "the unprovided import must still route to the STDLIB loader: {reason}"
    );
}
