// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `.olean` import reads the `@[implemented_by]` and `@[extern]` rows of a
//! module Lean 4.8.0 compiled (the v1 layout), as it reads the pinned
//! toolchain's (`compiler_attr_import.rs`, `docs/DECISIONS.md` R149). Before
//! R149 every v1 extension row was `Unmeasured`, so no binding registered, and
//! `clean run` over this fixture printed `3` at exit 0 for `implSlow 1`, where
//! Lean 4.8.0 prints `2`. Lean 4.8.0's `ExternAttrData` has a second field
//! (`arity?`), so its rows are a different shape from v4.30's.
//!
//! Fixture family `implemented_by_import` under
//! `tests/fixtures/lean/v4.8.0/`. Needs the `leanprover/lean4:v4.8.0`
//! toolchain installed under elan, and FAILS without it: these tests are the
//! only measurement of the v1 compiler-attribute rows R149 reads, and a skip
//! would leave that reader unmeasured while every runner printed `ok`
//! (`scripts/check_self_skipping_tests.py`).

use clean_kernel::env::Environment;
use clean_kernel::name::Name;
use clean_olean::load_module_with_deps;

// `skip_unmeasured`, the support module's skip verdict, is for tests that may
// go unmeasured; these may not, so it is never called here.
#[allow(dead_code)]
#[path = "support/installed_lean.rs"]
mod installed_lean;
use installed_lean::{compile_fixture, installed_lean, InstalledLean};

const TOOLCHAIN: &str = "leanprover/lean4:v4.8.0";
const IMPLEMENTED_BY_ATTR: &str = "Lean.Compiler.implementedByAttr";
const EXTERN_ATTR: &str = "Lean.externAttr";

fn n(s: &str) -> Name {
    Name::from_string(s)
}

/// Lean 4.8.0; a failure naming it when it is not installed (module docs).
fn lean_v4_8_0() -> InstalledLean {
    installed_lean(TOOLCHAIN).unwrap_or_else(|| {
        panic!(
            "{TOOLCHAIN} is not installed under elan (`elan toolchain install {TOOLCHAIN}`): \
             these tests measure the v1 compiler-attribute rows and never skip"
        )
    })
}

#[test]
fn test_lean_v4_8_0_import_registers_the_modules_compiler_attr_rows() {
    let lean = lean_v4_8_0();
    let fixture = compile_fixture(&lean, "implemented_by_import", "ImplByLib");
    let mut env = Environment::with_prelude();
    load_module_with_deps(
        &mut env,
        "ImplByLib",
        &[fixture.path().to_path_buf(), lean.lib.clone()],
    )
    .expect("load ImplByLib over Lean 4.8.0's Init.Prelude");
    for (decl, target) in [
        ("implSlow", "implFast"),
        ("chainHead", "chainMid"),
        ("chainMid", "chainEnd"),
        ("unsafeSlow", "unsafeFast"),
    ] {
        assert_eq!(
            env.get_implemented_by(&n(decl)),
            Some(&n(target)),
            "`{decl}` is @[implemented_by {target}] in ImplByLib"
        );
    }
    assert_eq!(
        env.get_extern(&n("externBody")).map(String::as_str),
        Some("clean_implby_fixture_no_such_symbol")
    );
    for plain in [
        "implFast",
        "implCaller",
        "chainEnd",
        "unsafeFast",
        "plainLib",
    ] {
        assert!(
            !env.has_implemented_by(&n(plain)) && !env.is_extern(&n(plain)),
            "`{plain}` carries no compiler attribute"
        );
    }
    assert!(
        env.compiled_before_record().is_none(),
        "every binding of ImplByLib is on its declaration: {:?}",
        env.compiled_before_record()
    );
}

/// A late `attribute [implemented_by]` in a module Lean 4.8.0 compiled
/// (fixture `tests/fixtures/lean/v4.8.0/implemented_by_late/`): the loader
/// records the module's referrers and the rebound declaration itself, so
/// every compiled lane refuses (`docs/DECISIONS.md` R149). Lean 4.8.0 prints
/// `30` for `lateCaller 1`; with the binding applied everywhere it is `20`.
#[test]
fn test_lean_v4_8_0_late_binding_is_recorded() {
    let lean = lean_v4_8_0();
    let fixture = compile_fixture(&lean, "implemented_by_late", "LateLib");
    let mut env = Environment::with_prelude();
    load_module_with_deps(
        &mut env,
        "LateLib",
        &[fixture.path().to_path_buf(), lean.lib.clone()],
    )
    .expect("load LateLib over Lean 4.8.0's Init.Prelude");
    assert_eq!(env.get_implemented_by(&n("lateSlow")), Some(&n("lateFast")));
    let mut recorded: Vec<String> = env
        .compiled_before_record()
        .expect("a late binding is recorded")
        .keys()
        .map(ToString::to_string)
        .collect();
    recorded.sort();
    assert_eq!(recorded, ["lateAfter", "lateCaller", "lateSlow"]);
}

/// Every compiler-attribute row of Lean 4.8.0's whole `Init` decodes. A row
/// that did not decode would have failed the load. Over a bare environment
/// the rows bind `Init`'s own declarations, Lean 4.8.0's two-field
/// `ExternAttrData` included.
#[test]
fn test_lean_v4_8_0_init_compiler_attr_rows_all_decode() {
    let lean = lean_v4_8_0();
    let mut env = Environment::default();
    let summaries = load_module_with_deps(&mut env, "Init", std::slice::from_ref(&lean.lib))
        .unwrap_or_else(|e| panic!("load Lean 4.8.0's Init ({}): {e}", lean.lib.display()));
    for table in [IMPLEMENTED_BY_ATTR, EXTERN_ATTR] {
        let rows: Vec<_> = summaries
            .iter()
            .flat_map(|summary| &summary.extension_accounting)
            .filter(|row| row.extension_name == n(table))
            .collect();
        let decoded: usize = rows.iter().map(|row| row.decoded_rows).sum();
        let undecoded: usize = rows.iter().map(|row| row.undecoded_rows).sum();
        assert!(decoded > 0, "{table}: Lean 4.8.0's Init writes rows");
        assert_eq!(undecoded, 0, "{table}: {rows:?}");
    }
    assert_eq!(
        env.get_extern(&n("Nat.add")).map(String::as_str),
        Some("lean_nat_add"),
        "Init.Prelude: @[extern \"lean_nat_add\"] protected def Nat.add"
    );
    assert_eq!(
        env.get_implemented_by(&n("Array.foldlM")),
        Some(&n("Array.foldlMUnsafe")),
        "Init.Data.Array.Basic: @[implemented_by foldlMUnsafe] def foldlM"
    );
    assert!(
        env.compiled_before_record().is_none(),
        "no binding of Lean 4.8.0's Init is judged late: {:?}",
        env.compiled_before_record()
    );
}
