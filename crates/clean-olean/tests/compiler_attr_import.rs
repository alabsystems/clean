// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `.olean` import registers the `@[implemented_by]` and `@[extern]` rows of
//! a Lean-built module (`Lean.Compiler.implementedByAttr`, `Lean.externAttr`)
//! in the registries source elaboration fills, so the native path sees an
//! imported binding as it sees a source one (`docs/DECISIONS.md` R149). Before
//! R149 neither table was read and every assertion below on a binding failed.
//! The fixture family is `implemented_by_import`
//! (`tests/fixtures/lean/v4.30.0-rc2/implemented_by_import/README.md`),
//! compiled by the pinned Lean on first use; fails closed without it.

use clean_kernel::env::Environment;
use clean_kernel::name::Name;
use clean_olean::load_module_with_deps;
use clean_olean::test_support::compiled_fixture_dir;

fn n(s: &str) -> Name {
    Name::from_string(s)
}

fn load_fixture(env: &mut Environment) {
    let mut paths = vec![compiled_fixture_dir("implemented_by_import")];
    paths.extend(clean_olean::pinned_lean_lib_path());
    load_module_with_deps(env, "ImplByLib", &paths).expect("load ImplByLib and Init.Prelude");
}

#[test]
fn test_import_registers_the_modules_implemented_by_and_extern_rows() {
    let mut env = Environment::with_prelude();
    load_fixture(&mut env);
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
}

/// A row about a declaration the environment already held when the module
/// loaded is not registered: the loader keeps the resident declaration (here
/// the builtin prelude's), and the row is about the one it dropped.
/// `Init.Prelude` writes `@[extern "lean_nat_add"]` for `Nat.add` and
/// `@[implemented_by]` rows for no prelude-resident declaration this test
/// names; without the builtin prelude the same rows bind the module's own
/// declarations.
#[test]
fn test_import_keeps_a_resident_declarations_meaning() {
    let mut with_prelude = Environment::with_prelude();
    load_fixture(&mut with_prelude);
    assert!(
        !with_prelude.is_extern(&n("Nat.add")),
        "the builtin prelude's `Nat.add` is not the declaration Init.Prelude's row binds"
    );

    let mut bare = Environment::default();
    load_fixture(&mut bare);
    assert_eq!(
        bare.get_extern(&n("Nat.add")).map(String::as_str),
        Some("lean_nat_add"),
        "Init.Prelude's own `Nat.add` is @[extern \"lean_nat_add\"]"
    );
    assert_eq!(
        bare.get_implemented_by(&n("implSlow")),
        Some(&n("implFast"))
    );
}

/// The pinned toolchain's whole `Init` writes every binding on its
/// declaration (its source has no `attribute [implemented_by]` command, and
/// `Init.Prelude`'s computed-field elaborator binds `Lean.Name.casesOn` to
/// its `_override` before anything is compiled), so the loader's
/// late-binding judgement records nothing for it: a program that imports
/// `Init` is not refused for the order hazard (`docs/DECISIONS.md` R149's
/// amendment of 2026-10-20). Over a bare environment the rows bind `Init`'s
/// own declarations.
///
/// About 24 minutes in a debug build (1458.7 s measured 2026-10-21). That is
/// the load, not the judgement: in three 20 s `sample` windows of this test,
/// 21,020 of its thread's 21,960 samples were under the kernel's stub
/// upgrade (`upgrade_stubs_to_fixpoint`) and none in `late_binding`.
#[test]
fn test_import_pinned_init_judges_no_binding_late() {
    let lib = clean_olean::pinned_lean_lib_path()
        .expect("the pinned Lean toolchain's library is required");
    let mut env = Environment::default();
    load_module_with_deps(&mut env, "Init", std::slice::from_ref(&lib))
        .unwrap_or_else(|e| panic!("load the pinned Init ({}): {e}", lib.display()));
    assert_eq!(
        env.get_implemented_by(&n("Array.foldlM")),
        Some(&n("Array.foldlMUnsafe")),
        "Init.Data.Array.Basic: @[implemented_by foldlMUnsafe, expose] def foldlM"
    );
    assert_eq!(
        env.get_extern(&n("Nat.add")).map(String::as_str),
        Some("lean_nat_add"),
        "Init.Prelude: @[extern \"lean_nat_add\", implicit_reducible] protected def Nat.add"
    );
    assert!(
        env.compiled_before_record().is_none(),
        "no binding of the pinned Init is judged late: {:?}",
        env.compiled_before_record()
    );
}
