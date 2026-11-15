// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KNOWN GAP, pinned so it fails loudly the day it closes: over Clean's
//! import-mode prelude (`Environment::try_with_prelude_for_import`, the
//! environment the elaborator imports into), the kernel refuses two honest
//! v4.30.0-rc2 `Init.GetElem` theorems that it admits over Lean's own world
//! (`Environment::for_lean_replay`): `Array.instLawfulGetElemNatLtSize` and
//! `Array.get!Internal_eq_getElem!`. R131 found the first through
//! `lean_v4_30_init_rederives_the_import_prelude_world`.
//!
//! The cause is a prelude stand-in, not a kernel definitional-equality gap.
//! The import keeps a resident declaration over Lean's of the same name, and
//! the prelude registers its own Lean-4.8-shaped `Array.instGetElemNatLtSize`
//! and `Array.instGetElem?NatLtSize` (`clean-kernel`'s
//! `env/data_getelem_list.rs`: `getElem` through `List.get (Array.data as)`,
//! `getElem?` through `List.get?`). Lean v4.30's proofs close by `Eq.refl`
//! only through v4.30's instances: `xs[i]!` must unfold to `dite (i <
//! xs.size) (fun h => xs.getInternal i h) (fun _ => default)` (through
//! `decidableGetElem?`), and `GetElem.getElem` on the Array instance to
//! `Array.getInternal`. With the stand-ins neither reduces to that, so the
//! checked upgrade of each value-free stub reports `Type mismatch` (measured
//! 2026-10-24, the expected `GetElem?.getElem! … (Array.instGetElem?NatLtSize
//! α) inst xs i = …` against Lean's `dite … Array.getInternal …`). The same
//! kernel admits both over Lean's world, where the instances are Lean's.
//!
//! Closing it means making the prelude's Array instances Lean's v4.30 ones
//! (or not seeding them where Lean's are imported), a prelude change outside
//! the kernel's checking code. R131's re-check policy already keeps this from
//! mattering to a verdict there: the re-check lanes load over Lean's world.

use clean_kernel::env::Environment;

/// The `Init.GetElem` declarations whose stub completion is refused over
/// `base`, by name, with the refusal text.
fn refused_completions(base: Environment) -> Vec<(String, String)> {
    let lib = clean_olean::pinned_lean_lib_path().expect("the pinned Lean toolchain");
    let mut env = base;
    let mut visited = hashbrown::HashSet::new();
    let summaries = clean_olean::load_module_with_deps_shared(
        &mut env,
        "Init.GetElem",
        std::slice::from_ref(&lib),
        &mut visited,
    )
    .expect("Init.GetElem loads");
    summaries
        .iter()
        .flat_map(|s| s.refused_completions.iter())
        .map(|(name, why)| (name.to_string(), why.clone()))
        .collect()
}

#[test]
fn test_import_prelude_array_getelem_standins_refuse_leans_lawful_proofs() {
    let refused = refused_completions(
        Environment::try_with_prelude_for_import().expect("import-mode prelude"),
    );
    let names: Vec<&str> = refused.iter().map(|(n, _)| n.as_str()).collect();
    for name in [
        "Array.instLawfulGetElemNatLtSize",
        "Array.get!Internal_eq_getElem!",
    ] {
        let why = refused
            .iter()
            .find(|(n, _)| n == name)
            .map(|(_, why)| why.as_str())
            .unwrap_or_else(|| {
                panic!("the gap closed for `{name}` — flip this pin; refused: {names:?}")
            });
        assert!(
            why.contains("Type mismatch") && why.contains("Array.getInternal"),
            "`{name}`: refused, but not for the stand-in mismatch: {why}"
        );
    }
    assert_eq!(names.len(), 2, "only the two GetElem proofs: {names:?}");
}

/// The control: the same kernel admits both over Lean's own world.
#[test]
fn test_lean_world_admits_the_array_getelem_lawful_proofs() {
    let refused = refused_completions(Environment::for_lean_replay());
    assert!(refused.is_empty(), "{refused:?}");
}
