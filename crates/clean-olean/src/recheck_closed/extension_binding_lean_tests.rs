// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The workspace pin's worlds of the extension-binding table
//! (`extension_binding_pins.rs`), re-derived from the pinned toolchain's own
//! `Init`, row for row.
//!
//! Until 2026-09-28 the table held Lean v4.8.0's world only, and every
//! citation of Lean v4.30.0-rc2's `Nat.add`, `Nat.beq`, … was refused by the
//! import gate (`Mathlib/Order/Basic.lean` 151 → 47 credited). These arms
//! fail against that table, and they fail again the day the fingerprinter,
//! the `.olean` decoder, the toolchain — or, for the import-mode world, any
//! prelude declaration one of those cones reaches — changes, before a lane
//! refuses a genuine key. A failure here asks for a REVIEWED re-pin
//! (`reports/2026-09-28-extension-binding-v4-30.md` says what the review is),
//! never for pasting the minted rows.

use super::super::extension_binding_pins::PINNED_WORLDS;
use super::super::fingerprint::Fingerprinter;
use super::{declares, encode_hex, EXTENSION_KEYS};
use crate::test_support::PINNED_LEAN_REQUIRED;
use clean_kernel::env::Environment;
use clean_kernel::name::Name;
use std::collections::BTreeMap;
use std::path::Path;

/// The workspace pin these worlds are minted from.
const PINNED: &str = "v4.30.0-rc2";

/// The modules that between them declare every extension key: `Init.Prelude`
/// (the `Nat`, `Bool`, `List`, `Eq`, `Char` and `String` keys and the
/// parameter annotations), `Init.Core` (`Lean.reduceBool`/`reduceNat`),
/// `Init.Tactics` (`autoParam`), `Init.Data.Int.Basic`,
/// `Init.Data.Nat.Bitwise.Basic` and `Init.Data.Nat.Gcd` (162 modules in the
/// largest closure). A key's fingerprint hashes its own cone and nothing else,
/// so it is the same under all of `Init` and under the corpus's
/// `Mathlib.Order.Basic` closure (both measured, same report); the arms do not
/// trust this list, they compare the minted rows with the world row for row.
/// Loading all of `Init` in a debug build runs the kernel's certificate path
/// over every module and did not finish in 16 minutes.
const KEY_MODULES: &[&str] = &[
    "Init.Prelude",
    "Init.Core",
    "Init.Tactics",
    "Init.Data.Int.Basic",
    "Init.Data.Nat.Bitwise.Basic",
    "Init.Data.Nat.Gcd",
];

/// [`KEY_MODULES`] from the pinned toolchain, loaded over `env`.
fn load_key_modules(mut env: Environment) -> Environment {
    assert_eq!(
        include_str!("../../../../lean-toolchain").trim(),
        format!("leanprover/lean4:{PINNED}"),
        "these arms re-derive the {PINNED} worlds; the workspace pin moved"
    );
    let lib = crate::pinned_lean_lib_path().expect(PINNED_LEAN_REQUIRED);
    let toolchain_dir = lib
        .parent()
        .and_then(Path::parent)
        .and_then(Path::file_name)
        .map(|n| n.to_string_lossy().into_owned())
        .unwrap_or_default();
    assert!(
        toolchain_dir.ends_with(&format!("---{PINNED}")),
        "the pinned toolchain is not {PINNED} ({toolchain_dir})"
    );
    let mut visited = hashbrown::HashSet::new();
    for module in KEY_MODULES {
        crate::load_module_with_deps_shared(
            &mut env,
            module,
            std::slice::from_ref(&lib),
            &mut visited,
        )
        .unwrap_or_else(|e| panic!("load {module} ({}): {e}", lib.display()));
    }
    env
}

/// `key -> fingerprint` for every extension key `env` declares and `base`
/// (if any) does not: the rows a world minted from `env` holds.
fn mint(env: &Environment, base: Option<&Environment>) -> BTreeMap<String, String> {
    let mut fp = Fingerprinter::new(env);
    EXTENSION_KEYS
        .iter()
        .map(|k| Name::from_string(k.name))
        .filter(|k| declares(env, k) && !base.is_some_and(|b| declares(b, k)))
        .map(|k| {
            let digest = fp.constant(&k);
            (k.to_string(), encode_hex(&digest))
        })
        .collect()
}

/// One pinned world's rows, `key -> fingerprint`.
fn world(label: &str) -> BTreeMap<String, String> {
    let world = PINNED_WORLDS
        .iter()
        .find(|w| w.label == label)
        .unwrap_or_else(|| panic!("no pinned world {label}"));
    world
        .rows
        .iter()
        .map(|(key, hex)| ((*key).to_string(), (*hex).to_string()))
        .collect()
}

/// Lean v4.30.0-rc2's own `Init` over an EMPTY base (the `.olean` re-check
/// lanes' `Environment::for_lean_replay`) re-mints `lean-v4.30.0-rc2-core`
/// exactly: all 41 keys, row for row.
#[test]
fn lean_v4_30_init_rederives_the_empty_base_world() {
    let env = load_key_modules(Environment::for_lean_replay());
    let minted = mint(&env, None);
    assert_eq!(
        minted.len(),
        EXTENSION_KEYS.len(),
        "v4.30 declares every key"
    );
    assert_eq!(minted, world("lean-v4.30.0-rc2-core"));
}

/// The same modules over the import-mode prelude — the base `clean check
/// --imports-prefer-olean` snapshots for its gate — re-mint
/// `clean-import+lean-v4.30.0-rc2-core` exactly: one row per key the import
/// adds, none for a key the prelude itself declares.
#[test]
fn lean_v4_30_init_rederives_the_import_prelude_world() {
    let base = Environment::try_with_prelude_for_import().expect("import-mode prelude");
    let env = load_key_modules(base.clone());
    let minted = mint(&env, Some(&base));
    assert!(
        minted.contains_key("Nat.add") && minted.contains_key("Nat.beq"),
        "the regression's keys come from Init, not the prelude: {minted:?}"
    );
    assert_eq!(minted, world("clean-import+lean-v4.30.0-rc2-core"));
}

/// A citation can reach any subset of the extension keys. Its fingerprint
/// must agree with the reviewed whole-world derivation, regardless of which
/// other keys this fingerprinter has already visited.
#[test]
fn lean_v4_30_extension_fingerprints_are_query_order_independent() {
    for base in [
        Environment::for_lean_replay(),
        Environment::try_with_prelude_for_import().expect("import prelude"),
    ] {
        let env = load_key_modules(base);
        let together = mint(&env, None);
        for key in EXTENSION_KEYS {
            let name = Name::from_string(key.name);
            if declares(&env, &name) {
                let isolated = encode_hex(&Fingerprinter::new(&env).constant(&name));
                assert_eq!(
                    together.get(key.name),
                    Some(&isolated),
                    "isolated {} differs from the world derivation",
                    key.name
                );
            }
        }
    }
}

/// The CIC_L prerequisites load these modules without the rest of the key
/// census. A key's binding must not require an unrelated later import.
#[test]
fn lean_v4_30_nat_bindings_are_stable_in_cic_l_prerequisites() {
    let mut env = Environment::try_with_prelude_for_import().expect("import prelude");
    let lib = crate::pinned_lean_lib_path().expect(PINNED_LEAN_REQUIRED);
    let expected = world("clean-import+lean-v4.30.0-rc2-core");
    for module in ["Init.Data.Nat.Lemmas", "Init.Data.List.Lemmas"] {
        crate::load_module_with_deps(&mut env, module, std::slice::from_ref(&lib))
            .expect("CIC_L prerequisite");
        for key in ["Nat.div", "Nat.mod"] {
            let actual = encode_hex(&Fingerprinter::new(&env).constant(&Name::from_string(key)));
            assert_eq!(Some(&actual), expected.get(key), "{key} after {module}");
        }
    }
}

/// The fenced kernel's judgments over `MData` on these worlds' real cones.
#[path = "fingerprint_mdata_lean_tests.rs"]
mod mdata_judgments;
