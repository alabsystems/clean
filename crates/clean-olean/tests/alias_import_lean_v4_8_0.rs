// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `.olean` import registers the `export` aliases of Lean 4.8.0's `Init` (the
//! v1 layout) exactly as Lean 4.8.0 itself reads them back.
//!
//! Lean persists `export Ns (a)` in `Lean.aliasExtension` as `AliasEntry :=
//! Name × Name`, the same type in v4.8.0 as in the pin. Until 2026-11-14 the
//! v1 rows of that table were `Unmeasured`, so no alias registered: once an
//! ordinary module with an artifact import started from the selected world's
//! genuine `Init` (6e12a7791), `toString (implSlow 1)` over a Lean 4.8.0
//! `.olean` stopped with `Unknown identifier: toString`, which Lean 4.8.0
//! resolves through `export ToString (toString)`
//! (`crates/clean/tests/implemented_by_lean_v4_8_0_cli.rs`).
//!
//! The oracle is Lean 4.8.0 run here: `aliasExtension.getModuleEntries` of
//! every `Init` module, compared as a set with the pairs Clean registered.
//! Needs the `leanprover/lean4:v4.8.0` toolchain under elan, and FAILS
//! without it (`scripts/check_self_skipping_tests.py`).

use std::collections::BTreeSet;
use std::process::Command;

use clean_kernel::env::Environment;
use clean_olean::load_module_with_deps;

#[allow(dead_code)]
#[path = "support/installed_lean.rs"]
mod installed_lean;
use installed_lean::{installed_lean, InstalledLean};

const TOOLCHAIN: &str = "leanprover/lean4:v4.8.0";

const ORACLE: &str = r#"import Lean
open Lean

#eval show CoreM Unit from do
  let env ← getEnv
  let header := env.header
  for i in [0:header.moduleNames.size] do
    let m := header.moduleNames[i]!
    if (`Init).isPrefixOf m then
      for (a, t) in aliasExtension.getModuleEntries env i do
        IO.println s!"ALIAS\t{a}\t{t}"
"#;

fn lean_v4_8_0() -> InstalledLean {
    installed_lean(TOOLCHAIN).unwrap_or_else(|| {
        panic!(
            "{TOOLCHAIN} is not installed under elan (`elan toolchain install {TOOLCHAIN}`): \
             this test measures the v1 alias rows and never skips"
        )
    })
}

/// Every `(alias, target)` pair Lean 4.8.0 reads from `Init`'s modules.
fn lean_init_aliases(lean: &InstalledLean) -> BTreeSet<(String, String)> {
    let dir = tempfile::tempdir().expect("oracle directory");
    std::fs::write(dir.path().join("Oracle.lean"), ORACLE).expect("write oracle");
    let output = Command::new(&lean.bin)
        .current_dir(dir.path())
        .arg("Oracle.lean")
        .output()
        .unwrap_or_else(|e| panic!("cannot execute {}: {e}", lean.bin.display()));
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        output.status.success(),
        "Lean 4.8.0 oracle failed with {}\n{stdout}\n{}",
        output.status,
        String::from_utf8_lossy(&output.stderr)
    );
    stdout
        .lines()
        .map(|line| {
            let mut fields = line.split('\t');
            match (fields.next(), fields.next(), fields.next(), fields.next()) {
                (Some("ALIAS"), Some(alias), Some(target), None) => {
                    (alias.to_string(), target.to_string())
                }
                _ => panic!("unexpected oracle line {line:?}"),
            }
        })
        .collect()
}

#[test]
fn test_lean_v4_8_0_init_import_registers_every_export_alias_lean_reads() {
    let lean = lean_v4_8_0();
    let expected = lean_init_aliases(&lean);
    // The row the CLI regression needs, so an empty oracle cannot pass.
    assert!(
        expected.contains(&("toString".to_string(), "ToString.toString".to_string())),
        "Lean 4.8.0's Init exports ToString (toString): {expected:?}"
    );

    let mut env = Environment::for_lean_replay();
    let before: BTreeSet<(String, String)> = env
        .export_alias_pairs()
        .map(|(alias, target)| (alias.to_string(), target.to_string()))
        .collect();
    load_module_with_deps(&mut env, "Init", std::slice::from_ref(&lean.lib))
        .expect("load Lean 4.8.0's Init");
    let registered: BTreeSet<(String, String)> = env
        .export_alias_pairs()
        .map(|(alias, target)| (alias.to_string(), target.to_string()))
        .filter(|pair| !before.contains(pair))
        .collect();
    assert_eq!(
        registered, expected,
        "Clean must register exactly the export aliases Lean 4.8.0 reads from Init"
    );
}
