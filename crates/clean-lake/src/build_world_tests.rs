// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `clean lake build` elaborates a module without `prelude` over genuine Init
//! of the project's Lean world, as Lean's implicit `import Init` does
//! (`crate::module_world`; `docs/DECISIONS.md`, 2026-11-15 reversal of the K1
//! citation-base deferral).
//!
//! Measured 2026-11-15 with pinned v4.30.0-rc2 (`lean`, no `LEAN_PATH`):
//! `theorem K.t (n : Nat) : 0 + n = n := Nat.zero_add n` elaborates and its
//! `lean -o` artifact records `Init` as its import; `def usesArrayData :=
//! @Array.data` is refused with "Unknown constant `Array.data`" (a name only
//! Clean's bootstrap prelude declares).

use super::*;
use tempfile::TempDir;

fn project(module: &str, source: &str) -> TempDir {
    let tmp = TempDir::new().expect("tempdir");
    std::fs::write(
        tmp.path().join("lakefile.toml"),
        format!("name = \"world\"\n\n[[lean_lib]]\nname = \"W\"\nroots = [\"{module}\"]\n"),
    )
    .expect("write lakefile");
    std::fs::write(tmp.path().join(format!("{module}.lean")), source).expect("write source");
    tmp
}

fn build(tmp: &TempDir) -> BuildResult {
    let ws = Workspace::load(tmp.path()).expect("workspace loads");
    BuildContext::new(ws).build_all().expect("build runs")
}

fn recorded_imports(tmp: &TempDir, module: &str) -> Vec<String> {
    let bytes = std::fs::read(tmp.path().join(format!(".lake/build/lib/{module}.olean")))
        .expect("the module's artifact");
    clean_olean::parse_typed_imports(&bytes)
        .expect("a readable header")
        .into_iter()
        .map(|import| import.module_name.to_string())
        .collect()
}

#[test]
fn test_import_free_module_records_genuine_init_as_lean_does() {
    let tmp = project("K", "theorem K.t (n : Nat) : 0 + n = n := Nat.zero_add n\n");
    let result = build(&tmp);
    assert!(result.failed.is_empty(), "K builds: {:?}", result.failed);
    assert_eq!(recorded_imports(&tmp, "K"), vec!["Init".to_string()]);
    let bytes = std::fs::read(tmp.path().join(".lake/build/lib/K.olean")).expect("artifact");
    // Init's own compiler records are the importer's to rebuild from the
    // `Init` the artifact records: repeated per module, they were about 6 MB.
    assert!(
        bytes.len() < 256 * 1024,
        "the artifact carries no copy of Init's records: {} bytes",
        bytes.len()
    );
    let payload = clean_olean::decode_clean_payload(&bytes)
        .expect("decodes")
        .expect("a Clean payload");
    let names: Vec<String> = payload
        .constants
        .iter()
        .map(|c| c.name.to_string())
        .chain(payload.inductives.iter().map(|i| i.name.to_string()))
        .collect();
    assert_eq!(
        names,
        vec!["K.t".to_string()],
        "the payload holds the module's own declaration and cites Init, never a copy of it"
    );
}

/// Negative control: a name only Clean's bootstrap prelude declares is
/// refused, as pinned Lean refuses it over genuine Init.
#[test]
fn test_bootstrap_only_name_is_refused_as_lean_refuses_it() {
    let tmp = project("A", "def usesArrayData := @Array.data\n");
    let result = build(&tmp);
    let failure = result
        .failed
        .iter()
        .find(|(module, _)| module == "A")
        .unwrap_or_else(|| panic!("A must not build over genuine Init: {:?}", result.built));
    assert!(
        failure.1.contains("Array.data"),
        "the refusal names the unknown constant: {failure:?}"
    );
    assert!(!tmp.path().join(".lake/build/lib/A.olean").exists());
}

/// A `prelude` module keeps its unchanged route, the bootstrap environment,
/// and so its existing refusal: the elaborator's `prelude` guard requires a
/// fresh environment, and no artifact is written.
#[test]
fn test_prelude_module_keeps_its_refusal() {
    let tmp = project("P", "prelude\ndef P.p : Nat := 0\n");
    let result = build(&tmp);
    let failure = result
        .failed
        .iter()
        .find(|(module, _)| module == "P")
        .unwrap_or_else(|| panic!("P keeps its refusal: {:?}", result.built));
    assert!(
        failure
            .1
            .contains("prelude requires a fresh module environment without implicit Init"),
        "the refusal is the prelude guard's: {failure:?}"
    );
    assert!(!tmp.path().join(".lake/build/lib/P.olean").exists());
}

#[test]
fn stable_project_prelude_can_check_a_bare_proof_and_has_no_implicit_nat() {
    let tmp = project(
        "W",
        "prelude\ntheorem bareIdentity (p : Prop) : p → p := fun h => h\n",
    );
    let toolchain = tmp.path().join("lean-toolchain");
    std::fs::write(&toolchain, "leanprover/lean4:v4.36.0\n").expect("write stable toolchain");
    let source = tmp.path().join("W.lean");
    let selected = clean_olean::source_world_for_file(&source, None).expect("source world");
    assert_eq!(
        selected.declared_world(),
        Some("v4.36.0"),
        "use the exact installed SDK: {:?}",
        selected.imports()
    );
    let result = build(&tmp);
    assert!(result.failed.is_empty(), "{:?}", result.failed);
    assert!(recorded_imports(&tmp, "W").is_empty());
    let cached = build(&tmp);
    assert_eq!(cached.skipped, ["W"], "unchanged stable artifact is reused");

    std::fs::write(&toolchain, "leanprover/lean4:v4.99.0\n").expect("change only the source world");
    let changed = build(&tmp);
    assert!(changed.skipped.is_empty(), "the stable artifact is stale");
    assert_eq!(changed.failed.len(), 1, "{:?}", changed.failed);
    assert!(
        changed.failed[0]
            .1
            .contains("prelude requires a fresh module environment"),
        "{:?}",
        changed.failed
    );
    std::fs::write(&toolchain, "leanprover/lean4:v4.36.0\n").expect("restore stable toolchain");

    std::fs::write(
        &source,
        include_str!("../../../tests/fixtures/olean/v4.36.0/plain/StablePlain.lean"),
    )
    .expect("rewrite with an explicit stable prelude import");
    let result = build(&tmp);
    assert!(result.failed.is_empty(), "{:?}", result.failed);
    assert_eq!(recorded_imports(&tmp, "W"), ["Init.Prelude"]);

    std::fs::write(
        &source,
        "prelude\nset_option autoImplicit false\naxiom accidentalNat : Nat\n",
    )
    .expect("rewrite as a genuine Lean refusal");
    let result = build(&tmp);
    assert_eq!(result.failed.len(), 1, "{:?}", result.failed);
    assert!(result.failed[0].1.contains("Nat"), "{:?}", result.failed);
}

#[test]
fn refused_project_world_still_builds_local_dependencies() {
    let tmp = project("W", "import W.Dep\ntheorem keep : W.value = 7 := rfl\n");
    std::fs::write(
        tmp.path().join("lean-toolchain"),
        "leanprover/lean4:v4.99.0\n",
    )
    .expect("write refused toolchain");
    std::fs::create_dir(tmp.path().join("W")).expect("create dependency directory");
    std::fs::write(tmp.path().join("W/Dep.lean"), "def W.value : Nat := 7\n")
        .expect("write local dependency");

    let result = build(&tmp);
    assert!(result.failed.is_empty(), "{:?}", result.failed);
    assert_eq!(recorded_imports(&tmp, "W"), ["W.Dep"]);
    assert!(recorded_imports(&tmp, "W/Dep").is_empty());
}

#[test]
fn refused_project_world_refuses_nonworkspace_imports_even_when_permissive() {
    for import in ["Init", "OtherPackage"] {
        let tmp = project("W", &format!("import {import}\ndef keep : Nat := 7\n"));
        std::fs::write(
            tmp.path().join("lean-toolchain"),
            "leanprover/lean4:v4.99.0\n",
        )
        .expect("write refused toolchain");
        for permissive in [false, true] {
            let ws = Workspace::load(tmp.path()).expect("workspace loads");
            let result = BuildContext::new(ws)
                .with_options(BuildOptions::new().with_permissive_imports(permissive))
                .build_all()
                .expect("build runs");
            assert_eq!(result.failed.len(), 1, "{:?}", result.failed);
            let (module, reason) = &result.failed[0];
            assert_eq!(module, "W");
            assert!(reason.contains(&format!("import '{import}'")), "{reason}");
            assert!(reason.contains("v4.99.0"), "{reason}");
            assert!(!tmp.path().join(".lake/build/lib/W.olean").exists());
        }
    }
}
