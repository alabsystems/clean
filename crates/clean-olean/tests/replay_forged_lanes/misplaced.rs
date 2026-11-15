// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Hole B1 (`docs/DECISIONS.md` R113) in the `.olean` loader: a declaration
//! placed in a part no importer reads. An importer (`lean` on a file that
//! imports the artifact; `leanchecker --fresh`) reads a non-module artifact
//! through its `.olean`, and a module-system artifact through its
//! `.olean.private` when it is not itself a `module` (`Environment.lean`:
//! `ImportedModule.mainModule?`); `leanchecker`'s default mode replays the last
//! part it found. `writeModule` never writes a part whose names that part does
//! not hold, so Clean refuses such an artifact. Where `leanchecker`'s default
//! mode would accept one (a non-module artifact whose companions hold a whole
//! well-typed set), the refusal is stricter than Lean: the safe direction.
//!
//! Fixtures (family README): `ReplayMisplacedServer` keeps `SO`/`SO.mk`/`SO.rec`
//! in its `.olean.server` alone; `ReplayMisplacedServerPlain` is the same
//! without the module system; `ReplayHonestServerParts` is the honest control
//! (`SH` in every part). Pinned `leanchecker` refuses the two misplaced ones
//! (`unknown constant 'SO'` / `'SOP'`) and admits the control.
//!
//! The loader refuses an artifact whose part declares a name its authoritative
//! part lacks (`ImportError::MisplacedDeclaration`), so every lane that loads
//! the artifact is refused by name.

use super::*;
use clean_olean::{read_artifact, ArtifactDepth, ImportError};

#[test]
fn test_loader_refuses_a_server_only_declaration_naming_it() {
    // Each refusal names the part that declares the misplaced name: the rule
    // checks the `.olean` before the `.olean.server`, so a refusal that names a
    // later part than the one listed here means an entry of the rule is gone.
    for (module, needle) in [
        (
            "ReplayMisplacedServer",
            "`ReplayMisplacedServer`'s `.olean.server` declares `SO`",
        ),
        (
            "ReplayMisplacedServerPlain",
            "`ReplayMisplacedServerPlain`'s `.olean.server` declares `SOP`",
        ),
        // The `.olean` half of the rule (review finding P7): `SX` in `.olean` and
        // `.olean.server`, absent from `.olean.private`.
        (
            "ReplayMisplacedOlean",
            "`ReplayMisplacedOlean`'s `.olean` declares `SX`",
        ),
    ] {
        let error = match try_load(module) {
            Ok(_) => panic!("{module}: a misplaced declaration must refuse the import"),
            Err(error) => error,
        };
        assert!(
            error.contains("does not") && error.contains("consumer that is not a `module` reads"),
            "{module}: the refusal must be a misplaced-declaration one: {error}"
        );
        assert!(
            error.contains(needle),
            "{module}: the refusal must name the misplaced family `{needle}`: {error}"
        );
    }
}

#[test]
fn test_honest_server_parts_control_loads_and_verifies() {
    // Every `.olean`/`.olean.server` name is a `.olean.private` name, so the
    // loader admits it and every lane verifies its value-bearing declarations.
    let targets = declared("ReplayHonestServerParts");
    assert!(
        targets.iter().any(|n| n == "sh_use"),
        "the honest control declares `sh_use`: {targets:?}"
    );
    for (lane, outcome) in lanes("ReplayHonestServerParts", &targets) {
        assert_eq!(outcome.1, 0, "{lane}: {:?}", outcome.2);
        assert!(outcome.0 >= 1, "{lane}: nothing verified: {:?}", outcome.2);
    }
}

/// Review findings P1-P3 through the loader: parts that disagree on a value or an import list,
/// and a misplaced family in a DEPENDENCY, each refused by the rule naming what it refuses (the
/// module's own part, or the import's). Pinned `leanchecker` refuses every user here (README); it
/// accepts `ReplayPartsValDep`, `ReplayPartsImpD` and `ReplayMisplacedDep` alone, which Clean
/// refuses because their parts disagree (stricter than Lean: the safe direction).
#[test]
fn test_loader_refuses_parts_that_disagree_and_misplaced_dependencies() {
    for (module, needle) in [
        ("ReplayPartsValDis", "state `pv_X` differently"),
        ("ReplayPartsValDepUser", "state `pd_X` differently"),
        ("ReplayPartsImpT", "state its imports differently"),
        (
            "ReplayMisplacedDepUser",
            "`ReplayMisplacedDep`'s `.olean` declares `MD`",
        ),
    ] {
        let error = match try_load(module) {
            Ok(_) => panic!("{module}: the import must be refused"),
            Err(error) => error,
        };
        assert!(
            error.contains(needle),
            "{module}: refused without `{needle}`: {error}"
        );
    }
    // Control: `MD` in every part of the dependency.
    let targets = declared("ReplayHonestDepUser");
    for (lane, outcome) in lanes("ReplayHonestDepUser", &targets) {
        assert_eq!((outcome.0, outcome.1), (1, 0), "{lane}: {:?}", outcome.2);
    }
}

/// The import closure a lane walks follows the imports of the part `lean` reads. Before R113's
/// reader, `build_import_closures_with_search_paths` (the `--incremental` cache key and
/// verify-batch's order) read `ReplayPartsImpD`'s `.olean`, which imports `ReplayPartsImpF`, while
/// `lean` follows its `.olean.private` to `ReplayPartsImpE`. Its parts disagree, so the reader
/// refuses `ReplayPartsImpD` and neither list is followed.
#[test]
fn test_import_closure_never_follows_a_part_lean_does_not_read() {
    let dir = compiled_fixture_dir(FAMILY);
    let target = dir.join("ReplayPartsImpT.olean");
    let mut search: Vec<std::path::PathBuf> = vec![dir.clone()];
    search.extend(default_search_paths());
    let search: Vec<&std::path::Path> = search.iter().map(std::path::PathBuf::as_path).collect();
    let closures = clean_olean::verify_batch::build_import_closures_with_search_paths(
        std::slice::from_ref(&target),
        &dir,
        &search,
    );
    let members = closures
        .get(&target)
        .expect("ReplayPartsImpT has a closure");
    assert!(
        !members.iter().any(|p| p.ends_with("ReplayPartsImpF.olean")),
        "the closure follows the `.olean`'s import list: {members:?}"
    );
}

/// Review finding S5 (R131): the two entries of the placement rule no other
/// fixture reaches alone. `ReplayMisplacedOleanOnlyDep` (a `module`) keeps `MO`
/// in its `.olean` and nowhere else, so only the rule's `.olean` entry refuses
/// it; `ReplayMisplacedPrivPlainDep` (not a `module`, read through its `.olean`)
/// keeps `MP` in its `.olean.private` alone, so only the `.olean.private` entry
/// does. Pinned `leanchecker` refuses each user (`unknown constant 'MO'` /
/// `'MP'`) and admits each dependency alone; Clean refuses the dependency
/// (stricter than Lean, the safe direction).
#[test]
fn test_loader_refuses_each_placement_entry_naming_its_part() {
    for (module, needle) in [
        (
            "ReplayMisplacedOleanOnlyDepUser",
            "`ReplayMisplacedOleanOnlyDep`'s `.olean` declares `MO`",
        ),
        (
            "ReplayMisplacedPrivPlainDepUser",
            "`ReplayMisplacedPrivPlainDep`'s `.olean.private` declares `MP`",
        ),
    ] {
        let error = match try_load(module) {
            Ok(_) => panic!("{module}: the import must be refused"),
            Err(error) => error,
        };
        assert!(
            error.contains(needle),
            "{module}: refused without `{needle}`: {error}"
        );
    }
}

/// A copy of `ReplayHonestDep` (its parts and `.ir`, less `missing`) and
/// `ReplayHonestDepUser`.
fn honest_dep_copy(missing: Option<&str>) -> tempfile::TempDir {
    let dir = tempfile::tempdir().expect("tempdir");
    let src = compiled_fixture_dir(FAMILY);
    for file in [
        "ReplayHonestDep.olean",
        "ReplayHonestDep.olean.server",
        "ReplayHonestDep.olean.private",
        "ReplayHonestDep.ir",
        "ReplayHonestDepUser.olean",
    ] {
        if missing.is_some_and(|part| file == format!("ReplayHonestDep{part}")) {
            continue;
        }
        let bytes = std::fs::read(src.join(file)).expect("read fixture part");
        std::fs::write(dir.path().join(file), &bytes).expect("write part");
    }
    dir
}

/// `module` loaded from `dir` (and the toolchain), the import's refusal as text.
fn load_from(dir: &std::path::Path, module: &str) -> Result<(), String> {
    let mut env = Environment::for_lean_replay();
    let mut search = vec![dir.to_path_buf()];
    search.extend(default_search_paths());
    let mut visited = hashbrown::HashSet::new();
    load_module_with_deps_shared_with_policy(
        &mut env,
        module,
        &search,
        &mut visited,
        OleanImportPolicy::default(),
    )
    .map(|_| ())
    .map_err(|e| e.to_string())
}

/// Review finding S6 (R131): `MissingModulePart` and the `isModule` agreement
/// check had no test. Pinned `leanchecker ReplayHonestDepUser` over a
/// `ReplayHonestDep` without its `.olean.private` is rc 1 (`missing data file
/// for module ReplayHonestDep`, default and `--fresh`); the dependency alone is
/// rc 0 in the default mode (it replays the server part).
#[test]
fn test_loader_refuses_a_module_artifact_without_a_part_or_with_two_module_flags() {
    load_from(honest_dep_copy(None).path(), "ReplayHonestDepUser").expect("the honest pair loads");
    for part in [".olean.private", ".olean.server"] {
        let dir = honest_dep_copy(Some(part));
        let needle = format!("`ReplayHonestDep` is a module-system artifact without its `{part}`");
        let error = load_from(dir.path(), "ReplayHonestDepUser")
            .expect_err("a missing part refuses the import");
        assert!(error.contains(&needle), "{part}: {error}");
        match read_artifact(
            "ReplayHonestDep",
            &dir.path().join("ReplayHonestDep.olean"),
            ArtifactDepth::Names,
        ) {
            Err(ImportError::MissingModulePart {
                module,
                part: refused,
            }) => {
                assert_eq!((module.as_str(), refused), ("ReplayHonestDep", part));
            }
            other => panic!("{part}: the reader must refuse the artifact: {other:?}"),
        }
    }
    // The `.olean` says it is not a module while its private part says it is:
    // the `isModule` scalar of the ModuleData root (the byte at root+48, the
    // `import_flags` README), cleared in the `.olean` alone. `ReplayStubHonest`'s
    // parts state different constants, so its `.olean.private` has a root object
    // of its own; `ReplayHonestDep`'s three parts are one `ModuleData` and share
    // the `.olean`'s root, so clearing that byte would flip every part at once.
    let dir = tempfile::tempdir().expect("tempdir");
    let src = compiled_fixture_dir(FAMILY);
    for ext in ["olean", "olean.server", "olean.private", "ir"] {
        let file = format!("ReplayStubHonest.{ext}");
        let mut bytes = std::fs::read(src.join(&file)).expect("read fixture part");
        if ext == "olean" {
            let word = |at: usize| {
                u64::from_le_bytes(bytes[at..at + 8].try_into().expect("an 8-byte header word"))
            };
            let root = usize::try_from(word(88) - word(80)).expect("the root lies in the part");
            assert_eq!(
                bytes[root + 48],
                1,
                "the `.olean` of a `module` says isModule"
            );
            bytes[root + 48] = 0;
        }
        std::fs::write(dir.path().join(&file), &bytes).expect("write part");
    }
    match read_artifact(
        "ReplayStubHonest",
        &dir.path().join("ReplayStubHonest.olean"),
        ArtifactDepth::Names,
    ) {
        Err(ImportError::PartsDisagreeOnHeader { module, what }) => {
            assert_eq!(
                (module.as_str(), what),
                ("ReplayStubHonest", "whether it is a module")
            );
        }
        other => panic!("the reader must refuse two `isModule` flags: {other:?}"),
    }
    let error = load_from(dir.path(), "ReplayStubHonest")
        .expect_err("two `isModule` flags refuse the import");
    assert!(
        error.contains("the parts of `ReplayStubHonest` state whether it is a module differently"),
        "{error}"
    );
}
