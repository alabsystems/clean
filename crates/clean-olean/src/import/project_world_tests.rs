// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Which world a checked file's imports resolve in (G72), over the real
//! world table and over an injected one holding the states no row has yet.

use super::*;
use std::fs;
use tempfile::TempDir;

#[test]
fn source_world_type_covers_exactly_the_measured_registry() {
    let tags: std::collections::HashSet<_> = lean_worlds().iter().map(|row| row.world).collect();
    let typed: std::collections::HashSet<_> =
        LeanWorld::ALL.into_iter().map(LeanWorld::tag).collect();
    assert_eq!(tags, typed);
    assert_eq!(oracle().world, LeanWorld::ORACLE.tag());
}

fn oracle_header() -> Vec<u8> {
    let bytes = fs::read(
        Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../tests/fixtures/olean/v4.30.0/module-system/Sigma.olean"),
    )
    .expect("genuine tracked Oracle fixture");
    bytes[..HEADER_SIZE_V2].to_vec()
}

#[test]
fn snapshot_world_declares_the_configured_library_without_a_source_path() {
    let root = TempDir::new().expect("tempdir");
    let lib = install(root.path(), oracle().world, &oracle_header());
    let decision = snapshot_world_for_library(lean_worlds(), lib.clone()).unwrap();
    assert_eq!(decision.world(), LeanWorld::ORACLE);
    assert_eq!(decision.declared_world(), Some(LeanWorld::ORACLE.tag()));
    assert_eq!(
        decision.imports(),
        Ok(&ImportWorld::Explicit {
            world: LeanWorld::ORACLE,
            lib,
        })
    );
}

#[test]
fn snapshot_world_refuses_an_authentic_other_world_under_the_pin_name() {
    let root = TempDir::new().expect("tempdir");
    let lib = install(root.path(), oracle().world, &v4_8_0_header());
    let error = snapshot_world_for_library(lean_worlds(), lib).unwrap_err();
    assert!(error.to_string().contains("another build"), "{error}");
}

#[test]
fn snapshot_world_refuses_missing_and_unreadable_headers_without_a_fallback() {
    let root = TempDir::new().expect("tempdir");
    let lib = root.path().join("missing-library");
    let error = snapshot_world_for_library(lean_worlds(), lib).unwrap_err();
    assert!(error.to_string().contains("unreadable header"), "{error}");
    let lib = install(root.path(), oracle().world, b"not an olean header");
    let error = snapshot_world_for_library(lean_worlds(), lib).unwrap_err();
    assert!(error.to_string().contains("unreadable header"), "{error}");
}

fn recent_header() -> Vec<u8> {
    let bytes = fs::read(
        Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../tests/fixtures/olean/v4.36.0-rc2/matcher-metadata/MatcherParity.olean"),
    )
    .expect("genuine tracked recent fixture");
    bytes[..HEADER_SIZE_V2].to_vec()
}

#[test]
fn explicit_source_world_uses_exact_library_and_overrides_project_choice() {
    let (root, file) = project(Some("leanprover/lean4:v4.99.0"));
    let world = LeanWorld::Lean436Rc2;
    let lib = install(root.path(), world.tag(), &recent_header());
    let roots = vec![root.path().join("elan")];
    // Implicitly, the unknown v4.99.0 world refuses the imports, resolving
    // none of them in the installed v4.36.0-rc2 or any other world.
    let implicit = source_world_for(lean_worlds(), &file, None, &roots).unwrap();
    let refusal = implicit.imports().unwrap_err();
    assert!(refusal.to_string().contains("v4.99.0"), "{refusal}");
    assert_eq!(implicit.world(), LeanWorld::ORACLE);
    assert_eq!(implicit.declared_world(), None);
    let selected = source_world_for(lean_worlds(), &file, Some(world), &roots).unwrap();
    assert_eq!(selected.world(), world);
    assert_eq!(
        selected.imports(),
        Ok(&ImportWorld::Explicit { world, lib })
    );
    assert_eq!(selected.declared_world(), Some(world.tag()));
    assert!(source_world_for(lean_worlds(), &file, Some(world), &[]).is_err());
    install(root.path(), world.tag(), &v4_8_0_header());
    let error = source_world_for(lean_worlds(), &file, Some(world), &roots).unwrap_err();
    assert!(error.to_string().contains("another build"), "{error}");
}

#[test]
fn source_world_preserves_implicit_measured_refusal_and_default_binding() {
    let (_root, file) = project(None);
    let selected = source_world_for(lean_worlds(), &file, None, &[]).unwrap();
    assert_eq!(selected.world(), LeanWorld::ORACLE);
    assert_eq!(selected.imports(), Ok(&ImportWorld::CheckoutPin));
    assert_eq!(selected.declared_world(), None);
    let (root, file) = project(Some("leanprover/lean4:v4.36.0-rc2"));
    install(root.path(), "v4.36.0-rc2", &recent_header());
    // The installed measured world is not opted into: its imports are
    // refused, and its source language (variable visibility) is not taken.
    let implicit =
        source_world_for(lean_worlds(), &file, None, &[root.path().join("elan")]).unwrap();
    let error = implicit.imports().unwrap_err();
    assert!(error.to_string().contains("measured world"), "{error}");
    assert_eq!(implicit.world(), LeanWorld::ORACLE);
    assert!(!implicit.world().variable_visibility());
    assert_eq!(implicit.declared_world(), None);
}

#[test]
fn stable_project_pin_declares_only_the_exact_installed_world() {
    let world = LeanWorld::Lean436;
    let (root, file) = project(Some("leanprover/lean4:v4.36.0"));
    let roots = [root.path().join("elan")];
    let select = || source_world_for(lean_worlds(), &file, None, &roots);
    let refusal = select().unwrap_err().to_string();
    assert!(
        refusal.contains("v4.36.0") && refusal.contains("not installed"),
        "{refusal}"
    );

    install(root.path(), world.tag(), &recent_header());
    let refusal = select().unwrap_err().to_string();
    assert!(
        refusal.contains("v4.36.0") && refusal.contains("another build"),
        "{refusal}"
    );

    let fixture = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures/olean/v4.36.0/plain/StablePlain.olean");
    let bytes = fs::read(fixture).expect("official stable fixture");
    let lib = install(root.path(), world.tag(), &bytes[..HEADER_SIZE_V2]);
    let selected = select().unwrap();
    assert_eq!(selected.world(), world);
    assert_eq!(selected.declared_world(), Some(world.tag()));
    assert_eq!(
        selected.imports(),
        Ok(&ImportWorld::Project {
            world: world.tag(),
            lean_toolchain: root
                .path()
                .join("proj/lean-toolchain")
                .canonicalize()
                .unwrap(),
            lib,
        })
    );
}

#[test]
fn an_explicit_source_choice_does_not_admit_canary_artifacts() {
    static CANARY: &[LeanWorldRow] = &[LeanWorldRow {
        world: "v4.35.0",
        state: WorldState::Canary,
        identity: HeaderIdentity::from_parts(2, 0, [b'a'; 40]),
        lean_version: Some("4.35.0"),
    }];
    let (_root, file) = project(None);
    let error = source_world_for(CANARY, &file, Some(LeanWorld::Lean435), &[]).unwrap_err();
    assert!(error
        .to_string()
        .contains("canary artifacts remain refused"));
}

/// A project directory holding `lean-toolchain` = `toolchain` (none when
/// `None`) and a source file, under a fresh temporary root.
fn project(toolchain: Option<&str>) -> (TempDir, PathBuf) {
    let root = TempDir::new().expect("tempdir");
    let dir = root.path().join("proj");
    fs::create_dir_all(dir.join("Src")).expect("project dirs");
    if let Some(toolchain) = toolchain {
        fs::write(dir.join("lean-toolchain"), format!("{toolchain}\n")).expect("lean-toolchain");
    }
    let file = dir.join("Src/Main.lean");
    fs::write(&file, "import Lean\n").expect("source");
    (root, file)
}

/// The tracked v4.8.0 witness (`lean_worlds.tsv`'s Frontend-only row): its
/// header is that world's identity.
fn v4_8_0_header() -> Vec<u8> {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures/olean/v4.8.0/witness/FactLib.olean");
    let bytes = fs::read(path).expect("tracked v4.8.0 witness");
    bytes[..crate::header::HEADER_SIZE].to_vec()
}

/// An elan root under `root` with `leanprover/lean4:<world>` installed: an
/// `Init/Prelude.olean` holding `header`.
fn install(root: &Path, world: &str, header: &[u8]) -> PathBuf {
    let lib = root
        .join("elan/toolchains")
        .join(format!("leanprover--lean4---{world}"))
        .join("lib/lean");
    fs::create_dir_all(lib.join("Init")).expect("lib dirs");
    fs::write(lib.join("Init/Prelude.olean"), header).expect("prelude header");
    lib
}

fn oracle() -> &'static LeanWorldRow {
    lean_worlds()
        .iter()
        .find(|row| row.state == WorldState::Oracle)
        .expect("exactly one Oracle row")
}

#[test]
fn test_import_world_without_lean_toolchain_is_the_checkout_pin() {
    let (_root, file) = project(None);
    assert_eq!(
        import_world_for(lean_worlds(), &file, &[]),
        Ok(ImportWorld::CheckoutPin)
    );
}

#[test]
fn test_import_world_naming_the_oracle_or_a_clean_toolchain_is_the_checkout_pin() {
    let pin = format!("{LEAN_OWNER}{}", oracle().world);
    for toolchain in [
        pin.as_str(),
        oracle().world,
        "clean",
        "clean:stable",
        "alabsystems/clean:v1.1.0",
        "  clean:stable  ",
    ] {
        let (_root, file) = project(Some(toolchain));
        assert_eq!(
            import_world_for(lean_worlds(), &file, &[]),
            Ok(ImportWorld::CheckoutPin),
            "{toolchain}"
        );
    }
}

#[test]
fn test_import_world_of_a_frontend_only_project_is_its_installed_stdlib() {
    let (root, file) = project(Some("leanprover/lean4:v4.8.0"));
    let lib = install(root.path(), "v4.8.0", &v4_8_0_header());
    let elan = vec![root.path().join("elan")];
    match import_world_for(lean_worlds(), &file, &elan).expect("an installed readable world") {
        ImportWorld::Project {
            world,
            lean_toolchain,
            lib: found,
        } => {
            assert_eq!(world, "v4.8.0");
            assert_eq!(found, lib);
            assert!(lean_toolchain.ends_with("proj/lean-toolchain"));
        }
        other => panic!("expected the project's world, got {other:?}"),
    }
    // elan's short spelling names the same toolchain.
    fs::write(
        file.parent()
            .and_then(Path::parent)
            .expect("project dir")
            .join("lean-toolchain"),
        "v4.8.0\n",
    )
    .expect("short spelling");
    assert!(matches!(
        import_world_for(lean_worlds(), &file, &elan),
        Ok(ImportWorld::Project {
            world: "v4.8.0",
            ..
        })
    ));
    // The project's world replaces the checkout's pin among the default
    // roots (over an empty environment, so no developer variable leaks in).
    let no_vars = |_: &str| None;
    let read_dir = |path: &Path| fs::read_dir(path);
    let world = ImportWorld::Project {
        world: "v4.8.0",
        lean_toolchain: PathBuf::from("lean-toolchain"),
        lib: lib.clone(),
    };
    assert_eq!(
        search_paths_in_world_with(&world, no_vars, read_dir),
        vec![lib]
    );
    let pin = crate::pinned_lean_lib_path().expect(crate::test_support::PINNED_LEAN_REQUIRED);
    assert_eq!(
        search_paths_in_world_with(&ImportWorld::CheckoutPin, no_vars, read_dir),
        vec![pin]
    );
}

#[test]
fn test_import_world_refuses_a_world_no_row_names_by_name() {
    for toolchain in [
        "leanprover/lean4:v4.99.0",
        "leanprover/lean4:v4.30.0",
        "leanprover/lean4:nightly-2026-10-01",
        "someone/lean4-fork:v4.8.0",
    ] {
        let (_root, file) = project(Some(toolchain));
        let err = import_world_for(lean_worlds(), &file, &[]).expect_err(toolchain);
        assert_eq!(err.toolchain, toolchain);
        assert!(
            err.reason
                .starts_with("is not a Lean world this Clean reads (it reads "),
            "{toolchain}: {err}"
        );
        assert!(err.reason.contains("v4.8.0 (frontend-only)"), "{err}");
        assert!(err.to_string().contains("are refused"), "{err}");
    }
}

/// What elan 4.2.3 does with each `lean-toolchain` (measured 2026-10-21 with
/// `elan show`): the first line, trimmed, names the toolchain; a file whose
/// first line is not a name is "invalid toolchain name".
#[test]
fn test_lean_toolchain_is_read_as_elan_reads_it() {
    for (content, elan_reads) in [
        ("leanprover/lean4:v4.8.0", true),
        ("  leanprover/lean4:v4.8.0  \n", true),
        ("leanprover/lean4:v4.8.0\n\n", true),
        ("leanprover/lean4:v4.8.0\nleanprover/lean4:v4.99.0\n", true),
        ("v4.8.0\n", true),
        ("\nleanprover/lean4:v4.8.0\n", false),
        ("# c\nleanprover/lean4:v4.8.0\n", false),
        ("-- c\nleanprover/lean4:v4.8.0\n", false),
        ("\u{feff}leanprover/lean4:v4.8.0\n", false),
        ("", false),
    ] {
        let root = TempDir::new().expect("tempdir");
        let dir = root.path().join("proj");
        fs::create_dir_all(&dir).expect("dir");
        fs::write(dir.join("lean-toolchain"), content).expect("lean-toolchain");
        let file = dir.join("Main.lean");
        fs::write(&file, "").expect("source");
        install(root.path(), "v4.8.0", &v4_8_0_header());
        let result = import_world_for(lean_worlds(), &file, &[root.path().join("elan")]);
        if elan_reads {
            assert!(
                matches!(
                    result,
                    Ok(ImportWorld::Project {
                        world: "v4.8.0",
                        ..
                    })
                ),
                "{content:?}: {result:?}"
            );
        } else {
            let err = result.expect_err(content);
            assert!(
                err.reason.starts_with("is not a toolchain name elan reads"),
                "{content:?}: {err}"
            );
        }
    }
}

/// Lake builds every package of a workspace with the root's toolchain: a
/// dependency's own `lean-toolchain` does not choose its world.
#[test]
fn test_a_lake_dependency_takes_the_workspace_roots_world() {
    let root = TempDir::new().expect("tempdir");
    let ws = root.path().join("ws");
    let dep = ws.join(".lake/packages/Dep");
    fs::create_dir_all(&dep).expect("dirs");
    fs::write(ws.join("lean-toolchain"), "leanprover/lean4:v4.8.0\n").expect("root");
    fs::write(
        dep.join("lean-toolchain"),
        format!("{LEAN_OWNER}{}\n", oracle().world),
    )
    .expect("dep");
    fs::write(dep.join("Dep.lean"), "").expect("dep source");
    fs::write(ws.join("Main.lean"), "").expect("root source");
    install(root.path(), "v4.8.0", &v4_8_0_header());
    let elan = vec![root.path().join("elan")];
    for file in [dep.join("Dep.lean"), ws.join("Main.lean")] {
        assert!(
            matches!(
                import_world_for(lean_worlds(), &file, &elan),
                Ok(ImportWorld::Project {
                    world: "v4.8.0",
                    ..
                })
            ),
            "{}",
            file.display()
        );
    }
    // Twin: the dependency's directory checked as a project of its own
    // (outside any `.lake/packages`) takes its own lean-toolchain.
    let alone = root.path().join("alone");
    fs::create_dir_all(&alone).expect("dir");
    fs::copy(dep.join("lean-toolchain"), alone.join("lean-toolchain")).expect("copy");
    fs::write(alone.join("Dep.lean"), "").expect("source");
    assert_eq!(
        import_world_for(lean_worlds(), &alone.join("Dep.lean"), &elan),
        Ok(ImportWorld::CheckoutPin)
    );
}

/// The `lean-toolchain` a file's checking tool reads (measured 2026-10-22,
/// elan 4.2.3): in a v4.8.0 package whose library `Inner` covers `Inner/`,
/// `lake build Inner.Lib` runs Lean 4.8.0 although `Inner/lean-toolchain`
/// names v4.30.0-rc2; under a package that does not build the file (`lake
/// build` there is "unknown target"), `lean` in the file's directory runs the
/// nearer toolchain; an `Inner/` with its own lakefile is its own package.
#[test]
fn test_a_file_takes_the_toolchain_of_the_package_that_builds_it() {
    let root = TempDir::new().expect("tempdir");
    let ws = root.path().join("ws");
    let inner = ws.join("Inner");
    fs::create_dir_all(&inner).expect("dirs");
    let lakefile = |libs: &str| {
        fs::write(ws.join("lakefile.toml"), format!("name = \"ws\"\n{libs}")).expect("lakefile");
    };
    lakefile("\n[[lean_lib]]\nname = \"Inner\"\n");
    fs::write(ws.join("lean-toolchain"), "leanprover/lean4:v4.8.0\n").expect("root");
    fs::write(
        inner.join("lean-toolchain"),
        format!("{LEAN_OWNER}{}\n", oracle().world),
    )
    .expect("inner toolchain");
    fs::write(inner.join("Lib.lean"), "").expect("inner source");
    install(root.path(), "v4.8.0", &v4_8_0_header());
    let elan = vec![root.path().join("elan")];
    let world = || import_world_for(lean_worlds(), &inner.join("Lib.lean"), &elan);
    assert!(
        matches!(
            world(),
            Ok(ImportWorld::Project {
                world: "v4.8.0",
                ..
            })
        ),
        "a module of the root package's library takes the root's world: {:?}",
        world()
    );
    // A package that does not build the file: the nearer toolchain.
    lakefile("\n[[lean_lib]]\nname = \"Outer\"\n");
    assert_eq!(world(), Ok(ImportWorld::CheckoutPin));
    // A lakefile that does not say plainly, over two toolchains: refused.
    lakefile("\n[[lean_lib]]\nname = \"Inner\"\nglobs = [\"Inner.+\"]\n");
    match world() {
        Err(refusal) => assert!(refusal.reason.contains("does not say plainly"), "{refusal}"),
        other => panic!("expected a refusal, got {other:?}"),
    }
    // ...and over one toolchain, that one.
    fs::write(inner.join("lean-toolchain"), "leanprover/lean4:v4.8.0\n").expect("same");
    assert!(matches!(
        world(),
        Ok(ImportWorld::Project {
            world: "v4.8.0",
            ..
        })
    ));
    fs::write(
        inner.join("lean-toolchain"),
        format!("{LEAN_OWNER}{}\n", oracle().world),
    )
    .expect("inner toolchain");
    // An `Inner/` with its own lakefile is its own package.
    lakefile("\n[[lean_lib]]\nname = \"Inner\"\n");
    fs::write(inner.join("lakefile.toml"), "name = \"inner\"\n").expect("inner lakefile");
    assert_eq!(world(), Ok(ImportWorld::CheckoutPin));
    // With no lakefile anywhere above, the nearest `lean-toolchain` decides.
    fs::remove_file(inner.join("lakefile.toml")).expect("rm inner lakefile");
    fs::remove_file(ws.join("lakefile.toml")).expect("rm root lakefile");
    assert_eq!(world(), Ok(ImportWorld::CheckoutPin));
}

/// A dependency reached through a symlinked `<ws>/.lake/packages/<dep>`
/// still takes the workspace's world: the anchor is read on the path as
/// given, before symlinks are resolved.
#[cfg(unix)]
#[test]
fn test_a_symlinked_lake_dependency_takes_the_workspace_roots_world() {
    let root = TempDir::new().expect("tempdir");
    let ws = root.path().join("ws");
    let shared = root.path().join("Dep-shared");
    fs::create_dir_all(ws.join(".lake/packages")).expect("dirs");
    fs::create_dir_all(&shared).expect("dirs");
    fs::write(ws.join("lean-toolchain"), "leanprover/lean4:v4.8.0\n").expect("root");
    fs::write(shared.join("lakefile.toml"), "name = \"Dep\"\n").expect("dep lakefile");
    fs::write(
        shared.join("lean-toolchain"),
        format!("{LEAN_OWNER}{}\n", oracle().world),
    )
    .expect("dep toolchain");
    fs::write(shared.join("Dep.lean"), "").expect("dep source");
    std::os::unix::fs::symlink(&shared, ws.join(".lake/packages/Dep")).expect("symlink");
    install(root.path(), "v4.8.0", &v4_8_0_header());
    let elan = vec![root.path().join("elan")];
    let through_link = ws.join(".lake/packages/Dep/Dep.lean");
    assert!(matches!(
        import_world_for(lean_worlds(), &through_link, &elan),
        Ok(ImportWorld::Project {
            world: "v4.8.0",
            ..
        })
    ));
    // Twin: the shared copy checked where it lives is its own package.
    assert_eq!(
        import_world_for(lean_worlds(), &shared.join("Dep.lean"), &elan),
        Ok(ImportWorld::CheckoutPin)
    );
}

#[test]
fn test_import_world_refuses_a_readable_world_that_is_not_installed() {
    let (root, file) = project(Some("leanprover/lean4:v4.8.0"));
    let empty = vec![root.path().join("no-elan-here")];
    let err = import_world_for(lean_worlds(), &file, &empty).expect_err("not installed");
    assert!(err.reason.contains("is not installed"), "{err}");
}

#[test]
fn test_import_world_refuses_another_build_installed_under_the_name() {
    let (root, file) = project(Some("leanprover/lean4:v4.8.0"));
    // Twin: the world's own build is selected.
    install(root.path(), "v4.8.0", &v4_8_0_header());
    let elan = vec![root.path().join("elan")];
    assert!(import_world_for(lean_worlds(), &file, &elan).is_ok());
    // Another githash under the same directory name is another build.
    let mut other = v4_8_0_header();
    other[6..14].copy_from_slice(b"819816b2");
    install(root.path(), "v4.8.0", &other);
    let err = import_world_for(lean_worlds(), &file, &elan).expect_err("another build");
    assert!(err.reason.contains("another build"), "{err}");
}

const fn row(world: &'static str, state: WorldState, fill: u8) -> LeanWorldRow {
    LeanWorldRow {
        world,
        state,
        identity: HeaderIdentity::from_parts(2, 1, [fill; 40]),
        lean_version: None,
    }
}

static TABLE: &[LeanWorldRow] = &[
    row("v4.30.0-rc2", WorldState::Oracle, b'0'),
    row("v4.35.0", WorldState::Measured, b'3'),
    row("v4.36.0-rc1", WorldState::Canary, b'4'),
];

#[test]
fn test_import_world_refuses_measured_and_canary_worlds_by_state() {
    for (world, state) in [("v4.35.0", "measured"), ("v4.36.0-rc1", "canary")] {
        let (_root, file) = project(Some(&format!("leanprover/lean4:{world}")));
        let err = import_world_for(TABLE, &file, &[]).expect_err(world);
        assert!(err.reason.contains(state), "{world}: {err}");
    }
}
