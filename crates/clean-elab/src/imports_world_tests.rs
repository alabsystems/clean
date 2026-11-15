// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! A checked file's imports resolve in its project's Lean world, and a
//! refused world refuses them by name (gap G72; decision R111 in
//! `docs/DECISIONS.md`).

use crate::{ElabError, FileContext};
use clean_kernel::{Environment, Name};
use clean_parser::SurfaceName;
use std::fs;
use std::path::{Path, PathBuf};

fn module_path(module: &'static str) -> Vec<SurfaceName> {
    vec![SurfaceName::generated_path(module)]
}

/// A source file in a fresh project whose `lean-toolchain` names
/// `toolchain`.
fn file_in_project(root: &Path, toolchain: &str) -> PathBuf {
    let dir = root.join("proj");
    fs::create_dir_all(&dir).expect("project dir");
    fs::write(dir.join("lean-toolchain"), format!("{toolchain}\n")).expect("lean-toolchain");
    let file = dir.join("Main.lean");
    fs::write(&file, "import Lean.NoSuchWorldGateModule\n").expect("source");
    file
}

#[test]
fn test_a_refused_project_world_refuses_imports_by_name_with_no_stand_in() {
    // Twin: in the checkout's world, a `Lean.*` module with no artifact is
    // served by Clean's declared meta shim, as it always was.
    let mut env = Environment::new();
    let mut file_ctx = FileContext::new();
    super::process_imports_for_file(
        &mut env,
        &module_path("Lean.NoSuchWorldGateModule"),
        &mut file_ctx,
    )
    .expect("the Lean.* shim serves an absent Lean.* module in the checkout's world");

    let root = tempfile::tempdir().expect("tempdir");
    let file = file_in_project(root.path(), "leanprover/lean4:v4.99.0");
    let mut env = Environment::new();
    let mut file_ctx = FileContext::new();
    file_ctx.set_import_context_for_file(&file);
    assert!(matches!(file_ctx.import_world(), Some(Err(_))));
    let err = super::process_imports_for_file(
        &mut env,
        &module_path("Lean.NoSuchWorldGateModule"),
        &mut file_ctx,
    )
    .expect_err("a project in a world Clean does not read has no import to resolve");
    match err {
        ElabError::UnresolvedImport { module, reason } => {
            assert_eq!(module, "Lean.NoSuchWorldGateModule");
            assert!(reason.contains("leanprover/lean4:v4.99.0"), "{reason}");
        }
        other => panic!("expected UnresolvedImport, got {other}"),
    }

    // A module this run elaborated from the project's own source stays
    // resolved: a refused run reads no part of any Lean world, so its file is
    // checked against what a file with no imports is (pinned Lean builds a
    // project whose imports are all its own source in any world).
    file_ctx.mark_import_satisfied_from_source(&Name::from_string("Proj.Sibling"));
    super::process_imports_for_file(&mut env, &module_path("Proj.Sibling"), &mut file_ctx)
        .expect("a module satisfied from source stays resolved in a refused world");
    // ...while a Lean module beside it in the same `import` is still refused.
    let both = vec![
        SurfaceName::generated_path("Proj.Sibling"),
        SurfaceName::generated_path("Lean.NoSuchWorldGateModule"),
    ];
    let err = super::process_imports_for_file(&mut env, &both, &mut file_ctx)
        .expect_err("a refused world refuses a module not satisfied from source");
    assert!(
        matches!(&err, ElabError::UnresolvedImport { module, .. }
            if module == "Lean.NoSuchWorldGateModule"),
        "{err}"
    );

    // `--permissive-imports` does not continue past it (R38: no
    // warn-and-continue mode).
    let mut file_ctx = FileContext::new();
    file_ctx.set_import_context_for_file(&file);
    file_ctx.set_import_policy(crate::ImportPolicy::Permissive);
    let err = super::process_imports_for_file(
        &mut env,
        &module_path("Lean.NoSuchWorldGateModule"),
        &mut file_ctx,
    )
    .expect_err("a refused world under the permissive policy");
    assert!(
        err.to_string().contains("leanprover/lean4:v4.99.0"),
        "{err}"
    );
}

#[test]
fn test_a_frontend_world_project_selects_its_own_stdlib() {
    let root = tempfile::tempdir().expect("tempdir");
    let file = file_in_project(root.path(), "leanprover/lean4:v4.8.0");
    let mut file_ctx = FileContext::new();
    file_ctx.set_import_context_for_file(&file);
    match clean_olean::installed_lean_lib_path("leanprover/lean4:v4.8.0") {
        Some(lib48) => match file_ctx.import_world() {
            Some(Ok(clean_olean::ImportWorld::Project { world, lib, .. })) => {
                assert_eq!(*world, "v4.8.0");
                assert_eq!(lib, &lib48);
            }
            other => panic!("expected the v4.8.0 world, got {other:?}"),
        },
        None => {
            let refusal = file_ctx
                .effective_import_search_paths()
                .expect_err("v4.8.0 is not installed here");
            assert!(refusal.reason.contains("is not installed"), "{refusal}");
        }
    }
    // Twin: with no `lean-toolchain`, the checkout's pin.
    let mut file_ctx = FileContext::new();
    file_ctx.set_import_context_for_file(&root.path().join("elsewhere.lean"));
    assert_eq!(
        file_ctx.import_world(),
        Some(&Ok(clean_olean::ImportWorld::CheckoutPin))
    );
}

/// A Lake root holding the committed v4.30.0-rc2 leaf as `Lean/WorldGate.olean`.
fn root_with_oracle_leaf() -> tempfile::TempDir {
    let lib = tempfile::tempdir().expect("tempdir");
    fs::create_dir_all(lib.path().join("Lean")).expect("lib dir");
    fs::copy(
        Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../tests/fixtures/olean/v4.30.0/closure_cache/Init.olean"),
        lib.path().join("Lean/WorldGate.olean"),
    )
    .expect("copy leaf");
    lib
}

#[test]
fn test_the_selected_world_is_declared_before_any_part_loads() {
    // A root searched before the project's stdlib (here a Lake root; the same
    // for LEAN_PATH or MATHLIB_PATH) supplies a part of the Oracle's world.
    let lib = root_with_oracle_leaf();
    let file = lib.path().join("Main.lean");
    let project = clean_olean::ImportWorld::Project {
        world: "v4.8.0",
        lean_toolchain: lib.path().join("lean-toolchain"),
        lib: lib.path().join("no-stdlib-here"),
    };
    let mut env = Environment::new();
    let mut file_ctx = FileContext::new();
    file_ctx.set_import_context(&file, Ok(project));
    file_ctx.set_import_search_paths(vec![lib.path().to_path_buf()]);
    let err =
        super::process_imports_for_file(&mut env, &module_path("Lean.WorldGate"), &mut file_ctx)
            .expect_err("a part of another world than the project's");
    assert!(err.to_string().contains("mixed Lean worlds"), "{err}");
    assert!(err.to_string().contains("v4.8.0"), "{err}");
    assert_eq!(clean_olean::environment_world(&env), Some("v4.8.0"));
    assert!(env.get_const(&Name::from_string("Leaf")).is_none());

    // Twin: in the checkout's world nothing is declared, and the part loads.
    let mut env = Environment::new();
    let mut file_ctx = FileContext::new();
    file_ctx.set_import_context(&file, Ok(clean_olean::ImportWorld::CheckoutPin));
    file_ctx.set_import_search_paths(vec![lib.path().to_path_buf()]);
    super::process_imports_for_file(&mut env, &module_path("Lean.WorldGate"), &mut file_ctx)
        .expect("the Oracle's leaf loads in the checkout's world");
    assert!(env.get_const(&Name::from_string("Leaf")).is_some());
}

/// `--imports-prefer-olean` asks whether a module has an artifact in the
/// run's world (`olean_available_in_world`), not in the world the importing
/// file would select alone (`olean_available_for_module`).
#[test]
fn test_the_prefer_olean_probe_asks_the_runs_world() {
    let root = tempfile::tempdir().expect("tempdir");
    let dir = root.path().join("proj");
    fs::create_dir_all(&dir).expect("project dir");
    let file = dir.join("Main.lean");
    fs::write(&file, "").expect("source");
    let with_leaf = root.path().join("lib-with-leaf");
    fs::create_dir_all(with_leaf.join("WorldGateProbe")).expect("lib dir");
    fs::write(with_leaf.join("WorldGateProbe/Leaf.olean"), "").expect("leaf");
    let without_leaf = root.path().join("lib-without-leaf");
    fs::create_dir_all(&without_leaf).expect("lib dir");
    let project = |lib: PathBuf| {
        Ok(clean_olean::ImportWorld::Project {
            world: "v4.8.0",
            lean_toolchain: dir.join("lean-toolchain"),
            lib,
        })
    };
    let module = Name::from_string("WorldGateProbe.Leaf");
    assert!(crate::olean_available_in_world(
        &module,
        &file,
        &project(with_leaf)
    ));
    assert!(!crate::olean_available_in_world(
        &module,
        &file,
        &project(without_leaf)
    ));
    // The file alone selects the checkout's pin, which has no such module.
    assert!(!crate::olean_available_for_module(&module, &file));
    // A refused world has no artifact to prefer.
    let refused = file_in_project(root.path(), "leanprover/lean4:v4.99.0");
    let world = clean_olean::import_world_for_file(&refused);
    assert!(world.is_err(), "{world:?}");
    assert!(!crate::olean_available_in_world(&module, &refused, &world));
}
