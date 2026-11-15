// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use clean_kernel::{env::Environment, name::Name};
use clean_olean::test_support::compiled_fixture_dir;
use clean_olean::{
    load_module_with_deps, load_module_with_deps_bounded, load_module_with_deps_bounded_shared,
    load_module_with_deps_shared, load_modules_with_deps, ImportError, LoadSummary, OleanExporter,
};
use std::path::PathBuf;

/// The `module_twins` family compiled by the pinned Lean (see
/// `tests/fixtures/lean/v4.30.0-rc2/module_twins/README.md`): `Root.olean`,
/// `Module.part.olean` (quoted, one component) and `Module/part.olean`
/// (hierarchical, two components), every source `prelude`, so this directory is
/// the only search path the uncached loaders need. Fails closed when the pinned
/// toolchain is absent.
fn fixture() -> PathBuf {
    compiled_fixture_dir("module_twins")
}

fn assert_original_graph(env: &Environment, summaries: &[LoadSummary]) {
    assert!(summaries
        .iter()
        .all(|summary| summary.skipped_constants.is_empty()));
    assert_eq!(
        env.constants().count(),
        4,
        "both original imports and both referring bodies"
    );
    for (reader, target) in [("fromQuoted", "quotedTag"), ("fromNested", "nestedTag")] {
        let target = Name::anon().str(target);
        assert!(
            env.get_const(&target).is_some(),
            "missing exact original dependency {target:?}"
        );
        let item = env
            .get_const(&Name::anon().str(reader))
            .expect("original root definition");
        assert_eq!(
            item.value
                .as_ref()
                .expect("original root body")
                .collect_constants(),
            [target].into_iter().collect()
        );
    }
}

#[test]
fn ordinary_imports_keep_quoted_and_nested_dependencies() {
    let mut env = Environment::default();
    let summaries = load_module_with_deps(&mut env, "Root", &[fixture()]).unwrap();
    assert_original_graph(&env, &summaries);
}

#[test]
fn shared_imports_keep_quoted_and_nested_dependencies() {
    let mut env = Environment::default();
    let mut visited = Default::default();
    let summaries =
        load_module_with_deps_shared(&mut env, "Root", &[fixture()], &mut visited).unwrap();
    assert_original_graph(&env, &summaries);
    assert_eq!(visited.len(), 3, "three exact source modules");
    assert!(
        load_module_with_deps_shared(&mut env, "Root", &[], &mut visited)
            .unwrap()
            .is_empty()
    );
    assert_original_graph(&env, &[]);
}

#[test]
fn prior_nested_import_does_not_hide_quoted_dependency() {
    let mut env = Environment::default();
    let mut visited = Default::default();
    load_module_with_deps_shared(&mut env, "Module.part", &[fixture()], &mut visited).unwrap();
    assert!(
        visited.contains("Module.part"),
        "ordinary shared keys stay compatible"
    );
    assert_eq!(env.constants().count(), 1);
    let summaries =
        load_module_with_deps_shared(&mut env, "Root", &[fixture()], &mut visited).unwrap();
    assert_original_graph(&env, &summaries);
    assert_eq!(visited.len(), 3);
}

#[test]
fn union_imports_keep_quoted_and_nested_dependencies() {
    let mut env = Environment::default();
    let summaries = load_modules_with_deps(
        &mut env,
        &["Root".into(), "Module.part".into()],
        &[fixture()],
    )
    .unwrap();
    assert_original_graph(&env, &summaries);
}

#[test]
fn bounded_imports_count_exact_names_and_preserve_bodies() {
    let mut env = Environment::default();
    let summaries = load_module_with_deps_bounded(&mut env, "Root", &[fixture()], 3).unwrap();
    assert_original_graph(&env, &summaries);
}

#[test]
fn bounded_discovery_cannot_collapse_distinct_module_names() {
    let mut env = Environment::default();
    let result = load_module_with_deps_bounded(&mut env, "Root", &[fixture()], 2);
    assert!(
        matches!(result, Err(ImportError::UnsupportedModule { reason, .. })
        if reason.contains("bounded loader limit")),
        "three exact modules cannot fit in two slots"
    );
    assert_eq!(
        env.constants().count(),
        0,
        "discovery refusal precedes registration"
    );
}

#[test]
fn bounded_shared_imports_count_only_exact_remaining_modules() {
    let mut env = Environment::default();
    let mut visited = Default::default();
    load_module_with_deps_shared(&mut env, "Module.part", &[fixture()], &mut visited).unwrap();
    let summaries =
        load_module_with_deps_bounded_shared(&mut env, "Root", &[fixture()], 2, &mut visited)
            .unwrap();
    assert_original_graph(&env, &summaries);
    assert_eq!(visited.len(), 3);
    assert!(
        load_module_with_deps_bounded_shared(&mut env, "Root", &[], 0, &mut visited)
            .unwrap()
            .is_empty()
    );
}

#[test]
fn missing_module_is_not_marked_successfully_loaded() {
    let mut env = Environment::default();
    let mut visited = Default::default();
    for _ in 0..2 {
        assert!(
            load_module_with_deps_shared(&mut env, "DefinitelyAbsent", &[], &mut visited).is_err()
        );
        assert!(
            visited.is_empty(),
            "failed discovery is not a completed import"
        );
        assert_eq!(env.constants().count(), 0);
    }
}

#[test]
fn explicit_completed_ordinary_shared_key_still_skips_io() {
    let mut env = Environment::default();
    // The legacy public API accepts caller-owned completed-module keys.
    let mut visited = ["Missing".to_owned()].into_iter().collect();
    assert!(
        load_module_with_deps_shared(&mut env, "Missing", &[], &mut visited)
            .unwrap()
            .is_empty()
    );
    assert!(
        load_module_with_deps_bounded_shared(&mut env, "Missing", &[], 0, &mut visited)
            .unwrap()
            .is_empty()
    );
    assert_eq!(visited.len(), 1);
    assert_eq!(env.constants().count(), 0);
}

#[test]
fn cyclic_module_is_not_a_successful_import() {
    let dir = tempfile::tempdir().unwrap();
    let bytes = OleanExporter::export_with_env(
        &Environment::default(),
        &[("Cycle", false)],
        &[],
        "0000000000000000000000000000000000000000",
    )
    .unwrap();
    std::fs::write(dir.path().join("Cycle.olean"), bytes).unwrap();
    let mut env = Environment::default();
    let mut visited = Default::default();
    for _ in 0..2 {
        let result = load_module_with_deps_shared(
            &mut env,
            "Cycle",
            &[dir.path().to_path_buf()],
            &mut visited,
        );
        assert!(
            matches!(result, Err(ImportError::UnsupportedModule { reason, .. })
            if reason.contains("cycle")),
            "a dependency cycle must be reported, not skipped as completed"
        );
        assert!(visited.is_empty());
        assert_eq!(env.constants().count(), 0);
    }
}
