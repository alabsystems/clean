// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use clean_kernel::{Environment, LeanWorld, Name};
use clean_olean::{
    declare_environment_world, load_typed_module_with_deps_bounded,
    load_typed_module_with_deps_cached, load_typed_module_with_deps_parallel,
    resolve_typed_module_path_in_world, ModuleCache, OleanExporter,
};
use std::fs;

fn environment(world: LeanWorld) -> Environment {
    let mut env = Environment::default();
    declare_environment_world(&mut env, world.tag()).unwrap();
    env
}

#[test]
fn a_package_shadows_later_submodules_on_cold_and_warm_loads() {
    for world in [LeanWorld::Lean430Rc2, LeanWorld::Lean436] {
        check_package_shadowing(world);
    }
}

fn check_package_shadowing(world: LeanWorld) {
    let dir = tempfile::tempdir().unwrap();
    let earlier = dir.path().join("earlier");
    let later = dir.path().join("later");
    fs::create_dir_all(&earlier).unwrap();
    fs::create_dir_all(later.join("Pkg.With.Dot")).unwrap();
    let module = Name::anon().str("Pkg.With.Dot").str("Child");
    let child = "Pkg.With.Dot/Child.olean";
    let bytes = OleanExporter::export_with_env(
        &Environment::default(),
        &[],
        &[],
        "0000000000000000000000000000000000000000",
    )
    .unwrap();
    fs::write(later.join(child), bytes).unwrap();
    let paths = [earlier.clone(), later.clone()];
    let cache = ModuleCache::new();
    load_typed_module_with_deps_cached(&mut environment(world), &module, &paths, &cache).unwrap();

    // A root can claim this quoted package with either a file or a directory.
    // Its later child remains on disk and in the cache in both cases.
    for package_file in [true, false] {
        if package_file {
            fs::write(earlier.join("Pkg.With.Dot.olean"), []).unwrap();
        } else {
            fs::remove_file(earlier.join("Pkg.With.Dot.olean")).unwrap();
            fs::create_dir(earlier.join("Pkg.With.Dot")).unwrap();
        }
        assert_eq!(
            resolve_typed_module_path_in_world(&module, &paths, Some(world.tag())).unwrap(),
            earlier.join(child)
        );
        assert_eq!(
            resolve_typed_module_path_in_world(&module, &paths, Some(LeanWorld::Lean435.tag()))
                .unwrap(),
            later.join(child)
        );
        let expected = earlier.join(child);
        for error in [
            load_typed_module_with_deps_bounded(&mut environment(world), &module, &paths, 3)
                .unwrap_err(),
            load_typed_module_with_deps_cached(&mut environment(world), &module, &paths, &cache)
                .unwrap_err(),
            load_typed_module_with_deps_parallel(&mut environment(world), &module, &paths, &cache)
                .unwrap_err(),
        ] {
            assert!(
                error.to_string().contains(expected.to_str().unwrap()),
                "{error}"
            );
        }
        load_typed_module_with_deps_bounded(
            &mut environment(LeanWorld::Lean435),
            &module,
            &paths,
            3,
        )
        .unwrap();
    }
}
