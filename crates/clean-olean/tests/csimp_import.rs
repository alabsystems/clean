// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use clean_kernel::{env::csimp, Environment, Name};

fn name(value: &str) -> Name {
    Name::from_string(value)
}

#[test]
fn genuine_imported_csimp_keeps_module_scope_and_reloads_without_duplicate_rules() {
    let fixture = clean_olean::test_support::compiled_fixture_dir("csimp_import");
    let paths = vec![
        fixture,
        clean_olean::require_pinned_lean_lib_path().expect("pinned SDK"),
    ];
    let mut env = Environment::for_lean_replay();
    csimp::begin_source_module(&mut env, name("Caller"), vec![]);
    clean_olean::load_module_with_deps(&mut env, "CSimpImport", &paths)
        .expect("genuine compiler metadata import");
    assert!(
        csimp::rules_for(&env, None).is_empty(),
        "preloading must preserve Caller"
    );
    csimp::begin_source_module(&mut env, name("UsesFixture"), vec![name("CSimpImport")]);
    let select = |env: &Environment, from: &str| {
        csimp::rules_for(env, None)
            .into_iter()
            .filter(|r| r.from == name(from))
            .collect::<Vec<_>>()
    };
    let global = select(&env, "slow");
    assert_eq!(global.len(), 1);
    assert_eq!(global[0].to, name("fast"));
    assert_eq!(global[0].theorem, name("slow_eq_fast"));
    assert!(select(&env, "Scoped.slow").is_empty());
    assert!(select(&env, "Local.slow").is_empty());
    let scoped = csimp::activate_namespace(&mut env, &name("Scoped")).expect("visible namespace");
    assert_eq!(select(&env, "Scoped.slow").len(), 1);
    for token in scoped {
        csimp::retire_local(&mut env, token);
    }
    clean_olean::load_module_with_deps(&mut env, "CSimpImport", &paths).expect("repeat import");
    assert_eq!(
        select(&env, "slow"),
        global,
        "repeat import must not duplicate rules"
    );
    csimp::begin_source_module(&mut env, name("Sibling"), vec![]);
    assert!(select(&env, "slow").is_empty());
    assert!(csimp::activate_namespace(&mut env, &name("Scoped"))
        .unwrap()
        .is_empty());
}
