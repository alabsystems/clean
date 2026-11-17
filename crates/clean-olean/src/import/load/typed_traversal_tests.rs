// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::OleanExporter;

#[test]
fn missing_dependency_retry_keeps_only_completed_children() {
    let dir = tempfile::tempdir().unwrap();
    let export = |name: &str, imports: &[(&str, bool)]| {
        let bytes = OleanExporter::export_with_env(
            &Environment::default(),
            imports,
            &[],
            "0000000000000000000000000000000000000000",
        )
        .unwrap();
        std::fs::write(dir.path().join(format!("{name}.olean")), bytes).unwrap();
    };
    export("Root", &[("Child", false), ("Missing", false)]);
    export("Child", &[]);
    let mut env = Environment::default();
    let mut visited = HashSet::new();
    for _ in 0..2 {
        assert!(load_module_with_deps_shared(
            &mut env,
            "Root",
            &[dir.path().to_path_buf()],
            &mut visited
        )
        .is_err());
        assert_eq!(visited, ["Child".to_owned()].into_iter().collect());
        assert_eq!(env.constants().count(), 0);
    }
    export("Missing", &[]);
    load_module_with_deps_shared(&mut env, "Root", &[dir.path().to_path_buf()], &mut visited)
        .unwrap();
    assert_eq!(
        visited,
        ["Root", "Child", "Missing"]
            .map(str::to_owned)
            .into_iter()
            .collect()
    );
    assert!(
        load_module_with_deps_shared(&mut env, "Root", &[], &mut visited)
            .unwrap()
            .is_empty()
    );
}

/// The guarded load asks about every module file before it reads it, the
/// requested module's and each one a header imports, with the index of the
/// search path it was found in. A refusal is the load's answer: the refused
/// file is not read (here it is not an `.olean`, so a read would have failed
/// otherwise), and nothing is registered.
#[test]
fn test_load_module_with_deps_cached_guarded_asks_before_each_read_and_stops_at_a_refusal() {
    use crate::ModuleCache;
    use clean_kernel::{Declaration, Expr};
    use std::path::Path;
    let first = tempfile::tempdir().unwrap();
    let second = tempfile::tempdir().unwrap();
    let export = |dir: &Path, name: &str, imports: &[(&str, bool)]| {
        let mut module = Environment::default();
        module
            .add_decl(Declaration::Axiom {
                name: Name::from_string(&format!("{name}.a")),
                level_params: vec![],
                type_: Expr::prop(),
            })
            .unwrap();
        let bytes = OleanExporter::export_with_env(
            &module,
            imports,
            &[],
            "0000000000000000000000000000000000000000",
        )
        .unwrap();
        std::fs::write(dir.join(format!("{name}.olean")), bytes).unwrap();
    };
    export(first.path(), "Root", &[("Child", false)]);
    export(second.path(), "Child", &[]);
    let search_paths = [first.path().to_path_buf(), second.path().to_path_buf()];

    let mut env = Environment::default();
    let mut asked = Vec::new();
    load_module_with_deps_cached_guarded(
        &mut env,
        "Root",
        &search_paths,
        &ModuleCache::new(),
        &mut |name: &Name, file: &Path, index: usize| {
            asked.push((name.to_string(), file.to_path_buf(), index));
            Ok(())
        },
    )
    .expect("a guard that admits every file loads the graph");
    assert_eq!(
        asked,
        vec![
            ("Root".to_owned(), first.path().join("Root.olean"), 0),
            ("Child".to_owned(), second.path().join("Child.olean"), 1),
        ]
    );
    for name in ["Root.a", "Child.a"] {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{name} was not loaded"
        );
    }

    std::fs::write(second.path().join("Child.olean"), b"not an olean").unwrap();
    let child = Name::anon().str("Child");
    let mut env = Environment::default();
    let refused = load_module_with_deps_cached_guarded(
        &mut env,
        "Root",
        &search_paths,
        &ModuleCache::new(),
        &mut |name: &Name, _: &Path, _: usize| {
            if *name == child {
                return Err(ImportError::UnsupportedModule {
                    module: "Child".to_owned(),
                    reason: "refused by the guard".to_owned(),
                });
            }
            Ok(())
        },
    );
    match refused {
        Err(ImportError::UnsupportedModule { module, reason }) => {
            assert_eq!(
                (module.as_str(), reason.as_str()),
                ("Child", "refused by the guard")
            );
        }
        Err(other) => panic!("the answer is not the guard's refusal: {other}"),
        Ok(_) => panic!("a load whose guard refused a file succeeded"),
    }
    assert_eq!(env.constants().count(), 0, "nothing is registered");
}

#[test]
fn completed_import_data_includes_zero_declaration_aggregators_and_exact_names() {
    let dir = tempfile::tempdir().unwrap();
    let export = |path: &str, imports: &[(&str, bool)]| {
        let bytes = OleanExporter::export_with_env(
            &Environment::default(),
            imports,
            &[],
            "0000000000000000000000000000000000000000",
        )
        .unwrap();
        let path = dir.path().join(path);
        std::fs::create_dir_all(path.parent().unwrap()).unwrap();
        std::fs::write(path, bytes).unwrap();
    };
    export("Root.olean", &[("Nested.Leaf", false)]);
    export("Nested/Leaf.olean", &[]);
    let mut env = Environment::default();
    let (_, completed) =
        load_module_with_deps_and_completed_imports(&mut env, "Root", &[dir.path().to_path_buf()])
            .unwrap();
    assert_eq!(
        env.constants().count(),
        0,
        "availability must not be inferred from declarations"
    );
    assert_eq!(completed.len(), 2);
    assert!(!completed.is_empty());
    assert!(completed.contains_module(&Name::from_string("Root")));
    assert!(completed.contains_module(&Name::from_string("Nested.Leaf")));
    assert!(
        !completed.contains_module(&Name::anon().str("Nested.Leaf")),
        "one quoted component is distinct from two components"
    );
    for name in [
        Name::from_string("Nested"),
        Name::from_string("Root.Missing"),
        Name::anon(),
        Name::anon().num(7),
    ] {
        assert!(
            !completed.contains_module(&name),
            "no namespace or malformed-name completion: {name:?}"
        );
    }
}

#[test]
fn failed_or_cyclic_load_returns_no_completed_import_receipt() {
    let dir = tempfile::tempdir().unwrap();
    let export = |name: &str, imports: &[(&str, bool)]| {
        let bytes = OleanExporter::export_with_env(
            &Environment::default(),
            imports,
            &[],
            "0000000000000000000000000000000000000000",
        )
        .unwrap();
        std::fs::write(dir.path().join(format!("{name}.olean")), bytes).unwrap();
    };
    export("Root", &[("Child", false), ("Missing", false)]);
    export("Child", &[]);
    let failed = load_module_with_deps_and_completed_imports(
        &mut Environment::default(),
        "Root",
        &[dir.path().to_path_buf()],
    )
    .expect_err("a completed child cannot certify a failed aggregate");
    assert!(failed.to_string().contains("Missing"), "{failed}");
    export("CycleA", &[("CycleB", false)]);
    export("CycleB", &[("CycleA", false)]);
    let cycle = load_module_with_deps_and_completed_imports(
        &mut Environment::default(),
        "CycleA",
        &[dir.path().to_path_buf()],
    )
    .expect_err("a cycle supplies no successful completed-import receipt");
    assert!(cycle.to_string().contains("cycle"), "{cycle}");
}

#[test]
fn completed_import_data_preserves_ordinary_loader_definition_bindings() {
    use clean_kernel::{Declaration, Expr};
    let dir = tempfile::tempdir().unwrap();
    let mut source = Environment::default();
    let name = Name::from_string("Snapshot.value");
    source
        .add_decl(Declaration::Definition {
            name: name.clone(),
            level_params: vec![],
            type_: Expr::type_(),
            value: Expr::prop(),
            is_reducible: false,
        })
        .unwrap();
    let bytes = OleanExporter::export_with_env(
        &source,
        &[],
        &[],
        "0000000000000000000000000000000000000000",
    )
    .unwrap();
    std::fs::write(dir.path().join("Snapshot.olean"), bytes).unwrap();
    let mut ordinary = Environment::default();
    load_module_with_deps(&mut ordinary, "Snapshot", &[dir.path().to_path_buf()]).unwrap();
    let mut tracked = Environment::default();
    let (_, completed) = load_module_with_deps_and_completed_imports(
        &mut tracked,
        "Snapshot",
        &[dir.path().to_path_buf()],
    )
    .unwrap();
    let left = ordinary.get_const(&name).unwrap();
    let right = tracked.get_const(&name).unwrap();
    assert!(
        right.value.is_some(),
        "nonvacuous original definition payload"
    );
    assert_eq!(left.name, right.name);
    assert_eq!(left.level_params, right.level_params);
    assert_eq!(left.type_, right.type_);
    assert_eq!(left.value, right.value);
    assert_eq!(left.kind, right.kind);
    assert_eq!(left.is_reducible, right.is_reducible);
    assert_eq!(left.reducibility, right.reducibility);
    assert!(completed.contains_module(&Name::from_string("Snapshot")));
}
