// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! R131's loader guard, part by part. The artifact reader's rule refuses a
//! non-module artifact whose companion completes its `.olean`'s value-free stub
//! before any part loads (`read_plan`); the per-part loader runs no such rule,
//! so it must not complete the stub itself either: only a module-system
//! artifact's later part completes an earlier part's stub (`Lean.addDecl`
//! exports a public theorem as an axiom of its type), while every importer
//! reads a non-module artifact's `.olean` alone.

use super::*;
use crate::import::load_register::load_part_direct_with_cache;
use crate::import::{ExprInternCache, ImportError};
use crate::test_support::compiled_fixture_dir;
use crate::OleanImportPolicy;
use clean_kernel::env::Environment;

/// Lean's replay environment with `Init.Prelude` loaded, the import of every
/// stub family.
fn prelude_env() -> Environment {
    let mut env = Environment::for_lean_replay();
    let mut search: Vec<std::path::PathBuf> = crate::pinned_lean_lib_path().into_iter().collect();
    search.extend(crate::default_search_paths());
    let mut visited = hashbrown::HashSet::new();
    crate::load_module_with_deps_shared_with_policy(
        &mut env,
        "Init.Prelude",
        &search,
        &mut visited,
        OleanImportPolicy::default(),
    )
    .expect("Init.Prelude loads");
    env
}

/// `module`'s parts in level order (`.olean`, then each companion present), parsed
/// as the loader parses them.
fn parts(module: &str) -> Vec<(String, LoadModule)> {
    let dir = compiled_fixture_dir("replay_forged");
    let base = std::fs::read(dir.join(format!("{module}.olean"))).expect("read the base part");
    let read = |ext: &str| std::fs::read(dir.join(format!("{module}.{ext}"))).ok();
    let server = read("olean.server");
    let private = read("olean.private");
    let mut out = vec![(
        module.to_string(),
        parse_load_module(base.clone()).expect("parse the base part"),
    )];
    if let Some(bytes) = &server {
        out.push((
            format!("{module}._server"),
            parse_load_module_incremental(&base, None, bytes.clone())
                .expect("parse the server part"),
        ));
    }
    if let Some(bytes) = private {
        out.push((
            format!("{module}._private"),
            parse_load_module_incremental(&base, server.as_deref(), bytes)
                .expect("parse the private part"),
        ));
    }
    out
}

/// Load `module`'s parts one by one as parts of one artifact.
fn load_parts(env: &mut Environment, module: &str) -> Result<(), ImportError> {
    let mut cache = ExprInternCache::with_capacity(64);
    for (label, part) in parts(module) {
        load_part_direct_with_cache(
            env,
            &part,
            Some(label),
            Some(module.to_string()),
            &mut cache,
        )?;
    }
    Ok(())
}

#[test]
fn test_a_non_module_companion_never_completes_its_olean_stub_part_by_part() {
    for (module, name) in [
        ("ReplayStubPlainDep", "spd_X"),
        ("ReplayStubPlainPrivDep", "sppd_X"),
    ] {
        let mut env = prelude_env();
        match load_parts(&mut env, module) {
            Err(ImportError::PartsDisagree {
                name: refused,
                module: label,
            }) => assert_eq!((refused.as_str(), label.as_str()), (name, module)),
            other => panic!(
                "{module}: the companion's `{name}` must be refused, not completed: {other:?}; \
                 resident: {:?}",
                env.get_const(&Name::from_string(name))
            ),
        }
    }
    // Control: a `module`'s private part completes the stubs of its `.olean`.
    let mut env = prelude_env();
    load_parts(&mut env, "ReplayStubHonest").expect("the module-system stub layout loads");
    for name in ["sh_t", "sh_u"] {
        let resident = env
            .get_const(&Name::from_string(name))
            .unwrap_or_else(|| panic!("`{name}` is resident"));
        assert!(
            resident.value.is_some(),
            "`{name}`'s stub is completed: {resident:?}"
        );
    }
}
