// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The bounded loaders' import-graph budget: discover a module's import
//! closure from `.olean` headers alone and refuse it past `max_modules`
//! before anything is converted.

use crate::import::path::{
    legacy_module_name, module_visit_key, resolve_typed_module_path_in_world,
};
use crate::import::typed_imports::parse_typed_imports;
use crate::import::ImportError;
use clean_kernel::env::Environment;
use clean_kernel::name::Name;
use hashbrown::HashSet;
use std::collections::VecDeque;
use std::path::PathBuf;

pub(super) fn enforce_module_graph_limit(
    env: &Environment,
    module: &str,
    search_paths: &[PathBuf],
    max_modules: usize,
) -> Result<(), ImportError> {
    enforce_module_graph_limit_with_loaded(env, module, search_paths, max_modules, &HashSet::new())
}

/// Bounded import-graph discovery that treats every module in `already_loaded`
/// as a leaf: it neither resolves its path nor descends into its imports, and
/// it does not count against `max_modules`.
///
/// This is the shared-env analog of [`enforce_module_graph_limit`]: when many
/// target closures are accumulated into one cumulative env, a subgraph an
/// earlier target already loaded must NOT be re-walked (no redundant header
/// reads) and must NOT recount against this target's budget. The cap then bounds
/// only the *new* modules this target contributes, which is the correct
/// per-target depth guard for the cumulative load.
fn enforce_module_graph_limit_with_loaded(
    env: &Environment,
    module: &str,
    search_paths: &[PathBuf],
    max_modules: usize,
    already_loaded: &HashSet<String>,
) -> Result<(), ImportError> {
    enforce_typed_module_graph_limit_with_loaded(
        env,
        &legacy_module_name(module)?,
        search_paths,
        max_modules,
        already_loaded,
    )
}

/// Every module the walk reads is held to `env`'s Lean world first (R81),
/// without binding it: a module of a refused world is refused by name here,
/// not by a parse error or the budget.
pub(super) fn enforce_typed_module_graph_limit_with_loaded(
    env: &Environment,
    module: &Name,
    search_paths: &[PathBuf],
    max_modules: usize,
    already_loaded: &HashSet<String>,
) -> Result<(), ImportError> {
    // A root already fully loaded by an earlier target contributes nothing new.
    let root = module.clone();
    if already_loaded.contains(&module_visit_key(&root)?) {
        return Ok(());
    }

    let mut discovered = HashSet::new();
    let mut pending = VecDeque::from([root]);

    while let Some(current) = pending.pop_front() {
        // Skip subgraphs already resident in the cumulative env: they were
        // walked and registered by a prior target, so re-reading their headers
        // here would re-do O(shared closure) work per target — exactly what the
        // shared-env cache exists to avoid.
        if already_loaded.contains(&module_visit_key(&current)?) {
            continue;
        }
        if !discovered.insert(current.clone()) {
            continue;
        }

        if discovered.len() > max_modules {
            return Err(ImportError::UnsupportedModule {
                module: module.to_string(),
                reason: format!(
                    "import graph exceeds the bounded loader limit of {max_modules} modules \
                     while discovering {current}; full Lean module loading is not yet \
                     supported on the frontend import path"
                ),
            });
        }

        let path = resolve_typed_module_path_in_world(
            &current,
            search_paths,
            crate::environment_world(env),
        )?;
        let bytes = std::fs::read(&path).map_err(|source| ImportError::FileUnreadable {
            path: path.clone(),
            source,
        })?;
        crate::import::world_gate::check_part_bytes(env, &current.to_string(), &bytes)?;
        for import in parse_typed_imports(&bytes)? {
            if !discovered.contains(&import.module_name)
                && !already_loaded.contains(&module_visit_key(&import.module_name)?)
            {
                pending.push_back(import.module_name);
            }
        }
    }

    Ok(())
}
