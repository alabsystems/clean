// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Cached and parallel loading: the module graph is captured once, cache
//! misses are parsed (in parallel when asked), and registration stays
//! dependency-ordered through the parent's `load_artifact_parts`.
//!
//! The load reads its caller's deadline (`super::super::deadline`) before it
//! reads, decodes or registers each module, and stops with
//! [`ImportError::Interrupted`] once it has passed. A decoded module enters the
//! cache only when its decode finished with the deadline not passed, so a load
//! cut anywhere leaves whole modules in the cache, or none.
//!
//! A guarded load ([`load_module_with_deps_cached_guarded`]) asks its caller
//! about each module file the walk resolves before it reads it.

use super::super::deadline;
pub use super::super::module_cache_direct::ModuleCaptureLimits;
use super::super::module_cache_direct::{CaptureBudget, CapturedModule, DirectModule};
use super::super::path::{legacy_module_name, resolve_typed_module_file};
use super::super::typed_imports::parse_typed_imports;
use super::super::world_gate;
use super::super::{
    estimate_module_graph_size, ExprInternCache, ImportError, LoadSummary, ModuleCache,
    OleanImportPolicy,
};
use super::load_artifact_parts;
use clean_kernel::env::Environment;
use clean_kernel::name::Name;
use hashbrown::HashMap;
use hashbrown::HashSet;
use rayon::prelude::*;
use std::path::{Path, PathBuf};
use std::sync::Arc;

/// Borrowed bytes from one actual module capture, before import discovery,
/// cache lookup, decoding or registration. These are the same owned bytes
/// the loader subsequently consumes; changing the source files in a callback
/// cannot change this capture. This view is comparison data, not proof authority.
#[derive(Clone, Copy, Debug)]
pub struct CapturedModuleBytes<'a> {
    /// Canonical base path recorded while capturing the artifact. The separate
    /// callback path is the original lexical path the search resolver selected.
    pub canonical_path: &'a Path,
    /// Actual base `.olean` contents.
    pub base: &'a [u8],
    /// Actual optional `.olean.server` contents, including an empty present file.
    pub server: Option<&'a [u8]>,
    /// Actual optional `.olean.private` contents, including an empty present file.
    pub private: Option<&'a [u8]>,
    /// Actual optional `.ir` contents. Absence is frozen too: late-binding
    /// metadata never discovers a file that appeared after this capture.
    pub ir: Option<&'a [u8]>,
}

type PathGuard<'a> = dyn FnMut(&Name, &Path, usize) -> Result<(), ImportError> + 'a;
type BytesGuard<'a> =
    dyn FnMut(&Name, &Path, CapturedModuleBytes<'_>) -> Result<(), ImportError> + 'a;

/// Load a complete multi-root graph after caller checks of both the selected
/// paths and the exact captured base/server/private bytes.
///
/// `before_read` receives each typed module Name, original resolved lexical
/// path and search-directory index before filesystem capture. `check_captured`
/// then receives that same lexical path and the actual owned contents, before
/// typed import discovery, cache lookup or decoding. Both checks run for every
/// discovered root/dependency, including a content-cache hit. The graph is
/// entirely captured, checked, decoded and cycle-checked before any artifact
/// declaration is registered. A rejection has no fallback to another path.
///
/// This uses the existing direct artifact registration policy and the full
/// uncached multi-root post-load metadata fixups. It does NOT authenticate
/// declarations already present in `env`, grant a verification grade, or close
/// the imported environment's TCB; callers requiring a fresh context supply one.
pub fn load_modules_with_deps_checked(
    env: &mut Environment,
    modules: &[String],
    search_paths: &[PathBuf],
    before_read: &mut PathGuard<'_>,
    check_captured: &mut BytesGuard<'_>,
) -> Result<Vec<LoadSummary>, ImportError> {
    let modules = modules
        .iter()
        .map(|module| legacy_module_name(module))
        .collect::<Result<Vec<_>, _>>()?;
    load_captured_graph(
        env,
        &modules,
        search_paths,
        &ModuleCache::new(),
        false,
        Some(before_read),
        Some(check_captured),
        true,
        None,
    )
}

/// The checked loader with an explicit caller-owned capture policy.
///
/// Every present base/server/private/IR descriptor is checked against the part
/// and remaining graph byte budget before allocation, including cache hits.
/// Module/root-selector and import-row limits bound graph capture, not later
/// kernel work. A refusal registers no artifact declaration. Exact byte and
/// absence identities and the two callbacks are otherwise the same as
/// [`load_modules_with_deps_checked`]; limits grant no trust or proof grade.
pub fn load_modules_with_deps_checked_with_limits(
    env: &mut Environment,
    modules: &[String],
    search_paths: &[PathBuf],
    limits: ModuleCaptureLimits,
    before_read: &mut PathGuard<'_>,
    check_captured: &mut BytesGuard<'_>,
) -> Result<Vec<LoadSummary>, ImportError> {
    CaptureBudget::new(Some(limits)).check_roots(modules.len())?;
    let modules = modules
        .iter()
        .map(|module| legacy_module_name(module))
        .collect::<Result<Vec<_>, _>>()?;
    load_captured_graph(
        env,
        &modules,
        search_paths,
        &ModuleCache::new(),
        false,
        Some(before_read),
        Some(check_captured),
        true,
        Some(limits),
    )
}

/// Load a module and its dependencies through the typed direct importer.
/// The cache reuses decoded raw parts only when their path and complete
/// base/server/private content identities still match. Display-projected
/// ParsedModule values never reconstruct a cached kernel declaration.
pub fn load_module_with_deps_cached(
    env: &mut Environment,
    module: &str,
    search_paths: &[PathBuf],
    cache: &ModuleCache,
) -> Result<Vec<LoadSummary>, ImportError> {
    load_typed_module_with_deps_cached(env, &legacy_module_name(module)?, search_paths, cache)
}

/// [`load_module_with_deps_cached`], asking `guard` about every module file
/// the graph walk resolves, before that file is read: the requested module's,
/// and each one an `.olean` header in its import graph lists, cached or not.
/// `guard(name, file, index)` names the module, the file, and the index in
/// `search_paths` of the directory the file was found in. The first `Err` it
/// returns stops the load and is its answer: the refused file is not read,
/// and nothing has been registered in `env`.
///
/// A caller that searches directories it does not control checks where each
/// module resolved here. A check made before the load sees the requested
/// module only, not the modules its headers import.
pub fn load_module_with_deps_cached_guarded(
    env: &mut Environment,
    module: &str,
    search_paths: &[PathBuf],
    cache: &ModuleCache,
    guard: &mut dyn FnMut(&Name, &Path, usize) -> Result<(), ImportError>,
) -> Result<Vec<LoadSummary>, ImportError> {
    load_cached_graph(
        env,
        &legacy_module_name(module)?,
        search_paths,
        cache,
        false,
        Some(guard),
    )
}

/// Same typed loading and content checks as the sequential cached API, with
/// parallel parsing of cache misses. Registration remains dependency-ordered.
pub fn load_module_with_deps_parallel(
    env: &mut Environment,
    module: &str,
    search_paths: &[PathBuf],
    cache: &ModuleCache,
) -> Result<Vec<LoadSummary>, ImportError> {
    load_typed_module_with_deps_parallel(env, &legacy_module_name(module)?, search_paths, cache)
}

/// Cached loading with an exact root Name, including quoted/digit-string
/// components. All transitive graph keys come from captured typed import rows.
pub fn load_typed_module_with_deps_cached(
    env: &mut Environment,
    module: &Name,
    search_paths: &[PathBuf],
    cache: &ModuleCache,
) -> Result<Vec<LoadSummary>, ImportError> {
    load_cached_graph(env, module, search_paths, cache, false, None)
}

/// Parallel counterpart of [`load_typed_module_with_deps_cached`].
pub fn load_typed_module_with_deps_parallel(
    env: &mut Environment,
    module: &Name,
    search_paths: &[PathBuf],
    cache: &ModuleCache,
) -> Result<Vec<LoadSummary>, ImportError> {
    load_cached_graph(env, module, search_paths, cache, true, None)
}

fn load_cached_graph(
    env: &mut Environment,
    module: &Name,
    search_paths: &[PathBuf],
    cache: &ModuleCache,
    parallel: bool,
    guard: Option<&mut PathGuard<'_>>,
) -> Result<Vec<LoadSummary>, ImportError> {
    load_captured_graph(
        env,
        std::slice::from_ref(module),
        search_paths,
        cache,
        parallel,
        guard,
        None,
        false,
        None,
    )
}

#[allow(clippy::too_many_arguments)]
fn load_captured_graph(
    env: &mut Environment,
    modules: &[Name],
    search_paths: &[PathBuf],
    cache: &ModuleCache,
    parallel: bool,
    mut guard: Option<&mut PathGuard<'_>>,
    mut check_captured: Option<&mut BytesGuard<'_>>,
    full_metadata_fixups: bool,
    limits: Option<ModuleCaptureLimits>,
) -> Result<Vec<LoadSummary>, ImportError> {
    let mut budget = CaptureBudget::new(limits);
    budget.check_roots(modules.len())?;
    let mut pending = Vec::new();
    pending
        .try_reserve_exact(modules.len())
        .map_err(|error| ImportError::ResourceLimit {
            operation: "capturing the module graph".into(),
            reason: format!("cannot allocate root selectors: {error}"),
        })?;
    pending.extend(modules.iter().rev().cloned());
    let mut discovered = HashSet::new();
    let mut graph: HashMap<Name, Arc<DirectModule>> = HashMap::new();
    let mut cold = Vec::new();
    while let Some(name) = pending.pop() {
        if discovered.contains(&name) {
            continue;
        }
        budget.module()?;
        discovered.insert(name.clone());
        deadline::check()?;
        let (found_in, path) = resolve_typed_module_file(&name, search_paths)?;
        // Every module file, the root's and each import's, before it is read
        // (`load_module_with_deps_cached_guarded`).
        if let Some(guard) = &mut guard {
            guard(&name, &path, found_in)?;
        }
        let captured = CapturedModule::read_with_budget(&path, &mut budget)?;
        let captured = if check_captured.is_some() {
            captured.capture_ir_with_budget(&path, &mut budget)?
        } else {
            captured
        };
        // The exact immutable contents checked here are the contents decoded
        // below, on a cold parse AND on a content-bound cache hit.
        if let Some(check) = &mut check_captured {
            check(
                &name,
                &path,
                CapturedModuleBytes {
                    canonical_path: &captured.path,
                    base: &captured.base,
                    server: captured.server.as_deref(),
                    private: captured.private.as_deref(),
                    ir: captured.captured_ir.as_ref().and_then(|ir| ir.as_deref()),
                },
            )?;
        }
        // A module of a refused world is refused by name before its imports
        // are walked or anything is decoded (R81); the binding itself is
        // decided where its parts register.
        let label = name.to_string();
        for (bytes, suffix) in [
            (Some(&captured.base), ""),
            (captured.server.as_ref(), "._server"),
            (captured.private.as_ref(), "._private"),
        ] {
            if let Some(bytes) = bytes {
                world_gate::check_part_bytes(env, &format!("{label}{suffix}"), bytes)?;
            }
        }
        // Charge the validated base AND companion root envelopes before
        // allocating/decoding import rows or touching cache entries. Keep the
        // existing refused-world diagnostic priority, and ordinary APIs'
        // parser/error ordering when no extra policy was requested.
        if limits.is_some() {
            captured.charge_import_rows(&mut budget)?;
        }
        let cached = cache.get_direct(&captured);
        let imports = match &cached {
            Some(bundle) => bundle.base.typed_imports.clone(),
            None => {
                parse_typed_imports(&captured.base).map_err(|source| ImportError::FileParse {
                    path: captured.path.clone(),
                    source,
                })?
            }
        };
        pending
            .try_reserve(imports.len())
            .map_err(|error| ImportError::ResourceLimit {
                operation: "capturing the module graph".into(),
                reason: format!("cannot allocate pending imports: {error}"),
            })?;
        for import in imports {
            if !discovered.contains(&import.module_name) {
                pending.push(import.module_name);
            }
        }
        if let Some(bundle) = cached {
            graph.insert(name, bundle);
        } else {
            cold.push((name, captured));
        }
    }

    // Keep the graph's Arc handles independently of the bounded cache. Eviction
    // during a large or concurrent load must not turn a valid module into a
    // missing entry, panic, or a second read of different bytes.
    //
    // A module enters the cache only from a decode that finished with the
    // caller's deadline not passed: the second check latches a deadline that
    // passed during the decode, so nothing decoded past it is kept. A decode
    // reads no deadline today (nothing in it reaches a tick site), so every
    // decode that returns is whole and the second check only keeps a whole
    // module out of the cache: no test can tell it is there. It stands for a
    // decode that comes to reach a tick site, which a latch fired during it
    // could cut short. (A rayon thread of the parallel load has no deadline:
    // its checks pass.)
    let parse = |(name, captured): (Name, CapturedModule)| {
        deadline::check()?;
        let path = captured.path.clone();
        let bundle = captured.parse()?;
        deadline::check()?;
        Ok((name, cache.insert_direct(path, bundle)))
    };
    let parsed: Vec<Result<(Name, Arc<DirectModule>), ImportError>> = if parallel {
        cold.into_par_iter().map(parse).collect()
    } else {
        cold.into_iter().map(parse).collect()
    };
    for result in parsed {
        let (name, bundle) = result?;
        graph.insert(name, bundle);
    }

    // Explicit post-order traversal rejects cycles before Environment mutation.
    // Structural import identities remain graph keys through the entire walk.
    // String summaries/origin labels are a separate compatibility surface.
    let mut stack: Vec<_> = modules
        .iter()
        .rev()
        .cloned()
        .map(|name| (name, false))
        .collect();
    let mut visiting = HashSet::new();
    let mut loaded = HashSet::new();
    let mut order = Vec::new();
    while let Some((name, expanded)) = stack.pop() {
        if loaded.contains(&name) {
            continue;
        }
        let bundle = graph
            .get(&name)
            .ok_or_else(|| ImportError::UnsupportedModule {
                module: format!("{name:?}"),
                reason: "dependency absent from captured module graph".into(),
            })?;
        if expanded {
            visiting.remove(&name);
            loaded.insert(name.clone());
            order.push(name);
        } else {
            if !visiting.insert(name.clone()) {
                return Err(ImportError::UnsupportedModule {
                    module: format!("{name:?}"),
                    reason: "cyclic module import graph".into(),
                });
            }
            stack.push((name, true));
            for import in bundle.base.typed_imports.iter().rev() {
                stack.push((import.module_name.clone(), false));
            }
        }
    }

    // Cache identity cannot grant permission in a different environment.
    // Validate the complete captured/parsed graph before registration starts.
    if super::super::clean_payload_requirement::clean_payload_imports_required(env) {
        for (name, bundle) in &graph {
            super::super::clean_payload_requirement::check_artifact_parts(
                env,
                &name.to_string(),
                &bundle.base,
                bundle.server.as_ref(),
                bundle.private.as_ref(),
            )?;
        }
    }

    env.ensure_native_reducers();
    let estimated = modules
        .iter()
        .map(|module| estimate_module_graph_size(&module.to_string()))
        .max()
        .unwrap_or(0);
    if estimated > 0 {
        env.reserve_capacity(estimated);
    }
    let mut intern_cache = ExprInternCache::with_capacity(65536);
    let mut summaries = Vec::new();
    let policy = OleanImportPolicy::default();
    for name in order {
        deadline::check()?;
        let bundle = graph
            .get(&name)
            .ok_or_else(|| ImportError::UnsupportedModule {
                module: format!("{name:?}"),
                reason: "captured module graph changed during loading".into(),
            })?;
        // Every part is of the one artifact `name`.
        load_artifact_parts(
            env,
            &name.to_string(),
            &bundle.base,
            bundle.server.as_ref(),
            bundle.private.as_ref(),
            &mut summaries,
            &mut intern_cache,
            policy,
        )?;
    }
    env.regenerate_missing_no_confusion();
    env.ensure_native_reducers();
    if full_metadata_fixups {
        // Match load_modules_with_deps_with_import_policy: decoded retained
        // metadata wins before projection-derived structure fields are filled.
        super::super::load_register::flush_pending_structure_metadata(env)?;
    }
    super::super::load_register::register_structure_fields_from_projections(env);
    // `Ok` only for a load the deadline never cut.
    deadline::check()?;
    Ok(summaries)
}

#[cfg(test)]
mod capture_limits_tests;
#[cfg(test)]
mod captured_guard_tests;
