// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Which `.olean`s `clean olean replay <Module>...` replays, and from where.
//!
//! Both halves port `LeanChecker.lean` (`src/lean/LeanChecker.lean`, pinned
//! v4.30.0-rc2): its `main` runs `initSearchPath (← findSysroot)`, whose search
//! path is every `LEAN_PATH` entry followed by the toolchain's own `lib/lean`,
//! and it replays every module `m` found there with `target.isPrefixOf m`
//! (Lean's `Name.isPrefixOf`, component-wise), or exactly `target` under
//! `--fresh`. A target that matches no `.olean` is an error ("Could not find
//! any oleans for: …").
//!
//! The search path deliberately has no fallback: `default_search_paths` also
//! lists every other installed toolchain, and a module resolved from a
//! different Lean would be replayed against definitions its own Lean never
//! had. The toolchain `lib/lean` here is the checkout's pinned one.

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};

/// Why the requested modules could not be resolved.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
#[non_exhaustive]
pub(crate) enum ReplayTargetError {
    /// The argument is not a module name.
    #[error("Could not resolve module: {0}")]
    BadModuleName(String),
    /// No `.olean` on the search path has the target as a prefix
    /// (`leanchecker`: "Could not find any oleans for: …").
    #[error("Could not find any oleans for: {target} (search path: {searched})")]
    NotFound {
        /// The requested module.
        target: String,
        /// The search path, `:`-separated.
        searched: String,
    },
    /// `--fresh` names exactly one module (`leanchecker`: "--fresh flag is
    /// only valid when specifying a single module").
    #[error("--fresh flag is only valid when specifying a single module: {0}")]
    FreshNeedsOneModule(String),
    /// The pinned toolchain's `lib/lean` could not be found.
    #[error("the pinned Lean toolchain is unavailable: {0}")]
    NoToolchain(String),
}

/// The replay search path: `explicit` first, then `LEAN_PATH`, then the pinned
/// toolchain's `lib/lean` (Lean's `initSearchPath`: `LEAN_PATH` entries, then
/// `<sysroot>/lib/lean`). Entries are kept in order, duplicates dropped.
pub(crate) fn replay_search_path(
    explicit: &[PathBuf],
    lean_path: Option<&std::ffi::OsStr>,
    toolchain_lib: Option<PathBuf>,
) -> Result<Vec<PathBuf>, ReplayTargetError> {
    let mut paths: Vec<PathBuf> = Vec::new();
    let mut push = |path: PathBuf| {
        if !path.as_os_str().is_empty() && !paths.contains(&path) {
            paths.push(path);
        }
    };
    explicit.iter().cloned().for_each(&mut push);
    if let Some(lean_path) = lean_path {
        std::env::split_paths(lean_path).for_each(&mut push);
    }
    let lib = toolchain_lib.ok_or_else(|| {
        ReplayTargetError::NoToolchain(
            "no `lib/lean` for this checkout's `lean-toolchain` pin".to_owned(),
        )
    })?;
    push(lib);
    Ok(paths)
}

/// The components of a module name as `LeanChecker.lean` reads its argument
/// (`String.toName`; Mathlib, `Init` and `Std` module names are plain dotted
/// identifiers). `None` for an empty name or an empty component.
pub(crate) fn module_components(module: &str) -> Option<Vec<String>> {
    let parts: Vec<String> = module.split('.').map(str::to_owned).collect();
    if parts.iter().any(String::is_empty) {
        None
    } else {
        Some(parts)
    }
}

/// Every module on `search_path` that `target` selects: exactly `target`
/// when `exact`, and otherwise every module `target` is a component prefix
/// of. The result is sorted and duplicate-free (a module found under two roots
/// is one module, and the loader resolves it from the first root, as Lean's
/// `findOLean` does).
///
/// # Errors
/// [`ReplayTargetError::BadModuleName`] or [`ReplayTargetError::NotFound`].
fn resolve_modules(
    target: &str,
    search_path: &[PathBuf],
    exact: bool,
) -> Result<BTreeSet<String>, ReplayTargetError> {
    let components = module_components(target)
        .ok_or_else(|| ReplayTargetError::BadModuleName(target.to_owned()))?;
    let mut found = BTreeSet::new();
    for root in search_path {
        let mut stem = root.clone();
        stem.extend(&components);
        if stem.with_extension("olean").is_file() {
            found.insert(target.to_owned());
        }
        if !exact && stem.is_dir() {
            collect_modules_under(&stem, target, &mut found, &mut BTreeSet::new());
        }
    }
    if found.is_empty() {
        return Err(ReplayTargetError::NotFound {
            target: target.to_owned(),
            searched: search_path
                .iter()
                .map(|p| p.display().to_string())
                .collect::<Vec<_>>()
                .join(":"),
        });
    }
    Ok(found)
}

/// The modules `targets` select, in name order: for each target, every module
/// it is a component prefix of (`leanchecker <Module>`), or exactly the target
/// when `exact` or `fresh` is set; `fresh` selects exactly one module in all
/// (`leanchecker --fresh`).
///
/// # Errors
/// A target that is no module name or matches no `.olean`, or `fresh` with a
/// selection other than one module.
pub(crate) fn select_modules(
    targets: &[String],
    search_path: &[PathBuf],
    exact: bool,
    fresh: bool,
) -> Result<BTreeSet<String>, ReplayTargetError> {
    let mut modules = BTreeSet::new();
    for target in targets {
        modules.extend(resolve_modules(target, search_path, exact || fresh)?);
    }
    if fresh && modules.len() != 1 {
        return Err(ReplayTargetError::FreshNeedsOneModule(
            modules.into_iter().collect::<Vec<_>>().join(", "),
        ));
    }
    Ok(modules)
}

/// Every `<dir>/**/<X>.olean` as the module `<prefix>.<…>.<X>`. A file whose
/// extension is not exactly `olean` (`X.olean.server`, `X.olean.private`,
/// `X.ilean`) is not a module, as for Lean's `findAllWithExt sp "olean"`.
/// Directories are visited once by canonical path, so a symlink cycle ends.
fn collect_modules_under(
    dir: &Path,
    prefix: &str,
    found: &mut BTreeSet<String>,
    seen: &mut BTreeSet<PathBuf>,
) {
    let Ok(canonical) = dir.canonicalize() else {
        return;
    };
    if !seen.insert(canonical) {
        return;
    }
    let Ok(entries) = std::fs::read_dir(dir) else {
        return;
    };
    let mut entries: Vec<_> = entries.flatten().collect();
    entries.sort_by_key(std::fs::DirEntry::file_name);
    for entry in entries {
        let path = entry.path();
        let Some(file_name) = path.file_name().and_then(|n| n.to_str()) else {
            continue;
        };
        if path.is_dir() {
            if !file_name.contains('.') {
                collect_modules_under(&path, &format!("{prefix}.{file_name}"), found, seen);
            }
        } else if let Some(stem) = file_name.strip_suffix(".olean") {
            if !stem.is_empty() && !stem.contains('.') {
                found.insert(format!("{prefix}.{stem}"));
            }
        }
    }
}
