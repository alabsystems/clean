// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Import processing and module loading.

use crate::error::ElabError;
use std::collections::HashSet;
use std::path::{Path, PathBuf};

/// Upper bound on the number of `.olean` modules the frontend import path will
/// discover (via [`clean_olean::load_module_with_deps_bounded`]) before failing
/// closed and falling back to hand-written stub preludes.
///
/// # Rationale
///
/// The previous bound (64) was far below real Lean library scale and forced the
/// frontend onto stub types for every non-trivial import: `Init` is ~320
/// modules, `Std` ~520, and full Mathlib aggregates exceed 7,000. With the old
/// cap, [`process_imports_with_search_paths`] would reject the real `.olean`
/// graph and silently degrade to stubs even when the actual artifacts were
/// present and the (unbounded) backend loader could have handled them.
///
/// The bound is now 16,384 — comfortably above current Mathlib (~7,000) with
/// headroom for growth — while still acting as a fail-fast guard against
/// runaway / pathological import graphs rather than allowing truly unbounded
/// discovery. The backend [`clean_olean::load_module_with_deps`] itself is
/// already unbounded and independently tested; this constant only governs the
/// frontend's fail-closed policy and its stub-fallback decision.
const FRONTEND_OLEAN_IMPORT_MODULE_LIMIT: usize = 16_384;

// NOTE (plan decision 1 — Clean-native meta shim): the previous
// `unsupported_frontend_import_reason` wall hard-rejected `import Lean` /
// `Lean.Elab` / `Lean.Elab.*` before `.olean` loading. It has been removed so
// those modules route through the normal path: real `.olean` if a toolchain is
// present, otherwise the Clean-native opaque meta shim registered by
// `prelude_providers::init_lean_meta_prelude` (reached via the `Lean.*` prefix
// fallback in `init_prelude_for_module`). The frontend remains bounded via
// `FRONTEND_OLEAN_IMPORT_MODULE_LIMIT`.

/// What the import path does with a module it cannot resolve to anything real.
///
/// # Why this exists
///
/// Until 2026-08-26 there was no policy: [`finish_import_module`] fell through
/// to `prelude_providers::init_prelude_for_module` unconditionally, discarded
/// its `bool`, and returned `Ok(())`. Two silent-substitution holes followed
/// from that, and both were reproduced on the shipped binary before this type
/// was written:
///
/// ```text
/// $ printf 'import Mathlib.Utterly.Fake.Nonsense\ntheorem t3 (R : Type) [Ring R] (a : R) : a = a := rfl\n' > fake.lean
/// $ clean check fake.lean
///   1 passed, 0 failed          # exit 0 — `Ring` came from a hand-written stub
/// $ printf 'import Totally.Fake.Module\ntheorem t4 : 1 = 1 := rfl\n' > fake2.lean
/// $ clean check fake2.lean
///   1 passed, 0 failed          # exit 0 — nothing at all served the import
/// ```
///
/// A `PASS` on such a file is meaningless: every declaration in it elaborated
/// against something the source did not ask for, so no whole-project run
/// through this path could be distinguished from a run against ~30 hand-written
/// structures. The same discipline already existed one crate over —
/// `clean-lake`'s builder has been fail-closed-by-default with an explicit
/// `--permissive-imports` opt-out — and was simply never extended here.
///
/// # What still counts as resolved
///
/// [`ImportPolicy::FailClosed`] refuses **fabrication**, not every stand-in:
///
/// * a real `.olean` load — resolved;
/// * an intra-project `.lean` source file this run already elaborated (the
///   caller records it via [`crate::FileContext::mark_import_satisfied_from_source`]) —
///   resolved, because the declarations really are in `env`;
/// * a module named verbatim by a Clean prelude provider, or the `Lean` /
///   `Lean.*` metaprogramming shim ([`crate::prelude_providers::has_declared_prelude`])
///   — a *declared* substitution, accepted but logged at `warn`;
/// * anything else — including the `Mathlib.*` prefix wildcard, which accepts
///   every name that has ever been typed — is **unresolved** and is an error.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum ImportPolicy {
    /// Default. An `import` that resolves to no `.olean`, no already-elaborated
    /// project source, and no *named* Clean prelude provider fails the
    /// declaration with [`ElabError::UnresolvedImport`].
    #[default]
    FailClosed,
    /// Legacy warn-and-continue: fabricate a prelude for the unresolved module
    /// and let elaboration proceed. Reached only through an explicit opt-in
    /// (`clean check --permissive-imports`), and every fabrication is logged at
    /// `warn` so the substitution is never silent even here.
    Permissive,
}

/// Per-file inputs the unresolved-import decision needs, beyond the module name.
#[derive(Debug, Clone, Copy)]
struct ImportResolution<'a> {
    policy: ImportPolicy,
    /// Modules whose declarations are already in `env` because this run
    /// elaborated their intra-project `.lean` source. Such an import is
    /// resolved even though no `.olean` exists for it.
    satisfied_from_source: &'a HashSet<String>,
}

impl ImportResolution<'_> {
    fn is_satisfied_from_source(&self, module: &str) -> bool {
        self.satisfied_from_source.contains(module)
    }
}

/// Empty borrow used by the entry points that have no per-file source-resolution
/// record of their own.
fn no_source_resolved() -> &'static HashSet<String> {
    static EMPTY: std::sync::OnceLock<HashSet<String>> = std::sync::OnceLock::new();
    EMPTY.get_or_init(HashSet::new)
}

/// Process import statements and load modules
///
/// Tries to load modules from .olean files first (real Mathlib), falling back
/// to stub initializers if .olean files are not found or fail to load.
///
/// # Priority
/// 1. Real .olean loading via clean_olean (requires MATHLIB_PATH/LEAN_PATH or elan)
/// 2. Fallback to stub initializers for modules a provider names verbatim
/// 3. Anything else is an [`ElabError::UnresolvedImport`] under the default
///    [`ImportPolicy::FailClosed`]
///
/// # Environment Variables
/// - `MATHLIB_PATH`: Colon-separated paths to Mathlib .olean directories
/// - `LEAN_PATH`: Colon-separated paths to Lean library directories
/// - Falls back to ~/.elan/toolchains/*/lib/lean for stdlib
///   Process import statements without loading external `.olean` artifacts.
///
/// This mode is used by Clean-native project authority checks: imports may
/// initialize Clean's built-in module preludes, but external Lean / Lake /
/// Mathlib `.olean` artifacts are not consulted as semantic evidence.
///
/// Under [`ImportPolicy::FailClosed`] a module with no built-in Clean prelude is
/// an error, matching the unknown-module behavior of [`process_imports`].
pub fn process_imports_clean_native(
    env: &mut clean_kernel::Environment,
    paths: &[Vec<String>],
    policy: ImportPolicy,
) -> Result<(), ElabError> {
    let resolution = ImportResolution {
        policy,
        satisfied_from_source: no_source_resolved(),
    };
    for path in paths {
        let module = path.join(".");
        if serve_from_prelude(env, &module, resolution)? {
            continue;
        }
        unresolved_import(&module, "no Clean-native prelude provides it", resolution)?;
    }
    Ok(())
}

pub fn process_imports(
    env: &mut clean_kernel::Environment,
    paths: &[Vec<String>],
) -> Result<(), ElabError> {
    process_imports_with_search_paths(env, paths, &[])
}

/// [`process_imports`] with an explicit [`ImportPolicy`].
pub fn process_imports_with_policy(
    env: &mut clean_kernel::Environment,
    paths: &[Vec<String>],
    policy: ImportPolicy,
) -> Result<(), ElabError> {
    process_imports_with_search_paths_and_policy(env, paths, &[], policy)
}

/// Process import statements with additional file/project-local `.olean` paths.
///
/// The extra paths are searched before environment/toolchain defaults so a Lake
/// project's build output wins over unrelated global packages.
pub fn process_imports_with_search_paths(
    env: &mut clean_kernel::Environment,
    paths: &[Vec<String>],
    extra_search_paths: &[PathBuf],
) -> Result<(), ElabError> {
    process_imports_with_search_paths_and_policy(
        env,
        paths,
        extra_search_paths,
        ImportPolicy::default(),
    )
}

/// [`process_imports_with_search_paths`] with an explicit [`ImportPolicy`].
pub fn process_imports_with_search_paths_and_policy(
    env: &mut clean_kernel::Environment,
    paths: &[Vec<String>],
    extra_search_paths: &[PathBuf],
    policy: ImportPolicy,
) -> Result<(), ElabError> {
    let search_paths = import_search_paths(extra_search_paths);
    let resolution = ImportResolution {
        policy,
        satisfied_from_source: no_source_resolved(),
    };

    for path in paths {
        let module = path.join(".");

        // Try .olean loading first if search paths are available. Each import
        // allocates a FRESH `visited` set, so overlapping closures are re-read
        // per import — acceptable for the low-import single-file callers, but
        // O(n²) for a Mathlib file: use `process_imports_with_search_paths_shared`
        // there.
        let outcome = if search_paths.is_empty() {
            None
        } else {
            Some(clean_olean::load_module_with_deps_bounded(
                env,
                &module,
                &search_paths,
                FRONTEND_OLEAN_IMPORT_MODULE_LIMIT,
            ))
        };
        finish_import_module(env, &module, outcome, resolution)?;
    }
    Ok(())
}

/// Like [`process_imports_with_search_paths`], but threads a caller-owned
/// `visited` set through every import so a single file's overlapping `.olean`
/// closures (e.g. a Mathlib file's `Lean.Elab.*` / `Lean.Server.*` /
/// `Mathlib.*` imports) are read and walked ONCE rather than re-read per
/// top-level `import`. Behavior is otherwise identical to the non-shared fn:
/// same empty-search-paths guard, same `init_surface_prelude_after_olean`
/// hook, same `UnsupportedModule` → `init_prelude_for_module` fallback, same
/// stub fallback.
///
/// SOUNDNESS: sharing `visited` is a pure performance change. A module already
/// present in `visited` was loaded and registered into this SAME `env` by an
/// earlier import in this file, so skipping its re-read is correct — `.olean`
/// registration is insert-only and idempotent on duplicates
/// (see [`clean_olean::load_module_with_deps_bounded_shared`]). It never
/// changes which constants are registered, nor their types or values. No
/// kernel / TCB code is touched.
pub fn process_imports_with_search_paths_shared(
    env: &mut clean_kernel::Environment,
    paths: &[Vec<String>],
    extra_search_paths: &[PathBuf],
    visited: &mut hashbrown::HashSet<String>,
) -> Result<(), ElabError> {
    process_imports_shared_inner(
        env,
        paths,
        extra_search_paths,
        visited,
        ImportResolution {
            policy: ImportPolicy::default(),
            satisfied_from_source: no_source_resolved(),
        },
    )
}

fn process_imports_shared_inner(
    env: &mut clean_kernel::Environment,
    paths: &[Vec<String>],
    extra_search_paths: &[PathBuf],
    visited: &mut hashbrown::HashSet<String>,
    resolution: ImportResolution<'_>,
) -> Result<(), ElabError> {
    let search_paths = import_search_paths(extra_search_paths);

    for path in paths {
        let module = path.join(".");

        let outcome = if search_paths.is_empty() {
            None
        } else {
            Some(clean_olean::load_module_with_deps_bounded_shared(
                env,
                &module,
                &search_paths,
                FRONTEND_OLEAN_IMPORT_MODULE_LIMIT,
                visited,
            ))
        };
        finish_import_module(env, &module, outcome, resolution)?;
    }
    Ok(())
}

/// The file-driven entry point: process one `import` declaration's module list
/// against the search paths, `visited` memo, [`ImportPolicy`] and
/// already-elaborated-from-source record that [`crate::FileContext`] carries.
///
/// This is what `clean check` and the LSP document path reach. It is the only
/// entry point that can see the intra-project source resolution the CLI
/// performs in its first pass, so it is the only one that can tell
/// "`import Foo` whose `Foo.lean` this run already elaborated" (resolved) apart
/// from "`import Foo` that names nothing at all" (unresolved).
pub fn process_imports_for_file(
    env: &mut clean_kernel::Environment,
    paths: &[Vec<String>],
    file_ctx: &mut crate::FileContext,
) -> Result<(), ElabError> {
    // Clone the (small — one PathBuf per Lake search root) path list so the
    // immutable borrow of `file_ctx` does not conflict with the mutable borrow
    // of its `visited` memo below.
    let extra_search_paths = file_ctx.import_search_paths().to_vec();
    let policy = file_ctx.import_policy();
    let (visited, satisfied_from_source) = file_ctx.import_loader_state_mut();
    process_imports_shared_inner(
        env,
        paths,
        &extra_search_paths,
        visited,
        ImportResolution {
            policy,
            satisfied_from_source,
        },
    )
}

/// One-shot batch variant of [`process_imports_with_search_paths_shared`] that
/// owns the shared `visited` set for a single load event.
///
/// Callers that load a document's entire import header as one unit — e.g. the
/// LSP editor path, which caches the resulting environment process-wide — get
/// the read-each-`.olean`-once behavior of the shared loader without threading
/// a `hashbrown` set through their own API surface. Semantics are identical to
/// [`process_imports_with_search_paths_shared`] with a fresh `visited` set.
pub fn process_import_batch_with_search_paths(
    env: &mut clean_kernel::Environment,
    paths: &[Vec<String>],
    extra_search_paths: &[PathBuf],
) -> Result<(), ElabError> {
    let mut visited = hashbrown::HashSet::new();
    process_imports_with_search_paths_shared(env, paths, extra_search_paths, &mut visited)
}

/// Apply the shared per-import outcome policy: register the surface prelude on
/// a successful `.olean` load, honor the `UnsupportedModule` → built-in prelude
/// fallback, and otherwise (load error, or `None` = no search paths) decide,
/// under `resolution`, whether a hand-written stand-in may serve the module at
/// all. `outcome` is `None` when search paths were empty (skip the `.olean`
/// attempt entirely) and `Some(result)` once a load has been attempted.
///
/// The last arm used to be `let _ = init_prelude_for_module(env, module)?;
/// Ok(())` — it discarded the "was anything actually registered?" bool and
/// reported success either way. That is the line that made every `clean check`
/// verdict on a file with an unresolvable import meaningless; see
/// [`ImportPolicy`] for the two reproductions.
fn finish_import_module(
    env: &mut clean_kernel::Environment,
    module: &str,
    outcome: Option<Result<Vec<clean_olean::LoadSummary>, clean_olean::ImportError>>,
    resolution: ImportResolution<'_>,
) -> Result<(), ElabError> {
    if let Some(result) = outcome {
        match result {
            Ok(summaries) => {
                let total_loaded: usize = summaries.iter().map(|s| s.added_constants).sum();
                let total_skipped: usize =
                    summaries.iter().map(|s| s.skipped_constants.len()).sum();
                tracing::info!(
                    module = %module,
                    loaded = total_loaded,
                    skipped = total_skipped,
                    "Loaded module from .olean"
                );
                let _ = crate::prelude_providers::init_surface_prelude_after_olean(env, module)?;
                return Ok(()); // Successfully loaded, skip stub fallback
            }
            Err(clean_olean::ImportError::UnsupportedModule { module, reason }) => {
                if serve_from_prelude(env, &module, resolution)? {
                    return Ok(());
                }
                return Err(ElabError::Unsupported {
                    feature: format!("import {module}: {reason}"),
                });
            }
            Err(e) => {
                tracing::debug!(
                    module = %module,
                    error = %e,
                    "Failed to load .olean, trying stub fallback"
                );
                // Fall through to the stand-in decision below, carrying the
                // loader's own reason so a fail-closed refusal can name it.
                return finish_unresolved(env, module, &e.to_string(), resolution);
            }
        }
    }

    finish_unresolved(
        env,
        module,
        "no `.olean` search path was available (set LEAN_PATH / MATHLIB_PATH, \
         or build the project with `lake build`)",
        resolution,
    )
}

/// No real `.olean` served `module`. Accept an already-elaborated project source
/// file or a *declared* Clean prelude; otherwise apply `resolution.policy`.
fn finish_unresolved(
    env: &mut clean_kernel::Environment,
    module: &str,
    reason: &str,
    resolution: ImportResolution<'_>,
) -> Result<(), ElabError> {
    if resolution.is_satisfied_from_source(module) {
        // The caller elaborated this module's own `.lean` in an earlier pass,
        // so its declarations really are in `env`. Absence of a compiled
        // artifact is expected here, not a gap.
        tracing::debug!(
            module = %module,
            "Import satisfied by intra-project source elaborated earlier this run"
        );
        return Ok(());
    }
    if serve_from_prelude(env, module, resolution)? {
        return Ok(());
    }
    unresolved_import(module, reason, resolution)
}

/// Register a hand-written stand-in for `module`, if policy allows one.
///
/// Under [`ImportPolicy::FailClosed`] only a module a provider names *verbatim*
/// (or the `Lean` / `Lean.*` shim) may be served, and the substitution is logged
/// at `warn`. Under [`ImportPolicy::Permissive`] the `Mathlib.*` prefix wildcard
/// is allowed to fabricate one too — also at `warn`, never silently.
fn serve_from_prelude(
    env: &mut clean_kernel::Environment,
    module: &str,
    resolution: ImportResolution<'_>,
) -> Result<bool, ElabError> {
    let declared = crate::prelude_providers::has_declared_prelude(module);
    if resolution.policy == ImportPolicy::FailClosed && !declared {
        return Ok(false);
    }
    if !crate::prelude_providers::init_prelude_for_module(env, module)? {
        return Ok(false);
    }
    if declared {
        tracing::warn!(
            module = %module,
            "import served by Clean's hand-written prelude for this module, not by a real \
             `.olean` — declarations checked against it are NOT checked against the real module"
        );
    } else {
        tracing::warn!(
            module = %module,
            "--permissive-imports: FABRICATING a prelude for an import that resolves to \
             nothing real; any verdict on this file is meaningless"
        );
    }
    Ok(true)
}

/// Nothing real and nothing declared serves `module`.
fn unresolved_import(
    module: &str,
    reason: &str,
    resolution: ImportResolution<'_>,
) -> Result<(), ElabError> {
    match resolution.policy {
        ImportPolicy::Permissive => {
            tracing::warn!(
                module = %module,
                reason = %reason,
                "--permissive-imports: unresolved import ignored; \
                 any verdict on this file is meaningless"
            );
            Ok(())
        }
        ImportPolicy::FailClosed => Err(ElabError::UnresolvedImport {
            module: module.to_string(),
            reason: reason.to_string(),
        }),
    }
}

fn import_search_paths(extra_search_paths: &[PathBuf]) -> Vec<PathBuf> {
    let mut search_paths = Vec::new();
    let mut seen = HashSet::new();

    for path in extra_search_paths {
        if seen.insert(path.clone()) {
            search_paths.push(path.clone());
        }
    }

    for path in clean_olean::default_search_paths() {
        if seen.insert(path.clone()) {
            search_paths.push(path);
        }
    }

    search_paths
}

/// Find the nearest Lake root for a checked file.
///
/// This is intentionally a read-only root detector: it recognizes the files
/// Lake projects already place at their root and does not evaluate the
/// lakefile.
#[must_use]
pub fn nearest_lake_root_for_file(path: &Path) -> Option<PathBuf> {
    let path = path.canonicalize().unwrap_or_else(|_| path.to_path_buf());
    let mut dir = if path.is_dir() {
        path
    } else {
        path.parent()?.to_path_buf()
    };

    loop {
        if is_lake_root(&dir) {
            return Some(dir);
        }
        if !dir.pop() {
            return None;
        }
    }
}

/// Discover Lake project/package `.olean` search paths for a checked file.
///
/// Returns only paths that exist under the nearest Lake root. Defaults
/// from `LEAN_PATH`, `MATHLIB_PATH`, `LEAN_PACKAGES_PATH`, and elan are added
/// later by import processing.
#[must_use]
pub fn lake_import_search_paths_for_file(path: &Path) -> Vec<PathBuf> {
    nearest_lake_root_for_file(path)
        .map(|root| {
            clean_olean::SearchPathBuilder::new()
                .add_package_root(root)
                .build()
        })
        .unwrap_or_default()
}

/// Return `true` if a prebuilt `.olean` for `module` is discoverable from the
/// import search paths of `from_file` (the file's nearest Lake root plus the
/// `LEAN_PATH`/elan defaults, matching [`process_imports_with_search_paths`]).
///
/// Read-only filesystem probe — loads nothing. The front-end uses it to prefer
/// loading a module's compiled artifact over recursively elaborating its source
/// when both exist on disk (the case when checking a `.lean` file that lives
/// *inside* a source tree — e.g. a Mathlib file — whose sibling imports also
/// resolve to `.lean`). This mirrors Lean's own model: the file under check
/// elaborates from source; its imports are loaded from `.olean`.
#[must_use]
pub fn olean_available_for_module(module: &str, from_file: &Path) -> bool {
    let mut search_paths = lake_import_search_paths_for_file(from_file);
    for default in clean_olean::default_search_paths() {
        if !search_paths.contains(&default) {
            search_paths.push(default);
        }
    }
    clean_olean::find_module_olean(module, &search_paths).is_some()
}

fn is_lake_root(path: &Path) -> bool {
    path.join("lakefile.lean").is_file()
        || path.join("lakefile.toml").is_file()
        || path.join("lake-manifest.json").is_file()
}

/// Resolve a Lean module name (e.g. `Mathbot.ResearchProgram` or a bare `Lib`)
/// to a `.lean` source file on disk, looking only within the surrounding
/// project tree.
///
/// This is the single shared implementation used by both the `clean check`
/// front-end (`clean-cli::cmd_core`) and the codegen / native-build env builder
/// (`clean-cli::cmd_compile`). It does **not** consult `.olean` artifacts; an
/// external module (Mathlib / Init / Batteries) for which no project-local
/// `.lean` exists returns `None`, and the caller keeps its existing `.olean`
/// flow for those.
///
/// `parent_path` is the importing source file (or a directory). Lookup order:
/// 1. The nearest Lake root parent of `parent_path` (project source root).
/// 2. `.lake/packages/<pkg>/...` siblings for cross-package intra-project imports.
/// 3. The walked parents of `parent_path` itself (covers ad-hoc / bare-dir
///    layouts where the file is not under a lakefile — the common case for a
///    sibling `Lib.lean` next to `Main.lean`).
///
/// Returns the first candidate that is an existing file, or `None`.
#[must_use]
pub fn resolve_intra_project_import(module: &str, parent_path: &Path) -> Option<PathBuf> {
    let parts: Vec<&str> = module.split('.').collect();
    if parts.is_empty() || parts.iter().any(|p| p.is_empty()) {
        return None;
    }
    let mut relative = PathBuf::new();
    for part in &parts {
        relative.push(part);
    }
    let relative_lean = relative.with_extension("lean");

    let mut candidates: Vec<PathBuf> = Vec::new();

    // 1. Nearest Lake root.
    if let Some(lake_root) = nearest_lake_root_for_file(parent_path) {
        candidates.push(lake_root.join(&relative_lean));
        // 2. Also try `.lake/packages/<head>/<tail>.lean` so packages vendored
        //    via Lake but built from source resolve too. The module head maps
        //    to the package directory by convention (case-preserving).
        if let Some((head, tail)) = parts.split_first() {
            let mut pkg_relative = PathBuf::new();
            for part in tail {
                pkg_relative.push(part);
            }
            let pkg_relative_lean = if pkg_relative.as_os_str().is_empty() {
                PathBuf::from(format!("{head}.lean"))
            } else {
                pkg_relative.with_extension("lean")
            };
            let packages_dir = lake_root.join(".lake").join("packages");
            for dir_name in package_dir_candidates(head) {
                candidates.push(packages_dir.join(&dir_name).join(&pkg_relative_lean));
                // Some packages place their sources under a top-level dir
                // named after the package itself (e.g. mathlib/Mathlib/...).
                candidates.push(
                    packages_dir
                        .join(&dir_name)
                        .join(head)
                        .join(&pkg_relative_lean),
                );
            }
        }
    }

    // 3. Walked parents of the source file (covers ad-hoc layouts where the
    //    file isn't under a lake root, e.g. a bare `Lib.lean` next to
    //    `Main.lean`, or unit tests with a tempdir).
    let start_dir = if parent_path.is_dir() {
        parent_path.to_path_buf()
    } else {
        parent_path
            .parent()
            .map(Path::to_path_buf)
            .unwrap_or_default()
    };
    let mut dir = Some(start_dir);
    while let Some(d) = dir {
        candidates.push(d.join(&relative_lean));
        dir = d.parent().map(Path::to_path_buf);
    }

    candidates.into_iter().find(|candidate| candidate.is_file())
}

/// Directory-name candidates for a Lake package head segment: the original
/// case, plus a lowercase variant when it differs (Lake conventionally vendors
/// packages under a lowercased directory name).
fn package_dir_candidates(head: &str) -> Vec<String> {
    let mut out = vec![head.to_owned()];
    let lower = head.to_lowercase();
    if lower != head {
        out.push(lower);
    }
    out
}

#[cfg(test)]
mod tests {
    use super::{
        lake_import_search_paths_for_file, nearest_lake_root_for_file, ElabError,
        FRONTEND_OLEAN_IMPORT_MODULE_LIMIT,
    };
    use std::fs;

    /// The frontend `.olean` import bound must admit full Mathlib-scale module
    /// graphs (~7,000 modules) so real imports use the unbounded backend loader
    /// instead of always degrading to hand-written stub preludes. Init (~320)
    /// and Std (~520) are comfortably below this; the assertion pins the policy
    /// at "at least Mathlib scale + headroom".
    #[test]
    fn frontend_olean_import_limit_admits_mathlib_scale_graph() {
        // Representative module counts for the real Lean libraries: Init ~320,
        // Std ~520, full Mathlib aggregates exceed 7,000. Evaluated at compile
        // time so a regression below Mathlib scale fails to build, not just at
        // runtime.
        const _: () = {
            assert!(
                FRONTEND_OLEAN_IMPORT_MODULE_LIMIT >= 320,
                "frontend import limit must admit Init (~320 modules)",
            );
            assert!(
                FRONTEND_OLEAN_IMPORT_MODULE_LIMIT >= 520,
                "frontend import limit must admit Std (~520 modules)",
            );
            assert!(
                FRONTEND_OLEAN_IMPORT_MODULE_LIMIT >= 7_000,
                "frontend import limit must admit Mathlib (~7,000 modules) so real \
                 imports skip the stub fallback",
            );
        };
    }

    /// The bound must stay a finite fail-fast guard against runaway import
    /// graphs rather than being effectively unbounded: it should be well below
    /// `usize::MAX`, leaving the truly-unbounded behavior to the backend loader.
    #[test]
    fn frontend_olean_import_limit_keeps_sane_upper_guard() {
        // Pin a generous-but-finite ceiling so the policy never becomes a no-op;
        // a pathological generated graph above this must still be rejected.
        const _: () = assert!(
            FRONTEND_OLEAN_IMPORT_MODULE_LIMIT <= 1_000_000,
            "frontend import limit should remain a finite guard (<= 1,000,000); \
             unbounded loading belongs to the backend loader",
        );
    }

    /// Raising the import-graph bound must not break the stub fallback: when no
    /// `.olean` is discoverable for a known module, [`process_imports`] must
    /// still degrade to the hand-written stub prelude (defining `Real`) rather
    /// than erroring. The extra search path is an empty temp directory, so the
    /// real `.olean` for this module is not resolvable from it.
    #[test]
    fn process_imports_falls_back_to_stub_when_no_olean_found() {
        use clean_kernel::{Environment, Name};

        let empty = tempfile::tempdir().expect("tempdir");
        let mut env = Environment::new();
        let paths = vec![vec!["Mathlib", "Data", "Real", "Basic"]
            .into_iter()
            .map(String::from)
            .collect()];

        super::process_imports_with_search_paths(&mut env, &paths, &[empty.path().to_path_buf()])
            .expect("known module with no discoverable .olean must fall back to a stub, not error");

        assert!(
            env.get_const(&Name::from_string("Real")).is_some(),
            "Real stub should be defined via fallback when no .olean is found",
        );
    }

    fn module_path(module: &str) -> Vec<Vec<String>> {
        vec![module.split('.').map(String::from).collect()]
    }

    /// An unknown module with no stub and no `.olean` must FAIL, not be ignored.
    ///
    /// This test asserted the opposite until 2026-08-26 ("unknown imports must
    /// be silently ignored"). Silently ignoring it is what let a file whose
    /// import names nothing at all report `1 passed, 0 failed` with exit 0.
    #[test]
    fn process_imports_unknown_module_fails_closed() {
        use clean_kernel::Environment;

        let empty = tempfile::tempdir().expect("tempdir");
        let mut env = Environment::new();
        let paths = module_path("Totally.Unknown.Module.Name");

        let err = super::process_imports_with_search_paths(
            &mut env,
            &paths,
            &[empty.path().to_path_buf()],
        )
        .expect_err("an import that resolves to nothing must not succeed");
        let ElabError::UnresolvedImport { module, .. } = &err else {
            panic!("expected UnresolvedImport, got {err:?}");
        };
        assert_eq!(module, "Totally.Unknown.Module.Name");
    }

    /// The `Mathlib.` PREFIX WILDCARD in `prelude_providers` accepts every name
    /// ever typed. Under the default policy that must no longer resolve an
    /// import: a nonexistent `Mathlib.*` module is exactly as unresolvable as
    /// any other nonexistent module.
    ///
    /// Reproduction this pins (measured at `84129fce7`, release binary):
    /// `clean check` on a file importing this module reported `1 passed,
    /// 0 failed`, exit 0, in 0.34 s, with a hand-written `Ring` substituted.
    #[test]
    fn process_imports_nonexistent_mathlib_module_fails_closed() {
        use clean_kernel::{Environment, Name};

        let empty = tempfile::tempdir().expect("tempdir");
        let mut env = Environment::new();
        let paths = module_path("Mathlib.Utterly.Fake.Nonsense");

        let err = super::process_imports_with_search_paths(
            &mut env,
            &paths,
            &[empty.path().to_path_buf()],
        )
        .expect_err("a nonexistent Mathlib module must not be served by the prefix wildcard");
        let ElabError::UnresolvedImport { module, .. } = &err else {
            panic!("expected UnresolvedImport, got {err:?}");
        };
        assert_eq!(module, "Mathlib.Utterly.Fake.Nonsense");
        assert!(
            env.get_const(&Name::from_string("Ring")).is_none(),
            "the refused import must not have registered the full Mathlib stub set anyway",
        );
    }

    /// The rule the refusal above rests on, pinned directly: a provider names a
    /// module VERBATIM or it does not, and the `Mathlib.` prefix wildcard is not
    /// a name. Pure function, no environment, no global state.
    #[test]
    fn declared_prelude_covers_named_modules_and_not_the_mathlib_wildcard() {
        use crate::prelude_providers::has_declared_prelude;

        assert!(has_declared_prelude("Mathlib.Data.Real.Basic"));
        assert!(has_declared_prelude("Mathlib"));
        assert!(has_declared_prelude("Lean"));
        assert!(has_declared_prelude("Lean.Elab.Tactic"));

        assert!(!has_declared_prelude("Mathlib.Utterly.Fake.Nonsense"));
        assert!(!has_declared_prelude("Mathlib.Data.Nat.Basic"));
        assert!(!has_declared_prelude("Totally.Fake.Module"));
        assert!(!has_declared_prelude("Init"));
    }

    /// `--permissive-imports` keeps the legacy warn-and-continue behavior.
    ///
    /// It deliberately uses a NON-`Mathlib` module. The permissive `Mathlib.*`
    /// path calls `init_full_mathlib`, which latches the process-global
    /// `MATHLIB_INIT` flag while environments are per-test — so asserting on it
    /// here poisons every later test that needs a declared Mathlib provider to
    /// actually register something. That is not hypothetical: the first draft of
    /// this test did exactly that and turned
    /// `process_imports_falls_back_to_stub_when_no_olean_found` and
    /// `test_process_imports_euclidean_geometry` red. The end-to-end proof that
    /// permissive mode still fabricates the Mathlib stub set is the release
    /// binary, one process per run:
    /// `clean check --permissive-imports fake.lean` → `1 passed, 0 failed`.
    #[test]
    fn permissive_policy_accepts_an_unresolvable_module() {
        use clean_kernel::Environment;

        let empty = tempfile::tempdir().expect("tempdir");
        let mut env = Environment::new();
        let paths = module_path("Totally.Fake.Module");

        super::process_imports_with_search_paths_and_policy(
            &mut env,
            &paths,
            &[empty.path().to_path_buf()],
            super::ImportPolicy::Permissive,
        )
        .expect("--permissive-imports must keep the legacy warn-and-continue behavior");
    }

    /// An import satisfied by intra-project `.lean` SOURCE this run already
    /// elaborated is RESOLVED, even though a source-only project has no
    /// `.olean` for it and never will. Without this, every ordinary multi-file
    /// project would fail closed on its own internal imports.
    #[test]
    fn import_satisfied_from_source_is_not_refused() {
        use clean_kernel::Environment;

        let empty = tempfile::tempdir().expect("tempdir");
        let mut env = Environment::new();
        let mut file_ctx = crate::FileContext::new();
        file_ctx.set_import_search_paths(vec![empty.path().to_path_buf()]);

        let paths = module_path("MyProject.Internal.Helpers");
        super::process_imports_for_file(&mut env, &paths, &mut file_ctx)
            .expect_err("control: without the source record this import is unresolvable");

        file_ctx.mark_import_satisfied_from_source("MyProject.Internal.Helpers");
        super::process_imports_for_file(&mut env, &paths, &mut file_ctx)
            .expect("an import whose source this run elaborated must be treated as resolved");
    }

    /// The `Lean` / `Lean.*` metaprogramming shim is a DECLARED provider, so it
    /// stays resolvable under the fail-closed default (plan decision 1).
    #[test]
    fn clean_native_lean_shim_survives_fail_closed() {
        use clean_kernel::Environment;

        let mut env = Environment::new();
        super::process_imports_clean_native(
            &mut env,
            &module_path("Lean.Elab.Tactic"),
            super::ImportPolicy::FailClosed,
        )
        .expect("the Lean.* shim is a declared provider and must remain resolvable");

        let err = super::process_imports_clean_native(
            &mut env,
            &module_path("Totally.Unknown.Module.Name"),
            super::ImportPolicy::FailClosed,
        )
        .expect_err("a module no Clean-native prelude provides must fail closed");
        assert!(matches!(err, ElabError::UnresolvedImport { .. }));
    }

    #[test]
    fn nearest_lake_root_prefers_closest_parent() {
        let dir = tempfile::tempdir().expect("tempdir");
        let outer = dir.path();
        let inner = outer.join("nested/project");
        let source_dir = inner.join("Mathbot");
        fs::create_dir_all(&source_dir).expect("source dirs");
        fs::write(outer.join("lakefile.lean"), "package outer\n").expect("outer lakefile");
        fs::write(inner.join("lakefile.toml"), "name = \"inner\"\n").expect("inner lakefile");
        let file = source_dir.join("ResearchProgram.lean");
        fs::write(&file, "def x := 1\n").expect("source file");

        let expected = fs::canonicalize(inner).expect("canonical inner root");
        assert_eq!(nearest_lake_root_for_file(&file), Some(expected));
    }

    #[test]
    fn lake_import_search_paths_include_project_and_package_build_outputs() {
        let dir = tempfile::tempdir().expect("tempdir");
        let root = dir.path();
        let source_dir = root.join("Mathbot");
        // The clean-olean SearchPathBuilder discovers `<root>/build/lib` and
        // `<root>/.lake/packages/*/build/lib` paths (see
        // crates/clean-olean/src/import/path.rs::discover_lake_package_paths).
        let project_lib = root.join("build/lib");
        let mathlib_lib = root.join(".lake/packages/Mathlib/build/lib");

        fs::create_dir_all(&source_dir).expect("source dirs");
        fs::create_dir_all(&project_lib).expect("project lib");
        fs::create_dir_all(&mathlib_lib).expect("mathlib lib");
        fs::write(root.join("lakefile.lean"), "package mathbot\n").expect("lakefile");
        let file = source_dir.join("ResearchProgram.lean");
        fs::write(&file, "def x := 1\n").expect("source file");

        let paths = lake_import_search_paths_for_file(&file);
        assert!(
            paths.iter().any(
                |p| p.ends_with("build/lib") && !p.to_string_lossy().contains(".lake/packages")
            ),
            "expected own build/lib in {paths:?}",
        );
        assert!(
            paths.iter().any(|p| p
                .to_string_lossy()
                .contains(".lake/packages/Mathlib/build/lib")),
            "expected mathlib build/lib in {paths:?}",
        );
    }

    #[test]
    fn lake_import_search_paths_are_empty_outside_lake_project() {
        let dir = tempfile::tempdir().expect("tempdir");
        let file = dir.path().join("Standalone.lean");
        fs::write(&file, "def x := 1\n").expect("source file");

        assert!(lake_import_search_paths_for_file(&file).is_empty());
    }

    /// Bare directory (NO lakefile): `import Lib` from `Main.lean` must resolve
    /// to the sibling `Lib.lean` via the walked-parents fallback. This is the
    /// common case both `clean check` and the codegen path rely on.
    #[test]
    fn resolve_intra_project_import_finds_bare_sibling() {
        let dir = tempfile::tempdir().expect("tempdir");
        let root = dir.path();
        fs::write(
            root.join("Lib.lean"),
            "def double (n : Nat) : Nat := n + n\n",
        )
        .expect("Lib.lean");
        let main = root.join("Main.lean");
        fs::write(&main, "import Lib\ndef five : Nat := double 5\n").expect("Main.lean");

        let resolved = super::resolve_intra_project_import("Lib", &main)
            .expect("bare sibling `Lib` should resolve to Lib.lean");
        assert!(
            resolved.ends_with("Lib.lean"),
            "resolved path should be Lib.lean: {resolved:?}"
        );
    }

    /// An external-looking module with no project-local `.lean` resolves to
    /// `None`, so the caller keeps its `.olean` flow.
    #[test]
    fn resolve_intra_project_import_returns_none_for_external() {
        let dir = tempfile::tempdir().expect("tempdir");
        let main = dir.path().join("Main.lean");
        fs::write(&main, "import Mathlib.Data.Nat.Basic\n").expect("Main.lean");

        assert!(
            super::resolve_intra_project_import("Mathlib.Data.Nat.Basic", &main).is_none(),
            "external Mathlib module must not resolve to a local .lean file",
        );
    }

    /// Dotted module names map to nested directories (`Sub.Inner` ->
    /// `Sub/Inner.lean`).
    #[test]
    fn resolve_intra_project_import_handles_dotted_nested_path() {
        let dir = tempfile::tempdir().expect("tempdir");
        let root = dir.path();
        fs::create_dir_all(root.join("Sub")).expect("subdir");
        fs::write(root.join("Sub/Inner.lean"), "def x := 1\n").expect("inner");
        let entry = root.join("Outer.lean");
        fs::write(&entry, "import Sub.Inner\n").expect("entry");

        let resolved = super::resolve_intra_project_import("Sub.Inner", &entry)
            .expect("Sub.Inner should resolve to Sub/Inner.lean");
        assert!(
            resolved.ends_with("Sub/Inner.lean"),
            "resolved path: {resolved:?}"
        );
    }
}
