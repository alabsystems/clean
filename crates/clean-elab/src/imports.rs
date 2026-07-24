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

/// Process import statements and load modules
///
/// Tries to load modules from .olean files first (real Mathlib), falling back
/// to stub initializers if .olean files are not found or fail to load.
///
/// # Priority
/// 1. Real .olean loading via clean_olean (requires MATHLIB_PATH/LEAN_PATH or elan)
/// 2. Fallback to stub initializers for known modules
/// 3. Unknown imports are silently ignored
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
/// Modules that have no built-in Clean prelude are silently ignored, mirroring
/// the unknown-module behavior of [`process_imports`].
pub fn process_imports_clean_native(
    env: &mut clean_kernel::Environment,
    paths: &[Vec<String>],
) -> Result<(), ElabError> {
    for path in paths {
        let module = path.join(".");
        let _ = crate::prelude_providers::init_prelude_for_module(env, &module)?;
    }
    Ok(())
}

pub fn process_imports(
    env: &mut clean_kernel::Environment,
    paths: &[Vec<String>],
) -> Result<(), ElabError> {
    process_imports_with_search_paths(env, paths, &[])
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
    let search_paths = import_search_paths(extra_search_paths);

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
        finish_import_module(env, &module, outcome)?;
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
        finish_import_module(env, &module, outcome)?;
    }
    Ok(())
}

/// Apply the shared per-import outcome policy: register the surface prelude on
/// a successful `.olean` load, honor the `UnsupportedModule` → built-in prelude
/// fallback, and otherwise (load error, or `None` = no search paths) fall back
/// to the hand-written stub prelude. `outcome` is `None` when search paths were
/// empty (skip the `.olean` attempt entirely) and `Some(result)` once a load
/// has been attempted.
fn finish_import_module(
    env: &mut clean_kernel::Environment,
    module: &str,
    outcome: Option<Result<Vec<clean_olean::LoadSummary>, clean_olean::ImportError>>,
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
                if crate::prelude_providers::init_prelude_for_module(env, &module)? {
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
                // Fall through to stub logic below
            }
        }
    }

    // Stub fallback for known modules
    let _ = crate::prelude_providers::init_prelude_for_module(env, module)?;
    Ok(())
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
        lake_import_search_paths_for_file, nearest_lake_root_for_file,
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

    /// An unknown module with no stub and no `.olean` must be silently ignored
    /// regardless of the (now larger) import-graph bound.
    #[test]
    fn process_imports_unknown_module_is_ignored_under_new_bound() {
        use clean_kernel::Environment;

        let empty = tempfile::tempdir().expect("tempdir");
        let mut env = Environment::new();
        let paths = vec![vec!["Totally", "Unknown", "Module", "Name"]
            .into_iter()
            .map(String::from)
            .collect()];

        let result = super::process_imports_with_search_paths(
            &mut env,
            &paths,
            &[empty.path().to_path_buf()],
        );
        assert!(
            result.is_ok(),
            "unknown imports must be silently ignored, got {result:?}",
        );
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
