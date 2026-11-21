// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Import processing and module loading.

use crate::error::ElabError;
use clean_kernel::Name;
use clean_parser::SurfaceName;
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
pub(crate) const FRONTEND_OLEAN_IMPORT_MODULE_LIMIT: usize = 16_384;

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
    requires_artifact: bool,
    /// Modules whose declarations are already in `env` because this run
    /// elaborated their intra-project `.lean` source. Such an import is
    /// resolved even though no `.olean` exists for it.
    satisfied_from_source: &'a HashSet<Name>,
}

impl ImportResolution<'_> {
    fn is_satisfied_from_source(&self, module: &Name) -> bool {
        !self.requires_artifact && self.satisfied_from_source.contains(module)
    }
}

/// Empty borrow used by the entry points that have no per-file source-resolution
/// record of their own.
fn no_source_resolved() -> &'static HashSet<Name> {
    static EMPTY: std::sync::OnceLock<HashSet<Name>> = std::sync::OnceLock::new();
    EMPTY.get_or_init(HashSet::new)
}

/// Process import statements without loading external `.olean` artifacts.
///
/// This mode is used by Clean-native project authority checks: imports may
/// initialize Clean's built-in module preludes, but external Lean / Lake /
/// Mathlib `.olean` artifacts are not consulted as semantic evidence.
///
/// Under [`ImportPolicy::FailClosed`] a module with no built-in Clean prelude is
/// an error, matching the unknown-module behavior of [`process_imports`].
pub(crate) fn process_imports_clean_native(
    env: &mut clean_kernel::Environment,
    paths: &[SurfaceName],
    policy: ImportPolicy,
) -> Result<(), ElabError> {
    process_imports_clean_native_with_satisfied(env, paths, policy, no_source_resolved())
}

/// [`process_imports_clean_native`] with the caller's satisfied-from-source
/// record — the same record [`crate::FileContext::mark_import_satisfied_from_source`]
/// keeps and the `.olean` file path already consults. The module doc above has
/// always counted "an intra-project `.lean` source file this run already
/// elaborated" as RESOLVED under [`ImportPolicy::FailClosed`]; this entry point
/// lets the clean-native path (which loads no `.olean` and previously built its
/// own resolution over an EMPTY set) honor that same class. A whole-unit
/// batch elaborating every member source in one run (header-first, so member
/// order cannot matter) records each member module here: the declarations
/// really are in `env` by that run's own elaboration, which is the exact
/// justification the doc gives. Nothing widens: an unsatisfied module keeps
/// the verbatim refusal, and no fabrication class is added.
pub(crate) fn process_imports_clean_native_with_satisfied(
    env: &mut clean_kernel::Environment,
    paths: &[SurfaceName],
    policy: ImportPolicy,
    satisfied_from_source: &HashSet<Name>,
) -> Result<(), ElabError> {
    process_imports_clean_native_with_provided(env, paths, policy, satisfied_from_source, None)
}

/// The source-module initializer's completed artifacts already inhabit this
/// environment. Honor that same-run DATA without searching or fabricating a
/// module. The caller's source refusal check retains precedence.
pub(crate) fn process_imports_clean_native_with_provided(
    env: &mut clean_kernel::Environment,
    paths: &[SurfaceName],
    policy: ImportPolicy,
    satisfied_from_source: &HashSet<Name>,
    provided: Option<&clean_olean::CompletedModuleImports>,
) -> Result<(), ElabError> {
    let resolution = ImportResolution {
        policy,
        requires_artifact: false,
        satisfied_from_source,
    };
    for path in paths {
        let module = path.name().clone();
        if resolution.is_satisfied_from_source(&module)
            || provided.is_some_and(|completed| completed.contains_module(&module))
        {
            continue;
        }
        if serve_from_prelude(env, &module, resolution)? {
            continue;
        }
        unresolved_import(&module, "no Clean-native prelude provides it", resolution)?;
    }
    Ok(())
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
/// - Then the checkout's pinned toolchain (`lean-toolchain`), and no other
///   installed toolchain (docs/DECISIONS.md R81)
pub fn process_imports(
    env: &mut clean_kernel::Environment,
    paths: &[SurfaceName],
) -> Result<(), ElabError> {
    process_imports_with_search_paths(env, paths, &[])
}

/// [`process_imports`] with an explicit [`ImportPolicy`].
pub fn process_imports_with_policy(
    env: &mut clean_kernel::Environment,
    paths: &[SurfaceName],
    policy: ImportPolicy,
) -> Result<(), ElabError> {
    process_imports_with_search_paths_and_policy(env, paths, &[], policy)
}

/// Process import statements with additional file/project-local `.olean` paths.
///
/// The extra paths are searched before environment/toolchain defaults so a Lake
/// project's build output wins over unrelated global packages.
pub(crate) fn process_imports_with_search_paths(
    env: &mut clean_kernel::Environment,
    paths: &[SurfaceName],
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
pub(crate) fn process_imports_with_search_paths_and_policy(
    env: &mut clean_kernel::Environment,
    paths: &[SurfaceName],
    extra_search_paths: &[PathBuf],
    policy: ImportPolicy,
) -> Result<(), ElabError> {
    let search_paths = import_search_paths(extra_search_paths);
    let resolution = ImportResolution {
        policy,
        requires_artifact: false,
        satisfied_from_source: no_source_resolved(),
    };

    for path in paths {
        let module = path.name().clone();

        // Try .olean loading first if search paths are available. Each import
        // allocates a FRESH `visited` set, so overlapping closures are re-read
        // per import — acceptable for the low-import single-file callers, but
        // O(n²) for a Mathlib file: use `process_imports_with_search_paths_shared`
        // there.
        let outcome = if search_paths.is_empty() {
            None
        } else {
            Some(clean_olean::load_typed_module_with_deps_bounded(
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
pub(crate) fn process_imports_with_search_paths_shared(
    env: &mut clean_kernel::Environment,
    paths: &[SurfaceName],
    extra_search_paths: &[PathBuf],
    visited: &mut hashbrown::HashSet<String>,
) -> Result<(), ElabError> {
    process_imports_shared_inner(
        env,
        paths,
        Ok(import_search_paths(extra_search_paths)),
        visited,
        ImportResolution {
            policy: ImportPolicy::default(),
            requires_artifact: false,
            satisfied_from_source: no_source_resolved(),
        },
    )
}

/// `search_paths` is every root the file's imports resolve on, or the
/// refusal of its run's Lean world (G72): then an import this run did not
/// satisfy from the project's own source is refused by name, with no
/// stand-in, whatever the policy (R38: no warn-and-continue mode). A module
/// the run elaborated from its own source stays resolved: the run selects one
/// world for every file (decision R111), so every file of a refused run comes
/// here, and no part of any Lean world is read; such a file is checked
/// against what a file with no imports is.
fn process_imports_shared_inner(
    env: &mut clean_kernel::Environment,
    paths: &[SurfaceName],
    search_paths: Result<Vec<PathBuf>, clean_olean::ImportWorldRefusal>,
    visited: &mut hashbrown::HashSet<String>,
    resolution: ImportResolution<'_>,
) -> Result<(), ElabError> {
    let search_paths = match search_paths {
        Ok(search_paths) => search_paths,
        Err(refusal) => {
            for path in paths {
                let module = path.name();
                if !resolution.is_satisfied_from_source(module) {
                    return Err(ElabError::UnresolvedImport {
                        module: module.to_string(),
                        reason: refusal.to_string(),
                    });
                }
            }
            return Ok(());
        }
    };

    for path in paths {
        let module = path.name().clone();

        // This run already checked the selected source in this environment.
        // Replaying an artifact can change its compiler context. Artifact-only
        // bootstrap still has to judge the selected artifact itself.
        if resolution.is_satisfied_from_source(&module)
            && !clean_olean::clean_payload_imports_required(env)
        {
            continue;
        }

        let outcome = if search_paths.is_empty() {
            None
        } else {
            Some(clean_olean::load_typed_module_with_deps_bounded_shared(
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
pub(crate) fn process_imports_for_file(
    env: &mut clean_kernel::Environment,
    paths: &[SurfaceName],
    file_ctx: &mut crate::FileContext,
) -> Result<(), ElabError> {
    // An owned path list (one PathBuf per search root) so the immutable
    // borrow of `file_ctx` does not conflict with the mutable borrow of its
    // `visited` memo below.
    let search_paths = file_ctx.effective_import_search_paths();
    // The run's project world is declared on the environment before any part
    // loads (G72, R38): a part another root supplies first (`LEAN_PATH`,
    // `MATHLIB_PATH`, a Lake root) from another world is then refused as
    // `MixedLeanWorlds`, as `lean` refuses its header, never read as the
    // project's. The checkout's own world (`CheckoutPin`: no
    // `lean-toolchain`, or one naming the Oracle or a Clean toolchain) is not
    // declared (R81, decision R111): its environment binds to the first world
    // it reads.
    if let Some(world) = file_ctx
        .import_world()
        .and_then(|choice| choice.as_ref().ok())
        .and_then(clean_olean::ImportWorld::declared_world)
    {
        if let Err(error) = clean_olean::declare_environment_world(env, world) {
            return Err(ElabError::UnresolvedImport {
                module: paths
                    .first()
                    .map(|path| path.name().to_string())
                    .unwrap_or_default(),
                reason: error.to_string(),
            });
        }
    }
    let policy = file_ctx.import_policy();
    let requires_artifact = file_ctx.imports_require_artifacts();
    let (visited, satisfied_from_source) = file_ctx.import_loader_state_mut();
    process_imports_shared_inner(
        env,
        paths,
        search_paths,
        visited,
        ImportResolution {
            policy,
            requires_artifact,
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
    paths: &[SurfaceName],
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
    module: &Name,
    outcome: Option<Result<Vec<clean_olean::LoadSummary>, clean_olean::ImportError>>,
    resolution: ImportResolution<'_>,
) -> Result<(), ElabError> {
    if resolution.requires_artifact {
        let reason = match outcome.as_ref() {
            Some(Ok(_)) => None,
            Some(Err(error)) => Some(error.to_string()),
            None => Some("no `.olean` search path was available".to_owned()),
        };
        if let Some(reason) = reason {
            return Err(ElabError::UnresolvedImport {
                module: module.to_string(),
                reason,
            });
        }
    }
    if clean_olean::clean_payload_imports_required(env) {
        if let Some(Err(error)) = outcome.as_ref() {
            // A bootstrap selected from Clean artifacts cannot silently change
            // its imported semantics after a missing, corrupt, or replaced
            // artifact. Keep the original diagnostic and all existing hard
            // refusals. Only errors that already reached finish_unresolved
            // may retain its legitimate satisfied-from-source exception.
            let hard = matches!(error, clean_olean::ImportError::UnsupportedModule { .. })
                || error.is_inconsistent_artifact()
                || error.is_world_refusal()
                || error.is_resource_refusal();
            if hard || !resolution.is_satisfied_from_source(module) {
                return Err(ElabError::UnresolvedImport {
                    module: module.to_string(),
                    reason: error.to_string(),
                });
            }
        }
    }
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
                // `CLEAN_IMPORT_SKIP_TRACE=<substring>` (or `1` for all) names
                // every constant the loader skipped and why — the only way to
                // tell a constant that is ABSENT from one that never existed.
                if let Some(filter) = std::env::var_os("CLEAN_IMPORT_SKIP_TRACE") {
                    let filter = filter.to_string_lossy();
                    for skip in summaries.iter().flat_map(|s| &s.skipped_constants) {
                        if filter == "1" || skip.name.contains(filter.as_ref()) {
                            eprintln!("import-skip {}: {}", skip.name, skip.reason);
                        }
                    }
                }
                if let Some(label) = canonical_prelude_label(module) {
                    let _ =
                        crate::prelude_providers::init_surface_prelude_after_olean(env, &label)?;
                }
                return Ok(()); // Successfully loaded, skip stub fallback
            }
            Err(clean_olean::ImportError::UnsupportedModule {
                module: failed_module,
                reason,
            }) => {
                if serve_from_prelude(env, module, resolution)? {
                    return Ok(());
                }
                return Err(ElabError::Unsupported {
                    feature: format!("import {module}: {reason} (loader: {failed_module})"),
                });
            }
            // A corrupt artifact (module-trust round 27: a structure-field
            // table contradicting its own projections; round 28: a payload
            // declaring one name twice) is not an absent one.
            // Its declarations are already partly in `env`, so no policy may
            // continue past it — `--permissive-imports` included, which would
            // otherwise check the file against the rewritten half. Nor past a
            // part of a refused or second Lean world (R38, R81): a stand-in
            // for it would check the file against another Lean. A resource stop
            // or interruption also leaves a partially loaded environment.
            Err(e)
                if e.is_inconsistent_artifact()
                    || e.is_world_refusal()
                    || e.is_resource_refusal() =>
            {
                return Err(ElabError::UnresolvedImport {
                    module: module.to_string(),
                    reason: e.to_string(),
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
    module: &Name,
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
    if clean_olean::clean_payload_imports_required(env) {
        return Err(ElabError::UnresolvedImport {
            module: module.to_string(),
            reason: reason.to_owned(),
        });
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
pub(crate) fn canonical_prelude_label(module: &Name) -> Option<String> {
    let label = module.to_string();
    (SurfaceName::generated_path(&label).name() == module).then_some(label)
}

fn serve_from_prelude(
    env: &mut clean_kernel::Environment,
    module: &Name,
    resolution: ImportResolution<'_>,
) -> Result<bool, ElabError> {
    let Some(label) = canonical_prelude_label(module) else {
        return Ok(false);
    };
    let declared = crate::prelude_providers::has_declared_prelude(&label);
    if resolution.policy == ImportPolicy::FailClosed && !declared {
        return Ok(false);
    }
    if !crate::prelude_providers::init_prelude_for_module(env, &label)? {
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
    module: &Name,
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

/// The search list the `.olean` loader uses for a file whose extra (Lake)
/// search paths are `extra_search_paths`: those first, then the
/// `LEAN_PATH`/toolchain defaults. Public so a consumer can say which file an
/// import it loaded came from.
#[must_use]
pub fn effective_import_search_paths(extra_search_paths: &[PathBuf]) -> Vec<PathBuf> {
    import_search_paths(extra_search_paths)
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
/// import search paths of `from_file`: its nearest Lake root, then the
/// defaults of its project's Lean world ([`clean_olean::import_world_for_file`];
/// `false` when that world is refused). A caller that elaborates several
/// files into one environment asks [`olean_available_in_world`] with the
/// run's world instead.
///
/// Read-only filesystem probe — loads nothing. The front-end uses it to prefer
/// loading a module's compiled artifact over recursively elaborating its source
/// when both exist on disk (the case when checking a `.lean` file that lives
/// *inside* a source tree — e.g. a Mathlib file — whose sibling imports also
/// resolve to `.lean`). This mirrors Lean's own model: the file under check
/// elaborates from source; its imports are loaded from `.olean`.
#[must_use]
pub fn olean_available_for_module(module: &Name, from_file: &Path) -> bool {
    olean_available_in_world(
        module,
        from_file,
        &clean_olean::import_world_for_file(from_file),
    )
}

/// [`olean_available_for_module`] in the run's Lean world `world`.
#[must_use]
pub fn olean_available_in_world(
    module: &Name,
    from_file: &Path,
    world: &Result<clean_olean::ImportWorld, clean_olean::ImportWorldRefusal>,
) -> bool {
    // A run whose Lean world is refused has no artifact to prefer.
    let Ok(world) = world else {
        return false;
    };
    let mut search_paths = lake_import_search_paths_for_file(from_file);
    for default in clean_olean::search_paths_in_world(world) {
        if !search_paths.contains(&default) {
            search_paths.push(default);
        }
    }
    clean_olean::resolve_typed_module_path_in_world(module, &search_paths, world.declared_world())
        .is_ok()
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
pub fn resolve_intra_project_import(module: &Name, parent_path: &Path) -> Option<PathBuf> {
    let relative_lean = clean_olean::typed_module_rel_path(module)
        .ok()?
        .with_extension("lean");
    // These are exact Name.str components, never segments recovered from Display.
    let mut parts = Vec::new();
    let mut current = module;
    while let clean_kernel::name::NameInner::Str(parent, component) = current.inner() {
        parts.push(component.as_ref());
        current = parent;
    }
    parts.reverse();

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
                pkg_relative.as_mut_os_string().push(".lean");
                pkg_relative
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
    use clean_kernel::Name;
    use clean_parser::SurfaceName;
    use std::fs;

    /// The clean-native path honors the same satisfied-from-source resolution
    /// class `finish_unresolved` has always honored — and ONLY that class: an
    /// unsatisfied module keeps the verbatim fail-closed refusal.
    #[test]
    fn clean_native_path_consults_the_satisfied_from_source_record() {
        let mut env = clean_kernel::Environment::with_prelude();
        let satisfied: super::HashSet<Name> = [Name::anon().str("ProjectSibling")].into();

        super::process_imports_clean_native_with_satisfied(
            &mut env,
            &[SurfaceName::component("ProjectSibling", false)],
            super::ImportPolicy::FailClosed,
            &satisfied,
        )
        .expect("a satisfied intra-project module is resolved, not refused");

        let err = super::process_imports_clean_native_with_satisfied(
            &mut env,
            &[SurfaceName::component("NotInThisRun", false)],
            super::ImportPolicy::FailClosed,
            &satisfied,
        )
        .expect_err("an unsatisfied module keeps the fail-closed refusal");
        match err {
            ElabError::UnresolvedImport { module, reason } => {
                assert_eq!(module, "NotInThisRun");
                assert!(
                    reason.contains("no Clean-native prelude provides it"),
                    "{reason}"
                );
            }
            other => panic!("expected UnresolvedImport, got {other:?}"),
        }

        // The delegating original stays byte-identical in behavior: same
        // refusal with the empty set.
        let err = super::process_imports_clean_native(
            &mut env,
            &[SurfaceName::component("ProjectSibling", false)],
            super::ImportPolicy::FailClosed,
        )
        .expect_err("without the record the same module still refuses");
        assert!(matches!(err, ElabError::UnresolvedImport { .. }));
    }

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
        let paths = vec![SurfaceName::from_name(
            Name::anon()
                .str("Mathlib")
                .str("Data")
                .str("Real")
                .str("Basic"),
        )];

        super::process_imports_with_search_paths(&mut env, &paths, &[empty.path().to_path_buf()])
            .expect("known module with no discoverable .olean must fall back to a stub, not error");

        assert!(
            env.get_const(&Name::from_string("Real")).is_some(),
            "Real stub should be defined via fallback when no .olean is found",
        );
    }

    #[test]
    fn raw_lean_import_context_requires_an_artifact_and_captured_context_keeps_the_shim() {
        let dir = tempfile::tempdir().expect("isolated import root");
        fs::write(
            dir.path().join("lean-toolchain"),
            "leanprover/lean4:v4.30.0-rc2\n",
        )
        .expect("default-world test pin");
        let decision = clean_olean::source_world_for_file(&dir.path().join("Main.lean"), None)
            .expect("default world needs no installed SDK");
        let paths = vec![dir.path().to_path_buf()];
        let module = "Lean.RawImportRequiresAnArtifact";
        let imports = [SurfaceName::generated_path(module)];
        let header = clean_parser::Parser::parse_header("prelude\n").expect("bare header");
        let (mut env, mut raw) =
            crate::module_driver::module_environment_and_context_with_import_paths(
                crate::module_driver::EnvironmentSetup::default(),
                &decision,
                &header,
                paths.clone(),
            )
            .expect("raw Lean context");
        let error = super::process_imports_for_file(&mut env, &imports, &mut raw)
            .expect_err("missing compiled import must fail");
        assert!(
            matches!(&error, ElabError::UnresolvedImport { module: name, reason }
                if name == module && reason.contains("not found")),
            "{error}"
        );

        let mut captured = crate::FileContext::new();
        captured.set_captured_source_world(&decision, paths);
        super::process_imports_for_file(
            &mut clean_kernel::Environment::new(),
            &imports,
            &mut captured,
        )
        .expect("captured sources still allow their declared Lean shim");
    }

    #[test]
    fn preloaded_artifact_imports_preserve_fail_closed_and_source_refusal_precedence() {
        let dir = tempfile::tempdir().unwrap();
        let bytes = clean_olean::OleanExporter::export_with_env(
            &clean_kernel::Environment::default(),
            &[],
            &[],
            "0000000000000000000000000000000000000000",
        )
        .unwrap();
        fs::write(dir.path().join("ActualSnapshot.olean"), bytes).unwrap();
        let mut env = clean_kernel::Environment::with_prelude();
        let (_, completed) = clean_olean::load_module_with_deps_and_completed_imports(
            &mut env,
            "ActualSnapshot",
            &[dir.path().to_path_buf()],
        )
        .unwrap();
        let paths = module_path("ActualSnapshot");
        super::process_imports_clean_native(&mut env, &paths, super::ImportPolicy::FailClosed)
            .expect_err("legacy no-artifact context remains refused");
        super::process_imports_clean_native_with_provided(
            &mut env,
            &paths,
            super::ImportPolicy::FailClosed,
            super::no_source_resolved(),
            Some(&completed),
        )
        .expect("the exact successfully loaded zero-declaration snapshot is present");
        super::process_imports_clean_native_with_provided(
            &mut env,
            &module_path("ActualSnapshot.Missing"),
            super::ImportPolicy::FailClosed,
            super::no_source_resolved(),
            Some(&completed),
        )
        .expect_err("a namespace prefix supplies no other module");
        let mut context = crate::FileContext::new();
        context.disable_external_import_search();
        context.set_preloaded_artifact_imports(completed);
        let declarations = clean_parser::parse_file("import ActualSnapshot").unwrap();
        crate::elaborate_decl_and_register_with_context(&mut env, &declarations[0], &mut context)
            .expect("same-run actual artifact availability reaches the ordinary import handler");
        context.mark_import_refused_from_source(
            &Name::from_string("ActualSnapshot"),
            "original source failure".into(),
        );
        let error = crate::elaborate_decl_and_register_with_context(
            &mut env,
            &declarations[0],
            &mut context,
        )
        .expect_err("source refusal must win over an actual completed artifact");
        assert!(
            error.to_string().contains("original source failure"),
            "{error}"
        );
    }

    fn module_path(module: &'static str) -> Vec<SurfaceName> {
        vec![SurfaceName::generated_path(module)]
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

        file_ctx
            .mark_import_satisfied_from_source(&Name::from_string("MyProject.Internal.Helpers"));
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

        let resolved = super::resolve_intra_project_import(&Name::from_string("Lib"), &main)
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
            super::resolve_intra_project_import(
                &Name::from_string("Mathlib.Data.Nat.Basic"),
                &main
            )
            .is_none(),
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

        let resolved = super::resolve_intra_project_import(&Name::from_string("Sub.Inner"), &entry)
            .expect("Sub.Inner should resolve to Sub/Inner.lean");
        assert!(
            resolved.ends_with("Sub/Inner.lean"),
            "resolved path: {resolved:?}"
        );
    }
}

#[cfg(test)]
#[path = "imports_world_tests.rs"]
mod world_tests;

#[cfg(test)]
#[path = "imports_resource_tests.rs"]
mod resource_tests;

#[cfg(test)]
#[path = "imports/clean_payload_requirement_tests.rs"]
mod clean_payload_requirement_tests;

#[cfg(test)]
#[path = "imports_source_satisfaction_tests.rs"]
mod source_satisfaction_tests;
