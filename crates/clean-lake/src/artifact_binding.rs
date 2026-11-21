// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Is an imported module's artifact the build of its source?
//!
//! # Why a consumer asks (module-trust round 27)
//!
//! `clean check` and `clean export-cert` re-admit every imported declaration
//! they cite through `clean_olean::ImportedConeGate`, which proves the
//! imported declarations WELL-TYPED. It cannot prove them FAITHFUL: a
//! definition whose value was rewritten to another well-typed value (`def
//! V0.v : Nat := 1` where the source says `0`) passes any re-check, and every
//! statement about it then means what the artifact says, not what the source
//! says. Measured on `d0789d05f`: `theorem Vu.v1 : V0.v = 1 := rfl` over such
//! an artifact, checked from outside the project with `LEAN_PATH` at its
//! `.lake/build/lib`, printed `1 passed` (exit 0) while the project's source
//! next to it says `V0.v := 0`.
//!
//! Only the source can say what a module means. When a consumer loads an
//! artifact that sits in a Lake workspace's build directory next to its
//! source, this module answers whether the artifact is what `clean lake
//! build` recorded building from that source ([`crate::build_trace`]); the
//! consumer refuses to credit anything checked against one that is not.
//!
//! Before any of that, an artifact Lean wrote in a world this build of Clean
//! does not read (`crates/clean-olean/lean_worlds.tsv`, docs/DECISIONS.md
//! R38, R81) is refused, with its source or without one: until 2026-10-17
//! one with no source beside it was disclosed and loaded.
//!
//! # What it does not establish
//!
//! * An artifact with no source anywhere near it (a directory of bare
//!   `.olean`s on `LEAN_PATH`) cannot be compared with anything: its
//!   definitions are the only definition of the module there is. The consumer
//!   discloses such an import rather than refusing it.
//! * An artifact another tool wrote (its header git hash is not this
//!   builder's, e.g. Lean's own `lake build`) carries no trace this builder
//!   could have written; it is disclosed, not refused.
//! * A trace is a cache key, not a signature ([`crate::build_trace`]): a
//!   writer that rewrites an artifact AND re-derives its trace is believed
//!   here, as it is by `clean lake build`. `clean lake verify-fresh`
//!   (rebuild and compare bytes) is the check that does not rest on a trace.

use crate::build::{BuildContext, CLEAN_OLEAN_GIT_HASH};
use crate::workspace::Workspace;
use clean_kernel::LeanWorld;
use std::collections::HashMap;
use std::path::{Path, PathBuf};

/// What admitting one imported module's artifact decided.
///
/// This is the one authority every consumer of an imported artifact uses:
/// `clean check`, `clean export-cert`, and — for every module a build loads
/// that the workspace does not build itself — `clean lake build` and
/// `clean lake check-build` (module-trust round 31: those two loaded a
/// module named `Mathlib.*`, `Std.*` or `Init.*` from the search paths with
/// no binding and no disclosure, so an artifact rewritten beside the source
/// it no longer matches built "OK" with a dependent while `clean check`
/// refused it). A module name says nothing about what an artifact is: a
/// module is the toolchain's only when every part it resolved to is the
/// pinned toolchain's own build, by digest
/// ([`clean_olean::toolchain_identity`]), wherever it sits.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum ImportAdmission {
    /// The pinned toolchain's own build of the module: the checker's
    /// declared base, neither bound nor listed.
    Toolchain,
    /// The build of the source beside it ([`ArtifactSourceBinding::Bound`]).
    Bound,
    /// Not the build of the source beside it: nothing may be checked or
    /// built against it. The row says why.
    Refused(String),
    /// No source to compare it with, or written by another tool: taken as
    /// built, and listed on the verdict. The row says which.
    Disclosed(String),
}

/// What [`ImportAdmitter::examine`] found among the modules it was given.
#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct ImportAdmissionFindings {
    /// One row per artifact that is not the build of the source next to it.
    pub refusals: Vec<String>,
    /// One row per artifact whose definitions were taken as built, with no
    /// source compared.
    pub disclosures: Vec<String>,
}

/// The artifact found in the first search root that owns its package.
#[must_use]
pub(crate) fn resolve_import(
    module: &str,
    search_paths: &[PathBuf],
    world: Option<LeanWorld>,
) -> Option<PathBuf> {
    let module = Workspace::parse_module_name(module).ok()?;
    clean_olean::resolve_typed_module_path_in_world(
        &module,
        search_paths,
        world.map(LeanWorld::tag),
    )
    .ok()
    .filter(|path| path.is_file())
}

fn artifact_digest(path: &Path) -> String {
    std::fs::read(path).map_or_else(
        |e| format!("unreadable: {e}"),
        |bytes| format!("blake3:{}", &blake3::hash(&bytes).to_hex()[..16]),
    )
}

/// Admits imported artifacts ([`ImportAdmission`]), remembering each
/// decision for the admitter's lifetime (one command).
#[derive(Debug, Default)]
pub struct ImportAdmitter {
    binder: ArtifactBinder,
    decided: HashMap<(String, PathBuf, Option<LeanWorld>), ImportAdmission>,
}

impl ImportAdmitter {
    /// An admitter that has decided nothing yet.
    #[must_use]
    pub(crate) fn new() -> Self {
        Self::default()
    }

    /// Apply artifact admission with the declaration used by the loader.
    pub(crate) fn admit_in_world(
        &mut self,
        module: &str,
        olean: &Path,
        world: Option<LeanWorld>,
    ) -> ImportAdmission {
        let key = (module.to_string(), olean.to_path_buf(), world);
        if let Some(decided) = self.decided.get(&key) {
            return decided.clone();
        }
        let pinned =
            clean_olean::toolchain_identity::pinned_toolchain_module(module, olean).is_ok();
        let world_check = match world {
            Some(world) => clean_olean::check_olean_file_in_world(olean, world),
            None if pinned => Ok(()),
            None => clean_olean::lean_world_of_olean_file(olean).map(|_| ()),
        };
        let decided = if let Err(e) = world_check {
            // A Lean world this build does not read, or an artifact whose
            // header does not parse, is refused whether or not a source
            // sits beside it (R81). A readable world goes on to be bound
            // or disclosed; loading it into an environment of another
            // world is the loader's refusal (`MixedLeanWorlds`).
            ImportAdmission::Refused(format!(
                "import `{module}`: {} ({}): {e}",
                olean.display(),
                artifact_digest(olean)
            ))
        } else if pinned {
            ImportAdmission::Toolchain
        } else {
            match self.binder.bind(module, olean) {
                ArtifactSourceBinding::Bound { .. } => ImportAdmission::Bound,
                ArtifactSourceBinding::Unbound { source, reason } => {
                    ImportAdmission::Refused(format!(
                        "import `{module}`: the artifact {} is not the build of its source {} \
                         ({reason}); nothing is checked against it — run `clean lake build`",
                        olean.display(),
                        source.display()
                    ))
                }
                ArtifactSourceBinding::ForeignBuilt { git_hash } => {
                    ImportAdmission::Disclosed(format!(
                        "{module}: {} ({}), written by another tool (header git hash \
                         {git_hash}); no build trace binds it to a source",
                        olean.display(),
                        artifact_digest(olean)
                    ))
                }
                ArtifactSourceBinding::NoSource { why } => ImportAdmission::Disclosed(format!(
                    "{module}: {} ({}); {why}",
                    olean.display(),
                    artifact_digest(olean)
                )),
            }
        };
        self.decided.insert(key, decided.clone());
        decided
    }

    /// Admit every module of `modules` as it resolves on `search_paths`,
    /// in name order. A module that resolves to no file was not loaded from
    /// an artifact and is skipped.
    pub fn examine(
        &mut self,
        modules: impl IntoIterator<Item = String>,
        search_paths: &[PathBuf],
    ) -> ImportAdmissionFindings {
        self.examine_in_world(modules, search_paths, None)
    }

    /// Examine resolved modules using the caller's selected import declaration.
    pub fn examine_in_world(
        &mut self,
        modules: impl IntoIterator<Item = String>,
        search_paths: &[PathBuf],
        world: Option<LeanWorld>,
    ) -> ImportAdmissionFindings {
        let mut modules: Vec<String> = modules.into_iter().collect();
        modules.sort();
        modules.dedup();
        let mut findings = ImportAdmissionFindings::default();
        for module in modules {
            let Some(olean) = resolve_import(&module, search_paths, world) else {
                continue;
            };
            match self.admit_in_world(&module, &olean, world) {
                ImportAdmission::Toolchain | ImportAdmission::Bound => {}
                ImportAdmission::Refused(row) => findings.refusals.push(row),
                ImportAdmission::Disclosed(row) => findings.disclosures.push(row),
            }
        }
        findings
    }
}

/// What a consumer may conclude about one imported artifact.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum ArtifactSourceBinding {
    /// The artifact sits in the build directory of the workspace that holds
    /// the module's source, and this builder's trace for it matches the
    /// source, the artifacts of its in-workspace closure, the toolchain
    /// import roots and the artifact itself.
    Bound {
        /// The module's source file.
        source: PathBuf,
    },
    /// The module's source is right there, and the artifact is not what this
    /// builder recorded building from it. Nothing checked against it may be
    /// credited.
    Unbound {
        /// The module's source file.
        source: PathBuf,
        /// Why (the same wording `clean lake build --verbose` prints).
        reason: String,
    },
    /// Written by another tool (a foreign header git hash); its source may be
    /// present, but no trace this builder could have written exists for it.
    ForeignBuilt {
        /// The header git hash the artifact carries.
        git_hash: String,
    },
    /// No source for this artifact could be located.
    NoSource {
        /// Why no source was found.
        why: String,
    },
}

/// Classifies imported artifacts, caching one [`BuildContext`] per Lake
/// workspace so a closure of many modules from one workspace loads it once.
#[derive(Default)]
pub(crate) struct ArtifactBinder {
    contexts: HashMap<PathBuf, Option<BuildContext>>,
}

impl std::fmt::Debug for ArtifactBinder {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ArtifactBinder")
            .field("workspaces", &self.contexts.len())
            .finish()
    }
}

/// The header git hash of an `.olean`, or `None` when the header does not
/// parse. The header is read whole for its version: 56 bytes for v1, 88 for
/// v2 (until 2026-10-17 only 56 were read, so every v2 artifact, every one
/// Lean v4.26 or later writes, was "unreadable").
fn header_git_hash(olean: &Path) -> Option<String> {
    let header = clean_olean::read_olean_header(olean).ok()?;
    let len = header.git_hash.len().min(CLEAN_OLEAN_GIT_HASH.len());
    Some(
        String::from_utf8_lossy(&header.git_hash[..len])
            .trim_end_matches('\0')
            .to_string(),
    )
}

fn is_lake_root(path: &Path) -> bool {
    path.join("lakefile.lean").is_file() || path.join("lakefile.toml").is_file()
}

fn same_file(a: &Path, b: &Path) -> bool {
    match (a.canonicalize(), b.canonicalize()) {
        (Ok(a), Ok(b)) => a == b,
        _ => false,
    }
}

impl ArtifactBinder {
    /// Classify the artifact `olean` that was loaded for `module`.
    pub(crate) fn bind(&mut self, module: &str, olean: &Path) -> ArtifactSourceBinding {
        // The nearest enclosing Lake workspace whose build directory is where
        // this artifact sits, and which can locate the module's source.
        let mut found: Option<(PathBuf, PathBuf)> = None;
        let mut nearest_unloadable: Option<String> = None;
        for dir in olean.ancestors().skip(1) {
            if !is_lake_root(dir) {
                continue;
            }
            let key = dir.canonicalize().unwrap_or_else(|_| dir.to_path_buf());
            let ctx = self
                .contexts
                .entry(key.clone())
                .or_insert_with(|| Workspace::load(&key).ok().map(BuildContext::new));
            let Some(ctx) = ctx.as_ref() else {
                nearest_unloadable.get_or_insert_with(|| {
                    format!("the workspace at {} does not load", key.display())
                });
                continue;
            };
            let writes_here = ctx
                .workspace()
                .olean_path(module)
                .is_ok_and(|p| same_file(&p, olean));
            if !writes_here {
                continue;
            }
            if let Some(source) = ctx.workspace().find_module(module) {
                found = Some((key, source));
            }
            break;
        }
        let Some((root, source)) = found else {
            return ArtifactSourceBinding::NoSource {
                why: nearest_unloadable.unwrap_or_else(|| {
                    "not in the build directory of a Lake workspace that holds its source"
                        .to_string()
                }),
            };
        };
        match header_git_hash(olean) {
            Some(hash) if hash == CLEAN_OLEAN_GIT_HASH => {}
            Some(git_hash) => return ArtifactSourceBinding::ForeignBuilt { git_hash },
            None => {
                return ArtifactSourceBinding::Unbound {
                    source,
                    reason: "unreadable artifact header".to_string(),
                }
            }
        }
        let Some(Some(ctx)) = self.contexts.get_mut(&root) else {
            return ArtifactSourceBinding::NoSource {
                why: format!("the workspace at {} does not load", root.display()),
            };
        };
        match ctx.artifact_trace_refusal(module) {
            Ok(None) => ArtifactSourceBinding::Bound { source },
            Ok(Some(reason)) => ArtifactSourceBinding::Unbound {
                source,
                reason: reason.to_string(),
            },
            Err(e) => ArtifactSourceBinding::Unbound {
                source,
                reason: format!("its build trace could not be compared: {e}"),
            },
        }
    }
}

#[cfg(test)]
#[path = "artifact_binding_tests.rs"]
mod tests;
