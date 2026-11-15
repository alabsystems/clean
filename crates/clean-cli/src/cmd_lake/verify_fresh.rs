// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `clean lake verify-fresh` — are the built `.olean` artifacts what the
//! current source builds to?
//!
//! Two checks, both fail-closed:
//!
//! 1. **Import freshness** (Cake's signature): stale iff the source declares an
//!    import the `.olean` lacks.
//! 2. **Fresh-build digest**: every module is rebuilt from source into a
//!    scratch directory (`BuildContext::build_fresh_artifacts`; the project's
//!    own build directory is neither read nor written), and the artifact on
//!    disk — `.olean`, `.olean.server`, `.olean.private` — must be
//!    byte-identical to what that build wrote.
//!
//! # What was wrong
//!
//! Until 2026-09-24 the command ran check 1 only. Its `env_digest` hashes the
//! artifact bytes, so rewriting an artifact CHANGED the digest the command
//! printed — and the verdict still read `fresh`, exit 0 (measured on
//! `7369eb6fd`: an artifact whose lemma's stated type had been rewritten, one
//! whose proof had been replaced by `sorry`, and a source edited after its
//! build without touching its imports, all three `OK: all 1 module(s) fresh`).
//! A digest nobody compares against a reference is not a check. The reference
//! is a fresh build: `clean lake build` is byte-reproducible, so any
//! difference is either a stale artifact or a rewritten one, and either way
//! the artifact is not what the source says.
//!
//! # Scope: a module and its in-workspace import closure
//!
//! A module is reported fresh only if its own artifact AND the artifact of
//! every in-workspace module it imports (transitively — the modules the fresh
//! build had to build for it) match that fresh build. Before 2026-09-25 only
//! the named modules were compared, so `--module ChC` said `fresh`, exit 0,
//! while the artifact of `ChA` two imports below it had been rewritten
//! (module-trust verification). Stdlib / out-of-workspace imports are not
//! built here and are not compared.
//!
//! An artifact this builder did not write (a different `.olean` header git
//! hash, e.g. one Lean's own Lake produced) cannot be reproduced here at all.
//! That is reported by name and fails too: this command cannot establish its
//! freshness, and saying `fresh` would be claiming it did.

use clean_lake::{BuildContext, FreshModuleArtifacts, Workspace, CLEAN_OLEAN_GIT_HASH};
use std::collections::HashMap;
use std::path::{Path, PathBuf};

/// Per-module outcome of the fresh-build comparison.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize)]
#[serde(tag = "status", rename_all = "kebab-case")]
enum FreshBuildVerdict {
    /// Byte-identical to the fresh build.
    DigestMatch { digest: String },
    /// The artifact differs from what the current source builds to.
    DigestMismatch {
        /// Which file(s) differ.
        files: Vec<String>,
        artifact: String,
        fresh_build: String,
    },
    /// No artifact on the search path.
    MissingArtifact,
    /// The artifact was not written by `clean lake build`.
    NotCleanBuilt { git_hash: String },
    /// The current source did not build.
    FreshBuildFailed { reason: String },
}

impl FreshBuildVerdict {
    fn label(&self) -> String {
        match self {
            Self::DigestMatch { .. } => "matches fresh build".to_string(),
            Self::DigestMismatch {
                files,
                artifact,
                fresh_build,
            } => format!(
                "DIGEST MISMATCH vs fresh build ({}): artifact {artifact}, fresh build {fresh_build}",
                files.join(", ")
            ),
            Self::MissingArtifact => "MISSING artifact".to_string(),
            Self::NotCleanBuilt { git_hash } => format!(
                "NOT REPRODUCIBLE: header git hash {git_hash} is not clean lake build's; no fresh \
                 build here can reproduce it"
            ),
            Self::FreshBuildFailed { reason } => format!("FRESH BUILD FAILED: {reason}"),
        }
    }

    fn ok(&self) -> bool {
        matches!(self, Self::DigestMatch { .. })
    }
}

#[derive(serde::Serialize)]
struct VerifyFreshReport<'a> {
    signature: &'a clean_cake::CakeBuildSignature,
    fresh_build: &'a [(String, FreshBuildVerdict)],
    fresh: bool,
}

pub(super) fn lake_verify_fresh(
    source_root: PathBuf,
    module: Vec<String>,
    olean_search_path: Vec<PathBuf>,
    json: bool,
) -> anyhow::Result<()> {
    if module.is_empty() {
        anyhow::bail!("verify-fresh: at least one --module is required");
    }
    let search_paths = if olean_search_path.is_empty() {
        // Lean's Lake layout first, then the one `clean lake build` writes.
        vec![
            source_root.join(".lake/build/lib/lean"),
            source_root.join(".lake/build/lib"),
        ]
    } else {
        olean_search_path
    };
    let toolchain = std::fs::read_to_string(source_root.join("lean-toolchain"))
        .ok()
        .map(|s| s.trim().to_string());

    let sig =
        clean_cake::signature_from_search_paths(&module, &source_root, &search_paths, toolchain);
    let fresh_build = compare_with_fresh_build(&source_root, &module, &search_paths);
    let digest_ok = fresh_build.iter().all(|(_, v)| v.ok());
    let fresh = sig.fresh && digest_ok;

    if json {
        let report = VerifyFreshReport {
            signature: &sig,
            fresh_build: &fresh_build,
            fresh,
        };
        println!("{}", serde_json::to_string_pretty(&report)?);
    } else {
        println!(
            "Cake freshness — {} module(s), env_digest {}",
            sig.modules.len(),
            sig.env_digest
        );
        for m in &sig.modules {
            let verdict = fresh_build
                .iter()
                .find(|(name, _)| name == &m.module)
                .map_or_else(|| "not compared".to_string(), |(_, v)| v.label());
            println!(
                "  {:<70} imports {}; {verdict}",
                m.module,
                m.freshness.label()
            );
        }
        for (dep, verdict) in fresh_build
            .iter()
            .filter(|(name, _)| !sig.modules.iter().any(|m| &m.module == name))
        {
            println!(
                "  {:<70} (in-workspace dependency); {}",
                dep,
                verdict.label()
            );
        }
        if let Some(summary) = sig.staleness_summary() {
            eprintln!("STALE: {summary}");
        }
        if fresh {
            println!(
                "OK: all {} module(s) fresh — imports current and every artifact (theirs and \
                 {} in-workspace dependenc(ies)) byte-identical to a fresh build of its source.",
                sig.modules.len(),
                fresh_build.len().saturating_sub(module.len())
            );
        }
    }

    if !sig.fresh {
        anyhow::bail!(
            "verify-fresh: {} stale module(s) — rebuild so the .olean artifacts reflect current source",
            sig.stale_modules.len()
        );
    }
    if !digest_ok {
        let bad: Vec<&str> = fresh_build
            .iter()
            .filter(|(_, v)| !v.ok())
            .map(|(m, _)| m.as_str())
            .collect();
        anyhow::bail!(
            "verify-fresh: {} module(s) whose artifact is not what the current source builds to: {}",
            bad.len(),
            bad.join(", ")
        );
    }
    Ok(())
}

/// The artifact for `module` on the ordered search path (first hit wins).
fn resolve_artifact(module: &str, search_paths: &[PathBuf]) -> Option<PathBuf> {
    let rel = module
        .split('.')
        .collect::<PathBuf>()
        .with_extension("olean");
    search_paths
        .iter()
        .map(|root| root.join(&rel))
        .find(|p| p.exists())
}

fn digest(bytes: &[u8]) -> String {
    format!("blake3:{}", blake3::hash(bytes).to_hex())
}

fn header_git_hash(bytes: &[u8]) -> Option<String> {
    let header = clean_olean::OleanHeader::parse(bytes).ok()?;
    Some(
        String::from_utf8_lossy(&header.git_hash[..CLEAN_OLEAN_GIT_HASH.len()])
            .trim_end_matches('\0')
            .to_string(),
    )
}

fn compare_with_fresh_build(
    source_root: &Path,
    modules: &[String],
    search_paths: &[PathBuf],
) -> Vec<(String, FreshBuildVerdict)> {
    let fresh: Result<
        (
            clean_lake::BuildResult,
            HashMap<String, FreshModuleArtifacts>,
        ),
        String,
    > = Workspace::load(source_root)
        .map_err(|e| format!("cannot load the project at {}: {e}", source_root.display()))
        .and_then(|ws| {
            BuildContext::new(ws)
                .build_fresh_artifacts(modules)
                .map_err(|e| e.to_string())
        });
    // The named modules first, then every in-workspace dependency the fresh
    // build built for them (sorted), each judged the same way.
    let mut subjects: Vec<String> = modules.to_vec();
    if let Ok((_, artifacts)) = &fresh {
        let mut deps: Vec<&String> = artifacts.keys().filter(|k| !modules.contains(k)).collect();
        deps.sort();
        subjects.extend(deps.into_iter().cloned());
    }
    subjects
        .into_iter()
        .map(|module| {
            let verdict = verdict_for(&module, search_paths, &fresh);
            (module, verdict)
        })
        .collect()
}

fn verdict_for(
    module: &str,
    search_paths: &[PathBuf],
    fresh: &Result<
        (
            clean_lake::BuildResult,
            HashMap<String, FreshModuleArtifacts>,
        ),
        String,
    >,
) -> FreshBuildVerdict {
    let Some(path) = resolve_artifact(module, search_paths) else {
        return FreshBuildVerdict::MissingArtifact;
    };
    let Ok(olean) = std::fs::read(&path) else {
        return FreshBuildVerdict::MissingArtifact;
    };
    match header_git_hash(&olean) {
        Some(hash) if hash == CLEAN_OLEAN_GIT_HASH => {}
        Some(hash) => return FreshBuildVerdict::NotCleanBuilt { git_hash: hash },
        None => {
            return FreshBuildVerdict::NotCleanBuilt {
                git_hash: "<unreadable header>".to_string(),
            }
        }
    }
    let (result, artifacts) = match fresh {
        Ok(ok) => ok,
        Err(reason) => {
            return FreshBuildVerdict::FreshBuildFailed {
                reason: reason.clone(),
            }
        }
    };
    let Some(reference) = artifacts.get(module) else {
        let reason = result.failed.iter().find(|(m, _)| m == module).map_or_else(
            || "the fresh build produced no artifact for it".to_string(),
            |(_, e)| e.clone(),
        );
        return FreshBuildVerdict::FreshBuildFailed { reason };
    };
    let companion = |ext: &str| std::fs::read(path.with_extension(ext)).ok();
    let mut files = Vec::new();
    if olean != reference.olean {
        files.push(".olean".to_string());
    }
    if companion("olean.server").as_deref() != Some(reference.server.as_slice()) {
        files.push(".olean.server".to_string());
    }
    if companion("olean.private").as_deref() != Some(reference.private.as_slice()) {
        files.push(".olean.private".to_string());
    }
    if files.is_empty() {
        FreshBuildVerdict::DigestMatch {
            digest: digest(&olean),
        }
    } else {
        FreshBuildVerdict::DigestMismatch {
            files,
            artifact: digest(&olean),
            fresh_build: digest(&reference.olean),
        }
    }
}

#[cfg(test)]
#[path = "verify_fresh_tests.rs"]
mod tests;
