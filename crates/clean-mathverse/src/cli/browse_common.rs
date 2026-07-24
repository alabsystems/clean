// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Shared helpers for the browse-oriented `clean mathverse <verb>` dispatch
//! module (`list`, `sample`, `deps`, `version`).
//!
//! Split out of `browse_dispatch.rs` so that module stays under the
//! 500-line file-size cap (see Issue #3512 risk note). These helpers are
//! intentionally near-duplicates of the ones in [`super::dispatch`]; the
//! two dispatch trees are kept independent so future changes to either
//! verb family do not ripple across both.

use std::path::Path;
use std::time::Instant;

use crate::cli::MathverseCliError;
use crate::library::MathverseLibrary;
use crate::shard::ShardReader;
use crate::trust::policy::TrustPolicy;
use crate::types::{ImportConfidence, SourceSystem};

/// Load every `*.mathverse` shard in `shard_dir` into a permissive
/// [`MathverseLibrary`].
///
/// Mirrors [`super::dispatch::load_library`]; duplicated here so the two
/// dispatch modules can evolve independently without cross-file coupling.
/// Shard read/load failures are emitted as warnings to stderr and skipped,
/// matching the standalone `mathverse` binary's behaviour.
pub(crate) fn load_library(shard_dir: &Path) -> Result<MathverseLibrary, MathverseCliError> {
    if !shard_dir.exists() {
        return Err(MathverseCliError::ShardDirMissing(shard_dir.to_path_buf()));
    }
    let t0 = Instant::now();
    let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
    let mut shard_count = 0u32;
    let mut load_errors = 0u32;

    let read_dir = std::fs::read_dir(shard_dir).map_err(|e| MathverseCliError::ShardDirIo {
        path: shard_dir.to_path_buf(),
        source: e,
    })?;
    let mut entries: Vec<_> = read_dir
        .filter_map(|e| e.ok())
        .filter(|e| e.path().extension().is_some_and(|ext| ext == "mathverse"))
        .collect();
    entries.sort_by_key(|e| e.file_name());

    for entry in &entries {
        let path = entry.path();
        match ShardReader::from_file(&path) {
            Ok(reader) => match lib.load_shard_deferred(&reader) {
                Ok(_) => shard_count += 1,
                Err(e) => {
                    tracing::warn!(shard = %path.display(), error = %e, "failed to load shard");
                    load_errors += 1;
                }
            },
            Err(e) => {
                tracing::warn!(shard = %path.display(), error = %e, "failed to read shard");
                load_errors += 1;
            }
        }
    }
    // One O(N) dependency-adjacency rebuild after the bulk load above, instead
    // of one per shard (which made the dir browse open O(N²)).
    lib.build_deps();

    let elapsed = t0.elapsed();
    tracing::info!(
        shards = shard_count,
        declarations = lib.constant_count(),
        elapsed_s = elapsed.as_secs_f64(),
        load_errors,
        "loaded mathverse shards"
    );
    Ok(lib)
}

/// Variant of [`load_library`] that returns `Ok(None)` when the shard
/// directory is missing. Used by `version` which must degrade gracefully.
pub(crate) fn load_library_opt(
    shard_dir: &Path,
) -> Result<Option<MathverseLibrary>, MathverseCliError> {
    if !shard_dir.exists() {
        return Ok(None);
    }
    load_library(shard_dir).map(Some)
}

/// Parse a source-system label or numeric id. Returns `None` for unknown
/// values so callers can treat that as "no match" (mirrors the standalone
/// binary's `parse_source_system`, without its `std::process::exit(1)`
/// side-effect).
pub(crate) fn parse_source_system(name: &str) -> Option<u8> {
    let lower = name.to_lowercase();
    if let Ok(n) = lower.parse::<u8>() {
        return Some(n);
    }
    let sys = match lower.as_str() {
        "lean4" | "lean" => SourceSystem::Lean4,
        "coq" => SourceSystem::Coq,
        "agda" => SourceSystem::Agda,
        "idris2" | "idris" => SourceSystem::Idris2,
        "fstar" | "f*" => SourceSystem::FStar,
        "cedille" => SourceSystem::Cedille,
        "isabelle" => SourceSystem::Isabelle,
        "hollight" | "hol-light" | "hol_light" => SourceSystem::HolLight,
        "hol4" => SourceSystem::Hol4,
        "metamath" | "mm" => SourceSystem::Metamath,
        "mizar" => SourceSystem::Mizar,
        "dafny" => SourceSystem::Dafny,
        "why3" => SourceSystem::Why3,
        "clean" | "cleannative" => SourceSystem::CleanNative,
        "gammacrown" | "gamma-crown" | "gamma_crown" => SourceSystem::GammaCrown,
        "arxiv" => SourceSystem::Arxiv,
        _ => return None,
    };
    Some(sys as u8)
}

/// Parse a trust / import-confidence label. Mirrors `parse_trust_level` in
/// the standalone binary.
pub(crate) fn parse_trust_level(name: &str) -> Option<u8> {
    let lower = name.to_lowercase();
    if let Ok(n) = lower.parse::<u8>() {
        return Some(n);
    }
    let level = match lower.as_str() {
        "kernelverified" | "kernel" | "verified" => ImportConfidence::KernelVerified,
        "sourceverified" | "source" => ImportConfidence::SourceVerified,
        "translated" => ImportConfidence::Translated,
        "axiomatized" | "axiom" => ImportConfidence::Axiomatized,
        "unverified" => ImportConfidence::Unverified,
        _ => return None,
    };
    Some(level as u8)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_source_system_accepts_numeric_id() {
        assert_eq!(parse_source_system("0"), Some(0));
        assert_eq!(parse_source_system("10"), Some(10));
    }

    #[test]
    fn test_parse_source_system_accepts_labels() {
        assert_eq!(
            parse_source_system("lean4"),
            Some(SourceSystem::Lean4 as u8)
        );
        assert_eq!(
            parse_source_system("METAMATH"),
            Some(SourceSystem::Metamath as u8)
        );
        assert_eq!(
            parse_source_system("hol-light"),
            Some(SourceSystem::HolLight as u8)
        );
    }

    #[test]
    fn test_parse_source_system_unknown_returns_none() {
        assert_eq!(parse_source_system("nonexistent"), None);
    }

    #[test]
    fn test_parse_trust_level_accepts_labels() {
        assert_eq!(
            parse_trust_level("kernelverified"),
            Some(ImportConfidence::KernelVerified as u8)
        );
        assert_eq!(
            parse_trust_level("axiomatized"),
            Some(ImportConfidence::Axiomatized as u8)
        );
    }

    #[test]
    fn test_parse_trust_level_unknown_returns_none() {
        assert_eq!(parse_trust_level("nonexistent-level"), None);
    }

    #[test]
    fn test_load_library_missing_dir_is_typed_error() {
        match load_library(Path::new("/nonexistent/shard/path/for/browse-common-test")) {
            Err(MathverseCliError::ShardDirMissing(_)) => {}
            Err(other) => panic!("expected ShardDirMissing, got {other:?}"),
            Ok(_) => panic!("expected failure on missing shard directory"),
        }
    }

    #[test]
    fn test_load_library_opt_missing_dir_returns_none() {
        let result = load_library_opt(Path::new("/nonexistent/opt/browse-common-test"));
        assert!(matches!(result, Ok(None)));
    }
}
