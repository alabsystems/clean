// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Incremental verification cache for batch .olean type-checking.
//!
//! Stores per-module verification results keyed by a blake3 content hash of
//! every part of the module's artifact (`.olean`, `.olean.server`,
//! `.olean.private`). When re-running verification, modules whose parts have
//! not changed are skipped, reducing wall-clock time for incremental workflows.
//!
//! The cache store is crate-internal and read only by the `cli` feature's
//! batch runner (and this module's tests), so it is compiled only there;
//! `artifact_content_hash` is also used by `verify_batch`'s Init snapshot and
//! is always built. Both key on every part of an artifact (R113).

#[cfg(any(test, feature = "cli"))]
use serde::{Deserialize, Serialize};
#[cfg(any(test, feature = "cli"))]
use std::collections::BTreeMap;
use std::path::Path;
#[cfg(any(test, feature = "cli"))]
use std::time::{SystemTime, UNIX_EPOCH};
#[cfg(any(test, feature = "cli"))]
use tracing::{info, warn};

/// Current cache format version. Bump when the schema changes, and when what a
/// cached "verified" means changes: `2` (2026-09-24) retires every verdict
/// minted before full re-checks replayed targets in Lean's order and in Lean's
/// kernel theory (`verify_batch_replay.rs`), because a module whose `.olean`
/// bytes did not change would otherwise replay a verdict that certified
/// `forged3_self : False := forged3_self`. `3` (R113) keys an entry on every
/// part of the artifact ([`artifact_content_hash`]), not its `.olean` alone.
#[cfg(any(test, feature = "cli"))]
const CACHE_VERSION: u32 = 3;

/// Top-level verification cache persisted to disk as JSON.
#[cfg(any(test, feature = "cli"))]
#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct VerificationCache {
    /// Format version for forward compatibility.
    pub version: u32,
    /// Per-module cache entries keyed by dot-separated module name.
    pub entries: BTreeMap<String, CacheEntry>,
}

/// Cached result for a single module.
#[cfg(any(test, feature = "cli"))]
#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct CacheEntry {
    /// [`artifact_content_hash`] of the module's parts (hex-encoded).
    pub file_hash: String,
    /// Names of constants that were successfully type-checked.
    pub verified_constants: Vec<String>,
    /// Number of constants that failed type-checking (for diagnostics).
    pub failed_count: usize,
    /// Unix timestamp (seconds) of when this entry was last verified.
    pub last_verified_at: u64,
}

#[cfg(any(test, feature = "cli"))]
impl Default for VerificationCache {
    fn default() -> Self {
        Self {
            version: CACHE_VERSION,
            entries: BTreeMap::new(),
        }
    }
}

/// Load a verification cache from a JSON file, or return an empty cache if
/// the file does not exist or cannot be parsed.
#[cfg(any(test, feature = "cli"))]
pub(crate) fn load_cache(path: &Path) -> VerificationCache {
    match std::fs::read_to_string(path) {
        Ok(contents) => match serde_json::from_str::<VerificationCache>(&contents) {
            Ok(cache) if cache.version == CACHE_VERSION => {
                info!(
                    entries = cache.entries.len(),
                    path = %path.display(),
                    "loaded verification cache"
                );
                cache
            }
            Ok(cache) => {
                warn!(
                    found_version = cache.version,
                    expected_version = CACHE_VERSION,
                    "cache version mismatch, starting fresh"
                );
                VerificationCache::default()
            }
            Err(e) => {
                warn!(err = %e, "failed to parse verification cache, starting fresh");
                VerificationCache::default()
            }
        },
        Err(_) => {
            info!(path = %path.display(), "no existing cache file, starting fresh");
            VerificationCache::default()
        }
    }
}

/// Save the verification cache to a JSON file.
#[cfg(any(test, feature = "cli"))]
pub(crate) fn save_cache(cache: &VerificationCache, path: &Path) -> std::io::Result<()> {
    let json = serde_json::to_string_pretty(cache)
        .map_err(|e| std::io::Error::other(format!("json serialize: {e}")))?;
    if let Some(parent) = path.parent() {
        std::fs::create_dir_all(parent)?;
    }
    std::fs::write(path, json)?;
    info!(
        entries = cache.entries.len(),
        path = %path.display(),
        "saved verification cache"
    );
    Ok(())
}

/// Compute a blake3 content hash of raw bytes, returning a hex string.
#[cfg(test)]
pub(crate) fn file_content_hash(bytes: &[u8]) -> String {
    blake3::hash(bytes).to_hex().to_string()
}

/// A blake3 content hash of every part the loader reads of the artifact whose
/// `.olean` is `path` — the `.olean`, `.olean.server` and `.olean.private`, each
/// length-prefixed, an absent companion a zero-length region (trailers are part
/// of the bytes). `None` when a part exists but cannot be read, which a caller
/// treats as a cache miss.
///
/// R113 (the class of review finding B2): a cache keyed on the `.olean` alone
/// replayed a verdict over a module whose `.olean.private` — where a
/// module-system artifact keeps its proofs and private declarations, and the
/// part `lean` reads — had changed with the `.olean` byte-identical (Lean's own
/// proof-only edits do exactly that).
pub(crate) fn artifact_content_hash(path: &Path) -> Option<String> {
    let mut hasher = blake3::Hasher::new();
    for (part, required) in [
        (path.to_path_buf(), true),
        (path.with_extension("olean.server"), false),
        (path.with_extension("olean.private"), false),
    ] {
        let bytes = match std::fs::read(&part) {
            Ok(bytes) => bytes,
            Err(e) if !required && e.kind() == std::io::ErrorKind::NotFound => Vec::new(),
            Err(_) => return None,
        };
        hasher.update(&(bytes.len() as u64).to_le_bytes());
        hasher.update(&bytes);
    }
    Some(hasher.finalize().to_hex().to_string())
}

/// Check whether a module's cached entry is still valid (file hash matches).
#[cfg(any(test, feature = "cli"))]
pub(crate) fn is_module_cached(
    cache: &VerificationCache,
    module_name: &str,
    file_hash: &str,
) -> bool {
    cache
        .entries
        .get(module_name)
        .is_some_and(|entry| entry.file_hash == file_hash)
}

/// Returns the set of already-verified constant names for a cached module,
/// or `None` if the module is not cached or the hash has changed.
#[cfg(feature = "cli")]
pub(crate) fn cached_constant_names<'a>(
    cache: &'a VerificationCache,
    module_name: &str,
    file_hash: &str,
) -> Option<&'a [String]> {
    cache
        .entries
        .get(module_name)
        .filter(|entry| entry.file_hash == file_hash)
        .map(|entry| entry.verified_constants.as_slice())
}

/// Insert or update a cache entry for a module.
#[cfg(any(test, feature = "cli"))]
pub(crate) fn update_cache_entry(
    cache: &mut VerificationCache,
    module_name: &str,
    file_hash: &str,
    verified_constants: Vec<String>,
    failed_count: usize,
) {
    let timestamp = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap_or_default()
        .as_secs();
    cache.entries.insert(
        module_name.to_string(),
        CacheEntry {
            file_hash: file_hash.to_string(),
            verified_constants,
            failed_count,
            last_verified_at: timestamp,
        },
    );
}

#[cfg(test)]
mod tests {
    use super::*;

    /// R113 (B2's class): the key covers every part the loader reads; an
    /// unreadable part is no key at all.
    #[test]
    fn test_artifact_content_hash_covers_every_part() {
        let dir = tempfile::tempdir().expect("tempdir");
        let olean = dir.path().join("M.olean");
        std::fs::write(&olean, b"base").expect("write base");
        let mut seen = vec![artifact_content_hash(&olean).expect("hash")];
        for (ext, bytes) in [
            ("olean.private", &b"private one"[..]),
            ("olean.private", &b"private two"[..]),
            ("olean.server", &b"server"[..]),
        ] {
            std::fs::write(olean.with_extension(ext), bytes).expect("write part");
            let h = artifact_content_hash(&olean).expect("hash");
            assert!(!seen.contains(&h), "{ext} must re-key: {h}");
            seen.push(h);
        }
        std::fs::remove_file(olean.with_extension("olean.server")).expect("remove server");
        std::fs::create_dir(olean.with_extension("olean.server")).expect("unreadable part");
        assert_eq!(artifact_content_hash(&olean), None);
    }

    #[test]
    fn test_cache_roundtrip() {
        let dir = tempfile::tempdir().expect("should create tempdir");
        let path = dir.path().join("test_cache.json");

        let mut cache = VerificationCache::default();
        update_cache_entry(
            &mut cache,
            "Init.Prelude",
            "abc123",
            vec!["Nat".to_string(), "Bool".to_string()],
            1,
        );

        save_cache(&cache, &path).expect("should save cache");
        let loaded = load_cache(&path);

        assert_eq!(loaded.version, CACHE_VERSION);
        assert_eq!(loaded.entries.len(), 1);
        let entry = loaded
            .entries
            .get("Init.Prelude")
            .expect("should have entry");
        assert_eq!(entry.file_hash, "abc123");
        assert_eq!(entry.verified_constants.len(), 2);
        assert_eq!(entry.failed_count, 1);
    }

    #[test]
    fn test_is_module_cached_hit() {
        let mut cache = VerificationCache::default();
        update_cache_entry(&mut cache, "Init.Core", "hash1", vec![], 0);
        assert!(is_module_cached(&cache, "Init.Core", "hash1"));
    }

    #[test]
    fn test_is_module_cached_miss_wrong_hash() {
        let mut cache = VerificationCache::default();
        update_cache_entry(&mut cache, "Init.Core", "hash1", vec![], 0);
        assert!(!is_module_cached(&cache, "Init.Core", "hash2"));
    }

    #[test]
    fn test_is_module_cached_miss_not_present() {
        let cache = VerificationCache::default();
        assert!(!is_module_cached(&cache, "Init.Core", "hash1"));
    }

    #[test]
    fn test_file_content_hash_deterministic() {
        let data = b"hello world";
        let h1 = file_content_hash(data);
        let h2 = file_content_hash(data);
        assert_eq!(h1, h2);
        assert_eq!(h1.len(), 64); // blake3 produces 32 bytes = 64 hex chars
    }

    #[test]
    fn test_load_missing_file() {
        let cache = load_cache(Path::new("/nonexistent/path/cache.json"));
        assert_eq!(cache.version, CACHE_VERSION);
        assert!(cache.entries.is_empty());
    }
}
