// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Incremental verification cache for batch .olean type-checking.
//!
//! Stores per-module verification results keyed by blake3 content hash of the
//! .olean file. When re-running verification, modules whose files have not
//! changed are skipped, reducing wall-clock time for incremental workflows.

use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;
use std::path::Path;
use std::time::{SystemTime, UNIX_EPOCH};
use tracing::{info, warn};

/// Current cache format version. Bump when the schema changes.
const CACHE_VERSION: u32 = 1;

/// Top-level verification cache persisted to disk as JSON.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct VerificationCache {
    /// Format version for forward compatibility.
    pub version: u32,
    /// Per-module cache entries keyed by dot-separated module name.
    pub entries: BTreeMap<String, CacheEntry>,
}

/// Cached result for a single module.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CacheEntry {
    /// blake3 hash of the .olean file bytes (hex-encoded).
    pub file_hash: String,
    /// Names of constants that were successfully type-checked.
    pub verified_constants: Vec<String>,
    /// Number of constants that failed type-checking (for diagnostics).
    pub failed_count: usize,
    /// Unix timestamp (seconds) of when this entry was last verified.
    pub last_verified_at: u64,
}

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
pub fn load_cache(path: &Path) -> VerificationCache {
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
pub fn save_cache(cache: &VerificationCache, path: &Path) -> std::io::Result<()> {
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
pub(crate) fn file_content_hash(bytes: &[u8]) -> String {
    blake3::hash(bytes).to_hex().to_string()
}

/// Check whether a module's cached entry is still valid (file hash matches).
pub fn is_module_cached(cache: &VerificationCache, module_name: &str, file_hash: &str) -> bool {
    cache
        .entries
        .get(module_name)
        .is_some_and(|entry| entry.file_hash == file_hash)
}

/// Returns the set of already-verified constant names for a cached module,
/// or `None` if the module is not cached or the hash has changed.
pub fn cached_constant_names<'a>(
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
pub fn update_cache_entry(
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
