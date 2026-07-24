// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Persistent lemma library for cross-session theorem reuse with hot-reload.
//!
//! As the library of proven NN verification theorems grows, proof search needs
//! access to all prior results without re-importing each session. This module
//! provides:
//!
//! - JSON-backed persistence of lemma entries (name, type signature, proof term,
//!   dependencies, content hash)
//! - Type-based and keyword-based search over the library
//! - Hot-reload: automatic re-read from disk when the backing file changes
//! - Stale dependency invalidation via content hash comparison
//!
//! Part of #3188.

use std::collections::hash_map::DefaultHasher;
use std::collections::HashMap;
use std::hash::{Hash, Hasher};
use std::path::{Path, PathBuf};
use std::time::SystemTime;

use serde::{Deserialize, Serialize};

use crate::error::DiscoveryError;

/// A single lemma stored in the persistent library.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
#[non_exhaustive]
pub struct LemmaEntry {
    /// Human-readable lemma name (unique key for deduplication).
    pub name: String,
    /// Type signature as a string (e.g. `"Nat -> Nat -> Prop"`).
    pub type_signature: String,
    /// Proof term serialized as a string.
    pub proof_term: String,
    /// Names of other lemmas this entry depends on.
    pub dependencies: Vec<String>,
    /// Epoch seconds when this lemma was added or last updated.
    pub timestamp: u64,
    /// Content hash for version tracking and staleness detection.
    pub content_hash: u64,
}

/// Persistent lemma library backed by a JSON file on disk.
///
/// Keeps an in-memory copy of all entries and synchronizes with the
/// backing store on mutations and hot-reload checks.
pub struct LemmaLibrary {
    entries: Vec<LemmaEntry>,
    path: PathBuf,
    last_modified: Option<SystemTime>,
}

impl LemmaLibrary {
    /// Create a new empty library that will persist to `path`.
    pub fn new(path: impl AsRef<Path>) -> Self {
        Self {
            entries: Vec::new(),
            path: path.as_ref().to_path_buf(),
            last_modified: None,
        }
    }

    /// Load a library from a JSON file on disk.
    ///
    /// Sets `last_modified` from the file's metadata so subsequent
    /// `hot_reload` calls can detect changes.
    pub fn load(path: impl AsRef<Path>) -> Result<Self, DiscoveryError> {
        let path = path.as_ref();
        let data = std::fs::read_to_string(path)?;
        let entries: Vec<LemmaEntry> = serde_json::from_str(&data)
            .map_err(|e| DiscoveryError::Serialization(e.to_string()))?;
        let last_modified = std::fs::metadata(path)?.modified().ok();
        Ok(Self {
            entries,
            path: path.to_path_buf(),
            last_modified,
        })
    }

    /// Write the library to disk as pretty-printed JSON.
    pub fn save(&self) -> Result<(), DiscoveryError> {
        let json = serde_json::to_string_pretty(&self.entries)
            .map_err(|e| DiscoveryError::Serialization(e.to_string()))?;
        std::fs::write(&self.path, json)?;
        Ok(())
    }

    /// Add a lemma, deduplicating by name (last write wins), and auto-save.
    pub fn add_lemma(&mut self, entry: LemmaEntry) -> Result<(), DiscoveryError> {
        if let Some(pos) = self.entries.iter().position(|e| e.name == entry.name) {
            self.entries[pos] = entry;
        } else {
            self.entries.push(entry);
        }
        self.save()?;
        // Update our mtime cache after saving.
        self.last_modified = std::fs::metadata(&self.path)
            .ok()
            .and_then(|m| m.modified().ok());
        Ok(())
    }

    /// Search for lemmas whose type signature contains `pattern` (case-insensitive).
    pub fn search_by_type(&self, pattern: &str) -> Vec<&LemmaEntry> {
        let lower = pattern.to_lowercase();
        self.entries
            .iter()
            .filter(|e| e.type_signature.to_lowercase().contains(&lower))
            .collect()
    }

    /// Search for lemmas where name or type signature contains ANY keyword
    /// (case-insensitive).
    pub fn search_by_keyword(&self, keywords: &[&str]) -> Vec<&LemmaEntry> {
        let lower_kw: Vec<String> = keywords.iter().map(|k| k.to_lowercase()).collect();
        self.entries
            .iter()
            .filter(|e| {
                let name_lower = e.name.to_lowercase();
                let sig_lower = e.type_signature.to_lowercase();
                lower_kw
                    .iter()
                    .any(|kw| name_lower.contains(kw) || sig_lower.contains(kw))
            })
            .collect()
    }

    /// Re-read the library from disk if the file has been modified since
    /// the last load/save.
    ///
    /// Returns `true` if the library was reloaded, `false` if the file
    /// has not changed (or does not exist yet).
    pub fn hot_reload(&mut self) -> Result<bool, DiscoveryError> {
        let current_mtime = match std::fs::metadata(&self.path) {
            Ok(meta) => meta.modified().ok(),
            Err(_) => return Ok(false),
        };

        if current_mtime != self.last_modified {
            let data = std::fs::read_to_string(&self.path)?;
            self.entries = serde_json::from_str(&data)
                .map_err(|e| DiscoveryError::Serialization(e.to_string()))?;
            self.last_modified = current_mtime;
            Ok(true)
        } else {
            Ok(false)
        }
    }

    /// Remove entries whose dependencies have changed content hashes.
    ///
    /// `current_hashes` maps dependency names to their current content hashes.
    /// Any entry that depends on a name present in `current_hashes` whose hash
    /// differs from the entry's recorded `content_hash` for that dependency is
    /// removed.
    ///
    /// Returns the number of entries removed.
    pub fn invalidate_stale(&mut self, current_hashes: &HashMap<String, u64>) -> usize {
        let before = self.entries.len();
        self.entries.retain(|entry| {
            !entry.dependencies.iter().any(|dep| {
                current_hashes
                    .get(dep)
                    .is_some_and(|&current| current != entry.content_hash)
            })
        });
        before - self.entries.len()
    }

    /// Number of lemmas in the library.
    #[must_use]
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    /// Whether the library is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// Immutable access to all entries.
    pub fn entries(&self) -> &[LemmaEntry] {
        &self.entries
    }
}

/// Compute a deterministic 64-bit content hash for a string.
///
/// Uses `DefaultHasher` for simplicity; not cryptographically secure,
/// but sufficient for version tracking.
pub fn compute_content_hash(content: &str) -> u64 {
    let mut hasher = DefaultHasher::new();
    content.hash(&mut hasher);
    hasher.finish()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sample_entry(name: &str) -> LemmaEntry {
        LemmaEntry {
            name: name.to_string(),
            type_signature: "Nat -> Nat -> Prop".to_string(),
            proof_term: "fun a b => le_refl a".to_string(),
            dependencies: vec![],
            timestamp: 1700000000,
            content_hash: compute_content_hash("fun a b => le_refl a"),
        }
    }

    fn temp_path(suffix: &str) -> PathBuf {
        std::env::temp_dir().join(format!("clean_lemma_lib_test_{suffix}.json"))
    }

    #[test]
    fn test_lemma_library_new_empty() {
        let lib = LemmaLibrary::new("/tmp/unused.json");
        assert!(lib.is_empty());
        assert_eq!(lib.len(), 0);
        assert!(lib.entries().is_empty());
    }

    #[test]
    fn test_lemma_library_add_and_len() {
        let path = temp_path("add_len");
        let mut lib = LemmaLibrary::new(&path);
        lib.add_lemma(sample_entry("lemma_a")).unwrap();
        assert_eq!(lib.len(), 1);
        lib.add_lemma(sample_entry("lemma_b")).unwrap();
        assert_eq!(lib.len(), 2);
        let _ = std::fs::remove_file(&path);
    }

    #[test]
    fn test_lemma_library_dedup_by_name() {
        let path = temp_path("dedup");
        let mut lib = LemmaLibrary::new(&path);

        let mut e1 = sample_entry("dup");
        e1.timestamp = 100;
        lib.add_lemma(e1).unwrap();

        let mut e2 = sample_entry("dup");
        e2.timestamp = 999;
        lib.add_lemma(e2).unwrap();

        assert_eq!(lib.len(), 1);
        assert_eq!(lib.entries()[0].timestamp, 999);
        let _ = std::fs::remove_file(&path);
    }

    #[test]
    fn test_lemma_library_save_load_roundtrip() {
        let path = temp_path("roundtrip");
        let mut lib = LemmaLibrary::new(&path);
        lib.add_lemma(sample_entry("roundtrip_thm")).unwrap();

        let loaded = LemmaLibrary::load(&path).unwrap();
        assert_eq!(loaded.len(), 1);
        assert_eq!(loaded.entries()[0].name, "roundtrip_thm");
        assert_eq!(loaded.entries()[0], lib.entries()[0]);

        let _ = std::fs::remove_file(&path);
    }

    #[test]
    fn test_lemma_library_search_by_type() {
        let path = temp_path("search_type");
        let mut lib = LemmaLibrary::new(&path);
        lib.add_lemma(sample_entry("nat_lemma")).unwrap();

        let mut bool_entry = sample_entry("bool_lemma");
        bool_entry.type_signature = "Bool -> Bool".to_string();
        lib.add_lemma(bool_entry).unwrap();

        let results = lib.search_by_type("Nat");
        assert_eq!(results.len(), 1);
        assert_eq!(results[0].name, "nat_lemma");

        assert!(lib.search_by_type("NonExistent").is_empty());
        let _ = std::fs::remove_file(&path);
    }

    #[test]
    fn test_lemma_library_search_by_type_case_insensitive() {
        let path = temp_path("search_case");
        let mut lib = LemmaLibrary::new(&path);
        lib.add_lemma(sample_entry("nat_lemma")).unwrap();

        let results = lib.search_by_type("nat");
        assert_eq!(results.len(), 1);

        let results = lib.search_by_type("NAT");
        assert_eq!(results.len(), 1);
        let _ = std::fs::remove_file(&path);
    }

    #[test]
    fn test_lemma_library_search_by_keyword() {
        let path = temp_path("search_kw");
        let mut lib = LemmaLibrary::new(&path);
        lib.add_lemma(sample_entry("cert_bound")).unwrap();

        let mut other = sample_entry("tightness");
        other.type_signature = "Real -> Real -> Prop".to_string();
        lib.add_lemma(other).unwrap();

        // Keyword in name
        let results = lib.search_by_keyword(&["cert"]);
        assert_eq!(results.len(), 1);
        assert_eq!(results[0].name, "cert_bound");

        // Keyword in type_signature
        let results = lib.search_by_keyword(&["Real"]);
        assert_eq!(results.len(), 1);
        assert_eq!(results[0].name, "tightness");

        // Multiple keywords (OR semantics)
        let results = lib.search_by_keyword(&["cert", "Real"]);
        assert_eq!(results.len(), 2);

        // No match
        assert!(lib.search_by_keyword(&["xyz"]).is_empty());
        let _ = std::fs::remove_file(&path);
    }

    #[test]
    fn test_lemma_library_hot_reload() {
        let path = temp_path("hot_reload");

        // Create and save initial library.
        let mut lib = LemmaLibrary::new(&path);
        lib.add_lemma(sample_entry("initial")).unwrap();
        assert_eq!(lib.len(), 1);

        // Externally modify the file by adding another entry.
        let mut entries: Vec<LemmaEntry> = {
            let data = std::fs::read_to_string(&path).unwrap();
            serde_json::from_str(&data).unwrap()
        };
        entries.push(sample_entry("external"));
        let json = serde_json::to_string_pretty(&entries).unwrap();
        // Small sleep to ensure mtime differs (filesystem granularity).
        std::thread::sleep(std::time::Duration::from_millis(50));
        std::fs::write(&path, json).unwrap();

        // hot_reload should detect the change.
        let reloaded = lib.hot_reload().unwrap();
        assert!(reloaded);
        assert_eq!(lib.len(), 2);

        let _ = std::fs::remove_file(&path);
    }

    #[test]
    fn test_lemma_library_hot_reload_no_change() {
        let path = temp_path("hot_reload_no");
        let mut lib = LemmaLibrary::new(&path);
        lib.add_lemma(sample_entry("stable")).unwrap();

        let reloaded = lib.hot_reload().unwrap();
        assert!(!reloaded);
        assert_eq!(lib.len(), 1);

        let _ = std::fs::remove_file(&path);
    }

    #[test]
    fn test_lemma_library_invalidate_stale() {
        let path = temp_path("invalidate");
        let mut lib = LemmaLibrary::new(&path);

        let mut e1 = sample_entry("depends_on_foo");
        e1.dependencies = vec!["foo".to_string()];
        e1.content_hash = 100;
        lib.add_lemma(e1).unwrap();

        let mut e2 = sample_entry("no_deps");
        e2.dependencies = vec![];
        lib.add_lemma(e2).unwrap();

        // "foo" hash changed from 100 to 200 -- e1 is stale.
        let mut current = HashMap::new();
        current.insert("foo".to_string(), 200);

        let removed = lib.invalidate_stale(&current);
        assert_eq!(removed, 1);
        assert_eq!(lib.len(), 1);
        assert_eq!(lib.entries()[0].name, "no_deps");

        let _ = std::fs::remove_file(&path);
    }

    #[test]
    fn test_compute_content_hash_deterministic() {
        let h1 = compute_content_hash("hello world");
        let h2 = compute_content_hash("hello world");
        assert_eq!(h1, h2);
    }

    #[test]
    fn test_compute_content_hash_different_inputs() {
        let h1 = compute_content_hash("aaa");
        let h2 = compute_content_hash("bbb");
        assert_ne!(h1, h2);
    }
}
