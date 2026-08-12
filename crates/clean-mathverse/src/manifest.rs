// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Manifest management for the Mathverse Library shard inventory.
//!
//! The manifest tracks all shards (base + delta), their content hashes,
//! constant counts, and toolchain digests. [`LibraryLoader`] handles
//! the full shard lifecycle: init, load, write, compact, and verify.

use std::path::{Path, PathBuf};

use serde::{Deserialize, Serialize};

use crate::error::{MathverseError, MathverseResult};
use crate::shard::{compact_deltas, ShardHeader, ShardReader, ShardWriter, HEADER_SIZE};
use crate::trust::policy::TrustPolicy;

/// Read only a shard file's 256-byte header (counts, version) without decoding
/// the body. Used to adapt a release manifest into the in-place shape.
fn read_shard_header(path: &Path) -> MathverseResult<ShardHeader> {
    use std::io::Read;
    let mut file =
        std::fs::File::open(path).map_err(|source| MathverseError::ShardFileUnreadable {
            path: path.display().to_string(),
            source,
        })?;
    let mut buf = [0u8; HEADER_SIZE];
    file.read_exact(&mut buf)
        .map_err(|source| MathverseError::ShardFileUnreadable {
            path: path.display().to_string(),
            source,
        })?;
    ShardHeader::from_bytes(&buf)
}

/// Derive a human-readable `source` label from a shard's relative path, e.g.
/// `"base/lean4_stdlib.mathverse"` → `"lean4_stdlib"`. Informational only.
fn derive_source_label(rel_path: &str) -> String {
    Path::new(rel_path)
        .file_stem()
        .map(|s| s.to_string_lossy().into_owned())
        .unwrap_or_else(|| rel_path.to_string())
}

/// Manifest for the Mathverse Library on-disk layout.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct MathverseManifest {
    pub version: u32,
    pub base_shards: Vec<ShardEntry>,
    pub delta_shards: Vec<ShardEntry>,
    pub total_constants: u64,
    pub total_exprs: u64,
}

/// Entry for a single shard in the manifest.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ShardEntry {
    pub path: String,
    pub content_hash: String,
    pub constant_count: u32,
    pub expr_count: u32,
    pub source: String,
}

/// Aggregate statistics across all shards in a manifest.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct ManifestStats {
    pub total_constants: u64,
    pub total_exprs: u64,
    pub total_shards: usize,
    pub base_shards: usize,
    pub delta_shards: usize,
    pub total_bytes: u64,
}

/// Result of compacting delta shards into the base.
#[derive(Clone, Debug)]
pub struct CompactionResult {
    pub deltas_merged: usize,
    pub constants_before: u64,
    pub constants_after: u64,
    pub bytes_before: u64,
    pub bytes_after: u64,
}

/// Report from shard integrity verification.
#[derive(Clone, Debug)]
pub struct IntegrityReport {
    pub shards_checked: usize,
    pub shards_valid: usize,
    pub shards_corrupt: Vec<String>,
    /// Shards referenced in manifest but missing from disk.
    pub shards_missing: Vec<String>,
    /// Files on disk not referenced by any manifest entry.
    pub shards_orphaned: Vec<PathBuf>,
}

impl MathverseManifest {
    pub fn new() -> Self {
        Self {
            version: 1,
            base_shards: Vec::new(),
            delta_shards: Vec::new(),
            total_constants: 0,
            total_exprs: 0,
        }
    }

    pub fn add_base_shard(&mut self, entry: ShardEntry) {
        self.total_constants += entry.constant_count as u64;
        self.total_exprs += entry.expr_count as u64;
        self.base_shards.push(entry);
    }

    pub fn add_delta_shard(&mut self, entry: ShardEntry) {
        self.total_constants += entry.constant_count as u64;
        self.total_exprs += entry.expr_count as u64;
        self.delta_shards.push(entry);
    }

    /// Read manifest from a JSON file.
    pub fn from_file(path: impl AsRef<Path>) -> MathverseResult<Self> {
        let data = std::fs::read_to_string(path)?;
        Ok(serde_json::from_str(&data)?)
    }

    /// Adapt a release-shipped [`ReleaseManifest`](crate::release::ReleaseManifest)
    /// (`mathverse-manifest.json`) into the in-place [`MathverseManifest`] shape.
    ///
    /// The release manifest enumerates the same shards but records only
    /// `{path, size, blake3}` per entry; this fills in `constant_count` /
    /// `expr_count` / `source` by reading each shard's 256-byte header (cheap,
    /// no full decode). `root` is the directory the shard paths are relative to.
    /// No shard data is fabricated — both manifests list the identical files.
    pub fn from_release_manifest(
        release: &crate::release::ReleaseManifest,
        root: &Path,
    ) -> MathverseResult<Self> {
        let mut manifest = Self::new();
        for shard in &release.shards {
            let abs = root.join(&shard.path);
            let header = read_shard_header(&abs)?;
            let source = derive_source_label(&shard.path);
            manifest.add_base_shard(ShardEntry {
                path: shard.path.clone(),
                content_hash: shard.blake3.clone(),
                constant_count: header.constant_count,
                expr_count: header.expr_count,
                source,
            });
        }
        Ok(manifest)
    }

    /// Write manifest to a JSON file (non-atomic).
    pub fn write_to_file(&self, path: impl AsRef<Path>) -> MathverseResult<()> {
        let data = serde_json::to_string_pretty(self)?;
        std::fs::write(path, data)?;
        Ok(())
    }

    /// Load manifest from JSON file. Alias for [`from_file`](Self::from_file).
    pub fn load(path: &Path) -> MathverseResult<Self> {
        Self::from_file(path)
    }

    /// Save manifest to JSON file with atomic write (write tmp then rename).
    pub fn save(&self, path: &Path) -> MathverseResult<()> {
        let data = serde_json::to_string_pretty(self)?;
        let tmp = path.with_extension("json.tmp");
        std::fs::write(&tmp, &data)?;
        std::fs::rename(&tmp, path)?;
        Ok(())
    }

    /// Register a new shard (base or delta) in the manifest.
    pub fn register_shard(&mut self, entry: ShardEntry, is_delta: bool) {
        if is_delta {
            self.add_delta_shard(entry)
        } else {
            self.add_base_shard(entry)
        }
    }

    /// Remove a shard entry by path. Returns `true` if found and removed.
    pub fn remove_shard(&mut self, path: &str) -> bool {
        let before = self.base_shards.len() + self.delta_shards.len();
        self.base_shards.retain(|e| e.path != path);
        self.delta_shards.retain(|e| e.path != path);
        let removed = (self.base_shards.len() + self.delta_shards.len()) < before;
        if removed {
            self.recompute_totals();
        }
        removed
    }

    /// Get all shard entries (base first, then delta) in load order.
    pub fn all_shards(&self) -> Vec<&ShardEntry> {
        self.base_shards
            .iter()
            .chain(self.delta_shards.iter())
            .collect()
    }

    /// Check if compaction is needed (too many delta shards).
    pub fn needs_compaction(&self, max_deltas: usize) -> bool {
        self.delta_shards.len() > max_deltas
    }

    /// Compute total statistics across all shards.
    pub fn total_stats(&self) -> ManifestStats {
        let mut stats = ManifestStats {
            total_shards: self.base_shards.len() + self.delta_shards.len(),
            base_shards: self.base_shards.len(),
            delta_shards: self.delta_shards.len(),
            ..Default::default()
        };
        for e in self.base_shards.iter().chain(self.delta_shards.iter()) {
            stats.total_constants += e.constant_count as u64;
            stats.total_exprs += e.expr_count as u64;
        }
        stats
    }

    /// Get the expected library root directory structure.
    pub fn library_paths(root: &Path) -> LibraryPaths {
        LibraryPaths::new(root.to_path_buf())
    }

    fn recompute_totals(&mut self) {
        self.total_constants = 0;
        self.total_exprs = 0;
        for e in self.base_shards.iter().chain(self.delta_shards.iter()) {
            self.total_constants += e.constant_count as u64;
            self.total_exprs += e.expr_count as u64;
        }
    }
}

impl Default for MathverseManifest {
    fn default() -> Self {
        Self::new()
    }
}

/// Filename of the release-shipped manifest (the [`crate::release::ReleaseManifest`]
/// shape), as packaged inside `mathverse-library-v*.tar.zst`. Distinct from the
/// in-place library's `manifest.json` ([`MathverseManifest`] shape).
pub const RELEASE_MANIFEST_FILENAME: &str = "mathverse-manifest.json";

/// Standard directory paths within an Mathverse Library.
#[derive(Clone, Debug)]
pub struct LibraryPaths {
    pub root: PathBuf,
    pub base: PathBuf,
    pub delta: PathBuf,
    pub index: PathBuf,
    pub manifest: PathBuf,
    /// Path to the release-shipped manifest (`mathverse-manifest.json`), used as
    /// a fallback when the in-place `manifest.json` is absent.
    pub release_manifest: PathBuf,
}

impl LibraryPaths {
    pub fn new(root: PathBuf) -> Self {
        let base = root.join("base");
        let delta = root.join("delta");
        let index = root.join("index");
        let manifest = root.join("manifest.json");
        let release_manifest = root.join(RELEASE_MANIFEST_FILENAME);
        Self {
            root,
            base,
            delta,
            index,
            manifest,
            release_manifest,
        }
    }

    pub fn manifest_path(&self) -> PathBuf {
        self.manifest.clone()
    }

    /// Path to the release-shipped manifest (`mathverse-manifest.json`).
    pub fn release_manifest_path(&self) -> PathBuf {
        self.release_manifest.clone()
    }
    pub fn base_shard_path(&self, name: &str) -> PathBuf {
        self.base.join(format!("{name}.mathverse"))
    }
    pub fn delta_shard_path(&self, name: &str) -> PathBuf {
        self.delta.join(format!("{name}.mathverse"))
    }
    pub fn index_path(&self) -> PathBuf {
        self.index.clone()
    }

    pub fn ensure_dirs(&self) -> MathverseResult<()> {
        self.create_dirs()
    }

    pub fn create_dirs(&self) -> MathverseResult<()> {
        std::fs::create_dir_all(&self.base)?;
        std::fs::create_dir_all(&self.delta)?;
        std::fs::create_dir_all(&self.index)?;
        Ok(())
    }
}

// ---------------------------------------------------------------------------
// LibraryLoader
// ---------------------------------------------------------------------------

/// Loads an Mathverse Library from disk using the manifest.
pub struct LibraryLoader {
    paths: LibraryPaths,
}

impl LibraryLoader {
    pub fn new(root: PathBuf) -> Self {
        Self {
            paths: LibraryPaths::new(root),
        }
    }

    /// Initialize a new library directory structure with an empty manifest.
    pub fn init(&self) -> MathverseResult<()> {
        self.paths.ensure_dirs()?;
        MathverseManifest::new().save(&self.paths.manifest)
    }

    /// Load the library manifest.
    ///
    /// Prefers the in-place `manifest.json` ([`MathverseManifest`] shape). If it
    /// is absent, falls back to the release-shipped `mathverse-manifest.json`
    /// ([`crate::release::ReleaseManifest`] shape) and adapts it — so an
    /// extracted release archive loads directly, without a separate
    /// manifest-conversion step. Both manifests enumerate the same shards.
    pub fn load_manifest(&self) -> MathverseResult<MathverseManifest> {
        if self.paths.manifest.exists() {
            return MathverseManifest::load(&self.paths.manifest);
        }
        if self.paths.release_manifest.exists() {
            let release = crate::release::ReleaseManifest::from_file(&self.paths.release_manifest)?;
            return MathverseManifest::from_release_manifest(&release, &self.paths.root);
        }
        // Neither exists: surface the legacy path's error for the canonical name.
        MathverseManifest::load(&self.paths.manifest)
    }

    /// Load all shards into an [`MathverseLibrary`](crate::library::MathverseLibrary).
    pub fn load_library(
        &self,
        trust_policy: TrustPolicy,
    ) -> MathverseResult<crate::library::MathverseLibrary> {
        let manifest = self.load_manifest()?;
        let mut library = crate::library::MathverseLibrary::new(trust_policy);
        for entry in manifest.all_shards() {
            library.load_shard_deferred(&self.load_shard(entry)?)?;
        }
        // One O(N) dependency-adjacency rebuild after all shards are merged,
        // instead of an O(N) rebuild per shard (which made library open O(N²)).
        library.build_deps();
        Ok(library)
    }

    pub fn load_shard(&self, entry: &ShardEntry) -> MathverseResult<ShardReader> {
        ShardReader::from_file(self.paths.root.join(&entry.path))
    }

    /// Write a new shard and register it in the manifest.
    pub fn write_shard(
        &self,
        writer: &ShardWriter,
        name: &str,
        is_delta: bool,
    ) -> MathverseResult<ShardEntry> {
        let (rel_path, abs_path) = if is_delta {
            (
                format!("delta/{name}.mathverse"),
                self.paths.delta_shard_path(name),
            )
        } else {
            (
                format!("base/{name}.mathverse"),
                self.paths.base_shard_path(name),
            )
        };
        writer.write_to_file(&abs_path)?;

        let data = std::fs::read(&abs_path)?;
        let content_hash = blake3::hash(&data).to_hex().to_string();
        let reader = ShardReader::from_file(&abs_path)?;
        let entry = ShardEntry {
            path: rel_path,
            content_hash,
            constant_count: reader.header.constant_count,
            expr_count: reader.header.expr_count,
            source: if is_delta {
                "delta".to_string()
            } else {
                name.to_string()
            },
        };

        let mut manifest = self.load_manifest()?;
        manifest.register_shard(entry.clone(), is_delta);
        manifest.save(&self.paths.manifest)?;
        Ok(entry)
    }

    /// Compact all delta shards into the base shard.
    pub fn compact(&self) -> MathverseResult<CompactionResult> {
        let manifest = self.load_manifest()?;
        if manifest.delta_shards.is_empty() {
            return Ok(CompactionResult {
                deltas_merged: 0,
                constants_before: manifest.total_constants,
                constants_after: manifest.total_constants,
                bytes_before: 0,
                bytes_after: 0,
            });
        }

        let mut readers = Vec::new();
        let mut bytes_before: u64 = 0;
        for entry in manifest.all_shards() {
            let p = self.paths.root.join(&entry.path);
            bytes_before += std::fs::metadata(&p).map(|m| m.len()).unwrap_or(0);
            readers.push(ShardReader::from_file(&p)?);
        }
        let constants_before = manifest.total_constants;
        let deltas_merged = manifest.delta_shards.len();

        let compacted_path = self.paths.base_shard_path("compacted");
        compact_deltas(&readers, &compacted_path)?;

        let data = std::fs::read(&compacted_path)?;
        let bytes_after = data.len() as u64;
        let cr = ShardReader::from_file(&compacted_path)?;

        let mut new_manifest = MathverseManifest::new();
        new_manifest.add_base_shard(ShardEntry {
            path: "base/compacted.mathverse".to_string(),
            content_hash: blake3::hash(&data).to_hex().to_string(),
            constant_count: cr.header.constant_count,
            expr_count: cr.header.expr_count,
            source: "compacted".to_string(),
        });

        for entry in manifest.all_shards() {
            let old = self.paths.root.join(&entry.path);
            if old != compacted_path {
                let _ = std::fs::remove_file(&old);
            }
        }
        new_manifest.save(&self.paths.manifest)?;

        Ok(CompactionResult {
            deltas_merged,
            constants_before,
            constants_after: cr.header.constant_count as u64,
            bytes_before,
            bytes_after,
        })
    }

    /// Verify integrity of all shards (checksum validation).
    pub fn verify_integrity(&self) -> MathverseResult<IntegrityReport> {
        let manifest = self.load_manifest()?;
        let mut report = IntegrityReport {
            shards_checked: 0,
            shards_valid: 0,
            shards_corrupt: Vec::new(),
            shards_missing: Vec::new(),
            shards_orphaned: Vec::new(),
        };
        for entry in manifest.all_shards() {
            report.shards_checked += 1;
            match ShardReader::from_file(self.paths.root.join(&entry.path)) {
                Ok(_) => report.shards_valid += 1,
                Err(_) => report.shards_corrupt.push(entry.path.clone()),
            }
        }
        Ok(report)
    }

    pub fn paths(&self) -> &LibraryPaths {
        &self.paths
    }
}

// ---------------------------------------------------------------------------
// Shard integrity verification
// ---------------------------------------------------------------------------

/// Verify a single shard file's integrity by checking its blake3 footer checksum.
///
/// Reads the entire file, splits off the 64-byte footer, and verifies the
/// blake3 hash of the content (everything before the footer) matches the
/// first 32 bytes of the footer.
pub fn verify_shard_integrity(path: &Path) -> MathverseResult<bool> {
    const FOOTER_SIZE: usize = 64;
    let data = std::fs::read(path)?;
    if data.len() < FOOTER_SIZE {
        return Err(MathverseError::Truncated {
            expected: FOOTER_SIZE,
            got: data.len(),
        });
    }
    let content = &data[..data.len() - FOOTER_SIZE];
    let footer = &data[data.len() - FOOTER_SIZE..];
    let expected_hash = &footer[..32];
    let actual_hash = blake3::hash(content);
    Ok(actual_hash.as_bytes() == expected_hash)
}

/// Verify integrity of all shards referenced by a manifest.
///
/// Checks that:
/// - All referenced shard files exist on disk.
/// - Each shard's content_hash matches a fresh blake3 hash of the file.
/// - Reports orphaned shard files on disk not in the manifest.
pub fn verify_manifest_integrity(manifest: &MathverseManifest, base_dir: &Path) -> IntegrityReport {
    let mut report = IntegrityReport {
        shards_checked: 0,
        shards_valid: 0,
        shards_corrupt: Vec::new(),
        shards_missing: Vec::new(),
        shards_orphaned: Vec::new(),
    };

    // Collect all manifest-referenced paths (relative).
    let mut manifest_paths: hashbrown::HashSet<String> = hashbrown::HashSet::new();

    for entry in manifest.all_shards() {
        report.shards_checked += 1;
        manifest_paths.insert(entry.path.clone());
        let abs_path = base_dir.join(&entry.path);

        if !abs_path.exists() {
            report.shards_missing.push(entry.path.clone());
            continue;
        }

        // Verify content hash matches stored hash.
        match std::fs::read(&abs_path) {
            Ok(data) => {
                let actual_hash = blake3::hash(&data).to_hex().to_string();
                if actual_hash == entry.content_hash {
                    report.shards_valid += 1;
                } else {
                    report.shards_corrupt.push(entry.path.clone());
                }
            }
            Err(_) => {
                report.shards_corrupt.push(entry.path.clone());
            }
        }
    }

    // Find orphaned shard files (on disk but not in manifest).
    for subdir in &["base", "delta"] {
        let dir = base_dir.join(subdir);
        if let Ok(entries) = std::fs::read_dir(&dir) {
            for entry in entries.flatten() {
                let file_path = entry.path();
                if file_path.extension().and_then(|e| e.to_str()) == Some("mathverse") {
                    let rel = format!(
                        "{}/{}",
                        subdir,
                        file_path.file_name().unwrap_or_default().to_string_lossy()
                    );
                    if !manifest_paths.contains(&rel) {
                        report.shards_orphaned.push(file_path);
                    }
                }
            }
        }
    }

    report
}

// ---------------------------------------------------------------------------
// GarbageCollector
// ---------------------------------------------------------------------------

/// Garbage collector for orphaned shard files not referenced by the manifest.
pub struct GarbageCollector;

impl GarbageCollector {
    /// Find shard files on disk that are not referenced by any manifest entry.
    pub fn find_orphaned_shards(manifest: &MathverseManifest, base_dir: &Path) -> Vec<PathBuf> {
        let manifest_paths: hashbrown::HashSet<String> = manifest
            .all_shards()
            .iter()
            .map(|e| e.path.clone())
            .collect();

        let mut orphans = Vec::new();
        for subdir in &["base", "delta"] {
            let dir = base_dir.join(subdir);
            if let Ok(entries) = std::fs::read_dir(&dir) {
                for entry in entries.flatten() {
                    let file_path = entry.path();
                    if file_path.extension().and_then(|e| e.to_str()) == Some("mathverse") {
                        let rel = format!(
                            "{}/{}",
                            subdir,
                            file_path.file_name().unwrap_or_default().to_string_lossy()
                        );
                        if !manifest_paths.contains(&rel) {
                            orphans.push(file_path);
                        }
                    }
                }
            }
        }
        orphans
    }

    /// Remove orphaned shard files from disk. Returns the number of files removed.
    pub fn cleanup(orphans: &[PathBuf]) -> usize {
        let mut removed = 0;
        for path in orphans {
            if std::fs::remove_file(path).is_ok() {
                removed += 1;
            }
        }
        removed
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn ent(path: &str, c: u32, e: u32, src: &str) -> ShardEntry {
        ShardEntry {
            path: path.into(),
            content_hash: format!("h_{path}"),
            constant_count: c,
            expr_count: e,
            source: src.into(),
        }
    }

    fn init_loader(dir: &tempfile::TempDir) -> LibraryLoader {
        let l = LibraryLoader::new(dir.path().join("mathverse"));
        l.init().unwrap();
        l
    }

    #[test]
    fn test_manifest_json_round_trip() {
        let mut m = MathverseManifest::new();
        m.add_base_shard(ent("base/lean4.mathverse", 130_000, 5_000_000, "Lean4"));
        m.add_delta_shard(ent("delta/d001.mathverse", 100, 5000, "delta"));
        assert_eq!(m.total_constants, 130_100);
        assert_eq!(m.total_exprs, 5_005_000);
        let json = serde_json::to_string_pretty(&m).unwrap();
        let r: MathverseManifest = serde_json::from_str(&json).unwrap();
        assert_eq!(r.base_shards.len(), 1);
        assert_eq!(r.total_constants, 130_100);
    }

    #[test]
    fn test_manifest_file_and_atomic_save() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("manifest.json");
        let mut m = MathverseManifest::new();
        m.add_base_shard(ent("base/test.mathverse", 42, 1000, "test"));
        // Non-atomic write_to_file
        m.write_to_file(&path).unwrap();
        assert_eq!(
            MathverseManifest::from_file(&path).unwrap().base_shards[0].constant_count,
            42
        );
        // Atomic save
        m.add_delta_shard(ent("delta/d.mathverse", 10, 20, "delta"));
        m.save(&path).unwrap();
        let r = MathverseManifest::load(&path).unwrap();
        assert_eq!(r.delta_shards.len(), 1);
        assert!(!dir.path().join("manifest.json.tmp").exists());
    }

    #[test]
    fn test_register_remove_all_shards() {
        let mut m = MathverseManifest::new();
        m.register_shard(ent("base/b.mathverse", 5, 10, "b"), false);
        m.register_shard(ent("delta/d.mathverse", 3, 7, "delta"), true);
        assert_eq!(
            (m.base_shards.len(), m.delta_shards.len(), m.total_constants),
            (1, 1, 8)
        );
        // all_shards order
        let all = m.all_shards();
        assert_eq!(all[0].path, "base/b.mathverse");
        assert_eq!(all[1].path, "delta/d.mathverse");
        // remove
        assert!(m.remove_shard("delta/d.mathverse"));
        assert_eq!(m.total_constants, 5);
        assert!(!m.remove_shard("no/such.mathverse"));
    }

    #[test]
    fn test_needs_compaction_and_stats() {
        let mut m = MathverseManifest::new();
        m.add_base_shard(ent("base/a.mathverse", 100, 200, "a"));
        for i in 0..3 {
            m.add_delta_shard(ent(&format!("delta/d{i}.mathverse"), 5, 8, "delta"));
        }
        assert!(!m.needs_compaction(3));
        m.add_delta_shard(ent("delta/d3.mathverse", 1, 1, "delta"));
        assert!(m.needs_compaction(3));
        let s = m.total_stats();
        assert_eq!((s.total_shards, s.base_shards, s.delta_shards), (5, 1, 4));
        assert_eq!(s.total_constants, 116);
    }

    #[test]
    fn test_library_paths() {
        let root = Path::new("/tmp/mathverse-library");
        let p = LibraryPaths::new(root.to_path_buf());
        assert_eq!(p.manifest_path(), root.join("manifest.json"));
        assert_eq!(
            p.base_shard_path("lean4"),
            root.join("base/lean4.mathverse")
        );
        assert_eq!(
            p.delta_shard_path("d001"),
            root.join("delta/d001.mathverse")
        );
        assert_eq!(p.index_path(), root.join("index"));
        assert_eq!(MathverseManifest::library_paths(root).base, p.base);
        // ensure_dirs
        let dir = tempfile::tempdir().unwrap();
        let p2 = LibraryPaths::new(dir.path().join("lib"));
        p2.ensure_dirs().unwrap();
        assert!(p2.base.is_dir() && p2.delta.is_dir() && p2.index.is_dir());
    }

    #[test]
    fn test_loader_init() {
        let dir = tempfile::tempdir().unwrap();
        let loader = init_loader(&dir);
        assert!(loader.paths().base.is_dir() && loader.paths().manifest.exists());
        let m = loader.load_manifest().unwrap();
        assert_eq!(m.version, 1);
        assert!(m.base_shards.is_empty());
    }

    #[test]
    fn test_write_and_load_shard() {
        let dir = tempfile::tempdir().unwrap();
        let loader = init_loader(&dir);
        let e = loader
            .write_shard(&ShardWriter::new(), "s1", false)
            .unwrap();
        assert_eq!(e.source, "s1");
        assert!(e.path.starts_with("base/"));
        let m = loader.load_manifest().unwrap();
        assert_eq!(m.base_shards[0].path, "base/s1.mathverse");
        assert_eq!(
            loader
                .load_shard(&m.base_shards[0])
                .unwrap()
                .header
                .constant_count,
            0
        );
    }

    #[test]
    fn test_integrity() {
        let dir = tempfile::tempdir().unwrap();
        let loader = init_loader(&dir);
        let w = ShardWriter::new();
        loader.write_shard(&w, "good", false).unwrap();
        loader.write_shard(&w, "bad", true).unwrap();
        assert_eq!(loader.verify_integrity().unwrap().shards_valid, 2);
        std::fs::write(loader.paths().delta.join("bad.mathverse"), b"garbage").unwrap();
        let r = loader.verify_integrity().unwrap();
        assert_eq!(r.shards_valid, 1);
        assert_eq!(r.shards_corrupt, vec!["delta/bad.mathverse"]);
    }

    #[test]
    fn test_compaction() {
        let dir = tempfile::tempdir().unwrap();
        let loader = init_loader(&dir);
        let w = ShardWriter::new();
        loader.write_shard(&w, "base0", false).unwrap();
        loader.write_shard(&w, "d1", true).unwrap();
        loader.write_shard(&w, "d2", true).unwrap();
        assert_eq!(loader.compact().unwrap().deltas_merged, 2);
        let m = loader.load_manifest().unwrap();
        assert_eq!((m.base_shards.len(), m.delta_shards.len()), (1, 0));
        assert_eq!(m.base_shards[0].path, "base/compacted.mathverse");
        // No-op compaction when no deltas
        assert_eq!(loader.compact().unwrap().deltas_merged, 0);
    }

    // -- verify_shard_integrity tests ----------------------------------------

    #[test]
    fn test_verify_shard_integrity_valid() {
        let dir = tempfile::tempdir().unwrap();
        let loader = init_loader(&dir);
        let w = ShardWriter::new();
        loader.write_shard(&w, "valid_shard", false).unwrap();
        let shard_path = loader.paths().base_shard_path("valid_shard");
        // A valid shard written by ShardWriter should pass integrity check.
        let result = verify_shard_integrity(&shard_path);
        assert!(result.is_ok(), "valid shard should not error: {result:?}");
    }

    #[test]
    fn test_verify_shard_integrity_truncated() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("tiny.mathverse");
        std::fs::write(&path, b"too short").unwrap();
        let result = verify_shard_integrity(&path);
        assert!(result.is_err(), "truncated file should error");
    }

    #[test]
    fn test_verify_shard_integrity_corrupt() {
        let dir = tempfile::tempdir().unwrap();
        let loader = init_loader(&dir);
        let w = ShardWriter::new();
        loader.write_shard(&w, "to_corrupt", false).unwrap();
        let shard_path = loader.paths().base_shard_path("to_corrupt");
        // Corrupt the file by flipping a byte in the content area.
        let mut data = std::fs::read(&shard_path).unwrap();
        if data.len() > 100 {
            data[50] ^= 0xFF;
            std::fs::write(&shard_path, &data).unwrap();
        }
        let result = verify_shard_integrity(&shard_path);
        // Should either return Ok(false) or an error, not Ok(true).
        // An Err is also acceptable; only Ok(true) is a failure.
        if let Ok(valid) = result {
            assert!(!valid, "corrupted shard should not pass");
        }
    }

    // -- verify_manifest_integrity tests -------------------------------------

    #[test]
    fn test_verify_manifest_integrity_all_valid() {
        let dir = tempfile::tempdir().unwrap();
        let loader = init_loader(&dir);
        let w = ShardWriter::new();
        loader.write_shard(&w, "s1", false).unwrap();
        loader.write_shard(&w, "d1", true).unwrap();
        let manifest = loader.load_manifest().unwrap();
        let report = verify_manifest_integrity(&manifest, loader.paths().root.as_path());
        assert_eq!(report.shards_checked, 2);
        assert_eq!(report.shards_valid, 2);
        assert!(report.shards_missing.is_empty());
        assert!(report.shards_corrupt.is_empty());
        assert!(report.shards_orphaned.is_empty());
    }

    #[test]
    fn test_verify_manifest_integrity_missing_shard() {
        let dir = tempfile::tempdir().unwrap();
        let loader = init_loader(&dir);
        let w = ShardWriter::new();
        loader.write_shard(&w, "exists", false).unwrap();
        // Manually add a reference to a non-existent shard.
        let mut manifest = loader.load_manifest().unwrap();
        manifest.add_delta_shard(ent("delta/ghost.mathverse", 10, 20, "ghost"));
        let report = verify_manifest_integrity(&manifest, loader.paths().root.as_path());
        assert_eq!(report.shards_missing, vec!["delta/ghost.mathverse"]);
        assert_eq!(report.shards_valid, 1);
    }

    #[test]
    fn test_verify_manifest_integrity_corrupt_hash() {
        let dir = tempfile::tempdir().unwrap();
        let loader = init_loader(&dir);
        let w = ShardWriter::new();
        loader.write_shard(&w, "to_tamper", false).unwrap();
        // Tamper with the stored content_hash.
        let mut manifest = loader.load_manifest().unwrap();
        manifest.base_shards[0].content_hash = "wrong_hash".to_string();
        let report = verify_manifest_integrity(&manifest, loader.paths().root.as_path());
        assert_eq!(report.shards_corrupt, vec!["base/to_tamper.mathverse"]);
        assert_eq!(report.shards_valid, 0);
    }

    #[test]
    fn test_verify_manifest_integrity_orphaned() {
        let dir = tempfile::tempdir().unwrap();
        let loader = init_loader(&dir);
        let w = ShardWriter::new();
        loader.write_shard(&w, "tracked", false).unwrap();
        // Write an orphaned file directly to base/.
        std::fs::write(loader.paths().base.join("orphan.mathverse"), b"orphan data").unwrap();
        let manifest = loader.load_manifest().unwrap();
        let report = verify_manifest_integrity(&manifest, loader.paths().root.as_path());
        assert_eq!(report.shards_orphaned.len(), 1);
        assert!(report.shards_orphaned[0].ends_with("orphan.mathverse"));
    }

    // -- GarbageCollector tests ----------------------------------------------

    #[test]
    fn test_gc_find_orphaned_shards() {
        let dir = tempfile::tempdir().unwrap();
        let loader = init_loader(&dir);
        let w = ShardWriter::new();
        loader.write_shard(&w, "kept", false).unwrap();
        // Create orphan files.
        std::fs::write(loader.paths().base.join("orphan1.mathverse"), b"x").unwrap();
        std::fs::write(loader.paths().delta.join("orphan2.mathverse"), b"y").unwrap();
        // Non-.mathverse files should be ignored.
        std::fs::write(loader.paths().base.join("readme.txt"), b"z").unwrap();

        let manifest = loader.load_manifest().unwrap();
        let orphans =
            GarbageCollector::find_orphaned_shards(&manifest, loader.paths().root.as_path());
        assert_eq!(
            orphans.len(),
            2,
            "should find 2 orphaned .mathverse files, got: {orphans:?}"
        );
    }

    #[test]
    fn test_gc_cleanup() {
        let dir = tempfile::tempdir().unwrap();
        let loader = init_loader(&dir);
        let orphan_path = loader.paths().base.join("orphan.mathverse");
        std::fs::write(&orphan_path, b"orphan").unwrap();
        assert!(orphan_path.exists());

        let removed = GarbageCollector::cleanup(std::slice::from_ref(&orphan_path));
        assert_eq!(removed, 1);
        assert!(!orphan_path.exists(), "orphan should be deleted");
    }

    #[test]
    fn test_gc_cleanup_nonexistent() {
        let removed =
            GarbageCollector::cleanup(&[PathBuf::from("/tmp/no_such_file_12345.mathverse")]);
        assert_eq!(removed, 0, "removing nonexistent file should return 0");
    }

    // --- Fix (4): release-manifest name+shape adapter -----------------------

    /// Build a shard with real content, write only the release-shipped
    /// `mathverse-manifest.json` (ReleaseManifest shape) — NOT the in-place
    /// `manifest.json` — and confirm `load_manifest` adapts it, deriving the
    /// constant/expr counts from the shard header. This mirrors an extracted
    /// `mathverse-library-v*.tar.zst` release on disk.
    #[test]
    fn test_load_manifest_falls_back_to_release_manifest() {
        use crate::release::{ReleaseManifest, ReleaseShardEntry};
        use crate::types::{
            AxiomProfile, ContentDomain, DeclKind, ImportConfidence, MathverseConstantHeader,
            SourceSystem, NO_VALUE,
        };

        let dir = tempfile::tempdir().unwrap();
        let root = dir.path().join("mathverse-library");
        let base = root.join("base");
        std::fs::create_dir_all(&base).unwrap();

        // A real shard with one constant and one expr.
        let mut w = ShardWriter::new();
        let name = w.add_string("Demo.thm");
        let e = w.add_expr(clean_kernel::flat::FlatExpr::sort(0));
        w.add_constant(MathverseConstantHeader {
            name_idx: name,
            type_idx: e,
            value_idx: NO_VALUE,
            source_system: SourceSystem::Lean4 as u8,
            import_confidence: ImportConfidence::Translated as u8,
            content_domain: ContentDomain::PureMath as u8,
            decl_kind: DeclKind::Definition as u8,
            axiom_profile: AxiomProfile::NONE,
            sidecar_digest: 0,
            provenance_idx: 0,
            level_params_start: 0,
            level_params_count: 0,
            _pad2: [0u8; 26],
        });
        let shard_path = base.join("demo.mathverse");
        w.write_to_file(&shard_path).unwrap();
        let bytes = std::fs::read(&shard_path).unwrap();
        let blake3 = blake3::hash(&bytes).to_hex().to_string();

        // Write ONLY the release manifest (mathverse-manifest.json), no manifest.json.
        let release = ReleaseManifest {
            manifest_version: 1,
            release_version: "1.3.0".to_string(),
            created_at: "2026-06-22T00:00:00Z".to_string(),
            shards: vec![ReleaseShardEntry {
                path: "base/demo.mathverse".to_string(),
                size: bytes.len() as u64,
                blake3: blake3.clone(),
            }],
            total_bytes: bytes.len() as u64,
            total_shards: 1,
            baseline_index: None,
        };
        std::fs::write(
            root.join(RELEASE_MANIFEST_FILENAME),
            release.to_json().unwrap(),
        )
        .unwrap();
        assert!(!root.join("manifest.json").exists());

        let loader = LibraryLoader::new(root);
        let m = loader
            .load_manifest()
            .expect("load_manifest must fall back to the release manifest");
        assert_eq!(m.base_shards.len(), 1);
        assert_eq!(m.base_shards[0].path, "base/demo.mathverse");
        assert_eq!(m.base_shards[0].content_hash, blake3);
        // Counts derived from the shard header.
        assert_eq!(m.base_shards[0].constant_count, 1);
        assert_eq!(m.base_shards[0].expr_count, 1);
        assert_eq!(m.base_shards[0].source, "demo");
        assert_eq!(m.total_constants, 1);

        // And the full library loads through this adapted manifest.
        let lib = loader
            .load_library(TrustPolicy::default())
            .expect("library loads via adapted manifest");
        assert_eq!(lib.constant_count(), 1);
    }

    /// The in-place `manifest.json` still takes precedence when present (the
    /// fallback is additive, not a replacement).
    #[test]
    fn test_load_manifest_prefers_in_place_manifest() {
        let dir = tempfile::tempdir().unwrap();
        let loader = init_loader(&dir);
        // init() wrote manifest.json. Also drop a release manifest that, if
        // (wrongly) preferred, would point at a nonexistent shard and error.
        std::fs::write(
            loader.paths().root.join(RELEASE_MANIFEST_FILENAME),
            r#"{"manifest_version":1,"release_version":"x","created_at":"t","shards":[{"path":"base/ghost.mathverse","size":1,"blake3":"deadbeef"}],"total_bytes":1,"total_shards":1}"#,
        )
        .unwrap();
        // Should load the (empty) in-place manifest, not touch the release one.
        let m = loader.load_manifest().expect("in-place manifest preferred");
        assert!(m.base_shards.is_empty());
    }
}
