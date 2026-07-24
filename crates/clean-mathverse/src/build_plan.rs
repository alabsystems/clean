//! Build plan + lockfile for incremental, cached Mathverse corpus reconstruction.
//!
//! The reconstruct CLI treats the corpus like a compiler bootstrap, but for a
//! math library: upstream artifacts are downloaded, each per-system import is
//! cached, and the whole baseline is pinned by a lockfile so it reconstructs
//! identically on any machine with internet + clean source. The strategic
//! payoff is risk tolerance — because the baseline is cheaply and verifiably
//! regenerable, the shard format, data model, and search/discovery indexes can
//! be changed aggressively without ever losing the corpus.
//!
//! This module is the cache/lockfile keystone:
//!
//! * a content-addressed [`fingerprint`] per system —
//!   `blake3(source_sha ‖ importer_version ‖ importer_args ‖ shard_schema)` — so
//!   an unchanged input is a free CACHE-HIT and any input change (upstream
//!   commit, importer logic, shard format) invalidates exactly that system;
//! * an on-disk ledger [`Lockfile`] (`data/mathverse.lock.json`) binding each
//!   system to the `(fingerprint, source_sha, importer_version, shard_hashes)`
//!   that produced it, so a build is reproducible and a release is pinnable.
//!
//! See `designs/2026-06-30-mathverse-reconstruct-cli.md`.

use std::collections::BTreeMap;
use std::path::Path;
use std::process::Command;
use std::time::{SystemTime, UNIX_EPOCH};

use serde::{Deserialize, Serialize};

use crate::error::MathverseResult;

/// Lockfile layout version. Bump on incompatible `mathverse.lock.json` changes.
pub const LOCKFILE_SCHEMA_VERSION: u32 = 1;

/// Shard-format / pipeline schema version folded into every fingerprint, so a
/// shard-format change invalidates all per-system caches at once.
pub const SHARD_SCHEMA_VERSION: u32 = 3;

/// The authoritative build ledger, persisted as `data/mathverse.lock.json`.
///
/// Unchanged systems are a free CACHE-HIT; only systems whose fingerprint moved
/// (upstream SHA changed, importer bumped, shard schema changed) are rebuilt.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Lockfile {
    pub schema_version: u32,
    /// Per-system pinned build state, keyed by system name (sorted for stable diffs).
    #[serde(default)]
    pub systems: BTreeMap<String, SystemLock>,
    /// Systems intentionally not built (no importer / no upstream), surfaced so a
    /// reconstruct never *silently* drops a system.
    #[serde(default)]
    pub dropped: Vec<DroppedSystem>,
}

impl Default for Lockfile {
    fn default() -> Self {
        Self {
            schema_version: LOCKFILE_SCHEMA_VERSION,
            systems: BTreeMap::new(),
            dropped: Vec::new(),
        }
    }
}

/// One system's pinned build state — the cache entry and the reproducibility record.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SystemLock {
    /// `fingerprint(source_sha, importer_version, importer_args)`.
    pub fingerprint: String,
    /// Resolved upstream commit that produced these shards (the cache key's source half).
    pub source_sha: String,
    /// The lane's importer version at build time.
    pub importer_version: u32,
    /// Shard paths relative to the library out dir (e.g. `delta/metamath_0000.mathverse`).
    pub shards: Vec<String>,
    /// blake3 hex per shard — equal to `ShardEntry.content_hash` and the shard footer hash.
    pub shard_hashes: Vec<String>,
    /// Total declarations emitted by this system.
    pub decl_count: u64,
    /// Maximum [`crate::types::ImportConfidence`] achievable for this lane
    /// (`KernelVerified` for Lean4-olean, `SourceVerified` for Metamath, else `Unverified`).
    pub trust_max: String,
    /// Build time, unix seconds.
    pub built_at_unix: u64,
    /// Cross-shard axiom-closure epoch this shard set is current for (see design §3.3).
    pub closure_epoch: u64,
}

/// A system intentionally not built — recorded so `status`/reconciliation can
/// account for every manifest system in exactly one bucket.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DroppedSystem {
    pub system: String,
    /// e.g. `no-importer`, `no-upstream`, `toolchain-missing:lake`.
    pub reason: String,
}

impl Lockfile {
    /// A fresh, empty lockfile at the current schema version.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Load the lockfile from `path`, or return a fresh empty one if it does not
    /// exist (so a first-ever build is a clean miss rather than an error).
    pub fn load(path: &Path) -> MathverseResult<Self> {
        if !path.exists() {
            return Ok(Self::new());
        }
        let text = std::fs::read_to_string(path)?;
        let lock: Lockfile = serde_json::from_str(&text)?;
        Ok(lock)
    }

    /// Atomically persist the lockfile (write tmp + rename), mirroring
    /// [`crate::manifest::MathverseManifest::save`].
    pub fn save(&self, path: &Path) -> MathverseResult<()> {
        let data = serde_json::to_string_pretty(self)?;
        let tmp = path.with_extension("json.tmp");
        std::fs::write(&tmp, &data)?;
        std::fs::rename(&tmp, path)?;
        Ok(())
    }

    /// Record (or replace) a system's pinned build state. Reconciles the buckets:
    /// a freshly-built system is removed from `dropped`, so it never appears in both
    /// (the [`DroppedSystem`] "exactly one bucket" invariant).
    pub fn record(&mut self, system: &str, lock: SystemLock) {
        self.dropped.retain(|d| d.system != system);
        self.systems.insert(system.to_string(), lock);
    }

    /// Record a system as intentionally dropped (deduplicated by name). Reconciles the
    /// buckets: a dropped system is removed from `systems`, so it never appears in both.
    pub fn record_dropped(&mut self, system: &str, reason: &str) {
        self.systems.remove(system);
        self.dropped.retain(|d| d.system != system);
        self.dropped.push(DroppedSystem {
            system: system.to_string(),
            reason: reason.to_string(),
        });
    }

    /// `true` iff `system`'s recorded fingerprint matches `fingerprint` **and**
    /// every recorded shard still exists under `out_root` with a matching blake3.
    ///
    /// The fingerprint check covers input identity; the per-file blake3 check
    /// covers on-disk integrity (a shard deleted, truncated, or corrupted since
    /// the last build is a MISS, forcing a rebuild rather than a stale CACHE-HIT).
    #[must_use]
    pub fn is_cache_hit(&self, system: &str, fingerprint: &str, out_root: &Path) -> bool {
        let Some(entry) = self.systems.get(system) else {
            return false;
        };
        // A zero-shard entry has no on-disk integrity anchor — never a CACHE-HIT
        // (else `.all()` over an empty list is vacuously true and serves nothing).
        if entry.fingerprint != fingerprint
            || entry.shards.is_empty()
            || entry.shards.len() != entry.shard_hashes.len()
        {
            return false;
        }
        entry
            .shards
            .iter()
            .zip(&entry.shard_hashes)
            .all(|(rel, want)| match std::fs::read(out_root.join(rel)) {
                Ok(bytes) => blake3::hash(&bytes).to_hex().to_string() == *want,
                Err(_) => false,
            })
    }
}

/// Content-addressed fingerprint for a system's build inputs.
///
/// `fp = blake3(source_sha ‖ importer_version ‖ importer_args ‖ shard_schema)`.
/// Domain-separated so concatenation is unambiguous. Two builds with the same
/// fingerprint produce byte-identical shards, so an unchanged fingerprint is a
/// safe CACHE-HIT; any change to upstream source, importer logic, importer
/// arguments, or shard format flips it.
#[must_use]
pub fn fingerprint(source_sha: &str, importer_version: u32, importer_args: &str) -> String {
    let mut hasher = blake3::Hasher::new();
    hasher.update(b"mathverse-build-plan-v1\0");
    hasher.update(source_sha.as_bytes());
    hasher.update(b"\0source\0");
    hasher.update(&importer_version.to_le_bytes());
    hasher.update(b"\0importer\0");
    hasher.update(importer_args.as_bytes());
    hasher.update(b"\0args\0");
    hasher.update(&SHARD_SCHEMA_VERSION.to_le_bytes());
    hasher.finalize().to_hex().to_string()
}

/// Resolve a git checkout's `HEAD` SHA — the source half of the cache key.
///
/// Returns `None` if `clone_path` is not a git work tree or `git` is
/// unavailable, in which case callers should treat the system as a forced
/// rebuild (no stable cache key) rather than risking a false CACHE-HIT.
#[must_use]
pub fn resolved_source_sha(clone_path: &Path) -> Option<String> {
    let out = Command::new("git")
        .args(["rev-parse", "HEAD"])
        .current_dir(clone_path)
        .output()
        .ok()?;
    if !out.status.success() {
        return None;
    }
    let sha = String::from_utf8_lossy(&out.stdout).trim().to_string();
    if sha.is_empty() {
        None
    } else {
        Some(sha)
    }
}

/// Current unix time in seconds, for [`SystemLock::built_at_unix`].
#[must_use]
pub fn now_unix() -> u64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|d| d.as_secs())
        .unwrap_or(0)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sample_lock(fingerprint: &str, shards: Vec<String>, hashes: Vec<String>) -> SystemLock {
        SystemLock {
            fingerprint: fingerprint.to_string(),
            source_sha: "deadbeef".to_string(),
            importer_version: 1,
            shards,
            shard_hashes: hashes,
            decl_count: 42,
            trust_max: "SourceVerified".to_string(),
            built_at_unix: 1_700_000_000,
            closure_epoch: 0,
        }
    }

    #[test]
    fn test_fingerprint_is_deterministic_and_input_sensitive() {
        let a = fingerprint("sha1", 1, "{}");
        assert_eq!(a, fingerprint("sha1", 1, "{}"), "same inputs => same fp");
        assert_ne!(a, fingerprint("sha2", 1, "{}"), "source sha flips fp");
        assert_ne!(a, fingerprint("sha1", 2, "{}"), "importer version flips fp");
        assert_ne!(a, fingerprint("sha1", 1, "{x:1}"), "importer args flip fp");
    }

    #[test]
    fn test_lockfile_roundtrips_through_disk() {
        let dir = tempfile::tempdir().expect("tempdir");
        let path = dir.path().join("mathverse.lock.json");

        let mut lock = Lockfile::new();
        lock.record(
            "metamath",
            sample_lock(
                "fp-mm",
                vec!["delta/mm_0000.mathverse".into()],
                vec!["h0".into()],
            ),
        );
        lock.record_dropped("hol-light", "no-importer");
        lock.save(&path).expect("save");

        let loaded = Lockfile::load(&path).expect("load");
        assert_eq!(loaded.schema_version, LOCKFILE_SCHEMA_VERSION);
        assert_eq!(loaded.systems.get("metamath"), lock.systems.get("metamath"));
        assert_eq!(loaded.dropped.len(), 1);
        assert_eq!(loaded.dropped[0].system, "hol-light");
    }

    #[test]
    fn test_load_missing_lockfile_is_empty_not_error() {
        let dir = tempfile::tempdir().expect("tempdir");
        let lock = Lockfile::load(&dir.path().join("absent.json")).expect("missing => empty");
        assert!(lock.systems.is_empty());
        assert!(lock.dropped.is_empty());
    }

    #[test]
    fn test_record_and_record_dropped_reconcile_buckets() {
        let mut lock = Lockfile::new();
        lock.record_dropped("metamath", "no-source");
        assert!(lock.systems.is_empty());
        assert_eq!(lock.dropped.len(), 1);
        // Building it later moves it out of `dropped` into `systems` (exactly one bucket).
        lock.record(
            "metamath",
            sample_lock("fp", vec!["delta/m.mathverse".into()], vec!["h".into()]),
        );
        assert!(lock.systems.contains_key("metamath"));
        assert!(lock.dropped.iter().all(|d| d.system != "metamath"));
        // Dropping it again moves it back out of `systems`.
        lock.record_dropped("metamath", "no-source");
        assert!(!lock.systems.contains_key("metamath"));
        assert_eq!(lock.dropped.len(), 1);
    }

    #[test]
    fn test_empty_shards_is_never_a_cache_hit() {
        let dir = tempfile::tempdir().expect("tempdir");
        let fp = fingerprint("sha", 1, "{}");
        let mut lock = Lockfile::new();
        lock.record("metamath", sample_lock(&fp, vec![], vec![]));
        assert!(
            !lock.is_cache_hit("metamath", &fp, dir.path()),
            "zero-shard entry must rebuild, not vacuously hit"
        );
    }

    #[test]
    fn test_cache_hit_requires_matching_fingerprint_and_intact_shards() {
        let dir = tempfile::tempdir().expect("tempdir");
        let out_root = dir.path();
        std::fs::create_dir_all(out_root.join("delta")).expect("mkdir");

        let shard_rel = "delta/mm_0000.mathverse";
        let shard_abs = out_root.join(shard_rel);
        std::fs::write(&shard_abs, b"shard-bytes").expect("write shard");
        let hash = blake3::hash(b"shard-bytes").to_hex().to_string();

        let fp = fingerprint("sha1", 1, "{}");
        let mut lock = Lockfile::new();
        lock.record(
            "metamath",
            sample_lock(&fp, vec![shard_rel.into()], vec![hash]),
        );

        assert!(
            lock.is_cache_hit("metamath", &fp, out_root),
            "intact + matching => HIT"
        );
        assert!(
            !lock.is_cache_hit("metamath", "other-fp", out_root),
            "fp mismatch => MISS"
        );
        assert!(
            !lock.is_cache_hit("lean4", &fp, out_root),
            "unknown system => MISS"
        );

        // Tamper with the shard on disk: blake3 changes => MISS (forces rebuild).
        std::fs::write(&shard_abs, b"corrupted").expect("rewrite");
        assert!(
            !lock.is_cache_hit("metamath", &fp, out_root),
            "corrupted shard => MISS"
        );

        // Missing shard => MISS.
        std::fs::remove_file(&shard_abs).expect("rm");
        assert!(
            !lock.is_cache_hit("metamath", &fp, out_root),
            "absent shard => MISS"
        );
    }
}
