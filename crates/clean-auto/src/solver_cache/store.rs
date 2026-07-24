// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Local content-addressed proof-term cache (Phase 0 hit-serving).
//!
//! Phase 0 of the solver-results cache (see
//! `designs/2026-06-24-solver-results-cache-service.md` §4). The store is a flat
//! directory of records keyed by the [`obligation_digest`] of the goal type. Each
//! record holds a `bincode`-serialized kernel proof term plus small JSON
//! metadata. It is enabled by `CLEAN_SOLVER_CACHE_DIR`; when that env var is
//! unset the store is a **zero-overhead no-op** (no lookup, no write).
//!
//! [`obligation_digest`]: super::obligation::obligation_digest
//!
//! # Soundness (load-bearing — read before changing)
//!
//! This is a **search-result cache, not a trust cache, and not in the TCB.**
//!
//! - A cache *hit* returns a stored **proof term**. The caller (swarm /
//!   graduation / `auto_prove`'s own downstream consumer) re-checks that proof
//!   term through the kernel exactly as it would a freshly-found proof. A stale,
//!   colliding, or deliberately-corrupted entry is therefore **caught by the
//!   kernel re-check** and is never silently trusted. The obligation digest is a
//!   soundness *bucket*; the kernel is the *arbiter*.
//! - Only **proof-bearing** results are stored. A bare `Unsat`/`Unknown` verdict
//!   without a re-checkable proof term is telemetry, never a cache entry that can
//!   be served as a "proof". [`put`] only accepts a proof term.
//! - The on-disk proof term is *untrusted input*. [`get`] decodes it through the
//!   same canonical, resource-bounded codec as `CertifiedPayload`; a decode
//!   failure is a clean miss, not a panic.

use crate::proof_codec;
use crate::solver_cache::SolverCacheError;
use clean_kernel::Expr;
use serde::{Deserialize, Serialize};
use std::path::{Path, PathBuf};
use std::time::{SystemTime, UNIX_EPOCH};

/// Environment variable naming the proof-cache directory. Unset ⇒ off.
pub(crate) const CACHE_DIR_ENV: &str = "CLEAN_SOLVER_CACHE_DIR";

/// File extension for a single cache record.
const RECORD_EXT: &str = "scache";

/// Schema discriminator embedded in every stored record.
const STORE_SCHEMA: &str = "solver-cache-entry-v1";

/// Provenance metadata stored alongside a cached proof term.
///
/// This is *not* trusted: it records which engine/strategy produced the proof and
/// when, for telemetry and skew analysis. The kernel re-check on hit is the sole
/// arbiter of correctness.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct CacheMeta {
    /// Producing engine name (`clean-smt`, `clean-superposition`, `oracle`).
    pub(crate) solver: String,
    /// Within-engine strategy id (the fixed `smt→superposition→oracle` order).
    pub(crate) strategy: String,
    /// Unix epoch seconds at which the proof was first cached.
    pub(crate) found_at_epoch_s: u64,
}

impl CacheMeta {
    /// Build provenance for an entry produced *now* by `solver`/`strategy`.
    pub(crate) fn new(solver: impl Into<String>, strategy: impl Into<String>) -> Self {
        Self {
            solver: solver.into(),
            strategy: strategy.into(),
            found_at_epoch_s: now_epoch_s(),
        }
    }
}

/// A proof term retrieved from the cache, plus its provenance.
///
/// The `proof_term` is **untrusted** until the caller re-checks it through the
/// kernel (see module docs). It is returned as a plain [`Expr`] precisely so it
/// flows through the same downstream `recheck_and_classify` path as a
/// freshly-found proof.
#[derive(Clone, Debug)]
pub(crate) struct CachedProof {
    /// The stored (untrusted-until-rechecked) proof term.
    pub(crate) proof_term: Expr,
    /// Provenance of the stored proof.
    pub(crate) meta: CacheMeta,
}

/// On-disk record: schema tag, the obligation key it is filed under, the
/// `bincode`-serialized proof term, and JSON-friendly metadata.
///
/// The proof term is stored as `bincode` bytes (the established kernel-term
/// serialization, matching `CertifiedPayload`) rather than nested JSON, so the
/// record is compact and the term round-trips through the kernel's own
/// `Deserialize`.
#[derive(Clone, Debug, Serialize, Deserialize)]
struct StoredRecord {
    schema: String,
    obligation_digest: String,
    /// `bincode`-serialized [`Expr`] proof term.
    proof_term_bincode: Vec<u8>,
    meta: CacheMeta,
}

/// Whether the proof cache is enabled (`CLEAN_SOLVER_CACHE_DIR` set, non-empty).
///
/// Cheap fast path mirroring the telemetry sink: callers gate *all* cache work
/// behind this so the disabled default costs one env lookup.
pub(crate) fn is_enabled() -> bool {
    std::env::var_os(CACHE_DIR_ENV).is_some_and(|v| !v.is_empty())
}

/// The configured cache directory, if enabled.
fn cache_dir() -> Option<PathBuf> {
    std::env::var_os(CACHE_DIR_ENV)
        .filter(|v| !v.is_empty())
        .map(PathBuf::from)
}

/// Path of the record filed under `digest` within `dir`.
///
/// The digest has the form `blake3:<64hex>`; we file under the hex body with a
/// fixed extension so the filename is a fixed-width, filesystem-safe content
/// address. A digest that is not a clean `blake3:`-tagged hex string yields
/// `None` (treated as a miss / skipped insert) rather than risking a path
/// outside `dir`.
fn record_path(dir: &Path, digest: &str) -> Option<PathBuf> {
    let hex = digest.strip_prefix("blake3:")?;
    if hex.len() != 64 || !hex.chars().all(|c| c.is_ascii_hexdigit()) {
        return None;
    }
    Some(dir.join(format!("{hex}.{RECORD_EXT}")))
}

/// Look up a cached proof term for `obligation_digest`.
///
/// Returns `None` (a miss) when: the cache is disabled, no record exists, the
/// digest is malformed, or the on-disk record fails to decode. A decode failure
/// is deliberately a **clean miss**, never an error or panic — a corrupt/garbage
/// file must not break solving, and any returned term is re-checked by the caller
/// regardless.
pub(crate) fn get(obligation_digest: &str) -> Option<CachedProof> {
    let dir = cache_dir()?;
    get_from(&dir, obligation_digest)
}

/// Look up a cached proof term for `obligation_digest` under an **explicit**
/// directory (the env-independent path used by the Phase-2 service, which is
/// configured by `$DIR` rather than the producer's `CLEAN_SOLVER_CACHE_DIR`).
///
/// Same clean-miss contract as [`get`]: a malformed digest, a missing file, a
/// wrong schema tag, or undecodable bytes is a `None`, never a panic. Any term
/// returned is still re-checked by the caller through the kernel.
pub(crate) fn get_from(dir: &Path, obligation_digest: &str) -> Option<CachedProof> {
    let path = record_path(dir, obligation_digest)?;
    let bytes = std::fs::read(&path).ok()?;
    let record: StoredRecord = serde_json::from_slice(&bytes).ok()?;
    if record.schema != STORE_SCHEMA {
        return None;
    }
    let proof_term = decode_proof_term(&record.proof_term_bincode).ok()?;
    Some(CachedProof {
        proof_term,
        meta: record.meta,
    })
}

/// Insert a proof term for `obligation_digest`.
///
/// No-op when the cache is disabled or the digest is malformed. Only
/// proof-bearing results reach this function (the caller gates on a `Verified`
/// outcome); a bare verdict is never stored as a proof. Write errors are surfaced
/// as [`SolverCacheError`] but callers treat them as non-fatal: a failed insert
/// only forgoes a future hit, it never affects the current proof.
pub(crate) fn put(
    obligation_digest: &str,
    proof_term: &Expr,
    meta: CacheMeta,
) -> Result<(), SolverCacheError> {
    let Some(dir) = cache_dir() else {
        return Ok(());
    };
    put_in(&dir, obligation_digest, proof_term, meta)
}

/// Insert a proof term for `obligation_digest` under an **explicit** directory.
///
/// The env-independent path used by the Phase-2 ingest endpoint (configured by
/// `$DIR`). Soundness is unchanged: only a proof-bearing result reaches here, the
/// stored term is untrusted, and the consumer re-checks it through the kernel. A
/// malformed digest is a silent no-op (no path is derived). Creates `dir` if
/// absent and writes atomically (temp-then-rename).
pub(crate) fn put_in(
    dir: &Path,
    obligation_digest: &str,
    proof_term: &Expr,
    meta: CacheMeta,
) -> Result<(), SolverCacheError> {
    let Some(path) = record_path(dir, obligation_digest) else {
        return Ok(());
    };
    let proof_term_bincode = encode_proof_term(proof_term)?;
    let record = StoredRecord {
        schema: STORE_SCHEMA.to_string(),
        obligation_digest: obligation_digest.to_string(),
        proof_term_bincode,
        meta,
    };
    let bytes =
        serde_json::to_vec(&record).map_err(|e| SolverCacheError::Serialize(e.to_string()))?;
    std::fs::create_dir_all(dir).map_err(|e| SolverCacheError::Sink(e.to_string()))?;
    atomic_write(&path, &bytes)
}

/// `bincode`-encode a kernel proof term, matching the `CertifiedPayload`
/// term-serialization convention used elsewhere in `clean-auto`. The Phase-2
/// ingest path encodes a submitted proof through this exact codec so a stored
/// blob round-trips through [`decode_proof_term`].
pub(crate) fn encode_proof_term(term: &Expr) -> Result<Vec<u8>, SolverCacheError> {
    proof_codec::encode_term(term).map_err(SolverCacheError::Serialize)
}

/// Decode a canonical, bounded kernel proof term using the exact shared
/// `CertifiedPayload` codec. Trailing bytes, non-minimal varints, excessive
/// allocation claims, and over-complex structures all fail as cache misses.
pub(crate) fn decode_proof_term(bytes: &[u8]) -> Result<Expr, SolverCacheError> {
    proof_codec::decode_term(bytes).map_err(SolverCacheError::Serialize)
}

/// Write `bytes` to `path` atomically: write a unique temp sibling, then rename.
///
/// Rename-into-place avoids a concurrent reader observing a half-written record
/// (multiple solver processes can share one cache dir). The temp name embeds the
/// process id and a nanosecond timestamp to avoid collisions.
fn atomic_write(path: &Path, bytes: &[u8]) -> Result<(), SolverCacheError> {
    use std::io::Write as _;
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|d| d.as_nanos())
        .unwrap_or(0);
    let tmp = path.with_extension(format!("{RECORD_EXT}.tmp.{}.{nanos}", std::process::id()));
    {
        let mut file =
            std::fs::File::create(&tmp).map_err(|e| SolverCacheError::Sink(e.to_string()))?;
        file.write_all(bytes)
            .map_err(|e| SolverCacheError::Sink(e.to_string()))?;
        file.flush()
            .map_err(|e| SolverCacheError::Sink(e.to_string()))?;
    }
    std::fs::rename(&tmp, path).map_err(|e| {
        // Best-effort cleanup of the temp file on a failed rename.
        let _ = std::fs::remove_file(&tmp);
        SolverCacheError::Sink(e.to_string())
    })
}

/// Current Unix epoch seconds (0 on the impossible pre-epoch clock).
fn now_epoch_s() -> u64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|d| d.as_secs())
        .unwrap_or(0)
}

/// Enumerate the `blake3:<64hex>` obligation digests with a cached proof term in
/// `dir`, in sorted order.
///
/// Used by the `VCIDX01` index builder to mark `cached = true` for an
/// obligation. Scans for `<64hex>.scache` filenames and reconstructs the digest
/// string; a filename whose stem is not a clean 64-hex body is ignored (the
/// store only ever writes such names). A missing/unreadable directory yields an
/// empty set — the cache simply contributes no `cached` bits, never an error.
pub(crate) fn cached_digests(dir: &Path) -> Vec<String> {
    let mut out = Vec::new();
    let Ok(entries) = std::fs::read_dir(dir) else {
        return out;
    };
    for entry in entries.flatten() {
        let path = entry.path();
        if path.extension().and_then(|e| e.to_str()) != Some(RECORD_EXT) {
            continue;
        }
        let Some(stem) = path.file_stem().and_then(|s| s.to_str()) else {
            continue;
        };
        if stem.len() == 64 && stem.chars().all(|c| c.is_ascii_hexdigit()) {
            out.push(format!("blake3:{stem}"));
        }
    }
    out.sort_unstable();
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::{BinderInfo, Level, Name};

    /// RAII guard setting `CLEAN_SOLVER_CACHE_DIR` for a test and restoring the
    /// previous value on drop (via the crate env choke point). The store tests
    /// are `#[serial]`, which supplies the cross-test serialization the raw env
    /// mutation needs.
    struct CacheEnvGuard {
        _var: crate::test_env::ScopedEnvVar,
    }

    impl CacheEnvGuard {
        fn set(dir: &Path) -> Self {
            Self {
                _var: crate::test_env::ScopedEnvVar::set(CACHE_DIR_ENV, &dir.to_string_lossy()),
            }
        }
    }

    fn sample_term() -> Expr {
        // `∀ (_ : Sort 0), v0` — a small closed kernel term.
        Expr::pi(
            BinderInfo::Default,
            Expr::sort(Level::zero()),
            Expr::bvar(0),
        )
    }

    fn sample_digest() -> String {
        "blake3:".to_string() + &"ab".repeat(32)
    }

    #[test]
    #[serial_test::serial]
    fn test_put_then_get_roundtrips_proof_term() {
        let tmp = tempfile::tempdir().expect("tempdir");
        let _guard = CacheEnvGuard::set(tmp.path());
        let digest = sample_digest();
        let term = sample_term();

        put(&digest, &term, CacheMeta::new("clean-smt", "test")).expect("put");
        let got = get(&digest).expect("hit after put");
        assert_eq!(got.proof_term, term, "round-tripped term must match");
        assert_eq!(got.meta.solver, "clean-smt");
        assert_eq!(got.meta.strategy, "test");
    }

    #[test]
    #[serial_test::serial]
    fn test_get_miss_when_absent() {
        let tmp = tempfile::tempdir().expect("tempdir");
        let _guard = CacheEnvGuard::set(tmp.path());
        assert!(
            get(&sample_digest()).is_none(),
            "absent key must be a clean miss"
        );
    }

    #[test]
    #[serial_test::serial]
    fn test_disabled_cache_is_noop() {
        let _guard = crate::test_env::ScopedEnvVar::unset(CACHE_DIR_ENV);
        // No env => put is a no-op (Ok) and get is a miss, with no panic.
        put(
            &sample_digest(),
            &sample_term(),
            CacheMeta::new("clean-smt", "x"),
        )
        .expect("disabled put is Ok no-op");
        assert!(get(&sample_digest()).is_none(), "disabled get is a miss");
    }

    #[test]
    #[serial_test::serial]
    fn test_corrupt_record_bytes_are_a_clean_miss() {
        let tmp = tempfile::tempdir().expect("tempdir");
        let _guard = CacheEnvGuard::set(tmp.path());
        let digest = sample_digest();
        // Write garbage at the record path: not valid JSON.
        let path = record_path(tmp.path(), &digest).expect("record path");
        std::fs::write(&path, b"this is not a valid record").expect("write garbage");
        assert!(
            get(&digest).is_none(),
            "a corrupt record must decode to a clean miss, never a panic"
        );
    }

    #[test]
    #[serial_test::serial]
    fn test_corrupt_proof_term_bincode_is_a_clean_miss() {
        let tmp = tempfile::tempdir().expect("tempdir");
        let _guard = CacheEnvGuard::set(tmp.path());
        let digest = sample_digest();
        // Valid record envelope, but the proof-term bytes are garbage bincode.
        let record = StoredRecord {
            schema: STORE_SCHEMA.to_string(),
            obligation_digest: digest.clone(),
            proof_term_bincode: vec![0xff, 0xff, 0xff, 0xff, 0xff, 0xff],
            meta: CacheMeta::new("clean-smt", "x"),
        };
        let path = record_path(tmp.path(), &digest).expect("record path");
        std::fs::write(&path, serde_json::to_vec(&record).expect("ser")).expect("write");
        assert!(
            get(&digest).is_none(),
            "undecodable proof-term bytes must be a clean miss"
        );
    }

    #[test]
    #[serial_test::serial]
    fn test_noncanonical_proof_term_is_a_clean_miss() {
        let tmp = tempfile::tempdir().expect("tempdir");
        let _guard = CacheEnvGuard::set(tmp.path());
        let digest = sample_digest();
        let mut proof_term_bincode = encode_proof_term(&sample_term()).expect("encode term");
        proof_term_bincode.push(0);
        let record = StoredRecord {
            schema: STORE_SCHEMA.to_string(),
            obligation_digest: digest.clone(),
            proof_term_bincode,
            meta: CacheMeta::new("clean-smt", "x"),
        };
        let path = record_path(tmp.path(), &digest).expect("record path");
        std::fs::write(&path, serde_json::to_vec(&record).expect("ser")).expect("write");

        assert!(
            get(&digest).is_none(),
            "trailing bytes must be rejected through the shared canonical codec"
        );
    }

    #[test]
    fn test_malformed_digest_yields_no_path() {
        let dir = Path::new("/tmp/x");
        assert!(record_path(dir, "not-a-digest").is_none());
        assert!(record_path(dir, "blake3:short").is_none());
        assert!(
            record_path(dir, "blake3:../etc/passwd").is_none(),
            "non-hex body (path traversal attempt) must be rejected"
        );
        assert!(record_path(dir, &sample_digest()).is_some());
    }

    #[test]
    fn test_const_name_distinct_terms_distinct_when_stored() {
        // Distinct terms must not alias under distinct keys (basic store sanity).
        let t1 = sample_term();
        let t2 = Expr::const_(Name::from_string("C"), Vec::<Level>::new());
        assert_ne!(
            encode_proof_term(&t1).expect("enc t1"),
            encode_proof_term(&t2).expect("enc t2"),
            "distinct terms encode to distinct bytes"
        );
    }
}
