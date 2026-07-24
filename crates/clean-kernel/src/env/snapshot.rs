// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Versioned environment snapshot (`.clean-cache` Init half).
//!
//! A snapshot is a bincode-encoded [`Environment`] wrapped in a small
//! versioned [`SnapshotHeader`]. It exists to skip the multi-minute full
//! re-load+re-verify of the `Init` closure on warm runs.
//!
//! # Soundness
//!
//! A snapshot is a *cache of a prior full re-verification*, never a trust
//! claim:
//!
//! - **WRITE** ([`Environment::save_snapshot`]) must be called ONLY from an
//!   environment whose constants were `add_decl`-re-verified in the SAME run.
//!   The kernel cannot enforce this (it does not record per-run re-verify
//!   provenance), so the caller is responsible. See the call site in
//!   `clean-olean`'s `preload_init_if_needed`, which writes only after a
//!   `--full-validation` re-check succeeded.
//! - **REUSE** ([`Environment::load_snapshot`]) is gated on an EXACT match of
//!   every header field against the current run. ANY mismatch (snapshot
//!   version, kernel format version, env schema fingerprint, or Init closure
//!   hash) yields [`SnapshotLoadOutcome::Mismatch`] — the caller MUST then fall
//!   back to a full re-verify. Reuse never trusts a stale/foreign snapshot.
//! - The deserialized environment is byte-for-byte the env that was written:
//!   bincode round-trips the full [`Environment`] (all `*_init` flags,
//!   inductives, constructors, recursors). It is therefore identical to a
//!   fresh re-verified env (see the equality test).
//!
//! The header carries the data needed to detect every way the cached bytes
//! could become stale relative to the current binary + inputs.

use serde::{Deserialize, Serialize};

use super::Environment;

/// Snapshot container format version. Bump when the *header* layout changes.
pub const SNAPSHOT_VERSION: u32 = 1;

/// Fingerprint of the [`Environment`] bincode layout. This is a compile-time
/// constant that MUST be bumped manually whenever the serialized shape of
/// `Environment` (or any type it transitively serializes) changes in a way
/// that would make old bincode bytes decode incorrectly — e.g. adding/removing
/// a non-`#[serde(default)]`/`#[serde(skip)]` field, reordering fields,
/// changing a field's type, or changing `Expr`/`Name` custom serde.
///
/// Mirrors the `CACHE_VERSION` pattern already used by `verify_cache`. Because
/// it is baked into the binary at compile time, a rebuilt binary with a
/// different layout will reject snapshots written by the old binary as long as
/// this string was bumped alongside the layout change.
pub const ENV_SCHEMA_FINGERPRINT: &str = "clean-env-bincode-v1";

/// Versioned header prepended to a snapshot. Every field is part of the reuse
/// gate: the snapshot is reused IFF all four match the current run.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SnapshotHeader {
    /// Snapshot container format version ([`SNAPSHOT_VERSION`]).
    pub snapshot_version: u32,
    /// Kernel crate version that produced the snapshot (`CARGO_PKG_VERSION`).
    pub kernel_format_version: String,
    /// [`ENV_SCHEMA_FINGERPRINT`] at write time.
    pub env_schema_fingerprint: String,
    /// blake3 (or any stable) hash of the Init closure inputs the snapshot was
    /// built from. Supplied by the caller; opaque to the kernel.
    pub init_closure_blake3: String,
}

impl SnapshotHeader {
    /// Construct a header for the CURRENT binary, tagged with the caller's
    /// `init_closure_blake3` closure hash.
    #[must_use]
    pub fn current(init_closure_blake3: impl Into<String>) -> Self {
        Self {
            snapshot_version: SNAPSHOT_VERSION,
            kernel_format_version: crate::VERSION.to_string(),
            env_schema_fingerprint: ENV_SCHEMA_FINGERPRINT.to_string(),
            init_closure_blake3: init_closure_blake3.into(),
        }
    }

    /// Whether this (deserialized) header is reusable by a run whose current
    /// header is `current`. Reuse requires an EXACT match of all fields.
    #[must_use]
    pub fn matches(&self, current: &SnapshotHeader) -> bool {
        self == current
    }
}

/// On-disk snapshot: header + bincode-encoded environment bytes.
#[derive(Clone, Debug, Serialize, Deserialize)]
struct SnapshotFile {
    header: SnapshotHeader,
    /// Bincode bytes of the [`Environment`] (the existing `to_bincode` output).
    env_bytes: Vec<u8>,
}

/// Errors from snapshot save/load.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum SnapshotError {
    /// Failed to encode the environment to bincode.
    #[error("snapshot encode: {0}")]
    Encode(#[from] bincode::error::EncodeError),
    /// Failed to decode the snapshot file or the inner environment.
    #[error("snapshot decode: {0}")]
    Decode(#[from] bincode::error::DecodeError),
    /// Filesystem error reading/writing the snapshot.
    #[error("snapshot io: {0}")]
    Io(#[from] std::io::Error),
}

/// Result of attempting to load + gate a snapshot.
#[derive(Debug)]
pub enum SnapshotLoadOutcome {
    /// Header matched the current run; the environment was restored.
    Loaded(Box<Environment>),
    /// The snapshot file parsed but its header did not match the current run.
    /// The caller MUST fall back to a full re-verify. The mismatched header is
    /// returned for diagnostics.
    Mismatch(Box<SnapshotHeader>),
}

impl Environment {
    /// Write a versioned snapshot of this environment to `path`.
    ///
    /// SOUNDNESS: callers MUST only invoke this on an environment whose
    /// constants were `add_decl`-re-verified in the current run (never a
    /// load-only / infer-only environment). The kernel cannot check this.
    ///
    /// `header` should be [`SnapshotHeader::current`] tagged with the closure
    /// hash of the inputs that produced this environment.
    pub fn save_snapshot(
        &self,
        path: &std::path::Path,
        header: SnapshotHeader,
    ) -> Result<(), SnapshotError> {
        let env_bytes = self.to_bincode()?;
        let file = SnapshotFile { header, env_bytes };
        let bytes = bincode::serde::encode_to_vec(&file, bincode::config::standard())?;
        if let Some(parent) = path.parent() {
            std::fs::create_dir_all(parent)?;
        }
        std::fs::write(path, bytes)?;
        Ok(())
    }

    /// Attempt to load a snapshot from `path`, gating reuse on an exact match
    /// of `expected` against the stored header.
    ///
    /// Returns:
    /// - [`SnapshotLoadOutcome::Loaded`] if (and only if) every header field
    ///   matches — the environment is restored.
    /// - [`SnapshotLoadOutcome::Mismatch`] if the file parses but the header
    ///   does not match (stale version, fingerprint, or hash). The caller MUST
    ///   then do a full re-verify; the stale snapshot is NOT used.
    /// - `Err` if the file is missing/unreadable or the bytes are corrupt
    ///   (fail safe: treat as a cache miss and full-load).
    pub fn load_snapshot(
        path: &std::path::Path,
        expected: &SnapshotHeader,
    ) -> Result<SnapshotLoadOutcome, SnapshotError> {
        let bytes = std::fs::read(path)?;
        let (file, _): (SnapshotFile, _) =
            bincode::serde::decode_from_slice(&bytes, bincode::config::standard())?;
        if !file.header.matches(expected) {
            return Ok(SnapshotLoadOutcome::Mismatch(Box::new(file.header)));
        }
        let env = Self::from_bincode(&file.env_bytes)?;
        Ok(SnapshotLoadOutcome::Loaded(Box::new(env)))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::Environment;
    use crate::expr::Expr;
    use crate::name::Name;
    use crate::Declaration;

    fn sample_env() -> Environment {
        let mut env = Environment::new();
        env.add_decl_unchecked(Declaration::Definition {
            name: Name::from_string("snap_def"),
            level_params: vec![],
            type_: Expr::type_(),
            value: Expr::prop(),
            is_reducible: true,
        });
        env.add_decl_unchecked(Declaration::Axiom {
            name: Name::from_string("snap_ax"),
            level_params: vec![],
            type_: Expr::prop(),
        });
        env
    }

    #[test]
    fn test_snapshot_roundtrip_loads_identical_env() {
        let dir = std::env::temp_dir().join(format!("clean-snap-{}", std::process::id()));
        let path = dir.join("init.snapshot");
        let env = sample_env();
        let header = SnapshotHeader::current("hash-abc");
        env.save_snapshot(&path, header.clone())
            .expect("save_snapshot must succeed");

        let outcome =
            Environment::load_snapshot(&path, &header).expect("load_snapshot must succeed");
        let loaded = match outcome {
            SnapshotLoadOutcome::Loaded(e) => *e,
            SnapshotLoadOutcome::Mismatch(_) => panic!("identical header must match"),
        };

        // Identical to a fresh env: same constant count + sample types.
        let fresh = sample_env();
        assert_eq!(
            loaded.constants().count(),
            fresh.constants().count(),
            "constant count must match fresh env"
        );
        for ci in fresh.constants() {
            let got = loaded
                .get_const(&ci.name)
                .expect("snapshot must contain every fresh constant");
            assert_eq!(got.type_, ci.type_, "constant type must round-trip");
        }
        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn test_snapshot_version_mismatch_falls_back() {
        let dir = std::env::temp_dir().join(format!("clean-snap-ver-{}", std::process::id()));
        let path = dir.join("init.snapshot");
        let env = sample_env();
        // Write with a header carrying a BUMPED (future) snapshot version.
        let mut stale = SnapshotHeader::current("hash-abc");
        stale.snapshot_version = SNAPSHOT_VERSION + 1;
        env.save_snapshot(&path, stale).expect("save must succeed");

        let expected = SnapshotHeader::current("hash-abc");
        let outcome = Environment::load_snapshot(&path, &expected).expect("parse should succeed");
        match outcome {
            SnapshotLoadOutcome::Mismatch(_) => {}
            SnapshotLoadOutcome::Loaded(_) => {
                panic!("version-mismatched snapshot must NOT be reused")
            }
        }
        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn test_snapshot_hash_mismatch_falls_back() {
        let dir = std::env::temp_dir().join(format!("clean-snap-hash-{}", std::process::id()));
        let path = dir.join("init.snapshot");
        let env = sample_env();
        env.save_snapshot(&path, SnapshotHeader::current("hash-OLD"))
            .expect("save must succeed");

        // Same binary, DIFFERENT closure hash => must fall back.
        let expected = SnapshotHeader::current("hash-NEW");
        let outcome = Environment::load_snapshot(&path, &expected).expect("parse should succeed");
        assert!(
            matches!(outcome, SnapshotLoadOutcome::Mismatch(_)),
            "closure-hash mismatch must NOT be reused"
        );
        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn test_snapshot_fingerprint_mismatch_falls_back() {
        let dir = std::env::temp_dir().join(format!("clean-snap-fp-{}", std::process::id()));
        let path = dir.join("init.snapshot");
        let env = sample_env();
        let mut stale = SnapshotHeader::current("hash-abc");
        stale.env_schema_fingerprint = "clean-env-bincode-OLD".to_string();
        env.save_snapshot(&path, stale).expect("save must succeed");

        let expected = SnapshotHeader::current("hash-abc");
        let outcome = Environment::load_snapshot(&path, &expected).expect("parse should succeed");
        assert!(
            matches!(outcome, SnapshotLoadOutcome::Mismatch(_)),
            "schema-fingerprint mismatch must NOT be reused"
        );
        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn test_snapshot_corrupt_data_errors() {
        // Mirror test_from_bincode_corrupt_data: random/empty bytes must error,
        // which the caller treats as a cache miss (full load).
        let dir = std::env::temp_dir().join(format!("clean-snap-corrupt-{}", std::process::id()));
        let path = dir.join("init.snapshot");
        std::fs::create_dir_all(&dir).expect("mkdir");
        std::fs::write(&path, [0u8, 1, 2, 3, 255, 128]).expect("write corrupt");

        let expected = SnapshotHeader::current("hash-abc");
        let result = Environment::load_snapshot(&path, &expected);
        assert!(
            result.is_err(),
            "corrupt snapshot bytes must error (caller full-loads)"
        );
        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn test_snapshot_header_current_fields() {
        let h = SnapshotHeader::current("xyz");
        assert_eq!(h.snapshot_version, SNAPSHOT_VERSION);
        assert_eq!(h.env_schema_fingerprint, ENV_SCHEMA_FINGERPRINT);
        assert_eq!(h.kernel_format_version, crate::VERSION);
        assert_eq!(h.init_closure_blake3, "xyz");
    }
}
