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
//!   The kernel cannot *check* that claim (it does not record per-run
//!   re-verify provenance), but since R1-SNAP (2026-08-25) it *binds* it: the
//!   caller passes a [`SnapshotAttestation`] describing the re-verification
//!   that just succeeded, and `save_snapshot` seals it into a
//!   [`SnapshotReceipt`] whose `env_content_sha256` is computed by the kernel
//!   over the exact serialized environment bytes being stored. The receipt is
//!   content-derived: no timestamp or other ambient state enters the binding
//!   hash. See the call site in `clean-olean`'s `preload_init_with_snapshot`,
//!   which attests only after a `--full-validation` re-check succeeded.
//! - **REUSE** ([`Environment::load_snapshot`]) is gated on (1) an EXACT match
//!   of every header gate field against the current run — ANY mismatch
//!   (snapshot version, kernel format version, env schema fingerprint, or
//!   Init closure hash) yields [`SnapshotLoadOutcome::Mismatch`] — and (2) a
//!   present, content-bound verification receipt: a snapshot whose receipt is
//!   absent, or whose recorded `env_content_sha256` does not match the stored
//!   environment bytes, yields [`SnapshotLoadOutcome::ReceiptRefused`] under
//!   the default [`SnapshotReceiptPolicy::RequireReceipt`]. The caller MUST
//!   then fall back to a full re-verify. The only way past the receipt gate
//!   is the explicit, loud opt-out
//!   [`SnapshotReceiptPolicy::AcceptUnreceipted`], which still reports the
//!   violation in its [`SnapshotLoadOutcome::LoadedUnreceipted`] outcome and
//!   is ledgered as the guard on this door in `data/env_bypass_census.json`
//!   (row `env-snapshot-restore`).
//! - The deserialized environment is byte-for-byte the env that was written:
//!   bincode round-trips the full [`Environment`] (all `*_init` flags,
//!   inductives, constructors, recursors). It is therefore identical to a
//!   fresh re-verified env (see the equality test).
//!
//! The residual trust after R1-SNAP is exactly the attestation's honesty: the
//! receipt proves "a writer CLAIMED this re-verification over EXACTLY these
//! bytes", not that the claim was true. What the gate removes is every silent
//! path — a snapshot written without any re-verification claim, a receipt
//! recycled from a different environment image, or tampered environment bytes
//! under an old receipt all refuse by default.
//!
//! The header carries the data needed to detect every way the cached bytes
//! could become stale relative to the current binary + inputs.

use serde::{Deserialize, Serialize};

use super::Environment;

/// Snapshot container format version. Bump when the *header* layout changes.
///
/// v2 (2026-08-25, R1-SNAP): the header gained the `receipt` field. v1
/// snapshots fail bincode decode (or the version gate) and are treated as a
/// cache miss — the caller full-loads, fail safe.
pub const SNAPSHOT_VERSION: u32 = 2;

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

/// The writer's claim about the re-verification that preceded a snapshot
/// write: *what* was re-verified, *how much* passed, and *when*.
///
/// This is an attestation, not a proof — the kernel cannot re-run the
/// verifying pass at load time. What the kernel adds on top is the content
/// binding: [`Environment::save_snapshot`] seals this claim into a
/// [`SnapshotReceipt`] whose digest it computes itself over the exact
/// environment bytes stored, so the claim can never drift to a different
/// environment image without detection.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SnapshotAttestation {
    /// What was re-verified, named precisely (e.g.
    /// `"typecheck_constants_full: add_decl-equivalent re-verify of the Init
    /// closure"`). A claim a reader can locate in source, not a mood.
    pub scope: String,
    /// How many declarations passed the re-check in the verifying run.
    pub decls_verified: u64,
    /// When the verifying run happened — diagnostic ONLY. This field is
    /// deliberately NOT part of the binding: the binding hash is computed over
    /// the environment content alone, so two writes of the same re-verified
    /// env bind identically regardless of wall clock.
    pub verified_at: String,
}

/// A digest-bound verification receipt, stored inside the snapshot header.
///
/// Minted exclusively by [`Environment::save_snapshot`]: the caller supplies
/// the [`SnapshotAttestation`]; the kernel computes `env_content_sha256` over
/// the exact serialized environment bytes it writes. Any receipt value the
/// caller pre-places in a header is discarded, never trusted.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SnapshotReceipt {
    /// The writer's claim (what was re-verified, how much, when).
    pub attestation: SnapshotAttestation,
    /// SHA-256 (lowercase hex) of the serialized environment bytes this
    /// receipt speaks for. Content-derived: nothing but the env bytes enters
    /// the hash. [`Environment::load_snapshot`] recomputes it over the stored
    /// bytes and refuses on mismatch.
    pub env_content_sha256: String,
}

/// Versioned header prepended to a snapshot.
///
/// The four *gate fields* (`snapshot_version`, `kernel_format_version`,
/// `env_schema_fingerprint`, `init_closure_blake3`) form the staleness gate:
/// the snapshot is reused IFF all four match the current run. The `receipt`
/// field is NOT part of that equality gate — it has its own dedicated gate
/// (see [`SnapshotReceiptPolicy`]) because the loader's `expected` header
/// cannot know the receipt in advance.
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
    /// The verification receipt binding this snapshot to the re-verification
    /// that produced it. Written by [`Environment::save_snapshot`] (never by
    /// the caller directly); `None` marks a deliberately unreceipted snapshot,
    /// which [`Environment::load_snapshot`] refuses by default.
    pub receipt: Option<SnapshotReceipt>,
}

impl SnapshotHeader {
    /// Construct a header for the CURRENT binary, tagged with the caller's
    /// `init_closure_blake3` closure hash. The receipt is `None` here — it is
    /// minted by [`Environment::save_snapshot`] from the caller's
    /// [`SnapshotAttestation`] at write time.
    #[must_use]
    pub fn current(init_closure_blake3: impl Into<String>) -> Self {
        Self {
            snapshot_version: SNAPSHOT_VERSION,
            kernel_format_version: crate::VERSION.to_string(),
            env_schema_fingerprint: ENV_SCHEMA_FINGERPRINT.to_string(),
            init_closure_blake3: init_closure_blake3.into(),
            receipt: None,
        }
    }

    /// Whether this (deserialized) header is reusable by a run whose current
    /// header is `current`. Reuse requires an EXACT match of all four gate
    /// fields. The receipt is deliberately excluded: the loader's `expected`
    /// header cannot know it, and it is enforced by the separate receipt gate
    /// in [`Environment::load_snapshot`].
    #[must_use]
    pub fn matches(&self, current: &SnapshotHeader) -> bool {
        self.snapshot_version == current.snapshot_version
            && self.kernel_format_version == current.kernel_format_version
            && self.env_schema_fingerprint == current.env_schema_fingerprint
            && self.init_closure_blake3 == current.init_closure_blake3
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

/// Receipt gate policy for [`Environment::load_snapshot`].
///
/// An enum rather than a bool so every call site names its intent
/// (`RequireReceipt` is the only production policy; the opt-out is the
/// ledgered guard on this door — census row `env-snapshot-restore`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SnapshotReceiptPolicy {
    /// Default, fail-closed: refuse a snapshot whose verification receipt is
    /// absent or does not bind to the stored environment bytes
    /// ([`SnapshotLoadOutcome::ReceiptRefused`]).
    RequireReceipt,
    /// Explicit opt-out: restore the environment DESPITE a missing or
    /// non-binding receipt. Deliberately loud — the outcome is
    /// [`SnapshotLoadOutcome::LoadedUnreceipted`], carrying the violation, so
    /// a caller cannot take this path and stay silent about it. No production
    /// caller uses this; it exists for forensics/migration and is ledgered as
    /// the guard in `data/env_bypass_census.json`.
    AcceptUnreceipted,
}

/// Why the receipt gate refused (or, under the opt-out, would have refused).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SnapshotReceiptViolation {
    /// The stored header carries no receipt at all: nothing ever attested that
    /// this snapshot was written after a successful re-verification.
    Absent,
    /// The receipt's recorded content digest does not match the environment
    /// bytes actually stored — tampered bytes, a truncated/reassembled file,
    /// or a receipt recycled from a different environment image.
    ContentMismatch {
        /// The digest recorded in the receipt.
        recorded: String,
        /// The digest recomputed over the stored env bytes.
        actual: String,
    },
}

impl std::fmt::Display for SnapshotReceiptViolation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SnapshotReceiptViolation::Absent => {
                write!(f, "verification receipt absent (unreceipted snapshot)")
            }
            SnapshotReceiptViolation::ContentMismatch { recorded, actual } => write!(
                f,
                "verification receipt does not bind to the stored env bytes \
                 (recorded {recorded}, actual {actual})"
            ),
        }
    }
}

/// Result of attempting to load + gate a snapshot.
#[derive(Debug)]
pub enum SnapshotLoadOutcome {
    /// Header gate and receipt gate both passed; the environment was restored.
    Loaded(Box<Environment>),
    /// The snapshot file parsed but its header did not match the current run.
    /// The caller MUST fall back to a full re-verify. The mismatched header is
    /// returned for diagnostics.
    Mismatch(Box<SnapshotHeader>),
    /// The header gate matched, but the verification receipt is absent or does
    /// not bind to the stored environment bytes, and the policy is
    /// [`SnapshotReceiptPolicy::RequireReceipt`]. The environment was NOT
    /// deserialized. The caller MUST fall back to a full re-verify.
    ReceiptRefused {
        /// The stored header, for diagnostics.
        header: Box<SnapshotHeader>,
        /// What the receipt gate found.
        violation: SnapshotReceiptViolation,
    },
    /// The [`SnapshotReceiptPolicy::AcceptUnreceipted`] opt-out took effect:
    /// the environment was restored DESPITE the reported receipt violation.
    /// Loud by construction — the violation rides in the outcome and the
    /// caller is responsible for surfacing it.
    LoadedUnreceipted {
        /// The restored environment.
        env: Box<Environment>,
        /// The violation the opt-out overrode.
        violation: SnapshotReceiptViolation,
    },
}

/// SHA-256 of `bytes` as lowercase hex. The receipt's binding digest:
/// content in, digest out — no other inputs.
fn sha256_hex(bytes: &[u8]) -> String {
    use sha2::{Digest, Sha256};
    let mut hasher = Sha256::new();
    hasher.update(bytes);
    hasher
        .finalize()
        .iter()
        .map(|b| format!("{b:02x}"))
        .collect()
}

/// Check `header`'s receipt against the stored `env_bytes`. `None` means the
/// receipt is present and binds.
fn receipt_violation(
    header: &SnapshotHeader,
    env_bytes: &[u8],
) -> Option<SnapshotReceiptViolation> {
    let Some(receipt) = &header.receipt else {
        return Some(SnapshotReceiptViolation::Absent);
    };
    let actual = sha256_hex(env_bytes);
    if receipt.env_content_sha256 != actual {
        return Some(SnapshotReceiptViolation::ContentMismatch {
            recorded: receipt.env_content_sha256.clone(),
            actual,
        });
    }
    None
}

impl Environment {
    /// Write a versioned snapshot of this environment to `path`.
    ///
    /// SOUNDNESS: callers MUST only invoke this on an environment whose
    /// constants were `add_decl`-re-verified in the current run (never a
    /// load-only / infer-only environment), and MUST say so through
    /// `attestation`: the claim is sealed into a [`SnapshotReceipt`] whose
    /// content digest this method computes over the exact bytes written, and
    /// [`Environment::load_snapshot`] refuses receipt-less snapshots by
    /// default. Passing `None` writes a deliberately unreceipted snapshot
    /// (test/forensics only) that the default load policy will refuse.
    ///
    /// Any `receipt` value already present in `header` is REPLACED (from
    /// `attestation`, or cleared to `None`) — a receipt is only ever minted
    /// here, over bytes this method serialized itself.
    ///
    /// `header` should be [`SnapshotHeader::current`] tagged with the closure
    /// hash of the inputs that produced this environment.
    pub fn save_snapshot(
        &self,
        path: &std::path::Path,
        header: SnapshotHeader,
        attestation: Option<&SnapshotAttestation>,
    ) -> Result<(), SnapshotError> {
        let env_bytes = self.to_bincode()?;
        let mut header = header;
        header.receipt = attestation.map(|attestation| SnapshotReceipt {
            attestation: attestation.clone(),
            env_content_sha256: sha256_hex(&env_bytes),
        });
        let file = SnapshotFile { header, env_bytes };
        let bytes = bincode::serde::encode_to_vec(&file, bincode::config::standard())?;
        if let Some(parent) = path.parent() {
            std::fs::create_dir_all(parent)?;
        }
        std::fs::write(path, bytes)?;
        Ok(())
    }

    /// Attempt to load a snapshot from `path`, gating reuse on an exact match
    /// of `expected` against the stored header AND on the verification
    /// receipt binding to the stored environment bytes.
    ///
    /// Returns:
    /// - [`SnapshotLoadOutcome::Loaded`] if (and only if) every header gate
    ///   field matches AND the receipt is present and content-bound — the
    ///   environment is restored.
    /// - [`SnapshotLoadOutcome::Mismatch`] if the file parses but the header
    ///   does not match (stale version, fingerprint, or hash). The caller MUST
    ///   then do a full re-verify; the stale snapshot is NOT used.
    /// - [`SnapshotLoadOutcome::ReceiptRefused`] if the header matches but the
    ///   receipt is absent or does not bind, under
    ///   [`SnapshotReceiptPolicy::RequireReceipt`]. The caller MUST then do a
    ///   full re-verify.
    /// - [`SnapshotLoadOutcome::LoadedUnreceipted`] only under the explicit
    ///   [`SnapshotReceiptPolicy::AcceptUnreceipted`] opt-out, carrying the
    ///   violation it overrode.
    /// - `Err` if the file is missing/unreadable or the bytes are corrupt
    ///   (fail safe: treat as a cache miss and full-load).
    pub fn load_snapshot(
        path: &std::path::Path,
        expected: &SnapshotHeader,
        policy: SnapshotReceiptPolicy,
    ) -> Result<SnapshotLoadOutcome, SnapshotError> {
        let bytes = std::fs::read(path)?;
        let (file, _): (SnapshotFile, _) =
            bincode::serde::decode_from_slice(&bytes, bincode::config::standard())?;
        if !file.header.matches(expected) {
            return Ok(SnapshotLoadOutcome::Mismatch(Box::new(file.header)));
        }
        if let Some(violation) = receipt_violation(&file.header, &file.env_bytes) {
            match policy {
                SnapshotReceiptPolicy::RequireReceipt => {
                    return Ok(SnapshotLoadOutcome::ReceiptRefused {
                        header: Box::new(file.header),
                        violation,
                    });
                }
                SnapshotReceiptPolicy::AcceptUnreceipted => {
                    let env = Self::from_bincode(&file.env_bytes)?;
                    return Ok(SnapshotLoadOutcome::LoadedUnreceipted {
                        env: Box::new(env),
                        violation,
                    });
                }
            }
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

    fn sample_attestation() -> SnapshotAttestation {
        SnapshotAttestation {
            scope: "test: add_decl-re-verified sample env".to_string(),
            decls_verified: 2,
            verified_at: "2026-08-25".to_string(),
        }
    }

    #[test]
    fn test_snapshot_roundtrip_loads_identical_env() {
        let dir = std::env::temp_dir().join(format!("clean-snap-{}", std::process::id()));
        let path = dir.join("init.snapshot");
        let env = sample_env();
        let header = SnapshotHeader::current("hash-abc");
        env.save_snapshot(&path, header.clone(), Some(&sample_attestation()))
            .expect("save_snapshot must succeed");

        let outcome =
            Environment::load_snapshot(&path, &header, SnapshotReceiptPolicy::RequireReceipt)
                .expect("load_snapshot must succeed");
        let loaded = match outcome {
            SnapshotLoadOutcome::Loaded(e) => *e,
            other => panic!("identical header + valid receipt must Load, got {other:?}"),
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
        env.save_snapshot(&path, stale, Some(&sample_attestation()))
            .expect("save must succeed");

        let expected = SnapshotHeader::current("hash-abc");
        let outcome =
            Environment::load_snapshot(&path, &expected, SnapshotReceiptPolicy::RequireReceipt)
                .expect("parse should succeed");
        match outcome {
            SnapshotLoadOutcome::Mismatch(_) => {}
            other => panic!("version-mismatched snapshot must NOT be reused, got {other:?}"),
        }
        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn test_snapshot_hash_mismatch_falls_back() {
        let dir = std::env::temp_dir().join(format!("clean-snap-hash-{}", std::process::id()));
        let path = dir.join("init.snapshot");
        let env = sample_env();
        env.save_snapshot(
            &path,
            SnapshotHeader::current("hash-OLD"),
            Some(&sample_attestation()),
        )
        .expect("save must succeed");

        // Same binary, DIFFERENT closure hash => must fall back.
        let expected = SnapshotHeader::current("hash-NEW");
        let outcome =
            Environment::load_snapshot(&path, &expected, SnapshotReceiptPolicy::RequireReceipt)
                .expect("parse should succeed");
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
        env.save_snapshot(&path, stale, Some(&sample_attestation()))
            .expect("save must succeed");

        let expected = SnapshotHeader::current("hash-abc");
        let outcome =
            Environment::load_snapshot(&path, &expected, SnapshotReceiptPolicy::RequireReceipt)
                .expect("parse should succeed");
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
        let result =
            Environment::load_snapshot(&path, &expected, SnapshotReceiptPolicy::RequireReceipt);
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
        assert_eq!(
            h.receipt, None,
            "current() must not mint a receipt — only save_snapshot does"
        );
    }

    // ------------------------------------------------------------------
    // R1-SNAP receipt gate: adversarial arms.
    // ------------------------------------------------------------------

    #[test]
    fn test_receiptless_snapshot_refused_by_default() {
        // A snapshot written WITHOUT an attestation (nothing ever claimed a
        // re-verification happened) must refuse under the default policy.
        let dir = std::env::temp_dir().join(format!("clean-snap-norcpt-{}", std::process::id()));
        let path = dir.join("init.snapshot");
        let env = sample_env();
        let header = SnapshotHeader::current("hash-abc");
        env.save_snapshot(&path, header.clone(), None)
            .expect("save must succeed");

        let outcome =
            Environment::load_snapshot(&path, &header, SnapshotReceiptPolicy::RequireReceipt)
                .expect("parse should succeed");
        match outcome {
            SnapshotLoadOutcome::ReceiptRefused { violation, .. } => {
                assert_eq!(
                    violation,
                    SnapshotReceiptViolation::Absent,
                    "the violation must name the absent receipt"
                );
            }
            other => panic!("receipt-less snapshot must be ReceiptRefused, got {other:?}"),
        }
        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn test_caller_supplied_receipt_is_never_trusted() {
        // A caller pre-placing a receipt in the header (claiming verification
        // it never attested through save_snapshot's parameter) gets it
        // STRIPPED: the stored snapshot is unreceipted and refuses.
        let dir = std::env::temp_dir().join(format!("clean-snap-forge-{}", std::process::id()));
        let path = dir.join("init.snapshot");
        let env = sample_env();
        let mut header = SnapshotHeader::current("hash-abc");
        header.receipt = Some(SnapshotReceipt {
            attestation: sample_attestation(),
            env_content_sha256: "forged-not-computed".to_string(),
        });
        env.save_snapshot(&path, header, None)
            .expect("save must succeed");

        let expected = SnapshotHeader::current("hash-abc");
        let outcome =
            Environment::load_snapshot(&path, &expected, SnapshotReceiptPolicy::RequireReceipt)
                .expect("parse should succeed");
        assert!(
            matches!(
                outcome,
                SnapshotLoadOutcome::ReceiptRefused {
                    violation: SnapshotReceiptViolation::Absent,
                    ..
                }
            ),
            "a pre-placed receipt must be stripped at save (only save_snapshot mints receipts)"
        );
        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn test_tampered_env_content_refused_hash_mismatch() {
        // Splice the RECEIPT of one snapshot onto the ENV BYTES of another —
        // the receipt no longer binds and the load must refuse. This is the
        // "recycled receipt / tampered content" arm: both files are
        // individually well-formed bincode, so only the content binding can
        // catch the swap.
        let dir = std::env::temp_dir().join(format!("clean-snap-tamper-{}", std::process::id()));
        std::fs::create_dir_all(&dir).expect("mkdir");
        let path_a = dir.join("a.snapshot");
        let header = SnapshotHeader::current("hash-abc");

        // Snapshot A: receipted, over sample_env.
        sample_env()
            .save_snapshot(&path_a, header.clone(), Some(&sample_attestation()))
            .expect("save A must succeed");

        // A DIFFERENT env (one extra constant => different bincode bytes).
        let mut other_env = sample_env();
        other_env.add_decl_unchecked(Declaration::Axiom {
            name: Name::from_string("snap_extra"),
            level_params: vec![],
            type_: Expr::prop(),
        });

        // Reassemble: A's receipted header over the OTHER env's bytes.
        let bytes_a = std::fs::read(&path_a).expect("read A");
        let (file_a, _): (SnapshotFile, _) =
            bincode::serde::decode_from_slice(&bytes_a, bincode::config::standard())
                .expect("decode A");
        let spliced = SnapshotFile {
            header: file_a.header,
            env_bytes: other_env.to_bincode().expect("encode other env"),
        };
        let path_spliced = dir.join("spliced.snapshot");
        std::fs::write(
            &path_spliced,
            bincode::serde::encode_to_vec(&spliced, bincode::config::standard())
                .expect("encode spliced"),
        )
        .expect("write spliced");

        let outcome = Environment::load_snapshot(
            &path_spliced,
            &header,
            SnapshotReceiptPolicy::RequireReceipt,
        )
        .expect("parse should succeed");
        match outcome {
            SnapshotLoadOutcome::ReceiptRefused { violation, .. } => match violation {
                SnapshotReceiptViolation::ContentMismatch { recorded, actual } => {
                    assert_ne!(
                        recorded, actual,
                        "the violation must carry both digests, differing"
                    );
                }
                SnapshotReceiptViolation::Absent => {
                    panic!("spliced snapshot has a receipt; violation must be ContentMismatch")
                }
            },
            other => panic!("tampered env content must be ReceiptRefused, got {other:?}"),
        }
        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn test_opt_out_loads_and_is_loud() {
        // The explicit AcceptUnreceipted opt-out restores the env BUT the
        // outcome carries the violation — the caller cannot take this path
        // silently.
        let dir = std::env::temp_dir().join(format!("clean-snap-optout-{}", std::process::id()));
        let path = dir.join("init.snapshot");
        let env = sample_env();
        let header = SnapshotHeader::current("hash-abc");
        env.save_snapshot(&path, header.clone(), None)
            .expect("save must succeed");

        let outcome =
            Environment::load_snapshot(&path, &header, SnapshotReceiptPolicy::AcceptUnreceipted)
                .expect("parse should succeed");
        match outcome {
            SnapshotLoadOutcome::LoadedUnreceipted {
                env: loaded,
                violation,
            } => {
                assert_eq!(
                    violation,
                    SnapshotReceiptViolation::Absent,
                    "the opt-out outcome must still report the violation"
                );
                assert_eq!(
                    loaded.constants().count(),
                    sample_env().constants().count(),
                    "the opt-out must actually restore the env"
                );
            }
            other => {
                panic!("opt-out on a receipt-less snapshot must LoadedUnreceipted, got {other:?}")
            }
        }
        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn test_receipted_snapshot_receipt_content_is_bound_and_recorded() {
        // The happy-path receipt: minted by save_snapshot, digest over the
        // exact stored bytes, attestation carried verbatim.
        let dir = std::env::temp_dir().join(format!("clean-snap-rcpt-{}", std::process::id()));
        let path = dir.join("init.snapshot");
        let env = sample_env();
        let header = SnapshotHeader::current("hash-abc");
        let attestation = sample_attestation();
        env.save_snapshot(&path, header, Some(&attestation))
            .expect("save must succeed");

        let bytes = std::fs::read(&path).expect("read snapshot");
        let (file, _): (SnapshotFile, _) =
            bincode::serde::decode_from_slice(&bytes, bincode::config::standard())
                .expect("decode snapshot");
        let receipt = file.header.receipt.expect("receipt must be present");
        assert_eq!(receipt.attestation, attestation, "attestation verbatim");
        assert_eq!(
            receipt.env_content_sha256,
            sha256_hex(&file.env_bytes),
            "the binding digest must be the digest of the stored env bytes \
             (content-derived, nothing else)"
        );
        let _ = std::fs::remove_dir_all(&dir);
    }
}
