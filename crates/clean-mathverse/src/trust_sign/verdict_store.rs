// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Read-only store over a re-auditor output directory.
//!
//! The re-auditor ([`super::reauditor`], via the `mathverse_reauditor` binary)
//! writes one signed [`SignedVerdict`] per declaration into `<out>/verdicts/`
//! plus an optional signed [`RevocationList`] at `<out>/revocation-list.json`.
//! This store loads that directory once and answers the Phase-2 read endpoints:
//!
//! - `/verdict/{name}` — the SIGNED provenance record for a declaration (or a
//!   "not re-audited" miss), tagged with whether the claim is revoked.
//! - `/audit` — the aggregate summary (how many examined, how many carry a
//!   `KernelVerified` signed verdict, how many are revoked).
//!
//! # The honesty contract (do not blur it)
//!
//! What this store serves is **attestable provenance**, not correctness. A
//! [`SignedVerdict`] says "verifier X re-ran its kernel over this de Bruijn
//! `expr_canonical_digest` and observed `KernelVerified`, foundational-only".
//! The independently-re-verifiable TRUTH stays the digest: a consumer re-runs
//! the open kernel over the shard constant and re-earns the green itself. The
//! store NEVER mints, upgrades, or alters a verdict — it only reads what the
//! re-auditor signed and reports revocation. Loading enforces the structural
//! invariants ([`SignedVerdict::check_invariants`]), so a malformed on-disk
//! record is dropped rather than served as if trustworthy (fail-closed).

use std::collections::HashMap;
use std::path::{Path, PathBuf};

use serde_json::{json, Value};

use super::revocation::RevocationList;
use super::signed_verdict::{SignedVerdict, SignedVerdictKind};

/// One loaded, structurally-valid signed verdict plus its revocation status.
#[derive(Clone, Debug)]
pub struct StoredVerdict {
    /// The signed provenance record (schema `mathverse-signed-verdict-v1`).
    pub signed: SignedVerdict,
    /// `true` iff this claim's digest appears in the loaded revocation list.
    /// A revoked record's badge is stripped even if it was once `KernelVerified`.
    pub revoked: bool,
}

impl StoredVerdict {
    /// `true` iff the record carries a live (non-revoked) `KernelVerified`
    /// signed verdict.
    #[must_use]
    pub fn is_live_kernel_verified(&self) -> bool {
        !self.revoked && self.signed.verdict == SignedVerdictKind::KernelVerified
    }

    /// The honest, badge-aware verdict label served to a consumer: `Revoked`
    /// overrides the signed verdict kind once the claim is in the revocation
    /// list (the badge changes; the digest stays the re-verifiable truth).
    #[must_use]
    pub fn effective_verdict(&self) -> SignedVerdictKind {
        if self.revoked {
            SignedVerdictKind::Revoked
        } else {
            self.signed.verdict
        }
    }
}

/// A read-only index over a re-auditor output directory.
///
/// Built once at service startup (or empty when no verdict directory is
/// configured). All lookups are in-memory.
#[derive(Debug, Default)]
pub struct VerdictStore {
    /// Verdicts keyed by declaration name (last writer wins on a name clash;
    /// the re-auditor writes one file per constant so clashes are not expected).
    by_name: HashMap<String, StoredVerdict>,
    /// The loaded, signed revocation list (if `revocation-list.json` was found).
    /// Retained so `/audit` can report its provenance.
    revocation: Option<RevocationList>,
    /// The directory the store was loaded from (for diagnostics).
    dir: Option<PathBuf>,
}

impl VerdictStore {
    /// An empty store — what the service uses when no verdict directory is
    /// configured. `/verdict` then answers "not re-audited" and `/audit`
    /// reports zero re-audited declarations.
    #[must_use]
    pub fn empty() -> Self {
        Self::default()
    }

    /// Load every `*.json` signed verdict under `<dir>/verdicts/` (falling back
    /// to `<dir>` itself if there is no `verdicts/` subdirectory) and, if
    /// present, the signed `<dir>/revocation-list.json`.
    ///
    /// A file that does not parse as a `SignedVerdict`, or that fails the
    /// signed-verdict structural invariants, is SKIPPED (fail-closed: we never
    /// serve a malformed record as if it were a valid provenance attestation).
    /// The revocation list is parsed structurally; its signature is verified by
    /// the consumer against the published public key, not here.
    ///
    /// # Errors
    /// Returns the directory-read error only when the verdict directory itself
    /// cannot be enumerated; per-file parse failures are skipped, not fatal.
    pub fn load(dir: impl AsRef<Path>) -> std::io::Result<Self> {
        let dir = dir.as_ref().to_path_buf();
        let verdicts_dir = {
            let nested = dir.join("verdicts");
            if nested.is_dir() {
                nested
            } else {
                dir.clone()
            }
        };

        let mut by_name = HashMap::new();
        let revocation = load_revocation_list(&dir);

        for entry in std::fs::read_dir(&verdicts_dir)? {
            let entry = entry?;
            let path = entry.path();
            if path.extension().is_some_and(|e| e == "json")
                && path
                    .file_name()
                    .is_some_and(|n| n != "revocation-list.json")
            {
                if let Some(signed) = load_signed_verdict(&path) {
                    let revoked = revocation
                        .as_ref()
                        .is_some_and(|rl| rl.is_revoked(&signed.expr_canonical_digest));
                    by_name.insert(signed.name.clone(), StoredVerdict { signed, revoked });
                }
            }
        }

        Ok(Self {
            by_name,
            revocation,
            dir: Some(dir),
        })
    }

    /// Number of declarations with a loaded signed verdict (any kind).
    #[must_use]
    pub fn examined(&self) -> usize {
        self.by_name.len()
    }

    /// Look up the stored verdict for `name`, or `None` if the declaration was
    /// not re-audited (no signed record on disk).
    #[must_use]
    pub fn get(&self, name: &str) -> Option<&StoredVerdict> {
        self.by_name.get(name)
    }

    /// `true` iff a verdict directory was configured and loaded (even if empty).
    /// When `false`, the endpoints report "re-audit data not loaded".
    #[must_use]
    pub fn is_loaded(&self) -> bool {
        self.dir.is_some()
    }

    // -- /verdict/{name} ---------------------------------------------------

    /// The signed-verdict JSON payload for `name`, or `None` for a miss (the
    /// HTTP layer answers 404 / "not re-audited"). The payload restates the
    /// honesty contract: the signature is provenance; the digest is the truth.
    #[must_use]
    pub fn verdict_json(&self, name: &str) -> Option<Value> {
        let stored = self.get(name)?;
        Some(json!({
            "name": stored.signed.name,
            "verdict": effective_verdict_label(stored),
            "revoked": stored.revoked,
            "foundational": stored.signed.foundational,
            "expr_canonical_digest": stored.signed.expr_canonical_digest,
            "proof_canonical_digest": stored.signed.proof_canonical_digest,
            "axiom_closure": stored.signed.axiom_closure,
            "verifier": {
                "clean_version": stored.signed.verifier.clean_version,
                "clean_commit": stored.signed.verifier.clean_commit,
                "tcb_axioms": stored.signed.verifier.tcb_axioms,
            },
            "verified_at": stored.signed.verified_at,
            "signature": {
                "key_id": stored.signed.key_id,
                "sig_alg": stored.signed.sig_alg,
                "value": stored.signed.signature,
            },
            // The full signed record, verbatim, so a consumer can recompute the
            // canonical bytes and verify the signature offline against the
            // published public key.
            "signed_record": signed_record_value(&stored.signed),
            "trust_note": VERDICT_TRUST_NOTE,
        }))
    }

    // -- /audit ------------------------------------------------------------

    /// The aggregate re-audit summary: how many declarations were re-audited,
    /// how many carry a live `KernelVerified` signed verdict, how many are
    /// revoked, plus the revocation-list provenance.
    #[must_use]
    pub fn audit_json(&self) -> Value {
        if !self.is_loaded() {
            return json!({
                "reaudited": false,
                "reason": "no verdict directory configured (set $MATHVERSE_VERDICTS_DIR); \
                           this service serves stored provenance, not a live re-audit",
                "trust_note": VERDICT_TRUST_NOTE,
            });
        }

        let mut kernel_verified = 0usize;
        let mut rejected = 0usize;
        let mut revoked = 0usize;
        for stored in self.by_name.values() {
            if stored.revoked {
                revoked += 1;
            } else if stored.signed.verdict == SignedVerdictKind::KernelVerified {
                kernel_verified += 1;
            } else {
                rejected += 1;
            }
        }

        let revocation = self.revocation.as_ref().map(|rl| {
            json!({
                "schema": rl.schema,
                "issued_at": rl.issued_at,
                "key_id": rl.key_id,
                "sig_alg": rl.sig_alg,
                "entries": rl.revocations.len(),
            })
        });

        json!({
            "reaudited": true,
            "examined": self.examined(),
            "signed_kernel_verified": kernel_verified,
            "rejected": rejected,
            "revoked": revoked,
            "revocation_list": revocation,
            "trust_note": VERDICT_TRUST_NOTE,
        })
    }
}

/// The honesty note attached to every verdict/audit payload: the signature is
/// attestable provenance; the de Bruijn digest is the independently
/// re-verifiable truth.
pub const VERDICT_TRUST_NOTE: &str =
    "A signed verdict attests PROVENANCE: a named verifier, at a pinned Clean \
     version with tcb_axioms=3, re-ran its kernel over this expr_canonical_digest \
     and observed this result. It is NOT a correctness oracle. Correctness stays \
     independently re-verifiable: re-run the open Clean kernel over the shard \
     constant matching expr_canonical_digest (de Bruijn) and re-earn the green \
     yourself. A revoked claim's badge is stripped; the digest is unchanged.";

/// The badge-aware verdict label (`Revoked` overrides the signed kind once the
/// claim is in the revocation list).
fn effective_verdict_label(stored: &StoredVerdict) -> &'static str {
    match stored.effective_verdict() {
        SignedVerdictKind::KernelVerified => "KernelVerified",
        SignedVerdictKind::Rejected => "Rejected",
        SignedVerdictKind::Revoked => "Revoked",
    }
}

/// Serialize the signed record verbatim for offline re-verification. Falls back
/// to a diagnostic object if (impossibly) serialization fails, never panicking.
fn signed_record_value(signed: &SignedVerdict) -> Value {
    serde_json::to_value(signed)
        .unwrap_or_else(|e| json!({ "error": format!("could not serialize signed record: {e}") }))
}

/// Parse and structurally-validate one signed verdict file. Returns `None`
/// (skipped) on any parse error or invariant violation — fail-closed.
fn load_signed_verdict(path: &Path) -> Option<SignedVerdict> {
    let bytes = std::fs::read(path).ok()?;
    let signed: SignedVerdict = serde_json::from_slice(&bytes).ok()?;
    // A record that violates the signed-verdict structural invariants (e.g. a
    // KernelVerified with a non-empty closure, or a wrong tcb_axioms) is NOT
    // served — it would be a malformed provenance claim.
    signed.check_invariants().ok()?;
    Some(signed)
}

/// Load the signed revocation list at `<dir>/revocation-list.json`, if present
/// and parseable. A missing or malformed list yields `None` (no revocations
/// applied); the list's signature is verified by the consumer, not here.
fn load_revocation_list(dir: &Path) -> Option<RevocationList> {
    let path = dir.join("revocation-list.json");
    let bytes = std::fs::read(path).ok()?;
    serde_json::from_slice(&bytes).ok()
}

#[cfg(test)]
#[path = "verdict_store_tests.rs"]
mod tests;
