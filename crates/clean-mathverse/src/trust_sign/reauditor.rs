// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The re-auditor: re-earn every published `KernelVerified` claim under the
//! CURRENT kernel and emit a signed verdict per declaration (or a
//! `could-not-reverify` verdict, honestly, when it does not re-earn).
//!
//! # What it does (and what it must never do)
//!
//! For a Core (a directory of `SourceSystem::Cake` shards, each beside its
//! digest-bound graduation record), the re-auditor, per shard:
//!
//! 1. runs the EXISTING fail-closed re-earner
//!    `shard_verify::cake_gate::verify_cake_shard` under the live kernel commit
//!    (clauses 1-2: digest binding, provenance, decl-kind, sorry, axiom-profile,
//!    record self-consistency; clause 3: the per-constant kernel replay +
//!    foundational-only axiom walk). This is the shard-level trust gate — it is
//!    NOT re-implemented here.
//! 2. for each value-bearing theorem constant, RECONSTRUCTS its declaration from
//!    the shard ([`crate::inductive_replay::reconstruct_constant`]) and runs the
//!    ONE trust verdict in a FRESH kernel environment via the attestation bridge
//!    ([`super::attest`] → `graduate::recheck::recheck_and_classify`). The
//!    bridge computes the de Bruijn statement/proof digests and returns a
//!    [`KernelAttestation`] carrying exactly the facts the kernel produced.
//! 3. builds a [`SignedVerdict`] from that attestation. A constant earns a
//!    `KernelVerified` signed verdict ONLY when BOTH the shard-level gate is
//!    clean (no `verify_cake_shard` violation, and none naming this constant)
//!    AND the per-decl attestation is foundational. Anything else is recorded as
//!    [`ReauditOutcome::CouldNotReverify`] or `Rejected` — **never** signed as
//!    `KernelVerified`.
//!
//! The signer's only legal `KernelVerified` input remains a `KernelAttestation`
//! produced by `recheck_and_classify`. The re-auditor consumes that verdict; it
//! does not fork, weaken, or fast-path it. The signature attests provenance; the
//! digest keeps the claim independently re-verifiable by any consumer.
//!
//! The re-auditor only ever DEMOTES: a claim that no longer re-earns is appended
//! to a signed [`RevocationList`]. It cannot mint a new green for a claim that
//! was not already published — minting is the publisher's separate, privileged
//! job (least privilege).

use std::collections::HashSet;
use std::path::{Path, PathBuf};

use clean_kernel::{Declaration, Environment};

use crate::graduate::record::graduation_record_path;
use crate::inductive_replay::{reconstruct_constant, ReconstructedConstant};
use crate::shard::ShardReader;
use crate::shard_verify::cake_gate::{verify_cake_shard, CakeGateError, CakeGateReport};
use crate::types::DeclKind;

use super::attestation::{attest, AttestError, KernelAttestation};
use super::backend::{SigningBackend, SigningError};
use super::revocation::{RevocationEntry, RevocationList, RevocationReason};
use super::signed_verdict::{SignedVerdict, SignedVerdictKind};

/// Why the re-auditor could not even begin to audit a shard (infrastructure /
/// shard-level failure, before any per-decl verdict). Fail-closed: an unreadable
/// shard or a shard-gate error is an error, never a silent pass.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum ReauditError {
    /// Reading the shard bytes failed.
    #[error("I/O error reading shard {path}: {source}")]
    Io {
        path: PathBuf,
        #[source]
        source: std::io::Error,
    },

    /// The shard bytes could not be parsed.
    #[error("shard read error for {path}: {reason}")]
    ShardRead { path: PathBuf, reason: String },

    /// The shard-level cake gate failed outright (missing record, schema
    /// mismatch, digest mismatch, decode error). The whole shard is untrusted.
    #[error("cake gate error for {path}: {source}")]
    CakeGate {
        path: PathBuf,
        #[source]
        source: CakeGateError,
    },

    /// Signing a produced verdict failed (key/primitive error). Treated as a
    /// hard error rather than emitting an unsigned record.
    #[error("signing error for `{name}`: {source}")]
    Signing {
        name: String,
        #[source]
        source: SigningError,
    },
}

/// The per-declaration outcome of a re-audit.
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum ReauditOutcome {
    /// The constant re-earned `KernelVerified` (shard gate clean for it AND the
    /// fresh-env attestation foundational): a valid signed `KernelVerified`
    /// verdict.
    KernelVerified,
    /// The constant re-checked but its closure is not foundational-only (an
    /// axiom was demoted out of the foundational set). Signed as `Rejected`;
    /// a previously-published green is revoked `now-axiom-dependent`.
    AxiomDependent,
    /// The constant could not be re-verified: reconstruction failed, the kernel
    /// rejected it, or the shard-level gate flagged it. NEVER signed as
    /// `KernelVerified`; a previously-published green is revoked
    /// `no-longer-verifies`.
    CouldNotReverify(String),
}

impl ReauditOutcome {
    /// `true` iff this outcome warrants a `KernelVerified` signed verdict.
    #[must_use]
    pub fn is_kernel_verified(&self) -> bool {
        matches!(self, Self::KernelVerified)
    }
}

/// One declaration's re-audit verdict record: the signed verdict plus the
/// classified outcome.
#[derive(Clone, Debug)]
pub struct ReauditVerdict {
    /// Declaration name.
    pub name: String,
    /// The classified outcome (drives signing kind + revocation).
    pub outcome: ReauditOutcome,
    /// The signed verdict record (schema v1). Its `verdict` is
    /// `KernelVerified` only when `outcome.is_kernel_verified()`.
    pub signed: SignedVerdict,
}

/// The aggregate result of re-auditing a shard (or a Core).
#[derive(Clone, Debug, Default)]
pub struct ReauditReport {
    /// Per-declaration signed verdicts (in shard order).
    pub verdicts: Vec<ReauditVerdict>,
    /// Number of value-bearing theorem constants examined.
    pub examined: usize,
    /// Number that re-earned `KernelVerified`.
    pub reverified: usize,
}

impl ReauditReport {
    /// Number that did NOT re-earn `KernelVerified` (axiom-dependent or
    /// could-not-reverify).
    #[must_use]
    pub fn demoted(&self) -> usize {
        self.examined.saturating_sub(self.reverified)
    }

    /// Append a signed revocation entry to `list` for every verdict that did not
    /// re-earn `KernelVerified`. Monotone (a digest already revoked is a no-op).
    /// `now` is the RFC-3339 UTC timestamp; `clean_commit` the live commit.
    pub fn append_revocations(
        &self,
        list: &mut RevocationList,
        now: &str,
        clean_commit: &str,
    ) -> usize {
        let mut appended = 0;
        for v in &self.verdicts {
            let (reason, detail) = match &v.outcome {
                ReauditOutcome::KernelVerified => continue,
                ReauditOutcome::AxiomDependent => (
                    RevocationReason::NowAxiomDependent,
                    format!("closure: {}", v.signed.axiom_closure.join(", ")),
                ),
                ReauditOutcome::CouldNotReverify(why) => {
                    (RevocationReason::NoLongerVerifies, why.clone())
                }
            };
            let entry = RevocationEntry {
                expr_canonical_digest: v.signed.expr_canonical_digest.clone(),
                name: v.name.clone(),
                revoked_at: now.to_string(),
                reason,
                detail,
                clean_commit_at_revocation: clean_commit.to_string(),
            };
            if list.revoke(entry) {
                appended += 1;
            }
        }
        appended
    }
}

/// Re-audit a single Cake shard and emit a signed verdict per value-bearing
/// theorem constant.
///
/// `verified_at` is the RFC-3339 UTC timestamp stamped into each verdict;
/// `clean_commit` is the live Clean commit recorded in the attestation.
///
/// # Errors
///
/// Returns [`ReauditError`] for shard-level / infrastructure failures (the whole
/// shard is untrusted); per-declaration failures are recorded as
/// [`ReauditOutcome::CouldNotReverify`], not errors.
pub fn reaudit_shard(
    path: &Path,
    backend: &dyn SigningBackend,
    clean_commit: &str,
    verified_at: &str,
) -> Result<ReauditReport, ReauditError> {
    let shard_bytes = std::fs::read(path).map_err(|source| ReauditError::Io {
        path: path.to_path_buf(),
        source,
    })?;
    let reader = ShardReader::from_bytes(&shard_bytes).map_err(|e| ReauditError::ShardRead {
        path: path.to_path_buf(),
        reason: e.to_string(),
    })?;

    // The EXISTING fail-closed re-earner under the current kernel commit. A
    // shard-level error (missing/tampered record, schema/digest mismatch) means
    // the whole shard is untrusted — fail closed.
    let gate = verify_cake_shard(path).map_err(|source| ReauditError::CakeGate {
        path: path.to_path_buf(),
        source,
    })?;
    let gate_clean = gate.is_clean();
    let flagged = flagged_names(&gate);

    let mut report = ReauditReport::default();
    for header in &reader.constants {
        // Only value-bearing theorems carry a proof term to re-verify. Carried
        // definitions / inductive-family members are gate-checked above but have
        // no standalone proof verdict to sign here.
        let Ok(DeclKind::Theorem) = header.decl_kind() else {
            continue;
        };
        if !header.has_value() {
            continue;
        }
        let Some(name) = reader.strings.get(header.name_idx as usize).cloned() else {
            continue;
        };
        report.examined += 1;

        let verdict = reaudit_one(
            &reader,
            header,
            &name,
            gate_clean,
            &flagged,
            backend,
            clean_commit,
            verified_at,
        )?;
        if verdict.outcome.is_kernel_verified() {
            report.reverified += 1;
        }
        report.verdicts.push(verdict);
    }
    Ok(report)
}

/// Re-audit every Cake shard under `dir` (a Core), aggregating verdicts.
///
/// # Errors
///
/// Propagates the first shard-level [`ReauditError`]; per-declaration failures
/// are recorded, not propagated.
pub fn reaudit_core(
    dir: &Path,
    backend: &dyn SigningBackend,
    clean_commit: &str,
    verified_at: &str,
) -> Result<ReauditReport, ReauditError> {
    let mut shard_paths = Vec::new();
    collect_cake_shards(dir, &mut shard_paths)?;
    shard_paths.sort();

    let mut report = ReauditReport::default();
    for path in shard_paths {
        let shard_report = reaudit_shard(&path, backend, clean_commit, verified_at)?;
        report.examined += shard_report.examined;
        report.reverified += shard_report.reverified;
        report.verdicts.extend(shard_report.verdicts);
    }
    Ok(report)
}

/// Re-audit one reconstructed theorem constant, returning its signed verdict.
#[allow(clippy::too_many_arguments)]
fn reaudit_one(
    reader: &ShardReader,
    header: &crate::types::MathverseConstantHeader,
    name: &str,
    gate_clean: bool,
    flagged: &HashSet<String>,
    backend: &dyn SigningBackend,
    clean_commit: &str,
    verified_at: &str,
) -> Result<ReauditVerdict, ReauditError> {
    // 1. Reconstruct the declaration from the shard. A reconstruction failure is
    //    handled honestly: could-not-reverify, never signed as KernelVerified.
    let recon = match reconstruct_constant(name, reader, header) {
        Ok(r) => r,
        Err(e) => {
            return sign_outcome(
                name,
                // No reconstructed term to digest; the attestation step is
                // skipped, so we synthesize a non-foundational placeholder
                // attestation that signs as Rejected (could-not-reverify).
                None,
                ReauditOutcome::CouldNotReverify(format!("reconstruct failed: {e}")),
                backend,
                clean_commit,
                verified_at,
            );
        }
    };

    // 2. Run the ONE trust verdict in a FRESH kernel environment via the
    //    attestation bridge (recheck_and_classify). A kernel rejection is a
    //    could-not-reverify; a successful-but-non-foundational closure is
    //    axiom-dependent.
    let mut env = Environment::new();
    let decl = reconstructed_to_decl(&recon);
    let att = match attest(&mut env, decl, clean_commit) {
        Ok(att) => att,
        Err(AttestError::Recheck(e)) => {
            return sign_outcome(
                name,
                None,
                ReauditOutcome::CouldNotReverify(format!("kernel re-check: {e}")),
                backend,
                clean_commit,
                verified_at,
            );
        }
        Err(other) => {
            return sign_outcome(
                name,
                None,
                ReauditOutcome::CouldNotReverify(format!("attest: {other}")),
                backend,
                clean_commit,
                verified_at,
            );
        }
    };

    // 3. Classify. A KernelVerified signed verdict requires BOTH the shard-level
    //    gate clean (and not naming this constant) AND a foundational
    //    attestation. The shard-gate condition guarantees the de-Bruijn-anchored
    //    shard faithfully encodes a kernel-verified closure; the fresh-env
    //    attestation guarantees THIS term re-earns foundational-only on its own.
    let gate_ok_for_this = gate_clean && !flagged.contains(name);
    let outcome = if att.foundational {
        if gate_ok_for_this {
            ReauditOutcome::KernelVerified
        } else {
            ReauditOutcome::CouldNotReverify(
                "fresh-env attestation foundational but shard-level cake gate flagged the \
                 shard/constant (fail closed)"
                    .to_string(),
            )
        }
    } else {
        ReauditOutcome::AxiomDependent
    };

    sign_outcome(name, Some(att), outcome, backend, clean_commit, verified_at)
}

/// Build and sign the verdict for a classified outcome.
///
/// When `att` is `Some`, the signed record carries the kernel's real digests and
/// closure. When `att` is `None` (reconstruction/recheck never produced one),
/// the record is a digest-less `Rejected`/could-not-reverify placeholder — never
/// `KernelVerified`. The signer's invariant guard
/// ([`SignedVerdict::check_invariants`]) is the structural reason a non-clean
/// outcome cannot be signed green.
fn sign_outcome(
    name: &str,
    att: Option<KernelAttestation>,
    outcome: ReauditOutcome,
    backend: &dyn SigningBackend,
    clean_commit: &str,
    verified_at: &str,
) -> Result<ReauditVerdict, ReauditError> {
    let att = att.unwrap_or_else(|| KernelAttestation {
        name: name.to_string(),
        statement_digest: String::new(),
        proof_digest: String::new(),
        foundational: false,
        domain_axioms: Vec::new(),
        clean_version: env!("CARGO_PKG_VERSION").to_string(),
        clean_commit: clean_commit.to_string(),
    });
    let mut signed = SignedVerdict::from_attestation(&att, verified_at.to_string());
    // The signed verdict kind must agree with the classified outcome. The only
    // way to a KernelVerified record is a foundational attestation AND a
    // KernelVerified outcome — `from_attestation` already sets KernelVerified
    // exactly when `att.foundational`, so a non-KernelVerified outcome over a
    // foundational attestation is force-downgraded to Rejected (fail closed:
    // the gate disagreed even though the fresh-env recheck was clean).
    if !outcome.is_kernel_verified() && signed.verdict == SignedVerdictKind::KernelVerified {
        signed.verdict = SignedVerdictKind::Rejected;
        signed.foundational = false;
    }
    signed
        .sign_with(backend)
        .map_err(|source| ReauditError::Signing {
            name: name.to_string(),
            source,
        })?;
    Ok(ReauditVerdict {
        name: name.to_string(),
        outcome,
        signed,
    })
}

/// Convert a reconstructed constant back into a kernel [`Declaration`] for the
/// fresh-env re-check. Only value-bearing theorems reach here (the caller
/// filters), so a missing value is itself a could-not-reverify (an axiom-shaped
/// theorem with no proof term).
fn reconstructed_to_decl(recon: &ReconstructedConstant) -> Declaration {
    match &recon.value_expr {
        Some(value) => Declaration::Theorem {
            name: recon.decl_name.clone(),
            level_params: recon.level_params.clone(),
            type_: recon.type_expr.clone(),
            value: value.clone(),
        },
        // No value: model as an axiom so `attest` returns `NoValue` →
        // could-not-reverify (never a silent green).
        None => Declaration::Axiom {
            name: recon.decl_name.clone(),
            level_params: recon.level_params.clone(),
            type_: recon.type_expr.clone(),
        },
    }
}

/// The set of constant names the shard-level cake gate flagged (so a clean
/// fresh-env re-check cannot override a shard-gate rejection of that constant).
fn flagged_names(gate: &CakeGateReport) -> HashSet<String> {
    gate.violations
        .iter()
        .map(|v| v.name().to_string())
        .collect()
}

/// Collect every Cake-tagged `.mathverse` shard under `dir` (by content, not
/// filename — a hand-rolled Cake shard cannot dodge the audit via its name).
fn collect_cake_shards(dir: &Path, out: &mut Vec<PathBuf>) -> Result<(), ReauditError> {
    let entries = std::fs::read_dir(dir).map_err(|source| ReauditError::Io {
        path: dir.to_path_buf(),
        source,
    })?;
    for entry in entries {
        let entry = entry.map_err(|source| ReauditError::Io {
            path: dir.to_path_buf(),
            source,
        })?;
        let path = entry.path();
        if path.is_dir() {
            collect_cake_shards(&path, out)?;
        } else if path.extension().is_some_and(|e| e == "mathverse") && is_cake_shard(&path) {
            out.push(path);
        }
    }
    Ok(())
}

fn is_cake_shard(path: &Path) -> bool {
    let Ok(bytes) = std::fs::read(path) else {
        return false;
    };
    let Ok(reader) = ShardReader::from_bytes(&bytes) else {
        return false;
    };
    reader
        .constants
        .iter()
        .any(|c| c.source_system == crate::types::SourceSystem::Cake as u8)
}

/// The graduation record path beside a shard (re-exported convenience for
/// callers locating the record a verdict refers to).
#[must_use]
pub fn record_path_for(shard_path: &Path) -> PathBuf {
    graduation_record_path(shard_path)
}

#[cfg(test)]
#[path = "reauditor_tests.rs"]
mod tests;
