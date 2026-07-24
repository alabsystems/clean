// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `mathverse-graduation-v3.1` record schema (still able to read/verify
//! v1+v2+v3).
//!
//! A [`GraduationRecord`] is the audit artifact produced by the graduation
//! intake gate ([`crate::graduate::intake::graduate`]). It is written as
//! `<shard-stem>.graduation.json` beside the produced `.mathverse` shard and
//! is **mutually digest-bound** to that shard:
//!
//! * the shard's per-constant [`crate::provenance::ProvenanceRecord`] notes
//!   carry `graduation-record:blake3:<binding-digest>` where the binding
//!   digest is [`GraduationRecord::binding_digest`] (the record serialized
//!   with `result.shard_digest` cleared — cleared because the shard bytes
//!   cannot embed a digest of a record that already contains the shard's own
//!   digest);
//! * `result.shard_digest` is the blake3 digest of the final shard bytes.
//!
//! Tampering with either side breaks one of the two bindings and fails
//! [`crate::shard_verify::cake_gate::verify_cake_shard`].
//!
//! The binding is tamper-*evidence*, not authenticity: a coordinated rewrite
//! of both files can restore digest consistency (no signing key in v1), but
//! can never launder a trust verdict — the cake gate re-earns
//! `KernelVerified` by kernel replay and cross-checks the record's own
//! accepted list against its per-theorem audit table.

use std::path::{Path, PathBuf};

use serde::{Deserialize, Serialize};

use crate::error::{MathverseError, MathverseResult};

/// Versioned schema identifier written by the current intake gate. The cake
/// gate accepts this, [`GRADUATION_SCHEMA_VERSION_V31`],
/// [`GRADUATION_SCHEMA_VERSION_V3`], [`GRADUATION_SCHEMA_VERSION_V2`], and
/// [`GRADUATION_SCHEMA_VERSION_V1`]; anything else is rejected.
pub const GRADUATION_SCHEMA_VERSION: &str = "mathverse-graduation-v3.2";

/// Legacy v3.1 schema identifier (carried theorems, implicit clean-prelude
/// recheck base). v3.1 records remain fully verifiable: the v3.2
/// `recheck_base` field is serde-defaulted to `clean-prelude` and skipped on
/// re-serialization, so v3.1 binding digests are reproduced byte-for-byte.
pub const GRADUATION_SCHEMA_VERSION_V31: &str = "mathverse-graduation-v3.1";

/// Legacy v3 schema identifier (carried definitions + carried inductive
/// families, no carried theorems). v3 records remain fully verifiable: the
/// v3.1 `carried_theorems` fields are serde-defaulted to empty and skipped on
/// re-serialization, so v3 binding digests are reproduced byte-for-byte.
pub const GRADUATION_SCHEMA_VERSION_V3: &str = "mathverse-graduation-v3";

/// Legacy v2 schema identifier (carried definitions, no carried inductive
/// families). v2 records remain fully verifiable: the v3 `carried_inductives`
/// fields are serde-defaulted to empty and skipped on re-serialization, so v2
/// binding digests are reproduced byte-for-byte.
pub const GRADUATION_SCHEMA_VERSION_V2: &str = "mathverse-graduation-v2";

/// Legacy v1 schema identifier. v1 records (no carried definitions) remain
/// fully verifiable: the `carried_definitions` fields are serde-defaulted to
/// empty and skipped on re-serialization, so v1 binding digests are
/// reproduced byte-for-byte.
pub const GRADUATION_SCHEMA_VERSION_V1: &str = "mathverse-graduation-v1";

/// Gate implementation version recorded in [`GateInfo::gate_version`].
/// 5 = graduation v3.2 (shadow-free `lean-core` recheck base + fail-closed
/// shadow guard); 4 = graduation v3.1 (carried theorems).
pub const GRADUATION_GATE_VERSION: u32 = 5;

/// Prefix of the provenance note binding a shard constant to its record.
pub const GRADUATION_NOTE_PREFIX: &str = "graduation-record:blake3:";

/// Fixed minimum-trust policy of graduation v1. Only declarations the kernel
/// re-checked with their proof value AND whose transitive axiom closure is
/// foundational-only can graduate.
pub const GRADUATION_MIN_TRUST: &str = "kernel_verified";

// ---------------------------------------------------------------------------
// Enums
// ---------------------------------------------------------------------------

/// Policy applied when a candidate duplicates a baseline-corpus declaration.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
#[non_exhaustive]
pub enum OnDuplicate {
    /// Reject duplicate candidates (the v1 behavior for both variants).
    Reject,
    /// Reserved: accept a duplicate whose statement is strictly sharper.
    /// Graduation v1 has no defeq-grade sharper detection, so this is
    /// honestly downgraded to `Reject` (with an explanatory reject reason).
    AcceptIfSharper,
}

/// How the graduation evidence was produced (design §7 honesty labels).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
#[non_exhaustive]
pub enum EvidenceClass {
    /// Transcribed by a deterministic harness; headline claims require this.
    HarnessTranscribed,
    /// Attested by an agent without a deterministic transcript.
    AgentAttested,
}

/// Kernel verdict for a single candidate. Only `KernelVerified` ever reaches
/// a shard; the other variants exist so rejected candidates stay auditable.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
#[non_exhaustive]
pub enum KernelVerdict {
    /// The kernel re-checked the declaration **with its proof value**
    /// (`Environment::add_decl` on a `Declaration::Theorem` succeeded) and
    /// its transitive axiom closure is foundational-only.
    KernelVerified,
    /// Reserved for certificate-replay evidence (not produced by v1).
    CertificateReplayed,
    /// The candidate did not earn a kernel verdict (see `reject_reason`).
    Rejected,
}

/// Novelty verdict against the pinned baseline corpus.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
#[non_exhaustive]
pub enum NoveltyVerdict {
    /// No baseline declaration matches by name or statement hash.
    New,
    /// A baseline declaration matches (see `matched_name` / `match_kind`).
    Duplicate,
    /// Reserved: duplicate by name but with a sharper statement (roadmap).
    Sharper,
    /// Novelty was not evaluated (candidate rejected before hashing).
    Unevaluated,
}

/// Which dedup primitive matched (v1 method is `name+statement-hash`).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
#[non_exhaustive]
pub enum NoveltyMatchKind {
    /// Exact declaration-name match.
    Name,
    /// Canonical statement-hash match (blake3 over the FlatExpr encoding of
    /// the type).
    StatementHash,
    /// Cake Tier-1.5 rewrite-canonical digest match — an "same object, different form"
    /// candidate (commutative-operand collapse, e.g. `a + b` / `b + a`, `a = b` / `b = a`).
    /// UNCONFIRMED and NON-BLOCKING: it appears with a [`NoveltyVerdict::New`] verdict (no
    /// `same_object`/`proved-iff` arbiter is available against the corpus index, which stores
    /// only digest prefixes), so it is recorded as an alternate-form hint for search/uniqueness
    /// but never rejects a candidate. A bucket, never a proof. Only produced under `--score`.
    SemanticDigest,
}

// ---------------------------------------------------------------------------
// Record sections
// ---------------------------------------------------------------------------

/// Gate identity: which gate, built from which Clean, decided when.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct GateInfo {
    pub gate_version: u32,
    pub clean_version: String,
    pub clean_commit: String,
    pub decided_at_epoch_s: u64,
    /// Recheck-environment base the run was decided against (v3.2):
    /// `"clean-prelude"` or `"lean-core"`. The cake gate replays the shard
    /// against the SAME base. Serde-defaulted (and skipped when default) so
    /// pre-v3.2 records keep byte-identical binding digests.
    #[serde(
        default = "default_recheck_base",
        skip_serializing_if = "is_default_recheck_base"
    )]
    pub recheck_base: String,
}

/// Pre-v3.2 records carry no `recheck_base`; they were decided against the
/// Clean prelude.
pub(crate) fn default_recheck_base() -> String {
    RECHECK_BASE_CLEAN_PRELUDE.to_string()
}

fn is_default_recheck_base(base: &String) -> bool {
    base == RECHECK_BASE_CLEAN_PRELUDE
}

/// Record label for the Clean-prelude recheck base.
pub const RECHECK_BASE_CLEAN_PRELUDE: &str = "clean-prelude";

/// Record label for the shadow-free Lean-core recheck base (v3.2).
pub const RECHECK_BASE_LEAN_CORE: &str = "lean-core";

/// The graduating project's manifest identity.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct ProjectInfo {
    pub name: String,
    pub manifest_kind: String,
    /// `blake3:<hex>` digest of the manifest file bytes.
    pub manifest_digest: String,
    /// Certificate schema when project-side evidence was attached
    /// (e.g. `clean-math-certificate-v1`). Cross-checked, never trusted.
    pub certificate_schema: Option<String>,
}

/// Novelty baseline pin (which corpus the dedup ran against).
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct CorpusPin {
    pub mathverse_release: String,
    /// `blake3:<hex>` digest over the baseline shard bytes.
    pub manifest_digest: String,
}

/// Gate policy knobs.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct PolicyInfo {
    /// Always [`GRADUATION_MIN_TRUST`] in v1.
    pub min_trust: String,
    pub on_duplicate: OnDuplicate,
}

/// Cake build-provenance fingerprint of the source `.olean` environment, bound
/// into the record when graduation is run with `--olean-source-root`.
///
/// Produced by `clean_lake::cake_provenance` (a content-hash signature over the
/// declared modules' `.lean` sources + `.olean` artifacts). `fresh = false` means
/// at least one declared module's `.olean` does not reflect its current source
/// (e.g. a stale root whose recorded imports differ from the source) — the
/// environment graduation decided against may be silently incomplete.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct EnvProvenance {
    /// `cake-build-signature-v1`.
    pub schema: String,
    /// `blake3:<hex>` reproducible fingerprint of the declared environment.
    pub env_digest: String,
    /// `lean-toolchain` identifier, if known.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub toolchain: Option<String>,
    /// True iff every declared module's `.olean` is content-fresh vs its source.
    pub fresh: bool,
    /// `"<module> (<status>)"` for each non-fresh declared module.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub stale_modules: Vec<String>,
}

/// Run provenance (attempt log / replay archive / honesty fields).
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct RunProvenance {
    pub attempt_id: Option<String>,
    pub replay_archive_sha256: Option<String>,
    pub engine: Option<String>,
    pub seed: Option<String>,
    pub evidence_class: EvidenceClass,
    /// Mandatory honesty field (may be `"none-known"`).
    pub residual_risk: String,
    /// Cake build-provenance fingerprint of the source environment. `None` (and
    /// omitted from the serialized record, preserving byte-for-byte determinism of
    /// records produced without `--olean-source-root`) unless freshness was checked.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub env_provenance: Option<EnvProvenance>,
}

/// Outcome summary plus the shard binding.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct GraduationResult {
    pub accepted: Vec<String>,
    pub rejected: Vec<String>,
    pub shard_filename: String,
    /// `blake3:<hex>` of the written shard bytes. Empty while computing the
    /// binding digest (see [`GraduationRecord::binding_digest`]).
    pub shard_digest: String,
}

/// Kernel re-check facts for one candidate — recomputed by the intake gate,
/// never copied from project-side claims.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct KernelFacts {
    pub verdict: KernelVerdict,
    /// `true` iff `Environment::add_decl(Declaration::Theorem { value, .. })`
    /// succeeded in the fresh recheck environment. Must be `true` for
    /// [`KernelVerdict::KernelVerified`] on theorems and carried definitions;
    /// honestly `false` for carried inductive families (there is no value —
    /// their certificate is `family_checked`).
    pub value_typechecked: bool,
    /// v3: `true` iff `Environment::add_inductive` re-checked the family
    /// (positivity, nested positivity, universe constraints, recursor
    /// generation) in the fresh recheck environment. Always `false` for
    /// theorems and carried definitions; absent in v1/v2 records (serde
    /// default) and skipped when `false`, preserving v1/v2 binding digests.
    #[serde(default, skip_serializing_if = "is_false")]
    pub family_checked: bool,
    pub checker: String,
}

/// Serde helper: skip serializing `false` booleans (v1/v2 byte stability).
#[allow(clippy::trivially_copy_pass_by_ref)] // serde's skip_serializing_if signature
fn is_false(value: &bool) -> bool {
    !*value
}

/// Transitive axiom-closure facts (step 2 of the gate).
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct AxiomClosure {
    /// `true` iff the transitive axiom closure is `⊆ FOUNDATIONAL_AXIOMS`.
    pub foundational_only: bool,
    /// Empty iff `foundational_only`.
    pub domain_axioms: Vec<String>,
    /// In-shard-closed `AxiomProfile` bits (0 for every accepted theorem).
    pub axiom_profile_bits: u64,
}

/// Novelty facts (step 3 of the gate).
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct NoveltyFacts {
    /// Dedup method label — `"name+statement-hash"` for an exact-identity verdict;
    /// `"name+statement-hash+tier1.5-rewrite-canonical"` when the env-free Tier-1.5
    /// semantic probe additionally fired (only under `--score`). Honest labeling: the label
    /// names exactly the primitives applied (defeq-grade duplicate detection remains a
    /// roadmap item, not shipped).
    pub method: String,
    /// Verdict by EXACT identity (name / structural statement-hash). An unconfirmed Tier-1.5
    /// semantic alternate-form match does NOT make this `Duplicate` — it stays `New` and is
    /// recorded via [`Self::match_kind`] = [`NoveltyMatchKind::SemanticDigest`] +
    /// [`Self::matched_name`] (see that variant). Only `Duplicate` blocks graduation.
    pub verdict: NoveltyVerdict,
    /// The matched declaration: a confirmed duplicate (with a `Duplicate` verdict) OR, with a
    /// `New` verdict and `match_kind = SemanticDigest`, an unconfirmed alternate-form hint.
    pub matched_name: Option<String>,
    pub match_kind: Option<NoveltyMatchKind>,
}

/// Per-candidate entry. Accepted and rejected candidates are both recorded.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct GraduatedTheorem {
    pub name: String,
    /// Declaration kind as seen in the source environment (v1 accepts only
    /// `"theorem"`; other kinds are recorded on rejected entries for audit).
    pub decl_kind: String,
    /// `blake3:<hex>` of the canonical FlatExpr byte encoding of the TYPE.
    pub statement_hash: String,
    /// Same encoding over the proof VALUE.
    pub proof_hash: String,
    pub kernel: KernelFacts,
    pub axiom_closure: AxiomClosure,
    pub novelty: NoveltyFacts,
    pub accepted: bool,
    pub reject_reason: Option<String>,
    /// v2: names of the non-prelude definitions this theorem transitively
    /// closes over (each one kernel re-checked and recorded in
    /// [`GraduationRecord::carried_definitions`] when the theorem is
    /// accepted). Empty — and skipped in serialization, preserving v1
    /// binding digests — when the theorem carries no definitions.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub carried_definitions: Vec<String>,
    /// v3: family-root names of the carried inductive families this theorem
    /// transitively closes over (each family re-checked through
    /// `add_inductive` and recorded in
    /// [`GraduationRecord::carried_inductives`] when the theorem is
    /// accepted). Empty — and skipped in serialization, preserving v1/v2
    /// binding digests — when the theorem carries no families.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub carried_inductives: Vec<String>,
    /// v3.1: names of the non-prelude THEOREMS this theorem transitively
    /// closes over (each one kernel re-checked WITH its proof value and
    /// recorded in [`GraduationRecord::carried_theorems`] when the theorem
    /// is accepted). Empty — and skipped in serialization, preserving
    /// v1/v2/v3 binding digests — when the theorem carries no theorems.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub carried_theorems: Vec<String>,
    /// Cake semantic identity of the *statement* (Tier-1 defeq-canonical + Tier-1.5
    /// rewrite-canonical digests), bound when graduation runs with `--score`. `None`
    /// (and omitted, preserving binding-digest determinism for runs without `--score`)
    /// otherwise. Beyond the structural `statement_hash`, this is the identity that
    /// catches "same object in a different form".
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub semantic_identity: Option<SemanticIdentityRecord>,
}

/// Cake semantic-identity digests of a statement (see `clean_cake::identity`).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SemanticIdentityRecord {
    /// `blake3:<hex>` over the **env-free** Tier-1.5 rewrite-canonical form
    /// (commutative-operand canonicalisation only, **no kernel `whnf`** — so it is O(term
    /// size) and never normalises a heavy statement). This is the *corpus-scale* semantic
    /// key: the `MVBIDX01` baseline index keys its semantic table on it, the gate matches a
    /// candidate against the whole corpus' alternate forms with it, and the intra-run probe
    /// uses it too. Always present under `--score`. A hit is a "same object, different form"
    /// candidate, never a soundness claim.
    pub structural_rewrite_digest: String,
    /// `blake3:<hex>` over the defeq normal form of the statement (Tier-1 defeq bucket).
    /// **Expensive** (runs the kernel normaliser) — only present under `--score-defeq`; `None`
    /// under plain `--score` (which is the fast, env-free path). On heavy mathlib statements
    /// the normalisation is bounded and may be incomplete (see [`Self::complete`]).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub canonical_digest: Option<String>,
    /// `blake3:<hex>` over the *env-dependent* Tier-1.5 rewrite-canonical form (defeq-normalise
    /// then canonicalise). The strongest bucket, but expensive — only under `--score-defeq`.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub rewrite_digest: Option<String>,
    /// Did the (`--score-defeq`) normalisation finish within fuel? `None` when no defeq
    /// normalisation was attempted (plain `--score`).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub complete: Option<bool>,
}

// Carried-dependency sections (v2 definitions, v3 inductive families, v3.1
// theorems) live in `record_carried.rs`; re-exported here so existing
// `record::CarriedX` paths stay stable.
pub(crate) use super::record_carried::{
    CarriedDefinition, CarriedInductive, CarriedInductiveConstructor, CarriedInductiveMember,
    CarriedTheorem,
};

// ---------------------------------------------------------------------------
// GraduationRecord
// ---------------------------------------------------------------------------

/// Top-level `mathverse-graduation-v1` record.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct GraduationRecord {
    pub schema: String,
    pub gate: GateInfo,
    pub project: ProjectInfo,
    pub corpus_pin: CorpusPin,
    pub policy: PolicyInfo,
    pub theorems: Vec<GraduatedTheorem>,
    /// v2: the definitions written into the shard (exactly those required by
    /// at least one accepted theorem), in shard/dependency order. Empty —
    /// and skipped in serialization, preserving v1 binding digests — for v1
    /// records and definition-free v2 runs.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub(crate) carried_definitions: Vec<CarriedDefinition>,
    /// v3: the inductive families written into the shard (exactly those
    /// required by at least one accepted theorem), in shard/dependency
    /// order. Empty — and skipped in serialization, preserving v1/v2 binding
    /// digests — for v1/v2 records and family-free v3 runs.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub(crate) carried_inductives: Vec<CarriedInductive>,
    /// v3.1: the theorems written into the shard as carried supporting
    /// material (exactly those required by at least one accepted theorem),
    /// in shard/dependency order. Empty — and skipped in serialization,
    /// preserving v1/v2/v3 binding digests — for pre-v3.1 records and
    /// theorem-carry-free runs.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub(crate) carried_theorems: Vec<CarriedTheorem>,
    pub provenance: RunProvenance,
    pub result: GraduationResult,
}

impl GraduationRecord {
    /// Binding digest: blake3 over the canonical JSON serialization of the
    /// record with `result.shard_digest` cleared.
    ///
    /// The clearing breaks the otherwise-circular dependency between the two
    /// bindings: the shard embeds this digest (in provenance notes) before
    /// the shard bytes exist, and `result.shard_digest` is filled afterwards
    /// from the final shard bytes.
    pub fn binding_digest(&self) -> MathverseResult<String> {
        let mut canonical = self.clone();
        canonical.result.shard_digest = String::new();
        let bytes = serde_json::to_vec(&canonical).map_err(MathverseError::Json)?;
        Ok(format!("blake3:{}", blake3::hash(&bytes).to_hex()))
    }

    /// The provenance-note string embedded in the shard for this record.
    pub fn provenance_note(&self) -> MathverseResult<String> {
        let digest = self.binding_digest()?;
        Ok(format!(
            "{GRADUATION_NOTE_PREFIX}{}",
            digest.trim_start_matches("blake3:")
        ))
    }

    /// Write the record as pretty JSON.
    pub fn write_to_file(&self, path: &Path) -> MathverseResult<()> {
        let json = serde_json::to_string_pretty(self).map_err(MathverseError::Json)?;
        std::fs::write(path, json).map_err(MathverseError::Io)
    }

    /// Read a record back from JSON.
    pub fn from_file(path: &Path) -> MathverseResult<Self> {
        let bytes = std::fs::read(path).map_err(MathverseError::Io)?;
        serde_json::from_slice(&bytes).map_err(MathverseError::Json)
    }
}

/// Canonical path of the graduation record for a shard:
/// `<dir>/<shard-stem>.graduation.json`.
#[must_use]
pub fn graduation_record_path(shard_path: &Path) -> PathBuf {
    let stem = shard_path
        .file_stem()
        .map(|s| s.to_string_lossy().into_owned())
        .unwrap_or_else(|| "shard".to_string());
    shard_path.with_file_name(format!("{stem}.graduation.json"))
}

/// `blake3:<hex>` digest of arbitrary bytes (shared digest convention).
#[must_use]
pub fn blake3_digest(bytes: &[u8]) -> String {
    format!("blake3:{}", blake3::hash(bytes).to_hex())
}

/// `blake3:<hex>` digest of a file's bytes.
pub fn blake3_file_digest(path: &Path) -> MathverseResult<String> {
    let bytes = std::fs::read(path).map_err(MathverseError::Io)?;
    Ok(blake3_digest(&bytes))
}

/// Canonical statement/proof hash: blake3 over the deterministic FlatExpr
/// byte encoding of a kernel expression.
///
/// This is the graduation-v1 **novelty primitive**: identity-grade for
/// structural equality of de Bruijn–indexed kernel terms (alpha-equivalent
/// terms share an encoding), NOT defeq-grade. Two definitionally-equal but
/// structurally-different statements hash differently; that limitation is
/// part of the honest `name+statement-hash` novelty label.
pub fn expr_canonical_digest(expr: &clean_kernel::Expr) -> MathverseResult<String> {
    let mut builder = clean_kernel::flat::FlatBuilder::new();
    builder
        .add_kernel_expr(expr)
        .map_err(|e| MathverseError::Kernel(format!("flatten for canonical digest failed: {e}")))?;
    let mut bytes = Vec::new();
    builder
        .write_to(&mut bytes)
        .map_err(|e| MathverseError::Kernel(format!("flat serialization failed: {e}")))?;
    Ok(blake3_digest(&bytes))
}
