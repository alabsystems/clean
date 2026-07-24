// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Strict kernel gate for `SourceSystem::Cake` (graduated) shards — the
//! unbypassable verify-side half of the graduation pipeline.
//!
//! A Cake shard is valid only when:
//!
//! 1. a `mathverse-graduation-v3.1` (or legacy v3/v2/v1) record sits beside
//!    it (`<stem>.graduation.json`), and the **mutual digest binding** holds —
//!    blake3 of the shard bytes matches `result.shard_digest`, and every
//!    constant's provenance notes carry the record's binding digest;
//! 2. every constant is a value-bearing **theorem** listed in
//!    `result.accepted` — or, under a v3.1 record, a value-bearing theorem
//!    listed in the record's `carried_theorems` section (carried supporting
//!    material; replayed exactly like an accepted theorem, never counted as
//!    graduated) — or, under a v2+ record, a value-bearing **definition**
//!    listed in the record's `carried_definitions` section — or, under a
//!    v3+ record, an **inductive-family member**
//!    (`DeclKind::Inductive/Constructor/Recursor`) belonging to exactly one
//!    family in the record's `carried_inductives` section (the `MissingValue`
//!    check is waived ONLY for those three kinds when family-bound) —
//!    `SourceSystem::Cake`, `ImportConfidence::KernelVerified`, empty
//!    `AxiomProfile`, no sorry;
//! 3. every constant round-trips through the live kernel in a fresh prelude
//!    environment, shard order, so carried items precede their users:
//!    theorems (accepted AND carried alike) and definitions via
//!    `Environment::add_decl` (theorems must classify
//!    `ProofQuality::Constructive`, definitions re-earn an empty
//!    non-foundational closure), and carried inductive families via the
//!    checked `Environment::add_inductive` replay at the family ROOT — the
//!    `InductiveDecl` is rebuilt from the shard's own constants + typed
//!    header metadata (the SAME shared reconstruction the incremental
//!    verifier uses, `crate::inductive_replay`), every shard-resident family
//!    member must byte-match the regenerated constant (level params + type),
//!    and the family re-earns a foundational-only union closure over all
//!    member types. Families outside the v3.0 fence (single-type,
//!    non-nested, non-mutual) fail `CarriedFamilyUnsupportedShape`. The
//!    KernelVerified stamp is *re-earned*, never taken on faith; neither a
//!    definition nor a family can launder an axiom — values and constructor
//!    types are replayed too, so a smuggled dependency either fails the
//!    kernel replay (constant absent from the shard) or surfaces in the
//!    replayed closure.
//!
//! Anyone can flip the `source_system` byte to Cake with
//! `KernelShardBuilder::with_source_system`; this gate is why that buys
//! nothing — without a digest-bound graduation record produced by
//! [`crate::graduate::intake::graduate`], the shard fails verification.
//!
//! The record must also be **self-consistent**: every name in
//! `result.accepted` must have a per-theorem entry that is itself marked
//! accepted, `KernelVerified`, value-typechecked, and foundational-only —
//! and vice versa. A record cannot claim acceptance its own audit table
//! contradicts.
//!
//! **Honest limitation (v1/v2):** the digest binding is tamper-*evidence*,
//! not authenticity — there is no signing key, so an attacker who can
//! rewrite BOTH files can re-forge a fully self-consistent shard/record
//! pair. What such a forgery can never do is launder the trust verdict:
//! clause 3 re-earns `KernelVerified` by live kernel replay, so an unproved
//! or axiom-dependent theorem fails the gate no matter what the forged
//! record claims (pinned by
//! `test_cake_gate_rejects_coordinated_forgery_of_axiom_dependent_theorem`).
//! Only the *provenance metadata* (project name, engine, honesty labels) is
//! forgeable under full two-file rewrite; cryptographic provenance
//! authenticity is an explicit non-goal of graduation v2.

use std::collections::{HashMap, HashSet};
use std::fmt;
use std::fs;
use std::path::{Path, PathBuf};
use std::time::{Duration, Instant};

use clean_kernel::expr::{BinderInfo, Expr};
use clean_kernel::level::Level;
use clean_kernel::{Declaration, Environment, Name, ProofQuality};
use thiserror::Error;

use crate::graduate::record::{
    graduation_record_path, CarriedDefinition, GraduationRecord, KernelVerdict, NoveltyVerdict,
    GRADUATION_SCHEMA_VERSION, GRADUATION_SCHEMA_VERSION_V1, GRADUATION_SCHEMA_VERSION_V2,
    GRADUATION_SCHEMA_VERSION_V3, GRADUATION_SCHEMA_VERSION_V31, RECHECK_BASE_CLEAN_PRELUDE,
    RECHECK_BASE_LEAN_CORE,
};
use crate::graduate::RecheckBase;
use crate::inductive_replay::{
    build_inductive_replay_metadata, checked_inductive_replay_matches_shard, reconstruct_constant,
    NormMode, ShardFamilyMatch,
};
use crate::provenance::ProvenanceSidecar;
use crate::shard::ShardReader;
use crate::shard_reconstruct::{reconstruct_from_shard_with_level_lists, reconstruct_level_params};
use crate::types::{AxiomProfile, DeclKind, ImportConfidence, SourceSystem};

/// Aggregate result from running the cake shard gate.
#[must_use]
#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct CakeGateReport {
    pub violations: Vec<CakeGateViolation>,
    pub checked: usize,
}

impl CakeGateReport {
    /// `true` iff every checked constant passed every clause.
    #[must_use]
    pub fn is_clean(&self) -> bool {
        self.violations.is_empty()
    }
}

/// Per-declaration gate violation.
#[must_use]
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum CakeGateViolation {
    WrongSourceSystem {
        name: String,
        found: u8,
    },
    NonKernelVerifiedProvenance {
        name: String,
        found: u8,
    },
    NonEmptyAxiomProfile {
        name: String,
        found: u64,
    },
    NotATheorem {
        name: String,
        found: u8,
    },
    MissingValue {
        name: String,
    },
    ContainsSorry {
        name: String,
    },
    DuplicateDeclaration {
        name: String,
        index: usize,
    },
    NotInAcceptedList {
        name: String,
    },
    AcceptedNameMissingFromShard {
        name: String,
    },
    UncarriedDefinition {
        name: String,
    },
    CarriedDefinitionMissingFromShard {
        name: String,
    },
    /// v3.1: a carried theorem listed in the record's `carried_theorems`
    /// section that the shard does not contain.
    CarriedTheoremMissingFromShard {
        name: String,
    },
    /// v3: an Inductive/Constructor/Recursor constant that is not a member
    /// of exactly one recorded `carried_inductives` family.
    UncarriedInductiveFamilyMember {
        name: String,
    },
    /// v3: a shard-resident family member that does not match the constant
    /// the checked `add_inductive` replay regenerated (or whose family root
    /// never replayed successfully).
    CarriedFamilyMismatch {
        name: String,
        family: String,
    },
    /// v3: shard metadata cannot rebuild a checked single-type family
    /// (mutual/nested shapes are outside the v3.0 fence; incoherent
    /// `num_params` / constructor metadata lands here too).
    CarriedFamilyUnsupportedShape {
        name: String,
    },
    MissingProvenanceRecord {
        name: String,
    },
    ProvenanceDigestMismatch {
        name: String,
    },
    MissingGraduationNote {
        name: String,
    },
    ReconstructFailed {
        name: String,
        error: String,
    },
    KernelRejected {
        name: String,
        error: String,
    },
    AxiomDependent {
        name: String,
        axioms: Vec<String>,
    },
    RecordInconsistent {
        name: String,
        reason: String,
    },
    /// ENV-FUSION (in-process fast path): the shard's reconstructed declaration
    /// is not structurally identical to the kernel-verified declaration the
    /// primary gate left resident in the recheck environment — so the shard
    /// does not faithfully encode the verified term (serializer defect or
    /// tamper). Fail closed; the standalone full-replay verb re-checks from
    /// scratch.
    FusedOracleMismatch {
        name: String,
    },
}

impl CakeGateViolation {
    #[must_use]
    pub fn name(&self) -> &str {
        match self {
            Self::WrongSourceSystem { name, .. }
            | Self::NonKernelVerifiedProvenance { name, .. }
            | Self::NonEmptyAxiomProfile { name, .. }
            | Self::NotATheorem { name, .. }
            | Self::MissingValue { name }
            | Self::ContainsSorry { name }
            | Self::DuplicateDeclaration { name, .. }
            | Self::NotInAcceptedList { name }
            | Self::AcceptedNameMissingFromShard { name }
            | Self::UncarriedDefinition { name }
            | Self::CarriedDefinitionMissingFromShard { name }
            | Self::CarriedTheoremMissingFromShard { name }
            | Self::UncarriedInductiveFamilyMember { name }
            | Self::CarriedFamilyMismatch { name, .. }
            | Self::CarriedFamilyUnsupportedShape { name }
            | Self::MissingProvenanceRecord { name }
            | Self::ProvenanceDigestMismatch { name }
            | Self::MissingGraduationNote { name }
            | Self::ReconstructFailed { name, .. }
            | Self::KernelRejected { name, .. }
            | Self::AxiomDependent { name, .. }
            | Self::FusedOracleMismatch { name }
            | Self::RecordInconsistent { name, .. } => name,
        }
    }

    #[must_use]
    pub fn reason(&self) -> String {
        match self {
            Self::WrongSourceSystem { found, .. } => format!(
                "wrong source_system {found}; expected Cake ({})",
                SourceSystem::Cake as u8
            ),
            Self::NonKernelVerifiedProvenance { found, .. } => format!(
                "non-kernel-verified provenance {found}; expected KernelVerified ({})",
                ImportConfidence::KernelVerified as u8
            ),
            Self::NonEmptyAxiomProfile { found, .. } => {
                format!("graduated declaration has non-empty axiom_profile 0x{found:x}")
            }
            Self::NotATheorem { found, .. } => {
                format!("non-theorem decl_kind {found} in graduated shard")
            }
            Self::MissingValue { .. } => "missing proof value in graduated shard".to_string(),
            Self::ContainsSorry { .. } => "declaration contains sorry/sorryAx".to_string(),
            Self::DuplicateDeclaration { index, .. } => {
                format!("duplicate declaration name at constant index {index}")
            }
            Self::NotInAcceptedList { .. } => {
                "theorem constant is listed neither in the graduation record's accepted \
                 set nor its carried_theorems section (pre-v3.1 records carry none)"
                    .to_string()
            }
            Self::AcceptedNameMissingFromShard { .. } => {
                "graduation record accepts a name the shard does not contain".to_string()
            }
            Self::UncarriedDefinition { .. } => {
                "definition constant is not listed in the graduation record's \
                 carried_definitions section (v1 records carry none)"
                    .to_string()
            }
            Self::CarriedDefinitionMissingFromShard { .. } => {
                "graduation record carries a definition the shard does not contain".to_string()
            }
            Self::CarriedTheoremMissingFromShard { .. } => {
                "graduation record carries a theorem the shard does not contain".to_string()
            }
            Self::UncarriedInductiveFamilyMember { .. } => {
                "inductive-family constant is not a member of exactly one family in the \
                 graduation record's carried_inductives section (v1/v2 records carry none)"
                    .to_string()
            }
            Self::CarriedFamilyMismatch { family, .. } => format!(
                "family member does not match the checked add_inductive replay of family \
                 `{family}` (level params + type must equal the regenerated constant, and \
                 the family root must have replayed successfully earlier in the shard)"
            ),
            Self::CarriedFamilyUnsupportedShape { .. } => {
                "shard metadata cannot rebuild a checked single-type InductiveDecl for this \
                 family (mutual/nested families are outside the graduation v3.0 fence)"
                    .to_string()
            }
            Self::MissingProvenanceRecord { .. } => {
                "constant has no provenance sidecar record".to_string()
            }
            Self::ProvenanceDigestMismatch { .. } => {
                "constant header sidecar_digest does not match its provenance record".to_string()
            }
            Self::MissingGraduationNote { .. } => {
                "provenance record lacks the digest-bound graduation note".to_string()
            }
            Self::ReconstructFailed { error, .. } => format!("reconstruction failed: {error}"),
            Self::KernelRejected { error, .. } => format!("kernel rejected declaration: {error}"),
            Self::AxiomDependent { axioms, .. } => {
                format!("depends on non-foundational axioms: {}", axioms.join(", "))
            }
            Self::RecordInconsistent { reason, .. } => {
                format!("graduation record inconsistent: {reason}")
            }
            Self::FusedOracleMismatch { .. } => {
                "env-fusion round-trip oracle: shard-reconstructed declaration is not \
                 structurally identical to the primary gate's kernel-verified declaration \
                 (serializer defect or tamper)"
                    .to_string()
            }
        }
    }
}

impl fmt::Display for CakeGateViolation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.reason())
    }
}

/// Shard-level errors from the cake gate (fail-closed before per-decl checks).
#[derive(Debug, Error)]
#[non_exhaustive]
pub enum CakeGateError {
    #[error("I/O error reading {path}: {source}")]
    Io {
        path: PathBuf,
        #[source]
        source: std::io::Error,
    },
    #[error("shard read error: {0}")]
    ShardRead(String),
    #[error(
        "missing graduation record `{0}` — a Cake shard is only valid with its \
         digest-bound graduation record sidecar (mathverse-graduation-v3.1 or legacy \
         v3/v2/v1)"
    )]
    MissingGraduationRecord(PathBuf),
    #[error("graduation record parse error at {path}: {reason}")]
    RecordParse { path: PathBuf, reason: String },
    #[error("graduation record schema mismatch: found `{found}`, expected `{expected}`")]
    SchemaMismatch { found: String, expected: String },
    #[error(
        "shard digest mismatch: record claims {recorded}, shard bytes hash to {actual} — \
         the shard or its record was tampered with after graduation"
    )]
    ShardDigestMismatch { recorded: String, actual: String },
    #[error("graduation record digest computation failed: {0}")]
    RecordDigest(String),
    #[error("provenance sidecar decode failed: {0}")]
    ProvenanceDecode(String),
}

/// Verify a single Cake shard against its graduation record.
pub fn verify_cake_shard(path: &Path) -> Result<CakeGateReport, CakeGateError> {
    verify_cake_shard_inner(path, None)
}

/// ENV-FUSION verify (in-process graduate fast path). Identical to
/// [`verify_cake_shard`] except clause 3 (the per-constant kernel replay — the
/// dominant verify-side cost on large closures) is discharged by the round-trip
/// oracle against `primary`, the primary gate's recheck environment in which
/// every constant already passed the real kernel re-check this run. Clauses 1-2
/// (digest binding, provenance, decl-kind, sorry, axiom-profile, record
/// consistency) and the live foundational-only axiom walk run unchanged on the
/// on-disk shard, so a serializer defect or tamper still fails closed (a
/// reconstructed decl that does not structurally equal the verified one yields
/// `FusedOracleMismatch`). For shards with no live primary env (downloaded /
/// release audit) use [`verify_cake_shard`].
pub fn verify_cake_shard_fused(
    path: &Path,
    primary: &mut Environment,
) -> Result<CakeGateReport, CakeGateError> {
    verify_cake_shard_inner(path, Some(primary))
}

fn verify_cake_shard_inner(
    path: &Path,
    primary: Option<&mut Environment>,
) -> Result<CakeGateReport, CakeGateError> {
    let shard_bytes = fs::read(path).map_err(|source| CakeGateError::Io {
        path: path.to_path_buf(),
        source,
    })?;

    let record_path = graduation_record_path(path);
    if !record_path.exists() {
        return Err(CakeGateError::MissingGraduationRecord(record_path));
    }
    let record =
        GraduationRecord::from_file(&record_path).map_err(|e| CakeGateError::RecordParse {
            path: record_path.clone(),
            reason: e.to_string(),
        })?;
    if record.schema != GRADUATION_SCHEMA_VERSION
        && record.schema != GRADUATION_SCHEMA_VERSION_V31
        && record.schema != GRADUATION_SCHEMA_VERSION_V3
        && record.schema != GRADUATION_SCHEMA_VERSION_V2
        && record.schema != GRADUATION_SCHEMA_VERSION_V1
    {
        return Err(CakeGateError::SchemaMismatch {
            found: record.schema.clone(),
            expected: format!(
                "{GRADUATION_SCHEMA_VERSION} (or {GRADUATION_SCHEMA_VERSION_V31} / \
                 {GRADUATION_SCHEMA_VERSION_V3} / {GRADUATION_SCHEMA_VERSION_V2} / \
                 {GRADUATION_SCHEMA_VERSION_V1})"
            ),
        });
    }

    let actual_digest = crate::graduate::record::blake3_digest(&shard_bytes);
    if actual_digest != record.result.shard_digest {
        return Err(CakeGateError::ShardDigestMismatch {
            recorded: record.result.shard_digest.clone(),
            actual: actual_digest,
        });
    }
    let expected_note = record
        .provenance_note()
        .map_err(|e| CakeGateError::RecordDigest(e.to_string()))?;

    let reader = ShardReader::from_bytes(&shard_bytes)
        .map_err(|error| CakeGateError::ShardRead(error.to_string()))?;
    let sidecar = if reader.provenance.is_empty() {
        // Empty shard (zero accepted theorems) carries no sidecar section.
        ProvenanceSidecar::new()
    } else {
        ProvenanceSidecar::from_bytes(&reader.provenance)
            .map_err(|error| CakeGateError::ProvenanceDecode(error.to_string()))?
    };

    Ok(verify_cake_reader(
        &reader,
        &sidecar,
        &record,
        &expected_note,
        primary,
    ))
}

/// Verify every Cake-tagged `.mathverse` shard under `dir`.
///
/// Detection is by content (any constant tagged `SourceSystem::Cake`), so a
/// hand-rolled Cake shard cannot dodge the gate via filename. Shards that
/// fail to read are skipped here (the general verifier reports those).
pub fn verify_cake_shard_dir(dir: &Path) -> Result<CakeGateReport, CakeGateError> {
    let mut shard_paths = Vec::new();
    collect_cake_shards(dir, &mut shard_paths)?;
    shard_paths.sort();

    let mut report = CakeGateReport::default();
    for path in shard_paths {
        let shard_report = verify_cake_shard(&path)?;
        report.checked += shard_report.checked;
        report.violations.extend(shard_report.violations);
    }
    Ok(report)
}

fn collect_cake_shards(dir: &Path, out: &mut Vec<PathBuf>) -> Result<(), CakeGateError> {
    let entries = fs::read_dir(dir).map_err(|source| CakeGateError::Io {
        path: dir.to_path_buf(),
        source,
    })?;
    for entry in entries {
        let entry = entry.map_err(|source| CakeGateError::Io {
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
    let Ok(bytes) = fs::read(path) else {
        return false;
    };
    let Ok(reader) = ShardReader::from_bytes(&bytes) else {
        return false;
    };
    reader
        .constants
        .iter()
        .any(|c| c.source_system == SourceSystem::Cake as u8)
}

/// v3 family replay bookkeeping: which shard constants belong to which
/// recorded family, and which members a successful checked family replay
/// has already verified byte-for-byte.
struct FamilyReplayState {
    /// member name -> family root, from `carried_inductives[*].members_in_shard`.
    member_to_family: HashMap<String, String>,
    /// Members verified by a successful `add_inductive` replay at their root.
    verified: HashSet<String>,
}

/// Seed the foundational TCB axioms `propext` and `Classical.choice` into the
/// lean-core verify environment, once their type prerequisites have been
/// replayed from the shard.
///
/// `RecheckBase::LeanCore::build()` starts empty except for the `Quot`
/// primitives (`init_quot` seeds `Quot`/`Quot.sound`). The other two
/// foundational axioms are part of the declared trusted base
/// (`axiom_audit::FOUNDATIONAL_AXIOMS` = `{propext, Quot.sound,
/// Classical.choice}`), but they cannot be added to the empty base up front:
/// their types reference core inductives (`Eq`/`Iff` for `propext`, `Nonempty`
/// for `Classical.choice`) that the gate only installs while replaying the
/// shard's carried families. This runs inside the replay loop and declares each
/// axiom the moment its prerequisites are present. Idempotent (skips if already
/// declared); the `add_decl` is best-effort — if it is ever rejected the
/// dependent constant simply fails closed with "Unknown constant".
///
/// SOUNDNESS:
///   * Only `propext` and `Classical.choice` are seeded here (and `Quot.sound`
///     comes from `init_quot`). No other axiom is added, so a carried constant
///     depending on any NON-foundational axiom still fails closed.
///   * The axiom types are constructed HERE from kernel primitives — never read
///     from the (forgeable) shard — using LEAN's exact convention
///     (`propext : {a b : Prop} → (a ↔ b) → a = b`, NOT Clean's native
///     `(a → b) → (b → a) → a = b`). A too-weak `propext` would let a forged
///     shard launder a false proof, so these types are pinned against the real
///     `Init` `.olean` by `tests::test_seeded_foundational_axiom_types_match_lean_core`.
fn ensure_foundational_axioms(env: &mut Environment) {
    let has = |env: &Environment, n: &str| env.get_const(&Name::from_string(n)).is_some();

    // propext : {a b : Prop} → (a ↔ b) → @Eq Prop a b
    if !has(env, "propext") && has(env, "Eq") && has(env, "Iff") {
        let _ = env.add_decl(Declaration::Axiom {
            name: Name::from_string("propext"),
            level_params: Vec::new(),
            type_: lean_propext_type(),
        });
    }

    // Classical.choice.{u} : {α : Sort u} → Nonempty α → α
    if !has(env, "Classical.choice") && has(env, "Nonempty") {
        let u = Name::from_string("u");
        let _ = env.add_decl(Declaration::Axiom {
            name: Name::from_string("Classical.choice"),
            level_params: vec![u.clone()],
            type_: lean_classical_choice_type(&u),
        });
    }
}

/// LEAN's `propext` type: `{a b : Prop} → (a ↔ b) → @Eq Prop a b`.
///
/// Note this is LEAN's convention (a single `Iff` hypothesis), NOT Clean's
/// native `propext` (`(a → b) → (b → a) → a = b`); the olean lane re-checks
/// Lean content, which applies `propext` to an `Iff`.
fn lean_propext_type() -> Expr {
    let prop = Expr::prop();
    // Body, under binders [a, b, h]: `@Eq.{1} Prop a b` (a = #2, b = #1).
    let eq_ab = Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [prop.clone(), Expr::bvar(2), Expr::bvar(1)],
    );
    // `h`'s domain, under binders [a, b]: `Iff a b` (a = #1, b = #0).
    let iff_ab = Expr::apps(
        Expr::const_(Name::from_string("Iff"), Vec::new()),
        [Expr::bvar(1), Expr::bvar(0)],
    );
    let ty = Expr::pi(BinderInfo::Default, iff_ab, eq_ab);
    let ty = Expr::pi(BinderInfo::Implicit, prop.clone(), ty);
    Expr::pi(BinderInfo::Implicit, prop, ty)
}

/// LEAN's `Classical.choice.{u}` type: `{α : Sort u} → Nonempty α → α`.
fn lean_classical_choice_type(u: &Name) -> Expr {
    let sort_u = Expr::sort(Level::param(u.clone()));
    // Body, under binders [α, h]: `α` (α = #1).
    let body = Expr::bvar(1);
    // `h`'s domain, under binder [α]: `Nonempty α` (α = #0).
    let nonempty_a = Expr::app(
        Expr::const_(Name::from_string("Nonempty"), vec![Level::param(u.clone())]),
        Expr::bvar(0),
    );
    let ty = Expr::pi(BinderInfo::Default, nonempty_a, body);
    Expr::pi(BinderInfo::Implicit, sort_u, ty)
}

/// Minimum carried-constant count before the per-constant kernel replay emits
/// progress to stderr. Small shards — every test fixture, every quick verify —
/// stay silent; only the heavy real closures (thousands of mathlib constants,
/// where the replay runs for minutes-to-hours) report.
const CAKE_VERIFY_PROGRESS_MIN: usize = 1_000;

/// Wall-clock between progress lines on a large replay. Coarse enough that even
/// a multi-hour run logs a bounded number of lines, fine enough to give a live
/// rate + ETA and to prove the run is advancing rather than hung.
const CAKE_VERIFY_PROGRESS_INTERVAL: Duration = Duration::from_secs(20);

/// Verify a cake shard reader.
///
/// `primary` selects the trust discharge for clause 3 (the per-constant kernel
/// replay):
/// * `None` — STANDALONE full replay. Build a fresh `replay_base` env and
///   re-run `add_decl`/`add_inductive` on every shard-reconstructed constant.
///   The path downloaded shards (no live env) take.
/// * `Some(primary_env)` — ENV-FUSION. `primary_env` is the in-process primary
///   gate's recheck environment, where every constant already passed the real
///   kernel re-check this run. Clause 3 is discharged per constant by the
///   round-trip oracle (`fused_oracle_matches`) instead of a second kernel
///   pass — eliminating the dominant verify-side cost. Clauses 1-2 (digest
///   binding, provenance, decl-kind, sorry, axiom-profile, record consistency)
///   and the live foundational-only axiom walk still run unchanged.
fn verify_cake_reader(
    reader: &ShardReader,
    sidecar: &ProvenanceSidecar,
    record: &GraduationRecord,
    expected_note: &str,
    primary: Option<&mut Environment>,
) -> CakeGateReport {
    let accepted: HashSet<&str> = record.result.accepted.iter().map(String::as_str).collect();
    let carried: HashMap<&str, &CarriedDefinition> = record
        .carried_definitions
        .iter()
        .map(|c| (c.name.as_str(), c))
        .collect();
    let carried_theorems: HashSet<&str> = record
        .carried_theorems
        .iter()
        .map(|c| c.name.as_str())
        .collect();
    let mut report = CakeGateReport {
        checked: reader.constants.len(),
        violations: Vec::new(),
    };
    check_record_consistency(record, &mut report.violations);
    let mut families = FamilyReplayState {
        member_to_family: HashMap::new(),
        verified: HashSet::new(),
    };
    for family in &record.carried_inductives {
        for member in &family.members_in_shard {
            // "Exactly one family": duplicates across families were already
            // reported by `check_record_consistency`; first mapping wins.
            families
                .member_to_family
                .entry(member.name.clone())
                .or_insert_with(|| family.name.clone());
        }
    }
    // v3.2: the replay environment is built from the SAME recheck base the
    // record claims the run was decided against. An unknown label fails
    // closed; a pre-v3.2 record claiming `lean-core` is a forgery (the field
    // did not exist before v3.2 — absent fields default to clean-prelude).
    let replay_base = match record.gate.recheck_base.as_str() {
        RECHECK_BASE_CLEAN_PRELUDE => RecheckBase::CleanPrelude,
        RECHECK_BASE_LEAN_CORE => {
            if record.schema != GRADUATION_SCHEMA_VERSION {
                report
                    .violations
                    .push(CakeGateViolation::RecordInconsistent {
                        name: "<record>".to_string(),
                        reason: format!(
                            "pre-v3.2-schema record claims recheck_base `{}` (the field is \
                             v3.2-only)",
                            record.gate.recheck_base
                        ),
                    });
            }
            RecheckBase::LeanCore
        }
        other => {
            report
                .violations
                .push(CakeGateViolation::RecordInconsistent {
                    name: "<record>".to_string(),
                    reason: format!(
                        "unknown recheck_base `{other}` (expected \
                         {RECHECK_BASE_CLEAN_PRELUDE} or {RECHECK_BASE_LEAN_CORE})"
                    ),
                });
            return report;
        }
    };
    // ENV-FUSION: when the caller supplies the primary gate's recheck env, use
    // it as the replay env (it already holds every kernel-verified decl) and
    // discharge clause 3 by the round-trip oracle; otherwise build a fresh
    // `replay_base` env and run the full standalone kernel replay.
    let fused = primary.is_some();
    let mut fresh_env;
    let env: &mut Environment = match primary {
        Some(primary_env) => primary_env,
        None => {
            fresh_env = replay_base.build();
            &mut fresh_env
        }
    };
    let mut seen_names: HashSet<String> = HashSet::new();
    let mut shard_names: HashSet<String> = HashSet::new();

    // The per-constant kernel replay below is the dominant cost on large
    // Real-analysis closures (thousands of constants, minutes-to-hours of
    // `add_decl`/`add_inductive` from shard-reconstructed exprs). Report
    // throttled progress so the run is observably advancing and its ETA known —
    // silent for small shards (see `CAKE_VERIFY_PROGRESS_MIN`).
    let total = reader.constants.len();
    let report_progress = total >= CAKE_VERIFY_PROGRESS_MIN;
    let started = Instant::now();
    let mut last_report = started;
    if report_progress {
        eprintln!(
            "[cake-verify] {} {total} shard constants ({} env) ...",
            if fused {
                "fused round-trip oracle over"
            } else {
                "re-checking"
            },
            replay_base.record_label()
        );
    }

    for (index, header) in reader.constants.iter().enumerate() {
        let Some(name) = reader.strings.get(header.name_idx as usize).cloned() else {
            report
                .violations
                .push(CakeGateViolation::ReconstructFailed {
                    name: format!("#{index}"),
                    error: "constant name index out of bounds".to_string(),
                });
            continue;
        };
        shard_names.insert(name.clone());
        if !seen_names.insert(name.clone()) {
            report
                .violations
                .push(CakeGateViolation::DuplicateDeclaration { name, index });
            continue;
        }
        // Seed the foundational TCB axioms (`propext`, `Classical.choice`) as
        // soon as their type prerequisites have been replayed from the shard.
        // The lean-core base starts with only `Quot`/`Quot.sound` (`init_quot`);
        // the other two cannot be added to the empty base up front because their
        // types reference core inductives (`Eq`/`Iff`, `Nonempty`) that arrive
        // during this loop. See `ensure_foundational_axioms`.
        // In fused mode `env` is the primary recheck env, where these axioms are
        // already present (the primary gate seeds them through the carried-axiom
        // path); `ensure_foundational_axioms` is idempotent, so this no-ops.
        if replay_base == RecheckBase::LeanCore {
            ensure_foundational_axioms(env);
        }
        verify_single_constant(
            reader,
            header,
            &name,
            sidecar,
            &accepted,
            &carried,
            &carried_theorems,
            expected_note,
            env,
            replay_base,
            fused,
            &mut families,
            &mut report.violations,
        );

        if report_progress {
            let done = index + 1;
            let now = Instant::now();
            if done == total || now.duration_since(last_report) >= CAKE_VERIFY_PROGRESS_INTERVAL {
                last_report = now;
                let elapsed = now.duration_since(started).as_secs_f64();
                let rate = done as f64 / elapsed.max(0.001);
                let remaining = total.saturating_sub(done);
                let eta = if rate > 0.0 {
                    remaining as f64 / rate
                } else {
                    0.0
                };
                eprintln!(
                    "[cake-verify] {done}/{total} ({pct:.1}%) re-checked · {rate:.0}/s · \
                     elapsed {elapsed:.0}s · eta ~{eta:.0}s · violations {viol}",
                    pct = 100.0 * done as f64 / total as f64,
                    viol = report.violations.len(),
                );
            }
        }
    }

    for name in &record.result.accepted {
        if !shard_names.contains(name) {
            report
                .violations
                .push(CakeGateViolation::AcceptedNameMissingFromShard { name: name.clone() });
        }
    }
    for def in &record.carried_definitions {
        if !shard_names.contains(&def.name) {
            report
                .violations
                .push(CakeGateViolation::CarriedDefinitionMissingFromShard {
                    name: def.name.clone(),
                });
        }
    }
    for thm in &record.carried_theorems {
        if !shard_names.contains(&thm.name) {
            report
                .violations
                .push(CakeGateViolation::CarriedTheoremMissingFromShard {
                    name: thm.name.clone(),
                });
        }
    }
    for family in &record.carried_inductives {
        for member in &family.members_in_shard {
            if !shard_names.contains(&member.name) {
                report
                    .violations
                    .push(CakeGateViolation::RecordInconsistent {
                        name: member.name.clone(),
                        reason: format!(
                            "graduation record's carried_inductives family `{}` lists a \
                         member the shard does not contain",
                            family.name
                        ),
                    });
            }
        }
    }

    report
}

/// Record self-consistency: `result.accepted` and the per-theorem audit
/// table must agree, and every accepted entry must carry the facts the gate
/// re-earns anyway (KernelVerified, value-typechecked, foundational-only).
///
/// The kernel replay makes verdict laundering impossible regardless; this
/// check additionally refuses *audit artifacts* whose own table contradicts
/// their headline accepted list, so downstream consumers can never read two
/// different stories out of one record.
fn check_record_consistency(record: &GraduationRecord, violations: &mut Vec<CakeGateViolation>) {
    let inconsistent = |name: &str, reason: &str| CakeGateViolation::RecordInconsistent {
        name: name.to_string(),
        reason: reason.to_string(),
    };

    for name in &record.result.accepted {
        let Some(theorem) = record.theorems.iter().find(|t| t.name == *name) else {
            violations.push(inconsistent(
                name,
                "result.accepted lists a name with no per-theorem entry",
            ));
            continue;
        };
        if !theorem.accepted {
            violations.push(inconsistent(
                name,
                "result.accepted lists a theorem whose own entry is marked rejected",
            ));
        }
        if theorem.kernel.verdict != KernelVerdict::KernelVerified {
            violations.push(inconsistent(
                name,
                "accepted theorem's entry does not carry the KernelVerified verdict",
            ));
        }
        if !theorem.kernel.value_typechecked {
            violations.push(inconsistent(
                name,
                "accepted theorem's entry is not marked value-typechecked",
            ));
        }
        if !theorem.axiom_closure.foundational_only
            || !theorem.axiom_closure.domain_axioms.is_empty()
        {
            violations.push(inconsistent(
                name,
                "accepted theorem's entry does not claim a foundational-only axiom closure",
            ));
        }
    }

    for theorem in &record.theorems {
        if theorem.accepted && !record.result.accepted.iter().any(|n| n == &theorem.name) {
            violations.push(inconsistent(
                &theorem.name,
                "entry is marked accepted but missing from result.accepted",
            ));
        }
        if theorem.accepted {
            for def in &theorem.carried_definitions {
                if !record.carried_definitions.iter().any(|c| &c.name == def) {
                    violations.push(inconsistent(
                        &theorem.name,
                        "accepted theorem requires a carried definition the record's \
                         carried_definitions section does not list",
                    ));
                }
            }
            for family in &theorem.carried_inductives {
                if !record.carried_inductives.iter().any(|c| &c.name == family) {
                    violations.push(inconsistent(
                        &theorem.name,
                        "accepted theorem requires a carried inductive family the \
                         record's carried_inductives section does not list",
                    ));
                }
            }
            for thm in &theorem.carried_theorems {
                if !record.carried_theorems.iter().any(|c| &c.name == thm) {
                    violations.push(inconsistent(
                        &theorem.name,
                        "accepted theorem requires a carried theorem the record's \
                         carried_theorems section does not list",
                    ));
                }
            }
        }
    }

    // v2 carried-definition consistency. A v1-schema record must carry none.
    if record.schema == GRADUATION_SCHEMA_VERSION_V1 && !record.carried_definitions.is_empty() {
        violations.push(inconsistent(
            "<record>",
            "v1-schema record lists carried_definitions (v1 carries none)",
        ));
    }
    let mut seen_defs: HashSet<&str> = HashSet::new();
    for def in &record.carried_definitions {
        if !seen_defs.insert(def.name.as_str()) {
            violations.push(inconsistent(
                &def.name,
                "duplicate carried_definitions entry",
            ));
        }
        if record.result.accepted.iter().any(|n| n == &def.name) {
            violations.push(inconsistent(
                &def.name,
                "carried definition also appears in result.accepted (a definition is \
                 carried, never graduated)",
            ));
        }
        if def.kernel.verdict != KernelVerdict::KernelVerified || !def.kernel.value_typechecked {
            violations.push(inconsistent(
                &def.name,
                "carried definition's entry does not carry the value-typechecked \
                 KernelVerified verdict",
            ));
        }
        if !def.axiom_closure.foundational_only || !def.axiom_closure.domain_axioms.is_empty() {
            violations.push(inconsistent(
                &def.name,
                "carried definition's entry does not claim a foundational-only axiom closure",
            ));
        }
        if def.required_by.is_empty() {
            violations.push(inconsistent(
                &def.name,
                "carried definition is required by no accepted theorem",
            ));
        }
        for user in &def.required_by {
            if !record.result.accepted.iter().any(|n| n == user) {
                violations.push(inconsistent(
                    &def.name,
                    "carried definition's required_by lists a name outside result.accepted",
                ));
            }
        }
    }

    check_record_carried_theorem_consistency(record, violations);
    check_record_family_consistency(record, violations);
}

/// v3.1 carried-theorem record consistency (the theorem analog of the
/// carried-definition block). A pre-v3.1-schema record must carry none.
///
/// The novelty field is honesty-checked for INTERNAL consistency only (a
/// `duplicate` verdict must name its match; the verdict must be evaluated):
/// the gate has no baseline to re-earn the verdict against, and a duplicate
/// carried theorem is perfectly valid — carried material is supporting
/// content, not a novelty claim, so `on_duplicate` never applies to it.
fn check_record_carried_theorem_consistency(
    record: &GraduationRecord,
    violations: &mut Vec<CakeGateViolation>,
) {
    let inconsistent = |name: &str, reason: &str| CakeGateViolation::RecordInconsistent {
        name: name.to_string(),
        reason: reason.to_string(),
    };

    if record.schema != GRADUATION_SCHEMA_VERSION
        && record.schema != GRADUATION_SCHEMA_VERSION_V31
        && !record.carried_theorems.is_empty()
    {
        violations.push(inconsistent(
            "<record>",
            "pre-v3.1-schema record lists carried_theorems (v1/v2/v3 carry none)",
        ));
    }
    let mut seen_thms: HashSet<&str> = HashSet::new();
    for thm in &record.carried_theorems {
        if !seen_thms.insert(thm.name.as_str()) {
            violations.push(inconsistent(&thm.name, "duplicate carried_theorems entry"));
        }
        if record.result.accepted.iter().any(|n| n == &thm.name) {
            violations.push(inconsistent(
                &thm.name,
                "carried theorem also appears in result.accepted (a carried theorem is \
                 supporting material, never a graduating candidate)",
            ));
        }
        if record
            .carried_definitions
            .iter()
            .any(|d| d.name == thm.name)
        {
            violations.push(inconsistent(
                &thm.name,
                "carried theorem also appears in carried_definitions",
            ));
        }
        if thm.kernel.verdict != KernelVerdict::KernelVerified || !thm.kernel.value_typechecked {
            violations.push(inconsistent(
                &thm.name,
                "carried theorem's entry does not carry the value-typechecked \
                 KernelVerified verdict",
            ));
        }
        if thm.kernel.family_checked {
            violations.push(inconsistent(
                &thm.name,
                "carried theorem's entry claims a family check — theorems are value-bearing; \
                 their certificate is the add_decl re-check",
            ));
        }
        if !thm.axiom_closure.foundational_only || !thm.axiom_closure.domain_axioms.is_empty() {
            violations.push(inconsistent(
                &thm.name,
                "carried theorem's entry does not claim a foundational-only axiom closure",
            ));
        }
        if thm.novelty.verdict == NoveltyVerdict::Unevaluated {
            violations.push(inconsistent(
                &thm.name,
                "carried theorem's novelty was never evaluated (the intake stamps the \
                 honest baseline verdict at record-write time)",
            ));
        }
        if thm.novelty.verdict == NoveltyVerdict::Duplicate && thm.novelty.matched_name.is_none() {
            violations.push(inconsistent(
                &thm.name,
                "carried theorem's duplicate novelty verdict names no matched declaration",
            ));
        }
        if thm.required_by.is_empty() {
            violations.push(inconsistent(
                &thm.name,
                "carried theorem is required by no accepted theorem",
            ));
        }
        for user in &thm.required_by {
            if !record.result.accepted.iter().any(|n| n == user) {
                violations.push(inconsistent(
                    &thm.name,
                    "carried theorem's required_by lists a name outside result.accepted",
                ));
            }
        }
    }
}

/// v3 carried-inductive record consistency (the family analog of the
/// carried-definition block). A v1/v2-schema record must carry none.
fn check_record_family_consistency(
    record: &GraduationRecord,
    violations: &mut Vec<CakeGateViolation>,
) {
    let inconsistent = |name: &str, reason: &str| CakeGateViolation::RecordInconsistent {
        name: name.to_string(),
        reason: reason.to_string(),
    };

    if record.schema != GRADUATION_SCHEMA_VERSION
        && record.schema != GRADUATION_SCHEMA_VERSION_V31
        && record.schema != GRADUATION_SCHEMA_VERSION_V3
        && !record.carried_inductives.is_empty()
    {
        violations.push(inconsistent(
            "<record>",
            "pre-v3-schema record lists carried_inductives (v1/v2 carry none)",
        ));
    }
    let mut seen_families: HashSet<&str> = HashSet::new();
    let mut seen_members: HashSet<&str> = HashSet::new();
    for family in &record.carried_inductives {
        if !seen_families.insert(family.name.as_str()) {
            violations.push(inconsistent(
                &family.name,
                "duplicate carried_inductives entry",
            ));
        }
        if record.result.accepted.iter().any(|n| n == &family.name) {
            violations.push(inconsistent(
                &family.name,
                "carried inductive family also appears in result.accepted (a family is \
                 carried, never graduated)",
            ));
        }
        if record
            .carried_definitions
            .iter()
            .any(|d| d.name == family.name)
        {
            violations.push(inconsistent(
                &family.name,
                "carried inductive family also appears in carried_definitions",
            ));
        }
        if record
            .carried_theorems
            .iter()
            .any(|t| t.name == family.name)
        {
            violations.push(inconsistent(
                &family.name,
                "carried inductive family also appears in carried_theorems",
            ));
        }
        if !family.kernel.family_checked || family.kernel.verdict != KernelVerdict::KernelVerified {
            violations.push(inconsistent(
                &family.name,
                "carried family's entry does not carry the family-checked KernelVerified \
                 verdict",
            ));
        }
        if family.kernel.value_typechecked {
            violations.push(inconsistent(
                &family.name,
                "carried family's entry claims a value typecheck — families are \
                 value-less; their certificate is family_checked",
            ));
        }
        if !family.axiom_closure.foundational_only || !family.axiom_closure.domain_axioms.is_empty()
        {
            violations.push(inconsistent(
                &family.name,
                "carried family's entry does not claim a foundational-only union closure",
            ));
        }
        if family.required_by.is_empty() {
            violations.push(inconsistent(
                &family.name,
                "carried family is required by no accepted theorem",
            ));
        }
        for user in &family.required_by {
            if !record.result.accepted.iter().any(|n| n == user) {
                violations.push(inconsistent(
                    &family.name,
                    "carried family's required_by lists a name outside result.accepted",
                ));
            }
        }
        let root_ok = family
            .members_in_shard
            .first()
            .is_some_and(|m| m.name == family.name && m.decl_kind == "inductive");
        if !root_ok {
            violations.push(inconsistent(
                &family.name,
                "carried family's members_in_shard must start with the family root \
                 (decl_kind `inductive`)",
            ));
        }
        for ctor in &family.constructors {
            if !family
                .members_in_shard
                .iter()
                .any(|m| m.name == ctor.name && m.decl_kind == "constructor")
            {
                violations.push(inconsistent(
                    &family.name,
                    "carried family's members_in_shard is missing a recorded constructor",
                ));
            }
        }
        for member in &family.members_in_shard {
            if !matches!(
                member.decl_kind.as_str(),
                "inductive" | "constructor" | "recursor"
            ) {
                violations.push(inconsistent(
                    &member.name,
                    "carried family member has a decl_kind outside \
                     inductive/constructor/recursor",
                ));
            }
            if !seen_members.insert(member.name.as_str()) {
                violations.push(inconsistent(
                    &member.name,
                    "family member listed more than once across carried_inductives \
                     (a member must belong to exactly one family)",
                ));
            }
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn verify_single_constant(
    reader: &ShardReader,
    header: &crate::types::MathverseConstantHeader,
    name: &str,
    sidecar: &ProvenanceSidecar,
    accepted: &HashSet<&str>,
    carried: &HashMap<&str, &CarriedDefinition>,
    carried_theorems: &HashSet<&str>,
    expected_note: &str,
    env: &mut Environment,
    replay_base: RecheckBase,
    fused: bool,
    families: &mut FamilyReplayState,
    violations: &mut Vec<CakeGateViolation>,
) {
    let before = violations.len();

    if header.source_system != SourceSystem::Cake as u8 {
        violations.push(CakeGateViolation::WrongSourceSystem {
            name: name.to_string(),
            found: header.source_system,
        });
    }
    if header.import_confidence != ImportConfidence::KernelVerified as u8 {
        violations.push(CakeGateViolation::NonKernelVerifiedProvenance {
            name: name.to_string(),
            found: header.import_confidence,
        });
    }
    if header.axiom_profile != AxiomProfile::NONE {
        violations.push(CakeGateViolation::NonEmptyAxiomProfile {
            name: name.to_string(),
            found: header.axiom_profile.0,
        });
    }
    // Theorems must sit in `result.accepted` OR (v3.1) in the record's
    // `carried_theorems`; definitions (v2) must sit in the record's
    // `carried_definitions`; Inductive/Constructor/Recursor constants (v3)
    // must be members of exactly one family in the record's
    // `carried_inductives`. Everything else fails. Legacy records
    // deserialize with zero carried theorems/families, so any such constant
    // under them fails `NotInAcceptedList` /
    // `UncarriedInductiveFamilyMember` — legacy strictness intact.
    let is_family_kind = header.is_inductive_family();
    let family_root = if is_family_kind {
        match families.member_to_family.get(name) {
            Some(root) => Some(root.clone()),
            None => {
                violations.push(CakeGateViolation::UncarriedInductiveFamilyMember {
                    name: name.to_string(),
                });
                None
            }
        }
    } else {
        None
    };
    let carried_entry = if is_family_kind {
        None
    } else if header.decl_kind == DeclKind::Definition as u8
        || header.decl_kind == DeclKind::Opaque as u8
    {
        // v3.2: carried opaques live in `carried_definitions` with
        // `decl_kind: "opaque"` and replay via `Declaration::Opaque`.
        match carried.get(name) {
            Some(entry) => Some(*entry),
            None => {
                violations.push(CakeGateViolation::UncarriedDefinition {
                    name: name.to_string(),
                });
                None
            }
        }
    } else {
        if header.decl_kind != DeclKind::Theorem as u8 {
            violations.push(CakeGateViolation::NotATheorem {
                name: name.to_string(),
                found: header.decl_kind,
            });
        }
        if !accepted.contains(name) && !carried_theorems.contains(name) {
            violations.push(CakeGateViolation::NotInAcceptedList {
                name: name.to_string(),
            });
        }
        None
    };
    check_graduation_binding(header, name, sidecar, expected_note, violations);
    // The MissingValue check is waived ONLY for the three family-bound
    // member kinds — an inductive's certificate is its checked family
    // replay, not a value typecheck.
    let family_bound = is_family_kind && family_root.is_some();
    if !(header.has_value() || family_bound) {
        violations.push(CakeGateViolation::MissingValue {
            name: name.to_string(),
        });
    }
    if violations.len() > before {
        return;
    }

    if let Some(root) = family_root {
        replay_family_member(
            reader,
            header,
            name,
            &root,
            env,
            replay_base,
            fused,
            families,
            violations,
        );
        return;
    }
    replay_constant(reader, header, name, carried_entry, env, fused, violations);
}

/// Clause-3 replay for v3 carried-family constants.
///
/// At the family ROOT this rebuilds the `InductiveDecl` from the shard's own
/// constants + typed header metadata (the shared
/// [`crate::inductive_replay`] reconstruction — the incremental verifier
/// uses the identical path), replays it through the kernel's checked
/// `add_inductive`, requires every shard-resident family member to match the
/// regenerated constants, and re-earns a foundational-only union closure
/// over all member types. Constructor/recursor constants encountered later
/// in the shard are verified members of an earlier successful root replay —
/// never re-added, never taken on faith.
fn replay_family_member(
    reader: &ShardReader,
    header: &crate::types::MathverseConstantHeader,
    name: &str,
    family_root: &str,
    env: &mut Environment,
    replay_base: RecheckBase,
    fused: bool,
    families: &mut FamilyReplayState,
    violations: &mut Vec<CakeGateViolation>,
) {
    if fused {
        // ENV-FUSION fast path for family members. `env` is the primary gate's
        // recheck environment, where this family already passed the checked
        // `add_inductive`/`add_inductive_core` replay this run — re-running it
        // would duplicate-declare. Discharge clause 3 by the round-trip oracle
        // per member (root, constructors, AND generated recursors/eliminators):
        // the shard's reconstructed member TYPE + level params must equal the
        // already-verified member resident in `env`, and the member's type must
        // re-earn an empty (foundational-only) axiom closure LIVE on `env`. A
        // mismatch/absence fails closed.
        let recon_type = match reconstruct_from_shard_with_level_lists(
            &reader.exprs,
            &reader.levels,
            &reader.strings,
            &reader.level_lists,
            header.type_idx,
        ) {
            Ok(t) => t,
            Err(error) => {
                violations.push(CakeGateViolation::ReconstructFailed {
                    name: name.to_string(),
                    error,
                });
                return;
            }
        };
        let level_params = match reconstruct_level_params(
            &reader.strings,
            header.level_params_start,
            header.level_params_count,
        ) {
            Ok(params) => params,
            Err(error) => {
                violations.push(CakeGateViolation::ReconstructFailed {
                    name: name.to_string(),
                    error,
                });
                return;
            }
        };
        if recon_type.has_sorry() {
            violations.push(CakeGateViolation::ContainsSorry {
                name: name.to_string(),
            });
            return;
        }
        let kname = Name::from_string(name);
        // SOUNDNESS: compare the shard-reconstructed family-member TYPE to the
        // already-kernel-verified env-resident type with the SAME round-trip
        // comparator the definition/theorem fused path uses
        // (`exprs_equal_up_to_roundtrip`), NOT a raw structural `==`. The flat
        // round-trip is lossy on exactly the kernel-MEANINGLESS fields (`MData`
        // wrappers stripped, `Let` binder name/`nonDep` reset) — fields the
        // kernel's own `def_eq`/`whnf` ignore — so a raw `==` rejected every
        // member type whose env-resident spelling carries `MData` (Lean olean
        // constructor types routinely do, e.g. `LawfulGetElem.mk`), even though
        // the shard faithfully encodes the same kernel type. The comparator does
        // no reduction, so it is strictly NARROWER than def-eq: it can only
        // REJECT, never ACCEPT, a genuinely different member type — universe
        // levels, de Bruijn indices, constants, binder info, and multiplicity all
        // stay compared exactly. Level params are still compared in order. This
        // closes the fused-path / standalone-path divergence: the standalone
        // family verb already widens through `types_equal_ignoring_binder_info`.
        match env.get_const(&kname) {
            Some(info)
                if exprs_equal_up_to_roundtrip(&info.type_, &recon_type)
                    && info.level_params == level_params => {}
            _ => {
                violations.push(CakeGateViolation::FusedOracleMismatch {
                    name: name.to_string(),
                });
                return;
            }
        }
        let mut axioms: Vec<String> = env
            .axiom_deps(&kname)
            .map(|deps| deps.iter().map(Name::to_string).collect())
            .unwrap_or_default();
        if !axioms.is_empty() {
            axioms.sort();
            axioms.dedup();
            violations.push(CakeGateViolation::AxiomDependent {
                name: name.to_string(),
                axioms,
            });
            return;
        }
        families.verified.insert(name.to_string());
        return;
    }
    if name != family_root {
        // Non-root member: must have been byte-verified by its root's
        // successful replay earlier in the shard (shard order is dependency
        // order; an out-of-order or failed family leaves this unset).
        if !families.verified.contains(name) {
            violations.push(CakeGateViolation::CarriedFamilyMismatch {
                name: name.to_string(),
                family: family_root.to_string(),
            });
        }
        return;
    }

    let reconstructed = match reconstruct_constant(name, reader, header) {
        Ok(reconstructed) => reconstructed,
        Err(error) => {
            violations.push(CakeGateViolation::ReconstructFailed {
                name: name.to_string(),
                error,
            });
            return;
        }
    };
    let metadata =
        match build_inductive_replay_metadata(reader, header, &reconstructed, NormMode::Off) {
            Ok(Some(metadata)) => metadata,
            Ok(None) => {
                violations.push(CakeGateViolation::CarriedFamilyUnsupportedShape {
                    name: name.to_string(),
                });
                return;
            }
            Err(error) => {
                violations.push(CakeGateViolation::ReconstructFailed {
                    name: name.to_string(),
                    error,
                });
                return;
            }
        };
    // v3.0 fence, re-enforced at verify time: single-type families only.
    if metadata.decl.types.len() != 1 {
        violations.push(CakeGateViolation::CarriedFamilyUnsupportedShape {
            name: name.to_string(),
        });
        return;
    }
    let family_type = &metadata.decl.types[0];
    if family_type.type_.has_sorry()
        || family_type
            .constructors
            .iter()
            .any(|ctor| ctor.type_.has_sorry())
    {
        violations.push(CakeGateViolation::ContainsSorry {
            name: name.to_string(),
        });
        return;
    }

    // The checked kernel replay — positivity, nested positivity, universe
    // constraints, recursor generation. The same checker that guards the
    // prelude decides forged families here (adversarial surface a3).
    if let Err(error) = replay_base.add_family(env, metadata.decl.clone()) {
        violations.push(CakeGateViolation::KernelRejected {
            name: name.to_string(),
            error: error.to_string(),
        });
        return;
    }
    match checked_inductive_replay_matches_shard(env, reader, &metadata, NormMode::Off) {
        Ok(ShardFamilyMatch::Matched) => {}
        Ok(ShardFamilyMatch::Mismatch { .. }) => {
            violations.push(CakeGateViolation::CarriedFamilyMismatch {
                name: name.to_string(),
                family: family_root.to_string(),
            });
            return;
        }
        Err(error) => {
            violations.push(CakeGateViolation::ReconstructFailed {
                name: name.to_string(),
                error,
            });
            return;
        }
    }

    // Re-earn the family's union closure over ALL member types (inductive
    // type + every constructor) — foundational-only or the family fails,
    // even for constructors no theorem references (surface a4).
    let mut axioms: Vec<String> = Vec::new();
    let mut closure_names: Vec<Name> = vec![family_type.name.clone()];
    closure_names.extend(family_type.constructors.iter().map(|c| c.name.clone()));
    for member in &closure_names {
        if let Some(deps) = env.axiom_deps(member) {
            axioms.extend(deps.iter().map(Name::to_string));
        }
    }
    if !axioms.is_empty() {
        axioms.sort();
        axioms.dedup();
        violations.push(CakeGateViolation::AxiomDependent {
            name: name.to_string(),
            axioms,
        });
        return;
    }

    // SOUNDNESS: only mark generated members the checked kernel replay ACTUALLY
    // re-derived into `env` as family-verified. Under `RecheckBase::LeanCore`,
    // `add_inductive_core` regenerates the inductive type, its constructors, and
    // `rec` — but NOT the value-bearing auxiliary eliminators `casesOn`/`recOn`
    // (`checked_inductive_replay_matches_shard` treats their absence as expected
    // and skips them, see `is_auxiliary_eliminator`). Those legitimately arrive
    // as `carried_definitions` and are value-checked by `replay_constant`'s
    // `add_decl`; they are NEVER legitimate name-trusted family members under the
    // lean-core base. Seeding `families.verified` from the raw `generated_names`
    // therefore vouched for `Foo.casesOn`/`Foo.recOn` that the kernel never
    // regenerated: a forged shard constant named `Foo.recOn` declared as
    // `DeclKind::Recursor` (routed here via `is_inductive_family`) then passed the
    // standalone non-root branch above on name membership ALONE, with its
    // attacker-chosen type checked NOWHERE — laundering e.g. `Foo.recOn : False`
    // to `ImportConfidence::KernelVerified`. Gating on `env.get_const(..).is_some()`
    // seeds exactly the members the kernel re-derived, so a forged
    // auxiliary-eliminator recursor now fails closed with `CarriedFamilyMismatch`.
    // Under the clean-prelude base the full `add_inductive` DOES regenerate
    // `casesOn`/`recOn`, so they are env-resident and still seeded here (and any
    // forgery is independently caught by the exact byte-match above).
    families.verified.extend(
        metadata
            .generated_names
            .iter()
            .filter(|name| env.get_const(name).is_some())
            .map(Name::to_string),
    );
}

/// Provenance binding: the constant must link a sidecar record whose digest
/// matches the header and whose notes carry the graduation binding note.
fn check_graduation_binding(
    header: &crate::types::MathverseConstantHeader,
    name: &str,
    sidecar: &ProvenanceSidecar,
    expected_note: &str,
    violations: &mut Vec<CakeGateViolation>,
) {
    let Some(prov) = sidecar.get(header.provenance_idx) else {
        violations.push(CakeGateViolation::MissingProvenanceRecord {
            name: name.to_string(),
        });
        return;
    };
    if !sidecar.verify_digest(header) {
        violations.push(CakeGateViolation::ProvenanceDigestMismatch {
            name: name.to_string(),
        });
        return;
    }
    if !prov.notes.iter().any(|note| note == expected_note) {
        violations.push(CakeGateViolation::MissingGraduationNote {
            name: name.to_string(),
        });
    }
}

/// Replay the constant through the live kernel and re-earn the verdict.
///
/// `carried_entry` is `Some` for definition constants (v2): the declaration
/// is replayed as a `Declaration::Definition` with the recorded reducibility
/// hint, and must re-earn an EMPTY non-foundational axiom closure. Theorems
/// must classify `ProofQuality::Constructive`.
/// Structural `Expr` equality UP TO the kernel-meaningless fields the flat/shard
/// round-trip canonicalizes — and only those. The flat encode→reconstruct path
/// is lossy on exactly two fields: it strips `MData` wrappers (`flat/convert.rs`
/// makes them transparent) and resets every `Let` binder NAME to `Name::anon()`
/// (and its `nonDep` optimization flag) (`flat/reconstruct.rs`). Both are
/// pretty-printing / optimization hints the kernel's own `def_eq`/`whnf` ignore
/// (every kernel `Let` handler matches `Let(_, …)`; `whnf` looks through
/// `MData`), so two terms equal under this comparator denote the same kernel
/// object. EVERYTHING kernel-relevant is compared EXACTLY: de Bruijn indices,
/// constants + their universe levels, sorts, literals, projections, application
/// shape, AND binder info + multiplicity (both observed to round-trip
/// losslessly, so kept strict — a flipped implicit/explicit binder or wrong
/// universe still fails closed). The widening does no reduction, so it is
/// strictly narrower than def-eq: it can only REJECT, never ACCEPT, a term the
/// kernel would reject. Iterative (explicit stack) to handle deep proof terms.
fn exprs_equal_up_to_roundtrip(a: &Expr, b: &Expr) -> bool {
    use clean_kernel::expr::ExprKind;
    fn peel(mut e: &Expr) -> &Expr {
        while let ExprKind::MData(_, inner) = e.kind() {
            e = inner;
        }
        e
    }
    let mut stack: Vec<(&Expr, &Expr)> = vec![(a, b)];
    while let Some((a, b)) = stack.pop() {
        let (a, b) = (peel(a), peel(b));
        match (a.kind(), b.kind()) {
            (ExprKind::App(f1, a1), ExprKind::App(f2, a2)) => {
                stack.push((f1, f2));
                stack.push((a1, a2));
            }
            (ExprKind::Lam(d1, t1, b1), ExprKind::Lam(d2, t2, b2))
            | (ExprKind::Pi(d1, t1, b1), ExprKind::Pi(d2, t2, b2)) => {
                // Binder info + multiplicity kept EXACT (round-trip preserves
                // both; 0 divergences observed) so a wrong binder shape fails.
                if d1.info != d2.info || d1.mult != d2.mult {
                    return false;
                }
                stack.push((t1, t2));
                stack.push((b1, b2));
            }
            // Let NAME (n) and nonDep flag (last field) are the round-trip's two
            // lossy fields — intentionally NOT compared. Type/value/body are.
            (ExprKind::Let(_, t1, v1, b1, _), ExprKind::Let(_, t2, v2, b2, _)) => {
                stack.push((t1, t2));
                stack.push((v1, v2));
                stack.push((b1, b2));
            }
            (ExprKind::Proj(n1, i1, e1), ExprKind::Proj(n2, i2, e2)) => {
                if n1 != n2 || i1 != i2 {
                    return false;
                }
                stack.push((e1, e2));
            }
            // Leaves (BVar/FVar/Sort/Const/Lit/SProp/…) and any other variant:
            // exact structural compare. (Const carries its universe LevelVec and
            // Sort its Level, so universe instantiation is compared exactly.)
            (ka, kb) => {
                if ka != kb {
                    return false;
                }
            }
        }
    }
    true
}

/// ENV-FUSION round-trip oracle. The shard's reconstructed `decl` must encode the
/// SAME kernel object as the declaration already resident in `env` — which, on
/// the fused path, is the primary gate's recheck environment, where this exact
/// declaration already passed the real `Environment::add_decl` kernel re-check
/// this run. The oracle is a round-trip INTEGRITY check ("did the shard bytes
/// faithfully encode the verified decl?"), not a kernel surrogate: the
/// foundational-only axiom walk still runs LIVE on `env` afterward.
///
/// Comparison is via [`exprs_equal_up_to_roundtrip`] — exact on every
/// kernel-relevant field, tolerant only of the two fields the flat/shard
/// round-trip canonicalizes (`MData` wrappers, `Let` binder names/`nonDep`),
/// which the kernel itself ignores. Level params are compared in ORDER. A `true`
/// result means the shard faithfully encodes the kernel-verified term; `false`
/// (mismatch or the name absent from the verified env) fails the gate closed.
fn fused_oracle_matches(env: &Environment, name: &Name, decl: &Declaration) -> bool {
    let Some(info) = env.get_const(name) else {
        return false;
    };
    let (type_, value, level_params) = match decl {
        Declaration::Theorem {
            type_,
            value,
            level_params,
            ..
        }
        | Declaration::Opaque {
            type_,
            value,
            level_params,
            ..
        }
        | Declaration::Definition {
            type_,
            value,
            level_params,
            ..
        } => (type_, value, level_params),
        _ => return false,
    };
    info.level_params == *level_params
        && exprs_equal_up_to_roundtrip(&info.type_, type_)
        && matches!(info.value.as_ref(), Some(v) if exprs_equal_up_to_roundtrip(v, value))
}

fn replay_constant(
    reader: &ShardReader,
    header: &crate::types::MathverseConstantHeader,
    name: &str,
    carried_entry: Option<&CarriedDefinition>,
    env: &mut Environment,
    fused: bool,
    violations: &mut Vec<CakeGateViolation>,
) {
    let reconstruct = |idx: u32| {
        reconstruct_from_shard_with_level_lists(
            &reader.exprs,
            &reader.levels,
            &reader.strings,
            &reader.level_lists,
            idx,
        )
    };
    let (type_, value) = match (reconstruct(header.type_idx), reconstruct(header.value_idx)) {
        (Ok(t), Ok(v)) => (t, v),
        (Err(error), _) | (_, Err(error)) => {
            violations.push(CakeGateViolation::ReconstructFailed {
                name: name.to_string(),
                error,
            });
            return;
        }
    };
    let level_params = match reconstruct_level_params(
        &reader.strings,
        header.level_params_start,
        header.level_params_count,
    ) {
        Ok(params) => params,
        Err(error) => {
            violations.push(CakeGateViolation::ReconstructFailed {
                name: name.to_string(),
                error,
            });
            return;
        }
    };
    if type_.has_sorry() || value.has_sorry() {
        violations.push(CakeGateViolation::ContainsSorry {
            name: name.to_string(),
        });
        return;
    }

    let kernel_name = Name::from_string(name);
    let decl = match carried_entry {
        Some(entry) if entry.decl_kind == "opaque" => Declaration::Opaque {
            name: kernel_name.clone(),
            level_params,
            type_,
            value,
        },
        Some(entry) => Declaration::Definition {
            name: kernel_name.clone(),
            level_params,
            type_,
            value,
            is_reducible: entry.is_reducible,
        },
        None => Declaration::Theorem {
            name: kernel_name.clone(),
            level_params,
            type_,
            value,
        },
    };
    if fused {
        // ENV-FUSION fast path. `env` IS the primary gate's recheck environment
        // (`graduate_with_base`'s `GateState.recheck`), in which this exact
        // declaration already passed the real `Environment::add_decl` kernel
        // re-check this same run. Re-running `add_decl` here would re-do that
        // identical work on shard-reconstructed exprs (the verify-side cost).
        // Instead, discharge clause 3 by the ROUND-TRIP ORACLE: the shard's
        // reconstructed decl must be structurally identical to the
        // already-kernel-verified decl resident in `env`. A match means the
        // shard faithfully encodes a decl the kernel accepted -> verified,
        // skip the re-check. A mismatch/absence means the shard does NOT encode
        // the verified decl (serializer defect or tamper) -> fail closed. The
        // foundational-only axiom walk below still runs LIVE on `env`.
        if !fused_oracle_matches(env, &kernel_name, &decl) {
            violations.push(CakeGateViolation::FusedOracleMismatch {
                name: name.to_string(),
            });
            return;
        }
    } else if let Err(error) = env.add_decl(decl) {
        violations.push(CakeGateViolation::KernelRejected {
            name: name.to_string(),
            error: error.to_string(),
        });
        return;
    }

    if carried_entry.is_some() {
        // Definitions: re-earn the foundational-only closure directly
        // (`proof_quality` reports `NotATheorem` for definitions).
        let mut axioms: Vec<String> = env
            .axiom_deps(&kernel_name)
            .map(|deps| deps.iter().map(Name::to_string).collect())
            .unwrap_or_default();
        if !axioms.is_empty() {
            axioms.sort();
            violations.push(CakeGateViolation::AxiomDependent {
                name: name.to_string(),
                axioms,
            });
        }
        return;
    }

    match env.proof_quality(&kernel_name) {
        Some(ProofQuality::Constructive) => {}
        Some(ProofQuality::AxiomDependent { axioms, .. }) => {
            violations.push(CakeGateViolation::AxiomDependent {
                name: name.to_string(),
                axioms: axioms.iter().map(Name::to_string).collect(),
            });
        }
        other => {
            violations.push(CakeGateViolation::KernelRejected {
                name: name.to_string(),
                error: format!("unexpected proof quality after replay: {other:?}"),
            });
        }
    }
}

#[cfg(test)]
mod fused_oracle_comparator_tests {
    use super::exprs_equal_up_to_roundtrip;
    use clean_kernel::expr::{BinderInfo, Expr};
    use clean_kernel::level::Level;
    use clean_kernel::Name;

    /// TOLERANCE (the regression guard for the `FusedOracleMismatch` bug): two
    /// terms that differ ONLY in the fields the flat/shard round-trip
    /// canonicalizes — `MData` wrappers and `Let` binder names/`nonDep` — must
    /// compare EQUAL. (`Nat.add`'s type carries MData; `eq_of_heq` /
    /// `Nat.succ_le_succ` values carry named `let`s — the real bug constants.)
    #[test]
    fn test_roundtrip_comparator_tolerates_mdata_and_let_name() {
        // primary (olean) spelling: MData-wrapped Const, and a NAMED let.
        let primary = Expr::app(
            Expr::mdata(vec![], Expr::const_str("Nat")),
            Expr::let_named(
                Name::from_string("this"),
                Expr::prop(),
                Expr::bvar(0),
                Expr::bvar(0),
                false,
            ),
        );
        // shard spelling: MData stripped, let name reset to anon, nonDep flipped.
        let shard = Expr::app(
            Expr::const_str("Nat"),
            Expr::let_named(
                Name::anon(),
                Expr::prop(),
                Expr::bvar(0),
                Expr::bvar(0),
                true,
            ),
        );
        assert!(
            exprs_equal_up_to_roundtrip(&primary, &shard),
            "comparator must look through MData and ignore Let name/nonDep"
        );
    }

    /// FAIL-CLOSED: the widening must NOT accept a genuinely different kernel
    /// object. A swapped constant, a changed universe level, or a flipped binder
    /// info must each still fail — otherwise the oracle would launder tamper.
    #[test]
    fn test_roundtrip_comparator_rejects_real_tamper() {
        // swapped constant name
        assert!(
            !exprs_equal_up_to_roundtrip(&Expr::const_str("Nat"), &Expr::const_str("Int")),
            "different constant must fail"
        );
        // different universe level
        assert!(
            !exprs_equal_up_to_roundtrip(
                &Expr::sort(Level::zero()),
                &Expr::sort(Level::succ(Level::zero()))
            ),
            "different universe level must fail"
        );
        // flipped binder info (implicit vs explicit) on an otherwise-identical Pi
        let pi_impl = Expr::pi(BinderInfo::Implicit, Expr::prop(), Expr::bvar(0));
        let pi_expl = Expr::pi(BinderInfo::Default, Expr::prop(), Expr::bvar(0));
        assert!(
            !exprs_equal_up_to_roundtrip(&pi_impl, &pi_expl),
            "flipped binder info must fail (kept exact)"
        );
        // different de Bruijn index
        assert!(
            !exprs_equal_up_to_roundtrip(&Expr::bvar(0), &Expr::bvar(1)),
            "different de Bruijn index must fail"
        );
    }
}

#[cfg(test)]
mod foundational_axiom_tests {
    use super::{lean_classical_choice_type, lean_propext_type};
    use clean_kernel::expr::{BinderInfo, Expr, ExprKind};
    use clean_kernel::level::Level;
    use clean_kernel::Name;

    /// Peel an application spine to its head `Const`, returning the name, the
    /// head's universe levels, and the argument expressions (outermost-first).
    fn const_head(expr: &Expr) -> Option<(String, Vec<Level>, Vec<Expr>)> {
        let mut args = Vec::new();
        let mut cur = expr.clone();
        loop {
            match cur.kind() {
                ExprKind::App(f, a) => {
                    args.push((**a).clone());
                    cur = (**f).clone();
                }
                ExprKind::Const(n, levels) => {
                    args.reverse();
                    return Some((n.to_string(), levels.to_vec(), args));
                }
                _ => return None,
            }
        }
    }

    fn as_bvar(expr: &Expr) -> Option<u32> {
        match expr.kind() {
            ExprKind::BVar(i) => Some(*i),
            _ => None,
        }
    }

    /// Pin LEAN's `propext` type EXACTLY (shape + binder kinds + de Bruijn
    /// indices): `{a b : Prop} → (a ↔ b) → @Eq Prop a b`. A regression here
    /// (e.g. a flipped index or a dropped hypothesis) would let the lean-core
    /// cake gate seed a mis-typed `propext` and launder a false proof, so this
    /// is a soundness guard. (End-to-end, `crown-proofs` `CakeRepro.cake_repro`
    /// — Lean's `eq_true`, i.e. `propext` applied to a real `Iff` — must
    /// kernel-replay against the seeded axiom, which independently pins it.)
    #[test]
    fn test_lean_propext_type_is_exact() {
        let ty = lean_propext_type();
        // {a : Prop}
        let ExprKind::Pi(bd_a, dom_a, body_a) = ty.kind() else {
            panic!("propext: outer not Pi");
        };
        assert_eq!(bd_a.info, BinderInfo::Implicit, "a must be implicit");
        assert!(matches!(dom_a.kind(), ExprKind::Sort(l) if *l == Level::zero()));
        // {b : Prop}
        let ExprKind::Pi(bd_b, dom_b, body_b) = body_a.kind() else {
            panic!("propext: 2nd not Pi");
        };
        assert_eq!(bd_b.info, BinderInfo::Implicit, "b must be implicit");
        assert!(matches!(dom_b.kind(), ExprKind::Sort(l) if *l == Level::zero()));
        // (a ↔ b) → ...
        let ExprKind::Pi(bd_h, dom_h, concl) = body_b.kind() else {
            panic!("propext: 3rd not Pi");
        };
        assert_eq!(bd_h.info, BinderInfo::Default);
        // hypothesis: Iff a b  (a = #1, b = #0 under binders [a,b])
        let (iff_head, iff_levels, iff_args) = const_head(dom_h).expect("hypothesis is an app");
        assert_eq!(iff_head, "Iff");
        assert!(iff_levels.is_empty(), "Iff is Prop-valued, no level params");
        assert_eq!(iff_args.len(), 2);
        assert_eq!(as_bvar(&iff_args[0]), Some(1));
        assert_eq!(as_bvar(&iff_args[1]), Some(0));
        // conclusion: @Eq.{1} Prop a b  (a = #2, b = #1 under binders [a,b,h])
        let (eq_head, eq_levels, eq_args) = const_head(concl).expect("conclusion is an app");
        assert_eq!(eq_head, "Eq");
        // Eq is instantiated at universe 1 (Prop : Sort 1).
        assert_eq!(eq_levels, vec![Level::succ(Level::zero())]);
        assert_eq!(eq_args.len(), 3);
        assert!(matches!(eq_args[0].kind(), ExprKind::Sort(l) if *l == Level::zero()));
        assert_eq!(as_bvar(&eq_args[1]), Some(2));
        assert_eq!(as_bvar(&eq_args[2]), Some(1));
    }

    /// Pin LEAN's `Classical.choice.{u}` type EXACTLY:
    /// `{α : Sort u} → Nonempty α → α`.
    #[test]
    fn test_lean_classical_choice_type_is_exact() {
        let u = Name::from_string("u");
        let ty = lean_classical_choice_type(&u);
        // {α : Sort u}
        let ExprKind::Pi(bd_a, dom_a, body_a) = ty.kind() else {
            panic!("choice: outer not Pi");
        };
        assert_eq!(bd_a.info, BinderInfo::Implicit, "α must be implicit");
        assert!(matches!(dom_a.kind(), ExprKind::Sort(l) if *l == Level::param(u.clone())));
        // Nonempty α → α
        let ExprKind::Pi(bd_h, dom_h, concl) = body_a.kind() else {
            panic!("choice: 2nd not Pi");
        };
        assert_eq!(bd_h.info, BinderInfo::Default);
        let (ne_head, ne_levels, ne_args) = const_head(dom_h).expect("hypothesis is an app");
        assert_eq!(ne_head, "Nonempty");
        assert_eq!(ne_levels, vec![Level::param(u.clone())]);
        assert_eq!(ne_args.len(), 1);
        assert_eq!(as_bvar(&ne_args[0]), Some(0)); // α = #0 under [α]
        assert_eq!(as_bvar(concl), Some(1)); // result α = #1 under [α, h]
    }
}
