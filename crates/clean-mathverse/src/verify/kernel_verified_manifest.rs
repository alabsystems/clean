// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `kernel-verified.json`, schema 2: the names a corpus run accepted, and the
//! identity of the theory and the checker that accepted them (unit P6, slice 1
//! of `docs/plans/SELF_PROOF_EXECUTION_PLAN_2026-11-12.md`; design
//! `designs/2026-11-16-p6-acceptance-identity.md`).
//!
//! The file name is kept (a path a dozen callers and the Coq baseline layout
//! use), and so is the type name (a root of the P7 census); the tier inside
//! decides what the file means. Every writer in this build runs a legacy
//! checker under a legacy profile, so every manifest it writes is
//! `development` tier: its names are data for regression gates, diffs and
//! target ranking, and nothing grants a label from it (P2 clause 1). No
//! reader accepts a `reference` identity until the reference producer lands
//! with its receipts (slice 1b).
//!
//! Every deserialization path validates ([`KernelVerifiedManifest`] has a
//! hand-written `Deserialize`), and the fields are private, so no manifest
//! without a valid identity exists in memory. Schema 1 is refused, never
//! upgraded; the one exception is [`RegressionReference`], a names-only reader
//! for the migration of the gitignored Coq baselines, which expires.

mod error;
mod identity;

use std::collections::BTreeSet;
use std::path::Path;

use serde::{Deserialize, Serialize};

pub use error::ManifestError;
#[cfg(test)]
pub(crate) use identity::{test_run, test_run_in};
pub use identity::{
    AcceptanceIdentity, AcceptanceTier, BaseEnvironment, BaseVariant, BuildIdentity, CheckSettings,
    CheckerEntry, DevelopmentRun, Discipline, Elision, ExecutableIdentity, Imports,
    InductiveReplay, KernelTheoryName, LegacyEntry, ProfileTheory, ReferenceTheoryClaim,
    TheoryRecord,
};

use crate::error::{MathverseError, MathverseResult};
use crate::verify::incremental::IncrementalVerifyReport;

/// The schema this build writes and reads.
pub const SCHEMA_VERSION: u32 = 2;

/// Inputs of the `stamp-verified --parallel` incremental cache key: the
/// requested knobs that can change which constants a module accepts, the
/// checker entry, and the SHA-256 of the executable, so every cache hit was
/// minted by these bytes under these settings (P6 review finding on cached
/// rows). Never persisted in a manifest: the manifest's identity records the
/// applied values.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct StampEnvFingerprint {
    /// clean-kernel crate version (`clean_kernel::VERSION`).
    pub kernel_version: String,
    /// The toolchain the binary was built with
    /// (`CLEAN_MATHVERSE_TOOLCHAIN_VERSION`, else `"unknown"`).
    pub toolchain: String,
    /// `CLEAN_KERNEL_HEARTBEAT` in effect: `"default"` if unset, else the raw
    /// value (`"0"` = unlimited).
    pub heartbeat: String,
    /// Proof-value elision policy: `"none"` | `"opaque"` | `"opaque-and-theorem"`.
    pub elision_policy: String,
    /// `CLEAN_MAX_CLOSURE_MODULES` ceiling actually used (default 1500).
    pub max_closure_modules: usize,
    /// Trusted-context variant: `"closure-root"` or `"prelude-only"`.
    pub prelude_variant: String,
    /// The checker entry whose verdicts the cache holds.
    pub checker_entry: String,
    /// SHA-256 of the executable that minted (and may replay) the verdicts.
    pub exe_sha256: String,
}

impl StampEnvFingerprint {
    /// A stable, single-line key folding every field that can change a verdict.
    /// Used as the incremental-cache's per-module closure-hash prefix: any change
    /// here re-keys every module, forcing an honest full re-verify.
    #[must_use]
    pub fn cache_key(&self) -> String {
        format!(
            "kv={};tc={};hb={};el={};mcm={};pv={};rd={};ck={};exe={}",
            self.kernel_version,
            self.toolchain,
            self.heartbeat,
            self.elision_policy,
            self.max_closure_modules,
            self.prelude_variant,
            REPLAY_DISCIPLINE,
            self.checker_entry,
            self.exe_sha256,
        )
    }
}

/// The verdict discipline the `.olean` re-check lanes mint under, folded into
/// [`StampEnvFingerprint::cache_key`]. The crate version does not move when the
/// discipline does, so without this a verdict cached by a binary that checked
/// each target with its own declaration resident (and with Clean's extended
/// reducer theory) would be REPLAYED as a cache hit: the 2026-09-23 forgeries
/// `forged3_self : False := forged3_self` and `System.Platform.isOSX = true :=
/// rfl` were stamped exactly that way. It is [`Discipline::LeanReplay`]'s
/// spelling; bump both whenever what earns an acceptance changes.
pub(crate) const REPLAY_DISCIPLINE: &str = "lean-replay-order+lean-kernel-theory/1";

/// Sidecar manifest of the constants a corpus run accepted, with the identity
/// of the theory and the checker that accepted them.
#[derive(Debug, Clone, PartialEq)]
pub struct KernelVerifiedManifest {
    tool: String,
    created_at: String,
    shard_dir: String,
    shards_loaded: usize,
    identity: AcceptanceIdentity,
    total_constants: usize,
    accepted: usize,
    axiom_accepted: usize,
    unsafe_accepted: usize,
    axiom_fallback: usize,
    failed: usize,
    cycle_skipped: usize,
    reconstruct_failed: usize,
    cache_hits: usize,
    elapsed_secs: f64,
    accepted_names: Vec<String>,
}

/// The serialized form. Field order is the JSON key order.
#[derive(Serialize)]
struct ManifestOut<'a> {
    schema_version: u32,
    tool: &'a str,
    created_at: &'a str,
    shard_dir: &'a str,
    shards_loaded: usize,
    identity: &'a AcceptanceIdentity,
    total_constants: usize,
    accepted: usize,
    axiom_accepted: usize,
    unsafe_accepted: usize,
    axiom_fallback: usize,
    failed: usize,
    cycle_skipped: usize,
    reconstruct_failed: usize,
    cache_hits: usize,
    elapsed_secs: f64,
    accepted_names: &'a [String],
}

/// The deserialized form, checked by [`KernelVerifiedManifest::from_value`]
/// before it becomes a manifest. Unknown fields are refused, so a hybrid file
/// (schema 2 with a leftover `kernel_verified_names`) is refused rather than
/// half read.
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct ManifestIn {
    schema_version: u32,
    tool: String,
    created_at: String,
    shard_dir: String,
    shards_loaded: usize,
    identity: AcceptanceIdentity,
    total_constants: usize,
    accepted: usize,
    axiom_accepted: usize,
    unsafe_accepted: usize,
    axiom_fallback: usize,
    failed: usize,
    cycle_skipped: usize,
    reconstruct_failed: usize,
    cache_hits: usize,
    elapsed_secs: f64,
    accepted_names: Vec<String>,
}

impl Serialize for KernelVerifiedManifest {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        ManifestOut {
            schema_version: SCHEMA_VERSION,
            tool: &self.tool,
            created_at: &self.created_at,
            shard_dir: &self.shard_dir,
            shards_loaded: self.shards_loaded,
            identity: &self.identity,
            total_constants: self.total_constants,
            accepted: self.accepted,
            axiom_accepted: self.axiom_accepted,
            unsafe_accepted: self.unsafe_accepted,
            axiom_fallback: self.axiom_fallback,
            failed: self.failed,
            cycle_skipped: self.cycle_skipped,
            reconstruct_failed: self.reconstruct_failed,
            cache_hits: self.cache_hits,
            elapsed_secs: self.elapsed_secs,
            accepted_names: &self.accepted_names,
        }
        .serialize(serializer)
    }
}

impl<'de> Deserialize<'de> for KernelVerifiedManifest {
    fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let value = serde_json::Value::deserialize(deserializer)?;
        Self::from_value(value).map_err(serde::de::Error::custom)
    }
}

/// The per-run counters a writer copies besides the accepted names.
#[derive(Debug, Clone, Default)]
struct Counts {
    total_constants: usize,
    axiom_accepted: usize,
    unsafe_accepted: usize,
    axiom_fallback: usize,
    failed: usize,
    cycle_skipped: usize,
    reconstruct_failed: usize,
    cache_hits: usize,
    elapsed_secs: f64,
}

impl Counts {
    fn of_report(report: &IncrementalVerifyReport) -> Self {
        Self {
            total_constants: report.total,
            axiom_accepted: report.axiom_accepted,
            unsafe_accepted: report.unsafe_accepted,
            axiom_fallback: report.axiom_fallback,
            failed: report.failed,
            cycle_skipped: report.cycle_skipped,
            reconstruct_failed: report.reconstruct_failed,
            cache_hits: 0,
            elapsed_secs: report.elapsed_secs,
        }
    }
}

impl KernelVerifiedManifest {
    fn assemble(
        tool: &str,
        shard_dir: &str,
        shards_loaded: usize,
        identity: AcceptanceIdentity,
        counts: Counts,
        names: Vec<String>,
    ) -> Self {
        let accepted_names: Vec<String> = names
            .into_iter()
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect();
        Self {
            tool: tool.to_string(),
            created_at: crate::release::now_iso8601(),
            shard_dir: shard_dir.to_string(),
            shards_loaded,
            identity,
            total_constants: counts.total_constants,
            accepted: accepted_names.len(),
            axiom_accepted: counts.axiom_accepted,
            unsafe_accepted: counts.unsafe_accepted,
            axiom_fallback: counts.axiom_fallback,
            failed: counts.failed,
            cycle_skipped: counts.cycle_skipped,
            reconstruct_failed: counts.reconstruct_failed,
            cache_hits: counts.cache_hits,
            elapsed_secs: counts.elapsed_secs,
            accepted_names,
        }
    }

    /// A development manifest from an incremental corpus replay
    /// (`verify::incremental::try_add_constant`): `verify-kernel --corpus`,
    /// `stamp-verified` and the Coq lane. `tool` names the verb that ran.
    #[must_use]
    pub fn from_incremental_report(
        tool: &str,
        shard_dir: &str,
        shards_loaded: usize,
        report: &IncrementalVerifyReport,
        run: DevelopmentRun,
    ) -> Self {
        Self::assemble(
            tool,
            shard_dir,
            shards_loaded,
            AcceptanceIdentity::development(LegacyEntry::IncrementalReplay, run),
            Counts::of_report(report),
            report.kernel_verified_names.clone(),
        )
    }

    /// A development manifest from `stamp-verified --parallel`
    /// (`check_value_bearing` through `check_decl_readonly_with_heartbeat`).
    /// `cache_hits` modules replayed verdicts the same executable minted
    /// under the same settings (their cache key folds both).
    #[must_use]
    pub fn from_parallel_report(
        shard_dir: &str,
        shards_loaded: usize,
        report: &IncrementalVerifyReport,
        run: DevelopmentRun,
        cache_hits: usize,
    ) -> Self {
        let mut counts = Counts::of_report(report);
        counts.cache_hits = cache_hits;
        Self::assemble(
            "clean mathverse stamp-verified --parallel",
            shard_dir,
            shards_loaded,
            AcceptanceIdentity::development(LegacyEntry::ParallelReadonlyReplay, run),
            counts,
            report.kernel_verified_names.clone(),
        )
    }

    /// A development sidecar from one sharded worker's check of one module's
    /// own constants (`kernel_verify_const_with_heartbeat`). The worker trusts
    /// the module's imports, so `imports` is forced to `trusted`. `module`
    /// is recorded as the shard directory of a per-module sidecar.
    #[must_use]
    pub fn from_sharded_worker(
        module: &str,
        total_constants: usize,
        axiom_accepted: usize,
        failed: usize,
        elapsed_secs: f64,
        accepted_names: Vec<String>,
        mut run: DevelopmentRun,
    ) -> Self {
        run.imports = Imports::Trusted;
        Self::assemble(
            "mathverse_shard verify-kernel --module",
            module,
            1,
            AcceptanceIdentity::development(LegacyEntry::ShardedConstTypecheck, run),
            Counts {
                total_constants,
                axiom_accepted,
                failed,
                elapsed_secs,
                ..Counts::default()
            },
            accepted_names,
        )
    }

    /// Merge per-module sidecars into one consolidated manifest (the sharded
    /// driver's reduce step). Names are set-unioned and every counter summed;
    /// each worker reports its own module's constants, which are disjoint.
    ///
    /// # Errors
    /// [`ManifestError::EmptyMerge`] for no sidecars, and
    /// [`ManifestError::IdentityMismatch`] when two sidecars are not
    /// [`AcceptanceIdentity::same_build`]: a sidecar written by another binary
    /// or under other settings is another checker run, and a consolidated
    /// file can name only one.
    pub fn merge(shard_dir: &str, sidecars: &[Self]) -> Result<Self, ManifestError> {
        let first = sidecars.first().ok_or(ManifestError::EmptyMerge)?;
        let mut counts = Counts::default();
        let mut names = Vec::new();
        for m in sidecars {
            first.identity.same_build(&m.identity).map_err(|e| {
                ManifestError::IdentityMismatch(format!("sidecar `{}`: {e}", m.shard_dir))
            })?;
            names.extend(m.accepted_names.iter().cloned());
            counts.total_constants += m.total_constants;
            counts.axiom_accepted += m.axiom_accepted;
            counts.unsafe_accepted += m.unsafe_accepted;
            counts.axiom_fallback += m.axiom_fallback;
            counts.failed += m.failed;
            counts.cycle_skipped += m.cycle_skipped;
            counts.reconstruct_failed += m.reconstruct_failed;
            counts.cache_hits += m.cache_hits;
            counts.elapsed_secs += m.elapsed_secs;
        }
        Ok(Self::assemble(
            "mathverse_shard verify-kernel --corpus-sharded",
            shard_dir,
            sidecars.len(),
            first.identity.clone(),
            counts,
            names,
        ))
    }

    /// Validate a parsed JSON value: schema first, then identity, then the
    /// counts.
    ///
    /// # Errors
    /// The [`ManifestError`] naming the refusal.
    pub fn from_value(value: serde_json::Value) -> Result<Self, ManifestError> {
        let object = value
            .as_object()
            .ok_or_else(|| ManifestError::Malformed("a manifest is a JSON object".to_string()))?;
        match object.get("schema_version") {
            Some(v) if v.as_u64() == Some(u64::from(SCHEMA_VERSION)) => {}
            Some(v) => {
                return Err(ManifestError::UnsupportedSchema {
                    found: v.to_string(),
                })
            }
            None => {
                return Err(ManifestError::UnsupportedSchema {
                    found: "absent".to_string(),
                })
            }
        }
        if !object.contains_key("identity") {
            return Err(ManifestError::NoIdentity);
        }
        let raw: ManifestIn =
            serde_json::from_value(value).map_err(|e| ManifestError::Malformed(e.to_string()))?;
        debug_assert_eq!(raw.schema_version, SCHEMA_VERSION);
        raw.identity.validate()?;
        let distinct: BTreeSet<&str> = raw.accepted_names.iter().map(String::as_str).collect();
        if raw.accepted != raw.accepted_names.len() || distinct.len() != raw.accepted_names.len() {
            return Err(ManifestError::CountMismatch {
                count: raw.accepted,
                names: distinct.len(),
            });
        }
        Ok(Self {
            tool: raw.tool,
            created_at: raw.created_at,
            shard_dir: raw.shard_dir,
            shards_loaded: raw.shards_loaded,
            identity: raw.identity,
            total_constants: raw.total_constants,
            accepted: raw.accepted,
            axiom_accepted: raw.axiom_accepted,
            unsafe_accepted: raw.unsafe_accepted,
            axiom_fallback: raw.axiom_fallback,
            failed: raw.failed,
            cycle_skipped: raw.cycle_skipped,
            reconstruct_failed: raw.reconstruct_failed,
            cache_hits: raw.cache_hits,
            elapsed_secs: raw.elapsed_secs,
            accepted_names: raw.accepted_names,
        })
    }

    /// Serialize to pretty JSON.
    ///
    /// # Errors
    /// Returns an error if serialization fails.
    pub fn to_json(&self) -> MathverseResult<String> {
        serde_json::to_string_pretty(self).map_err(MathverseError::from)
    }

    /// Write the manifest to `path` as pretty JSON.
    ///
    /// # Errors
    /// Returns an error if serialization or the file write fails.
    pub fn write_to_file(&self, path: &Path) -> MathverseResult<()> {
        std::fs::write(path, self.to_json()?)?;
        Ok(())
    }

    /// Read and validate a manifest from `path`.
    ///
    /// # Errors
    /// An I/O or JSON error, or [`MathverseError::Manifest`] naming the file
    /// and the [`ManifestError`] that refused it.
    pub fn from_file(path: &Path) -> MathverseResult<Self> {
        let data = std::fs::read_to_string(path)?;
        let value: serde_json::Value = serde_json::from_str(&data)?;
        Self::from_value(value).map_err(|source| MathverseError::Manifest {
            path: path.display().to_string(),
            source,
        })
    }

    /// What a grant site says when offered this manifest. Every manifest this
    /// build can read is `development` tier, which confers no label (P2
    /// clause 1); the reference tier has no producer and no reader yet.
    #[must_use]
    pub fn grant_refusal(&self, purpose: &'static str) -> ManifestError {
        match self.tier() {
            AcceptanceTier::Development => ManifestError::DevelopmentTier { purpose },
            AcceptanceTier::Reference => ManifestError::NoReferenceProducer,
        }
    }

    /// What a grant site (a stamp, a release, a label) returns when offered
    /// the manifest at `path` for `purpose`: the file's own validation
    /// refusal, else [`Self::grant_refusal`]. In this build there is no
    /// other outcome, so the return type is the error itself.
    #[must_use]
    pub fn refuse_grant(path: &Path, purpose: &'static str) -> MathverseError {
        match Self::from_file(path) {
            Err(e) => e,
            Ok(manifest) => MathverseError::Manifest {
                path: path.display().to_string(),
                source: manifest.grant_refusal(purpose),
            },
        }
    }

    /// The identity record.
    #[must_use]
    pub fn identity(&self) -> &AcceptanceIdentity {
        &self.identity
    }

    /// The tier a reader may grant from.
    #[must_use]
    pub fn tier(&self) -> AcceptanceTier {
        self.identity.tier()
    }

    /// The accepted names, sorted and distinct.
    #[must_use]
    pub fn accepted_names(&self) -> &[String] {
        &self.accepted_names
    }

    /// `accepted_names().len()`.
    #[must_use]
    pub fn accepted(&self) -> usize {
        self.accepted
    }

    /// The verb that wrote the manifest.
    #[must_use]
    pub fn tool(&self) -> &str {
        &self.tool
    }

    /// The shard directory (or module, for a sharded sidecar) checked.
    #[must_use]
    pub fn shard_dir(&self) -> &str {
        &self.shard_dir
    }

    /// Shards (or sidecars) merged into the run.
    #[must_use]
    pub fn shards_loaded(&self) -> usize {
        self.shards_loaded
    }

    /// Constants the run considered.
    #[must_use]
    pub fn total_constants(&self) -> usize {
        self.total_constants
    }

    /// Value-less constants accepted as well-formed axioms (not proof-checked).
    #[must_use]
    pub fn axiom_accepted(&self) -> usize {
        self.axiom_accepted
    }

    /// Value-bearing `unsafe` constants accepted type-only.
    #[must_use]
    pub fn unsafe_accepted(&self) -> usize {
        self.unsafe_accepted
    }

    /// Value-bearing constants that fell back to an axiom.
    #[must_use]
    pub fn axiom_fallback(&self) -> usize {
        self.axiom_fallback
    }

    /// Constants the checker refused.
    #[must_use]
    pub fn failed(&self) -> usize {
        self.failed
    }

    /// Constants skipped for a dependency cycle.
    #[must_use]
    pub fn cycle_skipped(&self) -> usize {
        self.cycle_skipped
    }

    /// Constants whose reconstruction failed.
    #[must_use]
    pub fn reconstruct_failed(&self) -> usize {
        self.reconstruct_failed
    }

    /// Modules whose verdicts came from the incremental cache.
    #[must_use]
    pub fn cache_hits(&self) -> usize {
        self.cache_hits
    }

    /// Wall-clock seconds.
    #[must_use]
    pub fn elapsed_secs(&self) -> f64 {
        self.elapsed_secs
    }
}

/// The end of the schema-1 migration window for [`RegressionReference`]:
/// 2027-01-01T00:00:00Z. After it the names-only reader refuses schema 1 like
/// every other reader, and the test that pins the date fails until the arm is
/// deleted (docs/DECISIONS.md, 2026-11-16, "P6 slice 1a").
pub const SCHEMA1_MIGRATION_ENDS_UNIX: u64 = 1_798_761_600;

/// A regression gate's reference set: the names a baseline accepted, as data.
///
/// It has no tier and no grant site accepts it. For schema 2 it is the
/// validated manifest's names and identity; for the gitignored schema-1 Coq
/// baselines (no identity) it is the bare name list, read only by
/// `mathverse_shard coq-import --rebaseline` and only until
/// [`SCHEMA1_MIGRATION_ENDS_UNIX`], so the 0-regression guard survives the
/// migration without the old file entering any acceptance.
#[derive(Debug, Clone)]
pub struct RegressionReference {
    names: Vec<String>,
    identity: Option<AcceptanceIdentity>,
}

#[derive(Deserialize)]
struct Schema1Names {
    schema_version: u32,
    kernel_verified_names: Vec<String>,
}

impl RegressionReference {
    /// Read a baseline at `path`, judged at `now` (seconds since the epoch).
    ///
    /// # Errors
    /// Every refusal of [`KernelVerifiedManifest::from_file`] for schema 2, and
    /// [`ManifestError::UnsupportedSchema`] for schema 1 once the migration
    /// window has closed.
    pub fn read(path: &Path, now_unix: u64) -> MathverseResult<Self> {
        let data = std::fs::read_to_string(path)?;
        let value: serde_json::Value = serde_json::from_str(&data)?;
        let refuse = |source| MathverseError::Manifest {
            path: path.display().to_string(),
            source,
        };
        if value
            .get("schema_version")
            .and_then(serde_json::Value::as_u64)
            == Some(1)
        {
            if now_unix >= SCHEMA1_MIGRATION_ENDS_UNIX {
                return Err(refuse(ManifestError::UnsupportedSchema {
                    found: "1".to_string(),
                }));
            }
            let old: Schema1Names = serde_json::from_value(value)
                .map_err(|e| refuse(ManifestError::Malformed(e.to_string())))?;
            debug_assert_eq!(old.schema_version, 1);
            return Ok(Self {
                names: old.kernel_verified_names,
                identity: None,
            });
        }
        let manifest = KernelVerifiedManifest::from_value(value).map_err(refuse)?;
        Ok(Self {
            identity: Some(manifest.identity),
            names: manifest.accepted_names,
        })
    }

    /// The baseline's accepted names.
    #[must_use]
    pub fn names(&self) -> &[String] {
        &self.names
    }

    /// The baseline's identity; `None` for a schema-1 baseline.
    #[must_use]
    pub fn identity(&self) -> Option<&AcceptanceIdentity> {
        self.identity.as_ref()
    }
}

/// Read the file at `path` to its end and return its size and SHA-256. This is
/// the one file read the identity record makes (the executable, hashed before
/// the first check, by [`ExecutableIdentity::capture`]); it sits beside this
/// module's manifest reads so that both stand under one read-bytes contract.
fn hash_file(path: &Path) -> std::io::Result<(u64, [u8; 32])> {
    use sha2::{Digest as _, Sha256};
    use std::io::Read as _;
    let mut file = std::fs::File::open(path)?;
    let mut hasher = Sha256::new();
    let mut buf = vec![0u8; 1 << 20];
    let mut size = 0u64;
    loop {
        let n = file.read(&mut buf)?;
        if n == 0 {
            return Ok((size, hasher.finalize().into()));
        }
        size += n as u64;
        hasher.update(&buf[..n]);
    }
}

#[cfg(test)]
mod tests;
