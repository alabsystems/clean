// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The identity record every persisted acceptance carries (unit P6): the
//! theory it was accepted under, the checker that accepted it, and the tier a
//! reader may grant from it. Design: `designs/2026-11-16-p6-acceptance-identity.md`
//! section 2, as amended by its review.
//!
//! The theory is a tagged union whose two arms have different JSON tags. The
//! `profile` arm is a snapshot of [`Environment::checker_settings`] plus the
//! measured base environment; it has no id or digest field, so a legacy
//! profile, `KernelTheory::LeanReference` included, can never be read as the
//! reference theory. The `reference` arm is parsed only to be refused: no
//! producer in this build writes one (slice 1b lands the producer, its receipts
//! and its reader together).

use std::path::Path;
use std::sync::OnceLock;

use clean_kernel::env::{CheckerSettings, KernelTheory, ProofValueElision};
use clean_kernel::Environment;
use serde::{Deserialize, Serialize};

use super::error::ManifestError;

/// What a reader may grant from a persisted acceptance. The names avoid the
/// census vocabulary on purpose: neither says kernel.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum AcceptanceTier {
    /// Accepted by the fenced reference entry under the pinned reference
    /// theory. No producer in this build writes it.
    Reference,
    /// Accepted by a legacy checker under a legacy profile. Confers no label
    /// (P2 clause 1); its names are data for gates, diffs and target ranking.
    Development,
}

impl AcceptanceTier {
    /// The serialized spelling.
    #[must_use]
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Reference => "reference",
            Self::Development => "development",
        }
    }
}

/// The checker entry that decided each accepted name: one value per entry
/// that produces the verdicts some writer copies.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum CheckerEntry {
    /// `ReferenceKernel::{add_checked, add_inductive_checked,
    /// add_quot_checked}`. Parsed only to be refused in this build.
    #[serde(rename = "clean-kernel/reference-entry/v1")]
    ReferenceEntry,
    /// `verify::incremental::try_add_constant` (add_decl, checked family
    /// admission, the seeded-duplicate upgrade, the existing-family alpha
    /// match and axiom discharge: one identifier for several arms, so it can
    /// never be reference tier without being split).
    #[serde(rename = "clean-mathverse/incremental-replay/v1")]
    IncrementalReplay,
    /// `cli::parallel_verify_replay::check_value_bearing` through
    /// `Environment::check_decl_readonly_with_heartbeat`.
    #[serde(rename = "clean-mathverse/parallel-readonly-replay/v1")]
    ParallelReadonlyReplay,
    /// `lean4::kernel_verify::kernel_verify_const_with_heartbeat`
    /// (`TypeChecker::infer_sort` / `check_type` on resident constants).
    #[serde(rename = "clean-mathverse/sharded-const-typecheck/v1")]
    ShardedConstTypecheck,
}

impl CheckerEntry {
    /// The serialized spelling.
    #[must_use]
    pub fn as_str(self) -> &'static str {
        match self {
            Self::ReferenceEntry => "clean-kernel/reference-entry/v1",
            Self::IncrementalReplay => "clean-mathverse/incremental-replay/v1",
            Self::ParallelReadonlyReplay => "clean-mathverse/parallel-readonly-replay/v1",
            Self::ShardedConstTypecheck => "clean-mathverse/sharded-const-typecheck/v1",
        }
    }
}

/// The legacy entries a development writer may name. There is no reference
/// variant, so a development identity cannot name the reference checker by
/// type; serde reads the flat [`CheckerEntry`], and a forged pairing is caught
/// by [`AcceptanceIdentity::validate`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LegacyEntry {
    /// See [`CheckerEntry::IncrementalReplay`].
    IncrementalReplay,
    /// See [`CheckerEntry::ParallelReadonlyReplay`].
    ParallelReadonlyReplay,
    /// See [`CheckerEntry::ShardedConstTypecheck`].
    ShardedConstTypecheck,
}

impl LegacyEntry {
    fn entry(self) -> CheckerEntry {
        match self {
            Self::IncrementalReplay => CheckerEntry::IncrementalReplay,
            Self::ParallelReadonlyReplay => CheckerEntry::ParallelReadonlyReplay,
            Self::ShardedConstTypecheck => CheckerEntry::ShardedConstTypecheck,
        }
    }
}

/// What earned the verdict, one value per lane. Derived from the theory
/// profile ([`Discipline::of`]), so a writer cannot claim Lean's replay
/// discipline for a run it did under Clean's prelude or with cumulative
/// subtyping, and a reader recomputes it.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum Discipline {
    /// Lean's replay order from Lean's replay environment, in a Lean kernel
    /// theory. Bump it whenever what earns the verdict changes.
    #[serde(rename = "lean-replay-order+lean-kernel-theory/1")]
    LeanReplay,
    /// Global incremental replay from Clean's import prelude, in Clean's
    /// extended theory.
    #[serde(rename = "extended-prelude-incremental/1")]
    ExtendedPrelude,
    /// The Coq lane: incremental replay with cumulative (pCIC) subtyping.
    #[serde(rename = "coq-cumulative-incremental/1")]
    CoqCumulative,
}

impl Discipline {
    /// The discipline a profile derives.
    #[must_use]
    pub fn of(profile: &ProfileTheory) -> Self {
        if profile.cumulative || profile.cumulative_ever {
            Self::CoqCumulative
        } else if profile.base.variant == BaseVariant::LeanReplay
            && profile.kernel_theory != KernelTheoryName::Extended
        {
            Self::LeanReplay
        } else {
            Self::ExtendedPrelude
        }
    }

    /// The serialized spelling.
    #[must_use]
    pub fn as_str(self) -> &'static str {
        match self {
            Self::LeanReplay => "lean-replay-order+lean-kernel-theory/1",
            Self::ExtendedPrelude => "extended-prelude-incremental/1",
            Self::CoqCumulative => "coq-cumulative-incremental/1",
        }
    }
}

/// `KernelTheory` by name: a reduction profile, never a reference witness.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum KernelTheoryName {
    /// `KernelTheory::Extended`.
    Extended,
    /// `KernelTheory::Lean`.
    Lean,
    /// `KernelTheory::LeanReference`: a legacy environment set to that
    /// profile. It stays a profile.
    LeanReference,
}

impl KernelTheoryName {
    fn of(theory: KernelTheory) -> Result<Self, ManifestError> {
        match theory {
            KernelTheory::Extended => Ok(Self::Extended),
            KernelTheory::Lean => Ok(Self::Lean),
            KernelTheory::LeanReference => Ok(Self::LeanReference),
            other => Err(ManifestError::UnnamedSetting(format!(
                "kernel theory {other:?}"
            ))),
        }
    }
}

/// Which constructor the run's starting environment came from.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum BaseVariant {
    /// `Environment::for_lean_replay`.
    LeanReplay,
    /// `Environment::try_with_prelude_for_import`, whose value-less prelude
    /// constants are trusted assumptions of the theory.
    ImportPrelude,
    /// `Environment::with_prelude` (Clean's full prelude).
    Prelude,
    /// The post-verification environment of the upstream libraries of the
    /// same run (the Coq lane's dependency order).
    UpstreamLibrary,
}

/// The measured starting environment: what the theory's base axioms are.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct BaseEnvironment {
    variant: BaseVariant,
    /// Constants resident in the base.
    constants: usize,
    /// `Environment::content_digest().total` of the base, 64 hex.
    content_sha256: String,
}

impl BaseEnvironment {
    /// Measure `env`, the environment the run started from (before any target
    /// was checked and before any import was loaded on top of it).
    #[must_use]
    pub fn measure(env: &Environment, variant: BaseVariant) -> Self {
        Self {
            variant,
            constants: env.num_constants(),
            content_sha256: env.content_digest().total,
        }
    }

    /// `Environment::for_lean_replay`, measured once per process: the lanes
    /// that start from it load their imports onto a fresh instance.
    #[must_use]
    pub fn lean_replay() -> Self {
        static BASE: OnceLock<BaseEnvironment> = OnceLock::new();
        BASE.get_or_init(|| Self::measure(&Environment::for_lean_replay(), BaseVariant::LeanReplay))
            .clone()
    }

    /// Which constructor the base came from.
    #[must_use]
    pub fn variant(&self) -> BaseVariant {
        self.variant
    }

    /// The base's content digest.
    #[must_use]
    pub fn content_sha256(&self) -> &str {
        &self.content_sha256
    }
}

/// The `profile` theory arm: a snapshot of the environment-wide settings a
/// check reads, plus the measured base. Heartbeat and cache bounds are left
/// out here because they can only turn an acceptance into a refusal; the
/// heartbeat is recorded with the checker settings.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ProfileTheory {
    kernel_theory: KernelTheoryName,
    mode: String,
    lean_level_profile: String,
    cumulative: bool,
    cumulative_ever: bool,
    base: BaseEnvironment,
}

impl ProfileTheory {
    /// Snapshot `settings` (from the environment the producer checked in)
    /// over the measured `base`.
    ///
    /// # Errors
    /// [`ManifestError::UnnamedSetting`] for a kernel theory this schema has
    /// no name for.
    pub fn snapshot(
        settings: CheckerSettings,
        base: BaseEnvironment,
    ) -> Result<Self, ManifestError> {
        Ok(Self {
            kernel_theory: KernelTheoryName::of(settings.kernel_theory)?,
            mode: format!("{:?}", settings.mode),
            lean_level_profile: format!("{:?}", settings.lean_level_profile),
            cumulative: settings.cumulative,
            cumulative_ever: settings.cumulative_ever,
            base,
        })
    }

    /// The kernel theory the producer's environment was set to.
    #[must_use]
    pub fn kernel_theory(&self) -> KernelTheoryName {
        self.kernel_theory
    }

    /// Whether cumulative subtyping was on.
    #[must_use]
    pub fn cumulative(&self) -> bool {
        self.cumulative
    }

    /// The measured base.
    #[must_use]
    pub fn base(&self) -> &BaseEnvironment {
        &self.base
    }
}

/// The `reference` theory arm as a file states it. Parsed only so a reader
/// can refuse it by name (forged pairing, or no reference producer).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ReferenceTheoryClaim {
    id: String,
    digest: String,
}

/// The theory an acceptance was made under.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum TheoryRecord {
    /// The pinned reference theory, as a file claims it.
    Reference(ReferenceTheoryClaim),
    /// A legacy reduction profile.
    Profile(ProfileTheory),
}

/// Whether the producer re-checked what its acceptances depend on.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Imports {
    /// Constants loaded from imports (an `.olean` closure, a module's
    /// dependencies) were admitted without re-check, as `leanchecker` trusts
    /// a module's imports.
    Trusted,
    /// Every constant the run's acceptances depend on is in the measured base
    /// or was checked by this run.
    Replayed,
}

/// Proof-value elision, as passed to the closure loader and the verifier.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum Elision {
    /// `ProofValueElision::None`.
    None,
    /// `ProofValueElision::OpaqueOnly`.
    Opaque,
    /// `ProofValueElision::OpaqueAndTheorem`.
    OpaqueAndTheorem,
}

impl Elision {
    /// Name a kernel elision policy.
    ///
    /// # Errors
    /// [`ManifestError::UnnamedSetting`] for a policy this schema has no name for.
    pub fn of(policy: ProofValueElision) -> Result<Self, ManifestError> {
        match policy {
            ProofValueElision::None => Ok(Self::None),
            ProofValueElision::OpaqueOnly => Ok(Self::Opaque),
            ProofValueElision::OpaqueAndTheorem => Ok(Self::OpaqueAndTheorem),
            other => Err(ManifestError::UnnamedSetting(format!(
                "proof-value elision {other:?}"
            ))),
        }
    }
}

/// How inductive families reached the environment the checks ran in.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum InductiveReplay {
    /// `InductiveReplayPolicy::Generate`: Clean's own convenience definitions.
    Generate,
    /// `InductiveReplayPolicy::LeanFaithful`: the kernel certificate only, the
    /// source's own convenience definitions through `add_decl`.
    LeanFaithful,
    /// Families admitted by the `.olean` loader, not by this lane.
    OleanLoader,
}

/// Checker settings that change which names are accepted.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct CheckSettings {
    /// Proof-value elision. Can ADD acceptances (the elision gate's premise).
    pub elision: Elision,
    /// How families were replayed.
    pub inductive_replay: InductiveReplay,
    /// Whether level-parameter repair rewrote declarations before checking
    /// (then the checked declarations are the repaired ones, not the shard's).
    pub level_repair: bool,
    /// Per-check heartbeat budget applied (`None`: the kernel default).
    pub heartbeat_limit: Option<u32>,
    /// `CLEAN_MAX_CLOSURE_MODULES` ceiling, for lanes that load a closure.
    pub max_closure_modules: Option<usize>,
}

/// The executable that ran, hashed when its identity was first captured.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ExecutableIdentity {
    path: String,
    size: u64,
    sha256: String,
}

impl ExecutableIdentity {
    /// Hash the file at `path` now. The result describes the file as it was
    /// at this call, whatever happens to the path afterwards.
    ///
    /// # Errors
    /// [`ManifestError::ExecutableUnreadable`] when the file cannot be read.
    pub fn capture(path: &Path) -> Result<Self, ManifestError> {
        let (size, digest) = super::hash_file(path)
            .map_err(|e| ManifestError::ExecutableUnreadable(format!("{}: {e}", path.display())))?;
        Ok(Self {
            path: path.display().to_string(),
            size,
            sha256: hex(&digest),
        })
    }

    /// The SHA-256 of the executable's bytes.
    #[must_use]
    pub fn sha256(&self) -> &str {
        &self.sha256
    }
}

/// The build that produced a verdict.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct BuildIdentity {
    clean_version: String,
    kernel_version: String,
    toolchain: String,
    /// The commit the build came from. Slice 1a writes `null`: capturing it
    /// would make `clean-mathverse` rebuild on every commit in a tree many
    /// lanes commit to; `exe.sha256` pins the bytes that ran.
    git_sha: Option<String>,
    exe: ExecutableIdentity,
}

impl BuildIdentity {
    /// The identity of this process's executable, captured on the first call
    /// and kept for the life of the process. Every writer calls it at the
    /// start of its command, before any check, so a rebuild of the same path
    /// during a long run cannot change what the manifest names.
    ///
    /// # Errors
    /// [`ManifestError::ExecutableUnreadable`] when the executable cannot be
    /// located or read.
    pub fn current() -> Result<Self, ManifestError> {
        static CURRENT: OnceLock<Result<BuildIdentity, ManifestError>> = OnceLock::new();
        CURRENT
            .get_or_init(|| {
                let exe = std::env::current_exe()
                    .map_err(|e| ManifestError::ExecutableUnreadable(e.to_string()))?;
                Ok(Self::with_executable(ExecutableIdentity::capture(&exe)?))
            })
            .clone()
    }

    /// This crate's build facts around an already captured executable.
    #[must_use]
    pub fn with_executable(exe: ExecutableIdentity) -> Self {
        Self {
            clean_version: env!("CARGO_PKG_VERSION").to_string(),
            kernel_version: clean_kernel::VERSION.to_string(),
            toolchain: option_env!("CLEAN_MATHVERSE_TOOLCHAIN_VERSION")
                .unwrap_or("unknown")
                .to_string(),
            git_sha: None,
            exe,
        }
    }

    /// The executable's identity.
    #[must_use]
    pub fn exe(&self) -> &ExecutableIdentity {
        &self.exe
    }

    /// `clean_kernel::VERSION` at build time.
    #[must_use]
    pub fn kernel_version(&self) -> &str {
        &self.kernel_version
    }

    /// The toolchain the binary was built with.
    #[must_use]
    pub fn toolchain(&self) -> &str {
        &self.toolchain
    }
}

/// The checker that accepted.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct CheckerRecord {
    entry: CheckerEntry,
    discipline: Discipline,
    imports: Imports,
    settings: CheckSettings,
    build: BuildIdentity,
}

/// What a development writer knows about its own run: everything in the
/// identity but the entry, which its manifest constructor fixes.
#[derive(Debug, Clone)]
pub struct DevelopmentRun {
    /// The theory profile it checked under.
    pub profile: ProfileTheory,
    /// Whether it trusted or replayed its imports.
    pub imports: Imports,
    /// The settings that change which names are accepted.
    pub settings: CheckSettings,
    /// The build that ran, captured before the first check.
    pub build: BuildIdentity,
}

impl DevelopmentRun {
    /// Describe a run that checked in an environment with `env_settings`
    /// (snapshot it from the environment the producer checked in) over the
    /// measured `base`, by the executable `build` captured at its start.
    ///
    /// # Errors
    /// [`ManifestError::UnnamedSetting`] for a kernel theory this schema has
    /// no name for.
    pub fn new(
        env_settings: CheckerSettings,
        base: BaseEnvironment,
        imports: Imports,
        settings: CheckSettings,
        build: BuildIdentity,
    ) -> Result<Self, ManifestError> {
        Ok(Self {
            profile: ProfileTheory::snapshot(env_settings, base)?,
            imports,
            settings,
            build,
        })
    }
}

/// The identity record: theory, checker and the tier they derive.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct AcceptanceIdentity {
    theory: TheoryRecord,
    checker: CheckerRecord,
    tier: AcceptanceTier,
}

impl AcceptanceIdentity {
    /// A development identity for a legacy entry: the discipline is derived
    /// from the profile, and the tier is `development`.
    #[must_use]
    pub(crate) fn development(entry: LegacyEntry, run: DevelopmentRun) -> Self {
        Self {
            checker: CheckerRecord {
                entry: entry.entry(),
                discipline: Discipline::of(&run.profile),
                imports: run.imports,
                settings: run.settings,
                build: run.build,
            },
            theory: TheoryRecord::Profile(run.profile),
            tier: AcceptanceTier::Development,
        }
    }

    /// Recompute the tier from the theory and the checker, and refuse every
    /// row of the validation table that is not an accepted pair.
    ///
    /// # Errors
    /// The [`ManifestError`] naming the refusal.
    pub fn validate(&self) -> Result<AcceptanceTier, ManifestError> {
        let profile = match (&self.theory, self.checker.entry) {
            (TheoryRecord::Profile(_), CheckerEntry::ReferenceEntry) => {
                return Err(ManifestError::ForgedIdentity(
                    "a profile theory paired with the reference entry",
                ))
            }
            (TheoryRecord::Reference(_), CheckerEntry::ReferenceEntry) => {
                return Err(ManifestError::NoReferenceProducer)
            }
            (
                TheoryRecord::Reference(_),
                CheckerEntry::IncrementalReplay
                | CheckerEntry::ParallelReadonlyReplay
                | CheckerEntry::ShardedConstTypecheck,
            ) => {
                return Err(ManifestError::ForgedIdentity(
                    "the reference theory paired with a legacy entry",
                ))
            }
            (TheoryRecord::Profile(profile), _) => profile,
        };
        let derived = AcceptanceTier::Development;
        if self.tier != derived {
            return Err(ManifestError::TierMismatch {
                stored: self.tier.as_str(),
                derived: derived.as_str(),
            });
        }
        let discipline = Discipline::of(profile);
        if self.checker.discipline != discipline {
            return Err(ManifestError::DisciplineMismatch {
                stored: self.checker.discipline.as_str(),
                derived: discipline.as_str(),
            });
        }
        if self.checker.entry == CheckerEntry::ShardedConstTypecheck
            && self.checker.imports != Imports::Trusted
        {
            return Err(ManifestError::ForgedIdentity(
                "the sharded constant check trusts its imports by construction",
            ));
        }
        require_hex("base content_sha256", &profile.base.content_sha256, 64)?;
        require_hex("exe sha256", &self.checker.build.exe.sha256, 64)?;
        if let Some(sha) = &self.checker.build.git_sha {
            require_hex("git_sha", sha, 40)?;
        }
        Ok(derived)
    }

    /// The stored tier (valid: every constructed identity was validated).
    #[must_use]
    pub fn tier(&self) -> AcceptanceTier {
        self.tier
    }

    /// The checker entry.
    #[must_use]
    pub fn entry(&self) -> CheckerEntry {
        self.checker.entry
    }

    /// The derived discipline.
    #[must_use]
    pub fn discipline(&self) -> Discipline {
        self.checker.discipline
    }

    /// Trusted or replayed imports.
    #[must_use]
    pub fn imports(&self) -> Imports {
        self.checker.imports
    }

    /// The checker settings.
    #[must_use]
    pub fn settings(&self) -> &CheckSettings {
        &self.checker.settings
    }

    /// The build that ran.
    #[must_use]
    pub fn build(&self) -> &BuildIdentity {
        &self.checker.build
    }

    /// The theory record.
    #[must_use]
    pub fn theory(&self) -> &TheoryRecord {
        &self.theory
    }

    /// The comparison a regression gate uses (a new build against an old
    /// baseline): theory (base included), entry, discipline, imports, and the
    /// settings that change which names are accepted (elision, family replay,
    /// level repair).
    ///
    /// # Errors
    /// [`ManifestError::IdentityMismatch`] naming the first field that differs.
    pub fn same_checker(&self, other: &Self) -> Result<(), ManifestError> {
        self.same_checker_but_elision(other)?;
        differ(
            "settings.elision",
            &self.checker.settings.elision,
            &other.checker.settings.elision,
        )
    }

    /// [`Self::same_checker`] with the elision policy left out: the elision
    /// gate compares two runs that differ in exactly that.
    ///
    /// # Errors
    /// [`ManifestError::IdentityMismatch`] naming the first field that differs.
    pub fn same_checker_but_elision(&self, other: &Self) -> Result<(), ManifestError> {
        let (a, b) = (&self.checker, &other.checker);
        differ("theory", &self.theory, &other.theory)?;
        differ("checker.entry", &a.entry, &b.entry)?;
        differ("checker.discipline", &a.discipline, &b.discipline)?;
        differ("checker.imports", &a.imports, &b.imports)?;
        differ(
            "settings.inductive_replay",
            &a.settings.inductive_replay,
            &b.settings.inductive_replay,
        )?;
        differ(
            "settings.level_repair",
            &a.settings.level_repair,
            &b.settings.level_repair,
        )
    }

    /// The comparison resume and merge use: [`Self::same_checker`] plus every
    /// other setting and every build field, because a sidecar written by
    /// another binary is another checker run.
    ///
    /// # Errors
    /// [`ManifestError::IdentityMismatch`] naming the first field that differs.
    pub fn same_build(&self, other: &Self) -> Result<(), ManifestError> {
        self.same_checker(other)?;
        differ(
            "checker.settings",
            &self.checker.settings,
            &other.checker.settings,
        )?;
        differ("checker.build", &self.checker.build, &other.checker.build)
    }
}

fn differ<T: PartialEq + std::fmt::Debug>(field: &str, a: &T, b: &T) -> Result<(), ManifestError> {
    if a == b {
        Ok(())
    } else {
        Err(ManifestError::IdentityMismatch(format!(
            "{field} differs: {a:?} vs {b:?}"
        )))
    }
}

fn require_hex(field: &str, value: &str, len: usize) -> Result<(), ManifestError> {
    let ok = value.len() == len
        && value
            .bytes()
            .all(|b| matches!(b, b'0'..=b'9' | b'a'..=b'f'));
    if ok {
        Ok(())
    } else {
        Err(ManifestError::Malformed(format!(
            "{field} must be {len} lowercase hex digits, found {value:?}"
        )))
    }
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

/// A development run over Lean's replay environment in Lean's kernel theory,
/// by this test binary, for the manifest controls.
#[cfg(test)]
pub(crate) fn test_run(elision: Elision) -> DevelopmentRun {
    let mut env = Environment::for_lean_replay();
    env.set_kernel_theory(KernelTheory::Lean);
    test_run_in(&env, BaseVariant::LeanReplay, elision)
}

/// [`test_run`] over a given environment and base variant.
#[cfg(test)]
pub(crate) fn test_run_in(
    env: &Environment,
    variant: BaseVariant,
    elision: Elision,
) -> DevelopmentRun {
    DevelopmentRun::new(
        env.checker_settings(),
        BaseEnvironment::measure(env, variant),
        Imports::Trusted,
        CheckSettings {
            elision,
            inductive_replay: InductiveReplay::LeanFaithful,
            level_repair: false,
            heartbeat_limit: None,
            max_closure_modules: None,
        },
        BuildIdentity::current().expect("the test binary is readable"),
    )
    .expect("every kernel theory this build has is named")
}
