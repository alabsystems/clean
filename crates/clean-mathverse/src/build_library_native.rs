// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! clean-Native save pipeline — export constructively-proved theorems
//! (transitive axiom closure ⊆ `FOUNDATIONAL_AXIOMS`) from a live kernel
//! `Environment` into a purity-filtered `.mathverse` shard. Rejected decls
//! carry an explicit [`ExcludeReason`]. Entry point:
//! [`build_clean_native_library`]. See
//! `designs/2026-04-18-mathverse-native-pipeline-and-cli.md`.

use std::path::{Path, PathBuf};
use std::time::Instant;

use clean_kernel::{
    is_foundational_axiom, ConstantInfo, ConstantKind, Declaration, Environment, Name, ProofQuality,
};

use crate::error::{MathverseError, MathverseResult};
use crate::export::kernel_export::{name_content_profile, KernelShardBuilder};
use crate::shard_metadata::{self, DeclKind, MetadataEntry, ShardMetadata};
use crate::types::{AxiomProfile, SourceSystem};

/// Reason a declaration was excluded from the clean-native shard.
///
/// Every accepted declaration is a theorem with zero domain-specific axiom
/// dependencies (`ProofQuality::Constructive`). Everything else is excluded
/// with an explicit reason for auditability.
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum ExcludeReason {
    /// Theorem depends on at least one domain-specific axiom.
    AxiomDependent {
        /// The specific domain-specific axioms referenced.
        axioms: Vec<String>,
    },
    /// Theorem was added via `add_decl_structural` and bypasses the kernel.
    Unchecked,
    /// Declaration has `kind = ConstantKind::Axiom` and is non-foundational.
    NonFoundationalAxiom,
    /// Declaration is an `Axiom` on `clean_kernel::is_foundational_axiom` —
    /// skipped (not exported, not counted as a trust gap). See #3536.
    FoundationalAxiom,
    /// Declaration is a definition / opaque (not a theorem).
    NotATheorem,
    /// Theorem is kernel-clean but carries a non-empty name-heuristic content
    /// profile (NN-verification topic: `FLOAT_APPROX | NN_ABSTRACTION`). It
    /// belongs in the gamma-crown shard, not the pure-foundational native
    /// shard, and would otherwise fail `shard_verify::native_gate` (which
    /// requires `axiom_profile == NONE`). Excluded only when
    /// [`NativeBuildConfig::gate_clean`] is set.
    ContentProfiled,
    /// Declaration is already provided by the verify-time kernel prelude
    /// (`Environment::with_prelude`); re-exporting it would duplicate-collide
    /// in `shard_verify::native_gate`. The prelude supplies it at verify time.
    InPrelude,
    /// Proof quality could not be determined (missing from environment).
    Unknown,
}

/// Single entry in a clean-native build result — declaration + acceptance.
#[derive(Clone, Debug)]
pub struct NativeDeclarationRecord {
    /// Fully qualified declaration name.
    pub name: String,
    /// Accepted into the shard?
    pub accepted: bool,
    /// Reason for exclusion (only populated when `!accepted`).
    pub exclude_reason: Option<ExcludeReason>,
}

/// Configuration for a native-pipeline shard build (#3473). Derived
/// pipelines (e.g. gamma-crown) override filename, sidecar system name,
/// `SourceSystem` tag, and namespace filter. Default: clean-Native
/// (`clean-native.mathverse` / `CleanNative`).
#[derive(Clone, Debug)]
pub struct NativeBuildConfig {
    /// Shard filename written inside `out_dir`.
    pub shard_filename: &'static str,
    /// Metadata-sidecar system-name field.
    pub metadata_system_name: &'static str,
    /// `SourceSystem` tag stamped on every exported constant header.
    pub source_system: SourceSystem,
    /// Optional namespace-prefix filter. When `Some(prefixes)`, only
    /// constants whose name starts with one of `prefixes` are scanned; other
    /// declarations are skipped entirely (not counted or reported).
    pub namespace_prefixes: Option<Vec<String>>,
    /// When `true`, produce a shard that passes `shard_verify::native_gate`:
    /// exclude theorems whose name-heuristic content profile is non-empty
    /// (NN-verification topics → gamma-crown's domain) and skip constants the
    /// verify-time prelude already provides (which would duplicate-collide).
    /// Default `false` preserves the historical whole-environment export
    /// (NN content included, no prelude-skip). Opt in via
    /// `mathverse_shard build-native --gate-clean`.
    pub gate_clean: bool,
}

impl Default for NativeBuildConfig {
    fn default() -> Self {
        Self {
            shard_filename: "clean-native.mathverse",
            metadata_system_name: "CleanNative",
            source_system: SourceSystem::CleanNative,
            namespace_prefixes: None,
            gate_clean: false,
        }
    }
}

/// Summary of a clean-native library build.
#[derive(Clone, Debug, Default)]
pub struct CleanNativeBuildResult {
    /// Total declarations scanned in the environment.
    pub total_declarations: usize,
    /// Constructive theorems accepted (zero domain axioms).
    pub constructive_theorems: usize,
    /// Theorems rejected for depending on domain axioms.
    pub axiom_dependent_rejected: usize,
    /// Theorems rejected as `Unchecked`.
    pub unchecked_rejected: usize,
    /// Non-foundational axioms rejected.
    pub axioms_rejected: usize,
    /// Foundational axioms skipped (see `FoundationalAxiom`, #3536).
    pub foundational_axioms_skipped: usize,
    /// Definitions / opaques that were not exported.
    pub definitions_skipped: usize,
    /// Kernel-clean theorems excluded for carrying a non-empty name-heuristic
    /// content profile (NN-verification topics → gamma-crown shard).
    pub content_profiled_rejected: usize,
    /// Constants skipped because the verify-time prelude already provides them
    /// (avoids `shard_verify::native_gate` duplicate collisions).
    pub prelude_skipped: usize,
    /// Expression-flattening failures. These do not abort the build.
    pub flatten_failures: Vec<(String, String)>,
    /// Per-declaration acceptance record (for audit and downstream tools).
    pub decisions: Vec<NativeDeclarationRecord>,
    /// Absolute path of the written `.mathverse` shard.
    pub shard_path: PathBuf,
    /// Absolute path of the metadata sidecar.
    pub sidecar_path: PathBuf,
    /// Wall-clock elapsed time (ms).
    pub elapsed_ms: u64,
}

/// Return `true` iff `name` refers to a theorem with an empty transitive
/// domain-axiom dependency set (a constructive proof in the sense of the
/// `Proof Soundness Rules` in `design doc`).
///
/// Declarations that are axioms, definitions, opaques, `Unchecked`, or that
/// depend on any non-foundational axiom return `false`.
#[must_use]
pub fn is_constructively_proved(env: &Environment, name: &Name) -> bool {
    matches!(env.proof_quality(name), Some(ProofQuality::Constructive))
}

/// Classify a single constant for the native pipeline.
///
/// Returns `None` iff the declaration should be accepted (constructive
/// theorem), `Some(reason)` otherwise.
pub(crate) fn classify_for_native(
    env: &Environment,
    name: &Name,
    kind: ConstantKind,
) -> Option<ExcludeReason> {
    match kind {
        ConstantKind::Theorem => match env.proof_quality(name) {
            Some(ProofQuality::Constructive) => None,
            Some(ProofQuality::AxiomDependent { axioms, .. }) => {
                Some(ExcludeReason::AxiomDependent {
                    axioms: axioms.iter().map(Name::to_string).collect(),
                })
            }
            Some(ProofQuality::Unchecked) => Some(ExcludeReason::Unchecked),
            Some(ProofQuality::NotATheorem) | None => Some(ExcludeReason::Unknown),
            _ => Some(ExcludeReason::Unknown),
        },
        // Delegate to the kernel whitelist — single source of truth (#3536).
        ConstantKind::Axiom if is_foundational_axiom(name) => {
            Some(ExcludeReason::FoundationalAxiom)
        }
        ConstantKind::Axiom => Some(ExcludeReason::NonFoundationalAxiom),
        ConstantKind::Definition | ConstantKind::Opaque => Some(ExcludeReason::NotATheorem),
    }
}

/// Reconstruct a kernel `Declaration` from a `ConstantInfo`.
///
/// The kernel does not expose a built-in `ConstantInfo -> Declaration`
/// conversion, so we inline it here.
fn constant_info_to_declaration(info: &ConstantInfo) -> Option<Declaration> {
    match info.kind {
        ConstantKind::Theorem => info.value.as_ref().map(|value| Declaration::Theorem {
            name: info.name.clone(),
            level_params: info.level_params.clone(),
            type_: info.type_.clone(),
            value: value.clone(),
        }),
        ConstantKind::Definition => info.value.as_ref().map(|value| Declaration::Definition {
            name: info.name.clone(),
            level_params: info.level_params.clone(),
            type_: info.type_.clone(),
            value: value.clone(),
            is_reducible: info.is_reducible,
        }),
        ConstantKind::Opaque => info.value.as_ref().map(|value| Declaration::Opaque {
            name: info.name.clone(),
            level_params: info.level_params.clone(),
            type_: info.type_.clone(),
            value: value.clone(),
        }),
        ConstantKind::Axiom => Some(Declaration::Axiom {
            name: info.name.clone(),
            level_params: info.level_params.clone(),
            type_: info.type_.clone(),
        }),
    }
}

/// Handle a single accepted declaration: flatten, add to builder, record
/// metadata and decision.
fn accept_declaration(
    env: &Environment,
    name: &Name,
    builder: &mut KernelShardBuilder,
    metadata: &mut ShardMetadata,
    result: &mut CleanNativeBuildResult,
) {
    let Some(info) = env.get_const(name) else {
        result.decisions.push(NativeDeclarationRecord {
            name: name.to_string(),
            accepted: false,
            exclude_reason: Some(ExcludeReason::Unknown),
        });
        return;
    };
    let Some(decl) = constant_info_to_declaration(info) else {
        result.decisions.push(NativeDeclarationRecord {
            name: name.to_string(),
            accepted: false,
            exclude_reason: Some(ExcludeReason::NotATheorem),
        });
        result.definitions_skipped += 1;
        return;
    };

    match builder.add_declaration(&decl, &[]) {
        Ok(_) => {
            result.constructive_theorems += 1;
            metadata.push(MetadataEntry {
                name: name.to_string(),
                kind: Some(DeclKind::Theorem),
                type_signature: None,
                source_file: None,
                line_number: None,
            });
            result.decisions.push(NativeDeclarationRecord {
                name: name.to_string(),
                accepted: true,
                exclude_reason: None,
            });
        }
        Err(e) => {
            result
                .flatten_failures
                .push((name.to_string(), e.to_string()));
            result.decisions.push(NativeDeclarationRecord {
                name: name.to_string(),
                accepted: false,
                exclude_reason: Some(ExcludeReason::Unknown),
            });
        }
    }
}

/// Handle a single rejected declaration: bump the appropriate counter and
/// record the decision.
fn reject_declaration(name: &Name, reason: ExcludeReason, result: &mut CleanNativeBuildResult) {
    match &reason {
        ExcludeReason::AxiomDependent { .. } => result.axiom_dependent_rejected += 1,
        ExcludeReason::Unchecked => result.unchecked_rejected += 1,
        ExcludeReason::NonFoundationalAxiom => result.axioms_rejected += 1,
        ExcludeReason::FoundationalAxiom => result.foundational_axioms_skipped += 1,
        ExcludeReason::NotATheorem => result.definitions_skipped += 1,
        ExcludeReason::ContentProfiled => result.content_profiled_rejected += 1,
        ExcludeReason::InPrelude => result.prelude_skipped += 1,
        ExcludeReason::Unknown => {}
    }
    result.decisions.push(NativeDeclarationRecord {
        name: name.to_string(),
        accepted: false,
        exclude_reason: Some(reason),
    });
}

/// Build a **clean-native** mathverse shard from a live kernel `Environment`.
///
/// Exports theorems whose transitive axiom closure ⊆ `FOUNDATIONAL_AXIOMS`
/// (`propext`, `Quot.sound`, `Classical.choice`, `Eq.*`, …). Accepted decls
/// are re-flattened via `KernelShardBuilder` so callers can re-type-check
/// from the shard alone. Writes `.mathverse` + JSON sidecar to `out_dir`.
///
/// # Errors
///
/// Returns an error if the output directory cannot be created or the shard
/// / sidecar cannot be written. Per-declaration flattening failures are
/// recorded in `flatten_failures` and do not abort the build.
pub fn build_clean_native_library(
    env: &Environment,
    out_dir: &Path,
) -> MathverseResult<CleanNativeBuildResult> {
    build_native_shard_with_config(env, out_dir, &NativeBuildConfig::default())
}

/// Build a native-pipeline mathverse shard with caller-provided configuration.
///
/// Generalisation of [`build_clean_native_library`] introduced by #3473 so
/// derived libraries (gamma-crown, future per-domain shards) can reuse the
/// env-walking + kernel-flattening pipeline with a different
/// [`SourceSystem`] tag and output filename.
///
/// # Errors
///
/// See [`build_clean_native_library`]. Additionally returns
/// [`MathverseError::TrustViolation`] when `config.source_system` is
/// [`SourceSystem::Cake`]: Cake shards may only be produced by the
/// graduation intake gate.
pub fn build_native_shard_with_config(
    env: &Environment,
    out_dir: &Path,
    config: &NativeBuildConfig,
) -> MathverseResult<CleanNativeBuildResult> {
    // SOUNDNESS: `SourceSystem::Cake` is reserved for the graduation intake
    // gate (`graduate::intake::graduate`), which digest-binds every Cake
    // shard to a `mathverse-graduation-v2` record. A Cake shard built here
    // would carry no record and fail `shard_verify::cake_gate` anyway;
    // refusing up front keeps the "sole producer" invariant explicit.
    if config.source_system == SourceSystem::Cake {
        return Err(MathverseError::TrustViolation(
            "SourceSystem::Cake is reserved for the graduation intake gate \
             (graduate::intake::graduate); the native build pipeline must not \
             stamp Cake"
                .to_string(),
        ));
    }
    let start = Instant::now();
    std::fs::create_dir_all(out_dir).map_err(MathverseError::Io)?;

    let shard_path = out_dir.join(config.shard_filename);
    let sidecar_path = shard_metadata::sidecar_path_for(&shard_path);

    let mut result = CleanNativeBuildResult {
        shard_path: shard_path.clone(),
        sidecar_path: sidecar_path.clone(),
        ..Default::default()
    };

    // Snapshot (name, kind) to sidestep borrow constraints while classifying.
    // Apply namespace-prefix filter early so out-of-scope declarations do not
    // inflate `total_declarations` or the decision log.
    let const_snapshot: Vec<(Name, ConstantKind)> = env
        .constants()
        .filter(|c| {
            matches_namespace_filter(&c.name.to_string(), config.namespace_prefixes.as_deref())
        })
        .map(|c| (c.name.clone(), c.kind))
        .collect();
    result.total_declarations = const_snapshot.len();

    let mut builder = KernelShardBuilder::new().with_source_system(config.source_system);
    let mut metadata = ShardMetadata::new(config.metadata_system_name);

    // Gate-clean mode skips constants the verify-time `with_prelude()` baseline
    // already provides — re-exporting them would duplicate-collide on re-add in
    // `shard_verify::native_gate` and cascade-reject their dependents. Only
    // computed when needed (default builds keep the historical whole-env export).
    let prelude_names: std::collections::HashSet<String> = if config.gate_clean {
        Environment::with_prelude()
            .constants()
            .map(|c| c.name.to_string())
            .collect()
    } else {
        std::collections::HashSet::new()
    };

    for (name, kind) in &const_snapshot {
        let name_str = name.to_string();
        if config.gate_clean {
            if prelude_names.contains(&name_str) {
                reject_declaration(name, ExcludeReason::InPrelude, &mut result);
                continue;
            }
            // Kernel-clean theorems with a non-empty name-heuristic content
            // profile (NN-verification topics) belong in the gamma-crown shard;
            // the native gate requires `axiom_profile == NONE`.
            if name_content_profile(&name_str) != AxiomProfile::NONE {
                reject_declaration(name, ExcludeReason::ContentProfiled, &mut result);
                continue;
            }
        }
        match classify_for_native(env, name, *kind) {
            None => accept_declaration(env, name, &mut builder, &mut metadata, &mut result),
            Some(reason) => reject_declaration(name, reason, &mut result),
        }
    }

    builder.write_to_file(&shard_path)?;
    let json = serde_json::to_string_pretty(&metadata).map_err(MathverseError::from)?;
    std::fs::write(&sidecar_path, json).map_err(MathverseError::Io)?;

    result.elapsed_ms = start.elapsed().as_millis() as u64;
    Ok(result)
}

/// Return `true` iff `name` matches the namespace filter.
///
/// A `None` filter accepts every name. A `Some(prefixes)` filter accepts a
/// name iff at least one prefix is a prefix of `name`.
fn matches_namespace_filter(name: &str, prefixes: Option<&[String]>) -> bool {
    match prefixes {
        None => true,
        Some(list) => list.iter().any(|p| name.starts_with(p.as_str())),
    }
}

/// Seed a fresh `Environment` with the NN-verification / interval-arithmetic
/// / CROWN overlay constants that the clean-Native shard pipeline exports.
///
/// This is the single source of truth for the "native pipeline" environment
/// shape: the `mathverse_shard build-native` CLI and the incremental
/// `clean kernel classify` verb (#3598) both call this function so they agree
/// byte-for-byte on which constants are present and how they are classified.
///
/// Initialization errors from individual overlay registrars are logged to
/// stderr (as `Warning: <overlay> init failed: <error>`) but do not abort —
/// the pipeline is designed to continue building whichever shards / reports
/// it can, even if one overlay is currently broken.
///
/// Requires the kernel-side `math-overlays` feature, which `clean-mathverse`
/// unconditionally enables in its direct `clean-kernel` dependency.
pub fn seed_native_environment(env: &mut Environment) {
    seed_overlays(env);
    seed_tier_a_rat_batch1(env);
    seed_tier_a_rat_batch2(env);
    seed_tier_a_rat_batch3(env);
    if let Err(e) = env.init_nn_verify_tier_a_nat_ordering() {
        eprintln!("Warning: tier-A nat_ordering init failed: {e}");
    }
    // #3599: top-level `Nat.*` ordering primitives promoted from Axiom to
    // constructive Theorem (`Nat.le_refl`, `Nat.succ_le_succ`,
    // `Nat.succ_lt_succ`, `Nat.le_of_lt`, `Nat.zero_lt_succ`). Registering
    // here so they land in the clean-native shard alongside the tier-A
    // `NNVerify.Nat.*` theorems.
    if let Err(e) = env.init_nat_top_level_ordering() {
        eprintln!("Warning: top-level Nat ordering init failed: {e}");
    }
    seed_tier_a_rat_batch4(env);
    // #3615: canonical general `Rat.min_le_max` constructive lemma.
    //   ∀ a b : Rat, Rat.le (Rat.min a b) (Rat.max a b)
    // Unblocks C004 Phase 2 γ-scale carrier body.
    if let Err(e) = env.init_rat_min_le_max() {
        eprintln!("Warning: Rat.min_le_max init failed: {e}");
    }
}

/// C006 / interval-arith / IBP-width-zero overlay inits.
fn seed_overlays(env: &mut Environment) {
    if let Err(e) = env.init_nn_verify_blockwise_crown_ext() {
        eprintln!("Warning: C006 ext init failed: {e}");
    }
    if let Err(e) = env.init_nn_verify_interval_arith_proofs() {
        eprintln!("Warning: interval-arith proofs init failed: {e}");
    }
    // #3603: foundational `interval_subset_refl` /
    // `interval_contains_self_lower|_upper` containment lemmas. Registered in
    // a sibling kernel module (`nn_verify_interval_containment_proofs`); its
    // `init_*` entry point is called directly so the three theorems land in
    // the native shard.
    if let Err(e) = env.init_nn_verify_interval_containment_proofs() {
        eprintln!("Warning: interval-containment proofs init failed: {e}");
    }
    // #3615: constructive `NNVerify.Rat.interval_*` monotonicity theorems
    // (`interval_add_valid`, `interval_hull_lo_le_fst_lo`,
    // `interval_hull_fst_hi_le_hi`). First follow-up slice after the
    // Step-1 primitive registrations landed — unblocks downstream
    // faithful LayerNorm carrier validity proofs.
    if let Err(e) = env.init_nn_verify_rat_interval_proofs() {
        eprintln!("Warning: rat_interval proofs init failed: {e}");
    }
    if let Err(e) = env.init_nn_verify_ibp_width_zero() {
        eprintln!("Warning: ibp_width_zero sub-lemmas init failed: {e}");
    }
}

/// Tier A Batch 1: foundational Rat min/le_refl/zero_eq ladder.
fn seed_tier_a_rat_batch1(env: &mut Environment) {
    if let Err(e) = env.init_nn_verify_tier_a_rat_min_zero() {
        eprintln!("Warning: tier-A rat_min_zero init failed: {e}");
    }
    if let Err(e) = env.init_nn_verify_tier_a_rat_le_refl_zero() {
        eprintln!("Warning: tier-A rat_le_refl_zero init failed: {e}");
    }
    if let Err(e) = env.init_nn_verify_tier_a_rat_zero_eq_max() {
        eprintln!("Warning: tier-A rat_zero_eq_max init failed: {e}");
    }
    if let Err(e) = env.init_nn_verify_tier_a_rat_zero_eq_min() {
        eprintln!("Warning: tier-A rat_zero_eq_min init failed: {e}");
    }
    if let Err(e) = env.init_nn_verify_tier_a_rat_max_eq_min() {
        eprintln!("Warning: tier-A rat_max_eq_min init failed: {e}");
    }
}

/// Tier A Batch 2 (#3551): symmetric / alt-proof Rat lemmas.
fn seed_tier_a_rat_batch2(env: &mut Environment) {
    if let Err(e) = env.init_nn_verify_tier_a_rat_min_eq_max() {
        eprintln!("Warning: tier-A rat_min_eq_max init failed: {e}");
    }
    if let Err(e) = env.init_nn_verify_tier_a_rat_max_zero_zero_alt() {
        eprintln!("Warning: tier-A rat_max_zero_zero_alt init failed: {e}");
    }
    if let Err(e) = env.init_nn_verify_tier_a_rat_min_zero_zero_alt() {
        eprintln!("Warning: tier-A rat_min_zero_zero_alt init failed: {e}");
    }
    if let Err(e) = env.init_nn_verify_tier_a_rat_le_refl_max_zero_zero() {
        eprintln!("Warning: tier-A rat_le_refl_max_zero_zero init failed: {e}");
    }
    if let Err(e) = env.init_nn_verify_tier_a_rat_le_refl_min_zero_zero() {
        eprintln!("Warning: tier-A rat_le_refl_min_zero_zero init failed: {e}");
    }
}

/// Tier A Batch 3 (#3551): Rat scalar lemmas via foundational axiom
/// instantiation (mul, add_neg_self, etc.).
fn seed_tier_a_rat_batch3(env: &mut Environment) {
    if let Err(e) = env.init_nn_verify_tier_a_rat_mul_zero_zero() {
        eprintln!("Warning: tier-A rat_mul_zero_zero init failed: {e}");
    }
    if let Err(e) = env.init_nn_verify_tier_a_rat_mul_one_zero() {
        eprintln!("Warning: tier-A rat_mul_one_zero init failed: {e}");
    }
    if let Err(e) = env.init_nn_verify_tier_a_rat_mul_zero_one() {
        eprintln!("Warning: tier-A rat_mul_zero_one init failed: {e}");
    }
    if let Err(e) = env.init_nn_verify_tier_a_rat_add_neg_self_zero() {
        eprintln!("Warning: tier-A rat_add_neg_self_zero init failed: {e}");
    }
    if let Err(e) = env.init_nn_verify_tier_a_rat_add_left_neg_zero() {
        eprintln!("Warning: tier-A rat_add_left_neg_zero init failed: {e}");
    }
    if let Err(e) = env.init_nn_verify_tier_a_rat_mul_neg_zero_zero() {
        eprintln!("Warning: tier-A rat_mul_neg_zero_zero init failed: {e}");
    }
    // Zero-trio (#3551): only `Rat.neg Rat.zero = Rat.zero` lands via pure
    // Eq.refl (kernel δι reduction). `Rat.sub x 0 = x` and
    // `Rat.abs Rat.zero = Rat.zero` are BLOCKED — their would-be proofs
    // depend on `Rat.add_zero` / `Rat.abs_zero` which transitively pull Int/Nat
    // domain axioms (Int.add_zero, Int.mul_one, Int.zero_mul, Nat.mul_one)
    // that are not in FOUNDATIONAL_AXIOMS. Chain-style proofs therefore
    // contaminate the non-foundational axiom closure. See commit log / issue
    // #3551 for blocker details.
    if let Err(e) = env.init_nn_verify_tier_a_rat_neg_zero_zero() {
        eprintln!("Warning: tier-A rat_neg_zero_zero init failed: {e}");
    }
}

/// Tier A Batch 4 (#3551): Rat min/max transitivity / idempotence at
/// ground zero. All compose Rat.{min,max,le}_def with Eq.trans and
/// NNVerify.le_of_{eq_of_le,le_of_eq}; axiom closure FOUNDATIONAL only.
fn seed_tier_a_rat_batch4(env: &mut Environment) {
    if let Err(e) = env.init_nn_verify_tier_a_rat_min_le_max_zero_zero() {
        eprintln!("Warning: tier-A rat_min_le_max_zero_zero init failed: {e}");
    }
    if let Err(e) = env.init_nn_verify_tier_a_rat_max_le_min_zero_zero() {
        eprintln!("Warning: tier-A rat_max_le_min_zero_zero init failed: {e}");
    }
    if let Err(e) = env.init_nn_verify_tier_a_rat_min_min_zero_zero() {
        eprintln!("Warning: tier-A rat_min_min_zero_zero init failed: {e}");
    }
    if let Err(e) = env.init_nn_verify_tier_a_rat_max_max_zero_zero() {
        eprintln!("Warning: tier-A rat_max_max_zero_zero init failed: {e}");
    }
    if let Err(e) = env.init_nn_verify_tier_a_rat_max_min_zero_zero() {
        eprintln!("Warning: tier-A rat_max_min_zero_zero init failed: {e}");
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::expr::Expr;

    use crate::shard::ShardReader;

    /// Seed `env` with three declarations covering the three exclude paths:
    /// returns the triple `(accepted_name, dependent_name, axiom_name)`.
    fn seed_native_triple(env: &mut Environment) -> (&'static str, &'static str, &'static str) {
        let prop = Expr::prop();

        // 1. Constructive theorem — value references only foundational axioms.
        let constructive = Declaration::Theorem {
            name: Name::from_string("test_native_constructive"),
            level_params: vec![],
            type_: prop.clone(),
            value: prop.clone(),
        };
        env.add_decl_structural(constructive)
            .expect("add constructive theorem");

        // 2. Domain-specific axiom — rejected as non-foundational.
        let domain_axiom = Declaration::Axiom {
            name: Name::from_string("test_native_domain_axiom"),
            level_params: vec![],
            type_: prop.clone(),
        };
        env.add_decl_structural(domain_axiom)
            .expect("add domain axiom");

        // 3. Theorem that references the domain axiom — AxiomDependent.
        let dependent = Declaration::Theorem {
            name: Name::from_string("test_native_axiom_dependent"),
            level_params: vec![],
            type_: prop.clone(),
            value: Expr::const_str("test_native_domain_axiom"),
        };
        env.add_decl_structural(dependent)
            .expect("add dependent theorem");

        (
            "test_native_constructive",
            "test_native_axiom_dependent",
            "test_native_domain_axiom",
        )
    }

    /// Sanity: the `is_constructively_proved` predicate agrees with the
    /// seeding above.
    fn assert_classifier_sanity(env: &Environment, accepted: &str, dependent: &str, axiom: &str) {
        assert!(is_constructively_proved(env, &Name::from_string(accepted)));
        assert!(!is_constructively_proved(
            env,
            &Name::from_string(dependent)
        ));
        assert!(!is_constructively_proved(env, &Name::from_string(axiom)));
    }

    /// Core build-result counts must exactly match the seeded environment.
    fn assert_counts(result: &CleanNativeBuildResult) {
        assert_eq!(
            result.constructive_theorems, 1,
            "exactly one constructive theorem should be accepted"
        );
        assert_eq!(
            result.axiom_dependent_rejected, 1,
            "exactly one theorem should be rejected as axiom-dependent"
        );
        assert_eq!(
            result.axioms_rejected, 1,
            "exactly one domain axiom should be rejected"
        );
        assert!(
            result.flatten_failures.is_empty(),
            "no flatten failures expected"
        );
        assert!(result.shard_path.exists(), "shard file should be written");
        assert!(result.sidecar_path.exists(), "sidecar should be written");
    }

    /// The produced shard must round-trip through `ShardReader`: exactly one
    /// declaration, tagged CleanNative, value retained, rejected names absent.
    fn assert_shard_roundtrip(
        result: &CleanNativeBuildResult,
        accepted: &str,
        dependent: &str,
        axiom: &str,
    ) {
        let reader = ShardReader::from_file(&result.shard_path).expect("read shard");
        assert_eq!(
            reader.header.constant_count, 1,
            "shard must contain exactly one declaration"
        );
        let (_idx, hdr) = reader
            .lookup_name(accepted)
            .expect("constructive theorem should be in the shard");
        assert_eq!(
            hdr.source_system,
            SourceSystem::CleanNative as u8,
            "every native shard entry must carry SourceSystem::CleanNative"
        );
        assert!(
            hdr.has_value(),
            "accepted theorem must retain its proof value in the shard"
        );
        assert!(
            reader.lookup_name(dependent).is_none(),
            "axiom-dependent theorem must NOT leak into a native shard"
        );
        assert!(
            reader.lookup_name(axiom).is_none(),
            "domain axiom must NOT leak into a native shard"
        );
    }

    /// The decision log must record every declaration we added.
    fn assert_decision_log_complete(
        result: &CleanNativeBuildResult,
        accepted: &str,
        dependent: &str,
        axiom: &str,
    ) {
        let log_names: std::collections::HashSet<_> =
            result.decisions.iter().map(|d| d.name.clone()).collect();
        assert!(log_names.contains(accepted));
        assert!(log_names.contains(dependent));
        assert!(log_names.contains(axiom));
    }

    /// Constructive theorem, theorem depending on a domain axiom, and a
    /// non-foundational axiom are all added to a live kernel environment.
    /// `build_clean_native_library` must accept exactly the constructive
    /// theorem and write a real round-trippable `.mathverse` shard.
    #[test]
    fn test_clean_native_shard_roundtrip() {
        let mut env = Environment::default();
        let (accepted, dependent, axiom) = seed_native_triple(&mut env);

        assert_classifier_sanity(&env, accepted, dependent, axiom);

        let tmp = tempfile::tempdir().expect("tempdir");
        let result = build_clean_native_library(&env, tmp.path()).expect("native build");

        assert_counts(&result);
        assert_shard_roundtrip(&result, accepted, dependent, axiom);
        assert_decision_log_complete(&result, accepted, dependent, axiom);
    }

    /// `SourceSystem::Cake` is reserved for the graduation intake gate; the
    /// native pipeline must refuse to stamp it (sole-producer invariant),
    /// and must refuse BEFORE writing any output files.
    #[test]
    fn test_build_native_refuses_cake_source_system() {
        let env = Environment::default();
        let tmp = tempfile::tempdir().expect("tempdir");
        let config = NativeBuildConfig {
            shard_filename: "forged-cake.mathverse",
            source_system: SourceSystem::Cake,
            ..Default::default()
        };

        let err = build_native_shard_with_config(&env, tmp.path(), &config)
            .expect_err("native build must refuse SourceSystem::Cake");
        assert!(
            matches!(err, MathverseError::TrustViolation(_)),
            "expected TrustViolation, got: {err}"
        );
        assert!(
            !tmp.path().join("forged-cake.mathverse").exists(),
            "no shard bytes may be written for a refused Cake build"
        );
    }

    /// `gate_clean` is opt-in: the default build keeps NN-content and prelude
    /// constants (historical behavior), while `gate_clean = true` excludes
    /// content-profiled (NN) theorems and skips constants the verify-time
    /// prelude already provides — the two producer-side gaps that made
    /// `build-native` output fail `shard_verify::native_gate`.
    #[test]
    fn test_gate_clean_excludes_nn_content_and_prelude() {
        let prop = Expr::prop();
        // Pick a name guaranteed to exist in the verify-time prelude baseline.
        let prelude_name = Environment::with_prelude()
            .constants()
            .next()
            .map(|c| c.name.to_string())
            .expect("prelude must be non-empty");

        let mut env = Environment::new();
        env.add_decl_structural(Declaration::Theorem {
            name: Name::from_string("NNVerify.gate_clean_probe"),
            level_params: vec![],
            type_: prop.clone(),
            value: prop.clone(),
        })
        .expect("add NN-content theorem");
        env.add_decl_structural(Declaration::Theorem {
            name: Name::from_string(&prelude_name),
            level_params: vec![],
            type_: prop.clone(),
            value: prop.clone(),
        })
        .expect("add prelude-named theorem");

        let tmp = tempfile::tempdir().expect("tempdir");

        // Default (gate_clean = false): no gate filtering; NN content accepted.
        let lax = build_native_shard_with_config(&env, tmp.path(), &NativeBuildConfig::default())
            .expect("default build");
        assert_eq!(
            lax.content_profiled_rejected, 0,
            "default must not gate-filter NN content"
        );
        assert_eq!(lax.prelude_skipped, 0, "default must not prelude-skip");
        assert!(
            lax.decisions
                .iter()
                .any(|d| d.name == "NNVerify.gate_clean_probe" && d.accepted),
            "default build must accept the constructive NN theorem"
        );

        // gate_clean = true: NN content excluded, prelude name skipped.
        let strict_dir = tmp.path().join("strict");
        let strict = build_native_shard_with_config(
            &env,
            &strict_dir,
            &NativeBuildConfig {
                gate_clean: true,
                ..Default::default()
            },
        )
        .expect("gate-clean build");
        assert!(
            strict.content_profiled_rejected >= 1,
            "gate-clean must reject NNVerify.* as content-profiled"
        );
        assert!(
            strict.prelude_skipped >= 1,
            "gate-clean must skip the prelude-provided constant"
        );
        let reader = ShardReader::from_file(strict_dir.join("clean-native.mathverse"))
            .expect("read gate-clean shard");
        assert!(
            reader.lookup_name("NNVerify.gate_clean_probe").is_none(),
            "NN content must not leak into a gate-clean shard"
        );
        assert!(
            reader.lookup_name(&prelude_name).is_none(),
            "prelude-provided constant must not be re-exported in a gate-clean shard"
        );
    }
}
