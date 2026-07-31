// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Package the native, kernel-checked IEEE-754 float→rational theory as a
//! self-contained `.mathverse` SHARD (`nnverify_ieee754`).
//!
//! The math is registered programmatically in a kernel [`Environment`] by
//! `clean_kernel::Environment::init_nn_verify_float_rational` (Stage A + Stage
//! B of #3185): the `NNVerify.FloatRational.*` namespace, the native
//! `Float.toRatExact` / `Float.ulpExact` / `Rat.roundToNearestEven` opaque
//! decompositions, the universal/denormal half-ulp soundness theorems, and the
//! per-constant `rounding_error_bound` discharges. None of it comes from an
//! upstream `.olean`/importer, so the export path here feeds live kernel
//! [`Declaration`]s straight into a [`KernelShardBuilder`].
//!
//! ## What "package + register" means here
//!
//! 1. [`build_nnverify_ieee754_shard`] seeds an `Environment::with_prelude()`,
//!    runs `init_nn_verify_float_rational`, then exports the float-theory
//!    declarations — in a fixed, dependency-safe order — through the existing
//!    `KernelShardBuilder` native-decl→shard adapter. The builder flattens each
//!    `Declaration`'s type and value into the shard's FlatExpr arena, exactly
//!    as the clean-Native / gamma-crown pipelines do.
//! 2. The shard is *sealed*: `ShardWriter::finalize_axiom_profiles` runs the
//!    in-shard axiom-profile closure so each constant's recorded profile
//!    reflects its in-shard dependency graph before the bytes are frozen.
//! 3. [`register_nnverify_ieee754_shard`] writes the sealed shard under
//!    `data/mathverse-library/nnverify_ieee754/` and appends a manifest entry
//!    with the REAL blake3 content hash and the REAL header constant/expr
//!    counts (mirroring `LibraryLoader::write_shard` / the `register_shard`
//!    example).
//! 4. [`verify_nnverify_ieee754_shard`] reloads the shard and RE-CHECKS every
//!    constant through Clean's kernel (`reconstruct_* → env.add_decl` against a
//!    fresh `with_prelude` env, exactly as `shard_verify`'s native gate does),
//!    and asserts that the empty-closure theorems re-verify with an EMPTY
//!    non-foundational axiom closure (`Environment::axiom_deps`).
//!
//! ## Why NOT the strict `shard_verify::native_gate`
//!
//! The native gate (`verify_native_shard`) is for the pure-foundational
//! clean-Native shard: it rejects anything that is not a `Theorem` and any
//! header whose `axiom_profile != NONE`. This shard deliberately bundles the
//! float *function symbols* (`Float.toRatExact` opaque, `float_to_rational`
//! axiom, …) that the soundness theorems are stated over, and every
//! `NNVerify.*` header carries the name-heuristic content-profile bits
//! (`FLOAT_APPROX | NN_ABSTRACTION`) by construction. So the appropriate
//! verifier is the kernel re-check + per-theorem axiom-closure assertion in
//! [`verify_nnverify_ieee754_shard`], not the foundational-only gate.

use std::path::Path;

use clean_kernel::{ConstantKind, Declaration, Environment, Expr, ExprKind, Name, TypeChecker};

use crate::error::{MathverseError, MathverseResult};
use crate::export::kernel_export::KernelShardBuilder;
use crate::manifest::{LibraryPaths, MathverseManifest, ShardEntry};
use crate::shard::ShardReader;
use crate::shard_reconstruct::{reconstruct_from_shard_with_level_lists, reconstruct_level_params};
use crate::types::{DeclKind, SourceSystem, NO_VALUE};

/// Logical name of this shard (manifest `source`, filename stem).
pub const NNVERIFY_IEEE754_SHARD_NAME: &str = "nnverify_ieee754";

/// Subdirectory (relative to the library root) the shard is written under, and
/// the manifest `path` prefix.
pub const NNVERIFY_IEEE754_SHARD_SUBDIR: &str = "nnverify_ieee754";

/// The IEEE-754 float-theory declarations packaged into the shard, in a fixed
/// **dependency-safe order**: every name appears after the constants it
/// references (the `with_prelude` baseline supplies Rat / Float / Nat / Int /
/// `Nat.ulp_universal_bound`; only the intra-shard ordering — function symbols
/// before the theorems stated over them — matters for kernel replay).
///
/// The kernel registers all of these from `init_nn_verify_float_rational`; this
/// is the single source of truth for which subset is published. Replay (in
/// [`verify_nnverify_ieee754_shard`]) walks this same order so each later
/// declaration's in-shard dependencies are already in the replay environment.
pub const NNVERIFY_IEEE754_DECLS: &[&str] = &[
    // --- function symbols (axioms / definition) the theory is stated over ---
    "NNVerify.FloatRational.float_to_rational",
    "NNVerify.FloatRational.ulp",
    "NNVerify.FloatRational.rounding_error",
    "NNVerify.FloatRational.interval_float_rational",
    "NNVerify.FloatRational.accumulated_error",
    // --- native, kernel-checked exact decomposition (Opaque, reducer-backed) ---
    "Float.toRatExact",
    "Float.ulpExact",
    // --- the IEEE-754 domain axioms (the guarantees being formalized) ---
    "NNVerify.FloatRational.float_to_rational_exact",
    "NNVerify.FloatRational.rounding_error_bound",
    "NNVerify.FloatRational.interval_contains_real",
    "NNVerify.FloatRational.matmul_error_bound",
    "NNVerify.FloatRational.ibp_float_sound",
    "NNVerify.FloatRational.error_propagation_linear",
    // --- the per-float exactness discharge (Theorem, Eq.refl, empty closure) ---
    "NNVerify.FloatRational.float_to_rat_exact_discharge_01",
    // --- the native ties-to-even round (Opaque, reducer-backed) ---
    "Rat.roundToNearestEven",
    // --- the universal + denormal half-ulp soundness theorems (empty closure) ---
    "NNVerify.FloatRational.rounding_error_le_half_ulp",
    "NNVerify.FloatRational.rounding_error_le_half_ulp_denormal",
    // --- the four rounding_error_bound discharges (Theorem, empty closure) ---
    "NNVerify.FloatRational.round_discharge_normal",
    "NNVerify.FloatRational.rounding_error_bound_discharge_normal",
    "NNVerify.FloatRational.round_discharge_subnormal",
    "NNVerify.FloatRational.rounding_error_bound_discharge_subnormal",
    "NNVerify.FloatRational.round_discharge_tie",
    "NNVerify.FloatRational.rounding_error_bound_discharge_tie",
    "NNVerify.FloatRational.round_discharge_exact",
    "NNVerify.FloatRational.rounding_error_bound_discharge_exact",
    // --- Higham dot-product accumulated-error development (empty closure) ---
    // `init_nn_verify_float_rational` pulls `init_nn_verify_dot_product_error`
    // in, so these are part of the registered float theory and must be
    // published with it. The accumulation chains reference
    // `error_accum_step`, so they follow it; the per-op discharges and the
    // concrete γ_n reductions are self-contained literal proofs.
    "NNVerify.FloatRational.error_accum_step",
    "NNVerify.FloatRational.error_accum_step3",
    "NNVerify.FloatRational.error_accum_step4",
    "NNVerify.FloatRational.fl_op_rel_error_discharge_f32",
    "NNVerify.FloatRational.fl_op_rel_error_discharge_f64",
    "NNVerify.FloatRational.gamma_n_reduces_u8_n2",
    "NNVerify.FloatRational.gamma_n_reduces_u8_n3",
    "NNVerify.FloatRational.gamma_n_reduces_u12_n2",
    "NNVerify.FloatRational.gamma_n_reduces_u12_n3",
    "NNVerify.FloatRational.gamma_n_reduces_f32_n2",
    "NNVerify.FloatRational.gamma_n_reduces_f32_n3",
    "NNVerify.FloatRational.gamma_n_reduces_f64_n2",
    "NNVerify.FloatRational.gamma_n_reduces_f64_n3",
];

/// The subset of [`NNVERIFY_IEEE754_DECLS`] that are kernel-checked `Theorem`s
/// whose transitive **non-foundational** axiom closure is EMPTY — i.e. proved
/// (by kernel computation), not asserted. These must re-verify from the shard
/// with `axiom_deps == ∅` (no `sorry`, no domain axiom). The round/ulp lemmas
/// and every discharge live here; the function-symbol axioms/opaques and the
/// six IEEE-754 domain axioms deliberately do NOT (they are the postulated
/// surface the theorems discharge).
pub const NNVERIFY_IEEE754_EMPTY_CLOSURE_THEOREMS: &[&str] = &[
    "NNVerify.FloatRational.float_to_rat_exact_discharge_01",
    "NNVerify.FloatRational.rounding_error_le_half_ulp",
    "NNVerify.FloatRational.rounding_error_le_half_ulp_denormal",
    "NNVerify.FloatRational.round_discharge_normal",
    "NNVerify.FloatRational.rounding_error_bound_discharge_normal",
    "NNVerify.FloatRational.round_discharge_subnormal",
    "NNVerify.FloatRational.rounding_error_bound_discharge_subnormal",
    "NNVerify.FloatRational.round_discharge_tie",
    "NNVerify.FloatRational.rounding_error_bound_discharge_tie",
    "NNVerify.FloatRational.round_discharge_exact",
    "NNVerify.FloatRational.rounding_error_bound_discharge_exact",
    // The dot-product accumulation development: `init_nn_verify_dot_product_error`
    // ENSURES every declaration it registers is a `Theorem` with an empty
    // non-foundational closure (the kernel-side `tests_nn_verify_dot_product_error`
    // suite asserts that per name), so the whole development belongs here.
    "NNVerify.FloatRational.error_accum_step",
    "NNVerify.FloatRational.error_accum_step3",
    "NNVerify.FloatRational.error_accum_step4",
    "NNVerify.FloatRational.fl_op_rel_error_discharge_f32",
    "NNVerify.FloatRational.fl_op_rel_error_discharge_f64",
    "NNVerify.FloatRational.gamma_n_reduces_u8_n2",
    "NNVerify.FloatRational.gamma_n_reduces_u8_n3",
    "NNVerify.FloatRational.gamma_n_reduces_u12_n2",
    "NNVerify.FloatRational.gamma_n_reduces_u12_n3",
    "NNVerify.FloatRational.gamma_n_reduces_f32_n2",
    "NNVerify.FloatRational.gamma_n_reduces_f32_n3",
    "NNVerify.FloatRational.gamma_n_reduces_f64_n2",
    "NNVerify.FloatRational.gamma_n_reduces_f64_n3",
];

/// Seed a kernel `Environment::with_prelude()` and register the full IEEE-754
/// float→rational theory (Stage A + Stage B). The prelude supplies the Rat /
/// Float / Nat / Int foundations and the native reducers, plus
/// `Nat.ulp_universal_bound` (which gates Stage B wiring).
pub fn seed_ieee754_environment() -> MathverseResult<Environment> {
    let mut env = Environment::with_prelude();
    env.init_nn_verify_float_rational().map_err(|e| {
        MathverseError::Kernel(format!("init_nn_verify_float_rational failed: {e}"))
    })?;
    Ok(env)
}

/// Reconstruct a kernel `Declaration` from a live environment constant.
///
/// The kernel exposes no `ConstantInfo → Declaration` conversion, so reconstruct
/// it from the stored kind / level params / type / value (mirrors
/// `build_library_native::constant_info_to_declaration`).
fn declaration_for(env: &Environment, name: &str) -> MathverseResult<Declaration> {
    let kernel_name = Name::from_string(name);
    let info = env.get_const(&kernel_name).ok_or_else(|| {
        MathverseError::Kernel(format!("{name} not registered in seeded environment"))
    })?;
    let decl =
        match info.kind {
            ConstantKind::Theorem => Declaration::Theorem {
                name: info.name.clone(),
                level_params: info.level_params.clone(),
                type_: info.type_.clone(),
                value: info.value.clone().ok_or_else(|| {
                    MathverseError::Kernel(format!("{name}: theorem has no value"))
                })?,
            },
            ConstantKind::Definition => Declaration::Definition {
                name: info.name.clone(),
                level_params: info.level_params.clone(),
                type_: info.type_.clone(),
                value: info.value.clone().ok_or_else(|| {
                    MathverseError::Kernel(format!("{name}: definition has no value"))
                })?,
                is_reducible: info.is_reducible,
            },
            ConstantKind::Opaque => Declaration::Opaque {
                name: info.name.clone(),
                level_params: info.level_params.clone(),
                type_: info.type_.clone(),
                value: info.value.clone().ok_or_else(|| {
                    MathverseError::Kernel(format!("{name}: opaque has no value"))
                })?,
            },
            ConstantKind::Axiom => Declaration::Axiom {
                name: info.name.clone(),
                level_params: info.level_params.clone(),
                type_: info.type_.clone(),
            },
        };
    Ok(decl)
}

/// Build the sealed `nnverify_ieee754` shard from a freshly-seeded kernel
/// environment, returning the in-memory [`KernelShardBuilder`].
///
/// Every declaration in [`NNVERIFY_IEEE754_DECLS`] is flattened into the shard
/// via the native-decl→shard adapter (`KernelShardBuilder::add_declaration`),
/// then `finalize_axiom_profiles` runs the in-shard axiom-profile closure so the
/// recorded profiles are exact before the bytes are written.
///
/// The shard is tagged [`SourceSystem::CleanNative`] (the math is Clean-native,
/// kernel-verified) — but see the module docs for why this shard is verified by
/// kernel re-check rather than the foundational-only `native_gate`.
pub fn build_nnverify_ieee754_shard() -> MathverseResult<KernelShardBuilder> {
    let env = seed_ieee754_environment()?;
    let mut builder = KernelShardBuilder::new().with_source_system(SourceSystem::CleanNative);

    for &name in NNVERIFY_IEEE754_DECLS {
        let decl = declaration_for(&env, name)?;
        builder.add_declaration(&decl, &["ieee754", "float", "rounding"])?;
    }

    // Seal: run the in-shard axiom-profile closure before freezing.
    builder.shard_writer_mut().finalize_axiom_profiles();
    Ok(builder)
}

/// Outcome of building + registering the shard in a library directory.
#[derive(Clone, Debug)]
pub struct RegisterResult {
    /// Manifest entry recorded for the shard (real hash + counts).
    pub entry: ShardEntry,
    /// Number of base shards in the manifest after registration.
    pub base_shard_count: usize,
}

/// Write the sealed `nnverify_ieee754` shard under `<library_root>/nnverify_ieee754/`
/// and register it in the library `manifest.json` with the REAL blake3 content
/// hash and the REAL header constant/expr counts.
///
/// Idempotent on `path`: an existing manifest entry for this shard is removed
/// before the fresh entry is appended (no duplicates across re-runs).
pub fn register_nnverify_ieee754_shard(library_root: &Path) -> MathverseResult<RegisterResult> {
    let builder = build_nnverify_ieee754_shard()?;

    let subdir = library_root.join(NNVERIFY_IEEE754_SHARD_SUBDIR);
    std::fs::create_dir_all(&subdir).map_err(MathverseError::Io)?;
    let shard_path = subdir.join(format!("{NNVERIFY_IEEE754_SHARD_NAME}.mathverse"));
    builder.write_to_file(&shard_path)?;

    // Real blake3 over the exact on-disk bytes (matches LibraryLoader::write_shard
    // and the register_shard example) and real header counts via ShardReader.
    let data = std::fs::read(&shard_path).map_err(MathverseError::Io)?;
    let content_hash = blake3::hash(&data).to_hex().to_string();
    let reader = ShardReader::from_file(&shard_path)?;
    let rel_path =
        format!("{NNVERIFY_IEEE754_SHARD_SUBDIR}/{NNVERIFY_IEEE754_SHARD_NAME}.mathverse");
    let entry = ShardEntry {
        path: rel_path.clone(),
        content_hash,
        constant_count: reader.header.constant_count,
        expr_count: reader.header.expr_count,
        source: NNVERIFY_IEEE754_SHARD_NAME.to_string(),
    };

    let paths = LibraryPaths::new(library_root.to_path_buf());
    let mut manifest = if paths.manifest.exists() {
        MathverseManifest::load(&paths.manifest)?
    } else {
        MathverseManifest::new()
    };
    manifest.remove_shard(&rel_path);
    manifest.add_base_shard(entry.clone());
    manifest.save(&paths.manifest)?;

    Ok(RegisterResult {
        entry,
        base_shard_count: manifest.base_shards.len(),
    })
}

/// Result of kernel-re-checking the `nnverify_ieee754` shard.
#[derive(Clone, Debug, Default)]
pub struct VerifyResult {
    /// Total constants in the shard.
    pub total: usize,
    /// Constants that round-tripped (reconstructed) and kernel-re-checked.
    pub kernel_rechecked: usize,
    /// Names of the empty-closure theorems that re-verified with `axiom_deps == ∅`.
    pub empty_closure_verified: Vec<String>,
    /// Per-constant rejection reasons (name, reason). Empty iff the shard is clean.
    pub rejections: Vec<(String, String)>,
}

impl VerifyResult {
    /// `true` iff every constant kernel-re-checked and every empty-closure
    /// theorem re-verified with an empty non-foundational axiom closure.
    #[must_use]
    pub fn is_clean(&self) -> bool {
        self.rejections.is_empty()
            && self.kernel_rechecked == self.total
            && self.empty_closure_verified.len() == NNVERIFY_IEEE754_EMPTY_CLOSURE_THEOREMS.len()
    }
}

/// Load the `nnverify_ieee754` shard from `shard_path` and RE-CHECK it through
/// Clean's kernel.
///
/// For every constant the shard records, this reconstructs its type / value /
/// level-params from the shard's FlatExpr arena (the round-trip oracle) and runs
/// the kernel `TypeChecker` against a foundational replay environment seeded
/// exactly as the producer was (`Environment::with_prelude()` +
/// `init_nn_verify_float_rational`, which supplies Rat / Float / Nat / Int and
/// the native float reducers):
///
/// - A `Theorem` / `Definition` / `Opaque` (has a value) is re-checked with
///   `TypeChecker::check_type(value, type)` — the kernel re-validates that the
///   reconstructed proof/value inhabits the reconstructed type (the same
///   `infer_only = false` path `Environment::add_decl` runs). For the discharge
///   and round/ulp theorems this is the kernel RE-VERIFYING the proof.
/// - An `Axiom` (no value) is re-checked with `infer_type_full(type)`, which
///   must yield a `Sort` — the postulated type is well-formed.
///
/// Then the non-foundational axiom closure of each empty-closure theorem is
/// re-derived from the replay environment (`Environment::axiom_deps`) and
/// asserted EMPTY (no `sorry`, no domain axiom) — the recorded axiom profile of
/// the empty-closure theorems is exactly the foundational base.
///
/// Seeding the replay env with the full theory (rather than replaying the shard
/// decls via `add_decl`, which would need the `pub(crate)` overlay foundations
/// and would duplicate-collide) means the kernel re-check runs against the real
/// `Rat`/`Float`/native-reducer environment the proofs were stated in, and the
/// shard's RECONSTRUCTED expressions are the thing under test.
pub fn verify_nnverify_ieee754_shard(shard_path: &Path) -> MathverseResult<VerifyResult> {
    let reader = ShardReader::from_file(shard_path)?;
    let mut result = VerifyResult {
        total: reader.constants.len(),
        ..Default::default()
    };

    // Foundational replay environment, seeded exactly as the producer was. This
    // gives the kernel `Rat`/`Float`/`Nat`/`Int` + the native float reducers the
    // reconstructed expressions reference.
    let env = seed_ieee754_environment()?;
    let tc = TypeChecker::with_mode(&env, env.mode());

    for (index, header) in reader.constants.iter().enumerate() {
        let name = reader
            .strings
            .get(header.name_idx as usize)
            .cloned()
            .unwrap_or_else(|| format!("#{index}"));

        let type_ = match reconstruct_from_shard_with_level_lists(
            &reader.exprs,
            &reader.levels,
            &reader.strings,
            &reader.level_lists,
            header.type_idx,
        ) {
            Ok(e) => e,
            Err(e) => {
                result
                    .rejections
                    .push((name, format!("type reconstruct failed: {e}")));
                continue;
            }
        };

        let value = if header.value_idx != NO_VALUE {
            match reconstruct_from_shard_with_level_lists(
                &reader.exprs,
                &reader.levels,
                &reader.strings,
                &reader.level_lists,
                header.value_idx,
            ) {
                Ok(e) => Some(e),
                Err(e) => {
                    result
                        .rejections
                        .push((name, format!("value reconstruct failed: {e}")));
                    continue;
                }
            }
        } else {
            None
        };

        // Reconstruct level params too (round-trip completeness), even though the
        // float theory is level-monomorphic.
        if let Err(e) = reconstruct_level_params(
            &reader.strings,
            header.level_params_start,
            header.level_params_count,
        ) {
            result
                .rejections
                .push((name, format!("level-param reconstruct failed: {e}")));
            continue;
        }

        let decl_kind = match DeclKind::try_from(header.decl_kind) {
            Ok(k) => k,
            Err(byte) => {
                result
                    .rejections
                    .push((name, format!("unknown decl_kind {byte}")));
                continue;
            }
        };

        if let Err(reason) = kernel_recheck_constant(&tc, decl_kind, &type_, value.as_ref()) {
            result.rejections.push((name, reason));
            continue;
        }
        result.kernel_rechecked += 1;
    }

    // Axiom-profile assertion: every empty-closure theorem must have an EMPTY
    // non-foundational axiom closure (sorry-free, no hidden domain axiom).
    for &thm in NNVERIFY_IEEE754_EMPTY_CLOSURE_THEOREMS {
        let kernel_name = Name::from_string(thm);
        match env.axiom_deps(&kernel_name) {
            Some(deps) if deps.is_empty() => {
                result.empty_closure_verified.push(thm.to_string());
            }
            Some(deps) => {
                let names: Vec<String> = deps.iter().map(Name::to_string).collect();
                result.rejections.push((
                    thm.to_string(),
                    format!("non-empty axiom closure: {names:?}"),
                ));
            }
            None => {
                result
                    .rejections
                    .push((thm.to_string(), "not present in replay env".to_string()));
            }
        }
    }

    Ok(result)
}

/// Kernel-re-check ONE reconstructed declaration against the replay env.
///
/// - has value (Theorem/Definition/Opaque): `check_type(value, type)` — the
///   kernel re-validates the proof/value inhabits the stated type.
/// - no value (Axiom): `infer_type_full(type)` must yield a `Sort`.
fn kernel_recheck_constant(
    tc: &TypeChecker<'_>,
    decl_kind: DeclKind,
    type_: &Expr,
    value: Option<&Expr>,
) -> Result<(), String> {
    match decl_kind {
        DeclKind::Theorem | DeclKind::Definition | DeclKind::Opaque => {
            let value = value.ok_or_else(|| "non-axiom declaration missing value".to_string())?;
            tc.check_type(value, type_)
                .map_err(|e| format!("kernel rejected value against type: {e:?}"))
        }
        DeclKind::Axiom => {
            let inferred = tc
                .infer_type_full(type_)
                .map_err(|e| format!("kernel rejected axiom type: {e:?}"))?;
            if matches!(inferred.kind(), ExprKind::Sort(_)) {
                Ok(())
            } else {
                Err(format!("axiom type is not a Sort; inferred {inferred:?}"))
            }
        }
        other => Err(format!(
            "unsupported decl_kind {other:?} for IEEE-754 shard"
        )),
    }
}

#[cfg(test)]
#[path = "nnverify_ieee754_shard_tests.rs"]
mod tests;
