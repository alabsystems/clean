// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The published-declaration manifest for the `nnverify_ieee754` shard.
//!
//! Two name tables, and the ordering / closure contracts they carry:
//! [`NNVERIFY_IEEE754_DECLS`] fixes WHICH of the kernel-registered
//! `NNVerify.FloatRational.*` theory is published and in what dependency-safe
//! order it replays, and [`NNVERIFY_IEEE754_EMPTY_CLOSURE_THEOREMS`] fixes
//! which of those must re-verify with an EMPTY non-foundational axiom closure.
//! Both are consulted by build, register and verify alike in [`super`], so the
//! tables live together, apart from the code that walks them.

/// NOT PUBLISHED since 2026-09-26 (`docs/issues/2026-09-26-kernel-native-fold-
/// by-name.md`): the per-constant "discharges" — `float_to_rat_exact_discharge_01`,
/// the four `round_discharge_*` / `rounding_error_bound_discharge_*` pairs and
/// `fl_op_rel_error_discharge_f32`/`_f64`. Each was proved by the kernel
/// computing `Float.toRatExact` or `Rat.roundToNearestEven` through a native
/// reducer, and both are OPAQUE placeholders (`fun _ => Rat.zero`) no
/// definition backs; native folds now fire only over a canonical definition,
/// so the kernel no longer registers them.
///
/// The IEEE-754 float-theory declarations packaged into the shard, in a fixed
/// **dependency-safe order**: every name appears after the constants it
/// references (the `with_prelude` baseline supplies Rat / Float / Nat / Int /
/// `Nat.ulp_universal_bound`; only the intra-shard ordering — function symbols
/// before the theorems stated over them — matters for kernel replay).
///
/// The kernel registers all of these from `init_nn_verify_float_rational`; this
/// is the single source of truth for which subset is published. Replay (in
/// [`super::verify_nnverify_ieee754_shard`]) walks this same order so each later
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
    // --- the native ties-to-even round (Opaque, reducer-backed) ---
    "Rat.roundToNearestEven",
    // --- the universal + denormal half-ulp soundness theorems (empty closure) ---
    "NNVerify.FloatRational.rounding_error_le_half_ulp",
    "NNVerify.FloatRational.rounding_error_le_half_ulp_denormal",
    // --- Higham dot-product accumulated-error development (empty closure) ---
    // `init_nn_verify_float_rational` pulls `init_nn_verify_dot_product_error`
    // in, so these are part of the registered float theory and must be
    // published with it. The accumulation chains reference
    // `error_accum_step`, so they follow it; the per-op discharges and the
    // concrete γ_n reductions are self-contained literal proofs.
    "NNVerify.FloatRational.error_accum_step",
    "NNVerify.FloatRational.error_accum_step3",
    "NNVerify.FloatRational.error_accum_step4",
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
    "NNVerify.FloatRational.rounding_error_le_half_ulp",
    "NNVerify.FloatRational.rounding_error_le_half_ulp_denormal",
    // The dot-product accumulation development: `init_nn_verify_dot_product_error`
    // ENSURES every declaration it registers is a `Theorem` with an empty
    // non-foundational closure (the kernel-side `tests_nn_verify_dot_product_error`
    // suite asserts that per name), so the whole development belongs here.
    "NNVerify.FloatRational.error_accum_step",
    "NNVerify.FloatRational.error_accum_step3",
    "NNVerify.FloatRational.error_accum_step4",
    "NNVerify.FloatRational.gamma_n_reduces_u8_n2",
    "NNVerify.FloatRational.gamma_n_reduces_u8_n3",
    "NNVerify.FloatRational.gamma_n_reduces_u12_n2",
    "NNVerify.FloatRational.gamma_n_reduces_u12_n3",
    "NNVerify.FloatRational.gamma_n_reduces_f32_n2",
    "NNVerify.FloatRational.gamma_n_reduces_f32_n3",
    "NNVerify.FloatRational.gamma_n_reduces_f64_n2",
    "NNVerify.FloatRational.gamma_n_reduces_f64_n3",
];
