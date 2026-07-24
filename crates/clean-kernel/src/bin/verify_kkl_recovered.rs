// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Kernel-verification harness for the RECOVERED unconditional-KKL overlays
//! (consolidate/kkl).
//!
//! Bins (unlike examples/tests) do NOT receive dev-dependencies, so this gate
//! compiles with only `clean-kernel`'s normal deps — avoiding the heavy
//! sibling-crate (`criterion`/`ay`) dev-dep build that stalls `cargo test -p
//! clean-kernel` in this worktree. Builds the env via the public `init_*` API
//! for every recovered layer and kernel-checks + axiom-closure-asserts each
//! recovered theorem.
//!
//! ```bash
//! cargo run --offline -p clean-kernel --features math-overlays --bin verify_kkl_recovered
//! ```
//!
//! Exit code 0 only if ALL recovered theorems kernel-check (TypeChecker accepts
//! the proof body against its stated type) with a foundational-only (empty
//! domain-axiom) closure and `ProofQuality::Constructive`.

use clean_kernel::{ConstantKind, Environment, Name, ProofQuality, TypeChecker};

fn main() {
    let mut env = Environment::with_prelude();

    // ── carrier-lattice ──────────────────────────────────────────────────
    env.init_algebra_nnreal_add_laws()
        .expect("init_algebra_nnreal_add_laws");
    env.init_algebra_nnreal_le_recovered()
        .expect("init_algebra_nnreal_le_recovered");
    env.init_algebra_nnreal_add_le()
        .expect("init_algebra_nnreal_add_le");
    env.init_algebra_nnreal_bounded_recovered()
        .expect("init_algebra_nnreal_bounded_recovered");
    env.init_algebra_nnreal_nnrat_max_recovered()
        .expect("init_algebra_nnreal_nnrat_max_recovered");
    env.init_algebra_nnreal_nnrat_order()
        .expect("init_algebra_nnreal_nnrat_order");
    env.init_algebra_nnreal_nnrat_prefixmax()
        .expect("init_algebra_nnreal_nnrat_prefixmax");

    // ── nnreal-mul ───────────────────────────────────────────────────────
    env.init_algebra_rat_inv_pos()
        .expect("init_algebra_rat_inv_pos");
    env.init_algebra_rat_div_mul_cancel()
        .expect("init_algebra_rat_div_mul_cancel");
    env.init_algebra_rat_mul_close_recovered()
        .expect("init_algebra_rat_mul_close_recovered");
    env.init_algebra_rat_mul_left_close()
        .expect("init_algebra_rat_mul_left_close");
    env.init_algebra_rat_add_lt_add_mixed()
        .expect("init_algebra_rat_add_lt_add_mixed");
    env.init_algebra_nnreal_iscauchy_mul()
        .expect("init_algebra_nnreal_iscauchy_mul");
    env.init_algebra_nnreal_causeq_mul()
        .expect("init_algebra_nnreal_causeq_mul");

    // ── cube-amgm ────────────────────────────────────────────────────────
    env.init_algebra_rat_cube_amgm_recovered()
        .expect("init_algebra_rat_cube_amgm_recovered");

    // ── dualhc-rational (unconditional dual-HC chain + assembly FIRED) ────
    env.init_boolean_analysis_kkl_dualhc_percoord_recovered()
        .expect("init_boolean_analysis_kkl_dualhc_percoord_recovered");

    // Recovered theorems (must kernel-check AND have a foundational-only,
    // Constructive closure). Definitions referenced by these proofs are
    // kernel-checked transitively by check_type.
    let theorems: &[&str] = &[
        // carrier-lattice
        "NNReal.le_refl",
        "NNReal.le_trans",
        "NNReal.add_comm",
        "NNReal.add_assoc",
        "NNReal.add_zero",
        "NNReal.zero_add",
        "NNReal.add_le_add",
        "NNReal.CauSeq.bounded",
        "Rat.le_of_lt",
        "NNRat.le_refl",
        "NNRat.le_trans",
        "NNRat.le_max_left",
        "NNRat.le_max_right",
        "NNRat.max_le",
        "NNRat.val_max",
        "NNRat.le_prefixMax",
        "NNRat.self_le_prefixMax",
        "NNRat.prefixMax_le_succ",
        "NNRat.prefixMax_mono",
        // nnreal-mul
        "Rat.inv_pos",
        "Rat.div_pos",
        "Rat.div_mul_cancel_pos",
        "Rat.mul_lt_mul_add_of_bounds",
        "Rat.mul_left_close",
        "NNReal.IsCauchy_mul",
        // cube-amgm
        "Rat.cube_amgm_two_one_recovered",
        // dualhc-rational
        "BoolAnalysis.dualhc_h1",
        "BoolAnalysis.dualhc_h2",
        "BoolAnalysis.dualhc_percoord_linear",
        "BoolAnalysis.dualhc_h_dual_sum",
        "BoolAnalysis.dualhc_final_le",
        "BoolAnalysis.dualhc_norm_cancel_8n",
        "BoolAnalysis.dualhc_m_pow2_eq_4pow_influence",
        "BoolAnalysis.dualhc_pow8_eq_two_pow_cube",
        "BoolAnalysis.rpow32_scale",
        "BoolAnalysis.kkl_lowband_mass_fired",
    ];

    let tc = TypeChecker::with_mode(&env, env.mode());
    let mut failures = 0usize;
    for name in theorems {
        let nm = Name::from_string(name);
        let Some(info) = env.get_const(&nm) else {
            eprintln!("[MISSING] {name} not registered");
            failures += 1;
            continue;
        };
        let value = info
            .value
            .clone()
            .expect("recovered theorem has a proof body");
        if let Err(e) = tc.check_type(&value, &info.type_) {
            eprintln!("[FAIL kernel-check] {name}: {e:?}");
            failures += 1;
            continue;
        }
        if info.kind != ConstantKind::Theorem {
            eprintln!("[FAIL] {name} is {:?}, not a Theorem", info.kind);
            failures += 1;
            continue;
        }
        if env.proof_quality(&nm) != Some(ProofQuality::Constructive) {
            eprintln!(
                "[FAIL] {name} is not Constructive: {:?}",
                env.proof_quality(&nm)
            );
            failures += 1;
            continue;
        }
        let deps = env.axiom_deps(&nm).expect("axiom deps computable");
        if !deps.is_empty() {
            eprintln!("[FAIL] {name} has non-foundational axiom closure: {deps:?}");
            failures += 1;
            continue;
        }
        println!("[OK kernel-check + empty-closure + Constructive] {name}");
    }

    if failures == 0 {
        println!(
            "\nALL {} RECOVERED KKL THEOREMS KERNEL-VERIFIED (foundational-only, Constructive).",
            theorems.len()
        );
    } else {
        eprintln!("\n{failures} recovered theorem(s) FAILED verification.");
        std::process::exit(1);
    }
}
