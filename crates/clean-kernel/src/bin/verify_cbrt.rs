// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Verification harness for the KKL cbrt (cube-root) layer.
//!
//! Bins (unlike examples/tests) do NOT receive dev-dependencies, so this gate
//! compiles with only `clean-kernel`'s normal deps — avoiding the unrelated
//! sibling-crate (`clean-auto`/`ay`) drift that blocks `cargo test -p
//! clean-kernel` in this worktree. Builds the env via the public `init_*` API
//! and kernel-checks + axiom-closure-asserts each cbrt declaration.
//!
//! ```bash
//! cargo run --offline -p clean-kernel --features math-overlays --bin verify_cbrt
//! ```
//!
//! Exit code 0 only if ALL cbrt decls kernel-check with foundational-only
//! (empty domain) axiom closure.

use clean_kernel::{ConstantKind, Environment, Name, ProofQuality, TypeChecker};

fn main() {
    let mut env = Environment::with_prelude();

    // Rung 1: cube dyadic-floor numerator + scale.
    env.init_algebra_nnreal_cbrt_dyadic()
        .expect("init_algebra_nnreal_cbrt_dyadic");
    // Rung 1: cube LOWER invariant.
    env.init_algebra_nnreal_cbrt_invariant()
        .expect("init_algebra_nnreal_cbrt_invariant");
    // Rung 1: cube STRICT UPPER bound.
    env.init_algebra_nnreal_cbrt_upper()
        .expect("init_algebra_nnreal_cbrt_upper");
    // Rung 1: cube digit-step increment bounds (for the telescoping Cauchy).
    env.init_algebra_nnreal_cbrt_mono()
        .expect("init_algebra_nnreal_cbrt_mono");
    // Rung 2: the scaled cube dyadic sequence + telescoping IsCauchy chain.
    env.init_algebra_nnreal_cbrt_seq()
        .expect("init_algebra_nnreal_cbrt_seq");
    env.init_algebra_nnreal_cbrt_iscauchy()
        .expect("init_algebra_nnreal_cbrt_iscauchy");
    // Rung 2 capstone: NNReal.cbrt defined.
    env.init_algebra_nnreal_cbrt_def()
        .expect("init_algebra_nnreal_cbrt_def");
    // Rung 3 part A: the LOWER cube squeeze + scale bridges.
    env.init_algebra_nnreal_cbrt_squeeze()
        .expect("init_algebra_nnreal_cbrt_squeeze");
    // Rung 1 + 2 helpers: pure Rat cube lemmas.
    env.init_algebra_rat_cube_identity()
        .expect("init_algebra_rat_cube_identity");
    // Rung 4: the cube keystone identity (cbrt x)³ = ofRat x.
    env.init_algebra_nnreal_cbrt_identity()
        .expect("init_algebra_nnreal_cbrt_identity");
    // Rung 5 (partial): 0 ≤ cbrt x + NNReal.pow43 definition.
    env.init_algebra_nnreal_pow43()
        .expect("init_algebra_nnreal_pow43");

    let defs: &[&str] = &[
        "Rat.cbrtDyadicPow8",
        "Rat.cbrtDyadicNum",
        "Rat.cbrtDyadicApprox",
        "Rat.cbrtDyadicApproxNN",
        "NNReal.cbrt",
        "NNReal.pow43",
    ];
    let theorems: &[&str] = &[
        "Rat.cbrtDyadicNum_cube_le",
        "Rat.zero_lt_ofNat_eight",
        "Rat.cbrtDyadicNum_cube_lt_succ",
        "Rat.cbrtDyadicNum_two_mul_le_succ",
        "Rat.cbrtDyadicNum_succ_le_two_mul_succ",
        "Rat.zero_le_cbrtDyadicApprox",
        "Rat.cbrtDyadicApprox_le_succ",
        "Rat.cbrtDyadicApprox_succ_le",
        "Rat.cbrtDyadicApprox_le_add_inv",
        "Rat.cbrtDyadicApprox_le_add",
        "Rat.cbrtDyadicApprox_mono",
        "Rat.cbrtDyadicApprox_le_add_inv_of_le",
        "NNReal.cbrtDyadicApprox_isCauchy",
        "Rat.ofNat_two_pow_cube_eq_pow8",
        "Rat.zero_lt_cbrtDyadicPow8",
        "Rat.inv_two_pow_cube_eq_inv_pow8",
        "Rat.cbrtDyadicApprox_cube_eq",
        "Rat.cbrtDyadicApprox_cube_le",
        "Rat.add_cube",
        "Rat.cube_lt_cube_of_lt_of_nonneg",
        "Rat.le_of_cube_le_cube",
        "Rat.cbrtDyadicApprox_le_one",
        "Rat.x_lt_cbrtDyadicApprox_cube_add_seven_inv",
        "NNReal.cbrtDyadicApprox_cube_equiv_const",
        "NNReal.cbrt_cubed",
        "NNReal.zero_le_cbrt",
    ];

    let tc = TypeChecker::with_mode(&env, env.mode());
    for name in defs.iter().chain(theorems.iter()) {
        let nm = Name::from_string(name);
        let info = env
            .get_const(&nm)
            .unwrap_or_else(|| panic!("{name} not registered"));
        let value = info.value.clone().expect("value present");
        tc.check_type(&value, &info.type_)
            .unwrap_or_else(|e| panic!("{name} FAILED kernel-check: {e:?}"));
        println!("[OK kernel-check] {name}  ({:?})", info.kind);
    }
    for name in theorems {
        let nm = Name::from_string(name);
        let info = env.get_const(&nm).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem, "{name} must be Theorem");
        assert_eq!(
            env.proof_quality(&nm),
            Some(ProofQuality::Constructive),
            "{name} must be Constructive"
        );
        let deps = env.axiom_deps(&nm).expect("deps");
        assert!(
            deps.is_empty(),
            "{name} closure must be foundational-only, got: {deps:?}"
        );
        println!("[OK empty-closure + Constructive] {name}");
    }
    println!("\nALL CBRT RUNGS VERIFIED.");
}
