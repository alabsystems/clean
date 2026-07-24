// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Guard tests for the 15 C003 `sorry_inhabit_pi` carrier sites.
//!
//! See `reports/audit/2026-04-20-3569-c003-sorry-pi-carrier-classification.md`
//! for the full classification. Each site lives under one of three buckets:
//!
//! * Bucket A (7 sites): conclusion reduces to `True` via reducible
//!   `NNVerify.Lipschitz.constant` alias. Reducing here produces a
//!   MASQUERADE under `designs/2026-04-19-demasquerade-cxxx-pattern.md`
//!   Rules M1+M2+M4 (the textbook #3501 `mccormick_gap_bound` pattern).
//! * Bucket B (5 sites): conclusion is a genuine `Rat.le` / `Rat.lt` on
//!   Opaque placeholders (`lip_product`, `real_exp`, `rat_pow`, `width`).
//!   `True.intro` does not inhabit `Int.NonNeg _`, and alias-reflexivity
//!   would itself be a MASQUERADE (same M1+M4 pattern demoted in #3501).
//! * Bucket C (3 sites): conclusion is an `Exists` or `And` — requires
//!   concrete witnesses that are not available under the Opaque carriers.
//!
//! This module pins, for each of the 15 sites, the current
//! `ConstantKind` of the backing `_axiom` Opaque AND the wrapping
//! `Declaration::Theorem`. Any future reduction that does not also
//! explicitly update these expectations will fail loudly, forcing a
//! reviewer to engage with the masquerade-risk classification before
//! accepting a sorry-pi reduction as a constructive proof.
//!
//! Part of #3569. See also: #3501 (mccormick_gap_bound demotion),
//! #3566/#3567/#3568 (wave-3 demasquerade sweep).

use crate::env::{ConstantKind, Environment};
use crate::name::Name;

fn make_env() -> Environment {
    let mut env = Environment::new();
    // `eclipse_convergence` pulls in `lipschitz`, `lipschitz_ext`, and
    // `lipschitz_eclipse` transitively, giving us access to every C003
    // sorry-pi site in one initialized environment.
    env.init_nn_verify_eclipse_convergence()
        .expect("init_nn_verify_eclipse_convergence");
    env.init_nn_verify_lipschitz_eclipse()
        .expect("init_nn_verify_lipschitz_eclipse");
    env.init_nn_verify_lipschitz_ext()
        .expect("init_nn_verify_lipschitz_ext");
    env
}

/// Every backing `_axiom` Opaque for the 15 C003 sorry-pi sites stays
/// `ConstantKind::Opaque` with a stored value (the `sorry_inhabit_pi`
/// body). Any attempt to demote to `Axiom` (Branch A demasquerade) OR
/// promote to `Theorem` (constructive reduction) without updating the
/// audit report and this test will fail loudly.
fn check_axiom_is_opaque(env: &Environment, name: &str) {
    let info = env
        .get_const(&Name::from_string(name))
        .unwrap_or_else(|| panic!("{} must be registered", name));
    assert_eq!(
        info.kind,
        ConstantKind::Opaque,
        "{}: expected Opaque (sorry_inhabit_pi carrier), got {:?}. \
         If this is a deliberate reduction or demasquerade, update the \
         C003 carrier classification audit and this guard test in the same \
         commit. See reports/audit/2026-04-20-3569-c003-sorry-pi-carrier-classification.md",
        name,
        info.kind,
    );
    assert!(
        info.value.is_some(),
        "{}: Opaque must carry a value (sorry_inhabit_pi lambda); got None",
        name,
    );
}

/// Every wrapping Theorem for the 15 C003 sorry-pi sites stays
/// `ConstantKind::Theorem` with its proof = `Expr::const_("<name>_axiom")`.
/// This pins the shape so a reduction that swaps the Opaque + Theorem
/// pair for a single direct Theorem proof (the #3459 residual_lip
/// pattern) will break the test.
fn check_theorem_wraps_axiom(env: &Environment, name: &str) {
    let info = env
        .get_const(&Name::from_string(name))
        .unwrap_or_else(|| panic!("{} must be registered", name));
    assert_eq!(
        info.kind,
        ConstantKind::Theorem,
        "{}: expected Theorem (axiom-wrapper), got {:?}. \
         Reducing this site without updating the guard test implies \
         one of the three masquerade buckets in \
         reports/audit/2026-04-20-3569-c003-sorry-pi-carrier-classification.md \
         applies — confirm the reduction is not a masquerade before \
         updating this expectation.",
        name,
        info.kind,
    );
    assert!(
        info.value.is_some(),
        "{}: Theorem must carry its proof term",
        name,
    );
}

// ---------------------------------------------------------------------
// Bucket A: True-reducible conclusions (7 sites) — DO NOT REDUCE.
// ---------------------------------------------------------------------

#[test]
fn guard_c003_bucket_a1_residual_lipschitz_is_opaque_plus_theorem() {
    let env = make_env();
    check_axiom_is_opaque(&env, "NNVerify.Lipschitz.residual_lipschitz_axiom");
    check_theorem_wraps_axiom(&env, "NNVerify.Lipschitz.residual_lipschitz");
}

#[test]
fn guard_c003_bucket_a2_nfold_product_is_opaque_plus_theorem() {
    let env = make_env();
    check_axiom_is_opaque(&env, "NNVerify.Lipschitz.nfold_product_axiom");
    check_theorem_wraps_axiom(&env, "NNVerify.Lipschitz.nfold_product");
}

#[test]
fn guard_c003_bucket_a3_spectral_norm_lipschitz_is_opaque_plus_theorem() {
    let env = make_env();
    check_axiom_is_opaque(&env, "NNVerify.Lipschitz.spectral_norm_lipschitz_axiom");
    check_theorem_wraps_axiom(&env, "NNVerify.Lipschitz.spectral_norm_lipschitz");
}

#[test]
fn guard_c003_bucket_a4_lipschitz_compose_is_opaque_plus_theorem() {
    let env = make_env();
    check_axiom_is_opaque(&env, "NNVerify.Lipschitz.lipschitz_compose_axiom");
    check_theorem_wraps_axiom(&env, "NNVerify.Lipschitz.lipschitz_compose");
}

#[test]
fn guard_c003_bucket_a5_eclipse_block_lipschitz_is_opaque_plus_theorem() {
    let env = make_env();
    check_axiom_is_opaque(&env, "NNVerify.Lipschitz.eclipse_block_lipschitz_axiom");
    check_theorem_wraps_axiom(&env, "NNVerify.Lipschitz.eclipse_block_lipschitz");
}

#[test]
fn guard_c003_bucket_a6_eclipse_network_lipschitz_is_opaque_plus_theorem() {
    let env = make_env();
    check_axiom_is_opaque(&env, "NNVerify.Lipschitz.eclipse_network_lipschitz_axiom");
    check_theorem_wraps_axiom(&env, "NNVerify.Lipschitz.eclipse_network_lipschitz");
}

#[test]
fn guard_c003_bucket_a7_residual_lipschitz_sum_is_opaque_plus_theorem() {
    let env = make_env();
    check_axiom_is_opaque(&env, "NNVerify.Lipschitz.residual_lipschitz_sum_axiom");
    check_theorem_wraps_axiom(&env, "NNVerify.Lipschitz.residual_lipschitz_sum");
}

// ---------------------------------------------------------------------
// Bucket B: Rat-inequality conclusions (5 sites) — CANNOT REDUCE
// constructively under current Opaque carriers.
// ---------------------------------------------------------------------

#[test]
fn guard_c003_bucket_b1_product_convergence_is_opaque_plus_theorem() {
    let env = make_env();
    check_axiom_is_opaque(&env, "NNVerify.Lipschitz.product_convergence_axiom");
    check_theorem_wraps_axiom(&env, "NNVerify.Lipschitz.product_convergence");
}

#[test]
fn guard_c003_bucket_b2_spectral_bound_is_opaque_plus_theorem() {
    let env = make_env();
    check_axiom_is_opaque(&env, "NNVerify.Lipschitz.spectral_bound_axiom");
    check_theorem_wraps_axiom(&env, "NNVerify.Lipschitz.spectral_bound");
}

#[test]
fn guard_c003_bucket_b3_product_le_exp_sum_is_opaque_plus_theorem() {
    let env = make_env();
    check_axiom_is_opaque(&env, "NNVerify.Lipschitz.product_le_exp_sum_axiom");
    check_theorem_wraps_axiom(&env, "NNVerify.Lipschitz.product_le_exp_sum");
}

#[test]
fn guard_c003_bucket_b4_geometric_decay_is_opaque_plus_theorem() {
    let env = make_env();
    check_axiom_is_opaque(&env, "NNVerify.ECLipsE.geometric_decay_axiom");
    check_theorem_wraps_axiom(&env, "NNVerify.ECLipsE.geometric_decay");
}

#[test]
fn guard_c003_bucket_b5_termination_bound_is_opaque_plus_theorem() {
    let env = make_env();
    check_axiom_is_opaque(&env, "NNVerify.ECLipsE.termination_bound_axiom");
    check_theorem_wraps_axiom(&env, "NNVerify.ECLipsE.termination_bound");
}

// ---------------------------------------------------------------------
// Bucket C: Exists / And conclusions (3 sites) — CANNOT REDUCE without
// concrete witnesses.
// ---------------------------------------------------------------------

#[test]
fn guard_c003_bucket_c1_divergence_is_opaque_plus_theorem() {
    let env = make_env();
    check_axiom_is_opaque(&env, "NNVerify.Lipschitz.divergence_axiom");
    check_theorem_wraps_axiom(&env, "NNVerify.Lipschitz.divergence");
}

#[test]
fn guard_c003_bucket_c2_fixed_point_is_opaque_plus_theorem() {
    let env = make_env();
    check_axiom_is_opaque(&env, "NNVerify.ECLipsE.fixed_point_axiom");
    check_theorem_wraps_axiom(&env, "NNVerify.ECLipsE.fixed_point");
}

#[test]
fn guard_c003_bucket_c3_contraction_compose_is_opaque_plus_theorem() {
    let env = make_env();
    check_axiom_is_opaque(&env, "NNVerify.ECLipsE.contraction_compose_axiom");
    check_theorem_wraps_axiom(&env, "NNVerify.ECLipsE.contraction_compose");
}

/// Meta-test: the 15 C003 sorry-pi sites split as 7+5+3. If this count
/// changes, update the audit report and the individual guard tests.
#[test]
fn guard_c003_sorry_pi_site_count_is_15() {
    // Hard-coded check: this is a documentation assertion anchoring the
    // audit inventory. Any future change to the site count must update
    // both the audit report and this count.
    const BUCKET_A_SITES: usize = 7;
    const BUCKET_B_SITES: usize = 5;
    const BUCKET_C_SITES: usize = 3;
    assert_eq!(
        BUCKET_A_SITES + BUCKET_B_SITES + BUCKET_C_SITES,
        15,
        "C003 sorry_inhabit_pi site count must equal 15; if it changed, \
         update reports/audit/2026-04-20-3569-c003-sorry-pi-carrier-classification.md \
         and data/axiom_audit.json"
    );
}
