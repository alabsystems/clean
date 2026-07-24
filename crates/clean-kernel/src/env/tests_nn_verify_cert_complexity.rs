// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for certificate complexity measurement infrastructure.
//!
//! Measures existing NN verification proof terms (T70, T72, T80, T81, T82)
//! and records baseline complexity metrics.
//!
//! Part of #3260.

use crate::env::nn_verify_cert_complexity::{
    cert_depth, cert_term_size, cert_unique_constants, measure_cert_complexity,
    CertComplexityMetrics,
};
use crate::env::Environment;
use crate::expr::{Expr, ExprKind};
use crate::name::Name;

// =============================================================================
// Unit tests for measurement functions on simple expressions
// =============================================================================

#[test]
fn test_cert_term_size_leaf_bvar() {
    let e = Expr::bvar(0);
    assert_eq!(cert_term_size(&e), 1);
}

#[test]
fn test_cert_term_size_leaf_const() {
    let e = Expr::const_(Name::from_string("Nat"), vec![]);
    assert_eq!(cert_term_size(&e), 1);
}

#[test]
fn test_cert_term_size_app() {
    let f = Expr::const_(Name::from_string("f"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let app = Expr::app(f, a);
    // App node + 2 leaves = 3
    assert_eq!(cert_term_size(&app), 3);
}

#[test]
fn test_cert_term_size_nested_app() {
    let f = Expr::const_(Name::from_string("f"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let app1 = Expr::app(f, a);
    let app2 = Expr::app(app1, b);
    // outer App(1) + inner App(1) + f(1) + a(1) + b(1) = 5
    assert_eq!(cert_term_size(&app2), 5);
}

#[test]
fn test_cert_depth_leaf() {
    let e = Expr::bvar(0);
    assert_eq!(cert_depth(&e), 1);
}

#[test]
fn test_cert_depth_app() {
    let f = Expr::const_(Name::from_string("f"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let app = Expr::app(f, a);
    // depth: App(1) + max(leaf(1), leaf(1)) = 2
    assert_eq!(cert_depth(&app), 2);
}

#[test]
fn test_cert_depth_nested_app() {
    let f = Expr::const_(Name::from_string("f"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let app1 = Expr::app(f, a);
    let app2 = Expr::app(app1, b);
    // depth: outer App(1) + max(inner_app_depth=2, b_depth=1) = 3
    assert_eq!(cert_depth(&app2), 3);
}

#[test]
fn test_cert_unique_constants_empty() {
    let e = Expr::bvar(0);
    let consts = cert_unique_constants(&e);
    assert!(consts.is_empty());
}

#[test]
fn test_cert_unique_constants_single() {
    let e = Expr::const_(Name::from_string("Nat"), vec![]);
    let consts = cert_unique_constants(&e);
    assert_eq!(consts.len(), 1);
    assert!(consts.contains(&Name::from_string("Nat")));
}

#[test]
fn test_cert_unique_constants_dedup() {
    let nat1 = Expr::const_(Name::from_string("Nat"), vec![]);
    let nat2 = Expr::const_(Name::from_string("Nat"), vec![]);
    let app = Expr::app(nat1, nat2);
    let consts = cert_unique_constants(&app);
    // Same constant referenced twice => 1 unique
    assert_eq!(consts.len(), 1);
}

#[test]
fn test_measure_cert_complexity_simple() {
    let f = Expr::const_(Name::from_string("f"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let app = Expr::app(f, a);
    let metrics = measure_cert_complexity(&app);
    assert_eq!(
        metrics,
        CertComplexityMetrics {
            term_size: 3,
            depth: 2,
            unique_constants: 2, // "f" and "a"
        }
    );
}

#[test]
fn test_cert_term_size_pi() {
    use crate::expr::BinderInfo;
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let pi = Expr::pi(BinderInfo::Default, nat.clone(), nat);
    // Pi node + domain(Nat) + body(Nat) = 3
    assert_eq!(cert_term_size(&pi), 3);
}

#[test]
fn test_cert_depth_pi() {
    use crate::expr::BinderInfo;
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let pi = Expr::pi(BinderInfo::Default, nat.clone(), nat);
    assert_eq!(cert_depth(&pi), 2);
}

// =============================================================================
// Baseline measurements for existing NN verification proof terms
// =============================================================================

/// Helper: create env with T70 (entailment_transitivity) + T03 (interval_contains_refl)
fn make_env_proofs() -> Environment {
    let mut env = Environment::new();
    env.init_nn_verify_proofs().expect("init_nn_verify_proofs");
    env
}

/// Helper: create env with T72 (cert_composition_trust)
fn make_env_cert_proofs() -> Environment {
    let mut env = Environment::new();
    env.init_nn_verify_cert_proofs()
        .expect("init_nn_verify_cert_proofs");
    env
}

/// Helper: create env with T80, T81
fn make_env_ibp_linear() -> Environment {
    let mut env = Environment::new();
    env.init_nn_verify_ibp_linear()
        .expect("init_nn_verify_ibp_linear");
    env
}

/// Helper: create env with T82 (ibp_composition)
fn make_env_ibp_composition() -> Environment {
    let mut env = Environment::new();
    env.init_nn_verify_ibp_composition()
        .expect("init_nn_verify_ibp_composition");
    env
}

/// Extract proof term from environment by name.
fn get_proof_term(env: &Environment, name: &str) -> Expr {
    let info = env
        .get_const(&Name::from_string(name))
        .unwrap_or_else(|| panic!("{} should be registered", name));
    info.value
        .as_ref()
        .unwrap_or_else(|| panic!("{} should have a proof term", name))
        .clone()
}

/// Extract theorem type from environment by name.
fn get_theorem_type(env: &Environment, name: &str) -> Expr {
    let info = env
        .get_const(&Name::from_string(name))
        .unwrap_or_else(|| panic!("{} should be registered", name));
    info.type_.clone()
}

// -- T03: interval_contains_refl -----------------------------------------

#[test]
fn test_t03_interval_contains_refl_proof_size() {
    let env = make_env_proofs();
    let proof = get_proof_term(&env, "NNVerify.interval_contains_refl");
    let size = cert_term_size(&proof);
    // The proof is essentially `fun d B x h => h` (identity)
    // Should be small — a few lambda nodes + leaves
    assert!(size > 0, "proof term should be non-empty");
    assert!(
        size < 100,
        "identity-like proof should be small, got {}",
        size
    );
}

#[test]
fn test_t03_interval_contains_refl_depth() {
    let env = make_env_proofs();
    let proof = get_proof_term(&env, "NNVerify.interval_contains_refl");
    let depth = cert_depth(&proof);
    assert!(depth > 0);
    assert!(
        depth < 50,
        "identity-like proof should be shallow, got {}",
        depth
    );
}

// -- T70: entailment_transitivity ----------------------------------------

#[test]
fn test_t70_entailment_transitivity_proof_size() {
    let env = make_env_proofs();
    let proof = get_proof_term(&env, "NNVerify.entailment_transitivity");
    let metrics = measure_cert_complexity(&proof);
    // T70 is a non-trivial proof using le_trans + And.intro/left/right
    assert!(
        metrics.term_size > 10,
        "T70 proof should be substantial, got {}",
        metrics.term_size
    );
    assert!(
        metrics.depth > 3,
        "T70 proof should have some depth, got {}",
        metrics.depth
    );
    assert!(
        metrics.unique_constants > 3,
        "T70 proof should reference several constants, got {}",
        metrics.unique_constants
    );
}

#[test]
fn test_t70_type_complexity() {
    let env = make_env_proofs();
    let ty = get_theorem_type(&env, "NNVerify.entailment_transitivity");
    let metrics = measure_cert_complexity(&ty);
    // The type is `{d} -> (B1 B2 B3 : IB d) -> subset B1 B2 -> subset B2 B3 -> subset B1 B3`
    assert!(
        metrics.term_size > 5,
        "T70 type should be non-trivial, got {}",
        metrics.term_size
    );
}

// -- T72: cert_composition_trust -----------------------------------------

#[test]
fn test_t72_cert_composition_trust_is_axiom_post_3592() {
    // Post-#3592: T72 cert_composition_trust was demoted from
    // Declaration::Theorem (masquerade: Eq.refl over reducible
    // axiomProfile/composePair/BlockCert alias chain) to
    // Declaration::Axiom. It no longer has a proof term — proof-size
    // measurement is therefore meaningless and replaced with a
    // structural assertion pinning the post-demotion shape.
    use crate::env::ConstantKind;
    let env = make_env_cert_proofs();
    let info = env
        .get_const(&Name::from_string("NNVerify.cert_composition_trust"))
        .expect("NNVerify.cert_composition_trust should be registered");
    assert_eq!(info.kind, ConstantKind::Axiom);
    assert!(
        info.value.is_none(),
        "post-#3592: cert_composition_trust is Axiom with no stored proof term"
    );
}

// -- T80: ibp_linear_sound -----------------------------------------------

#[test]
fn test_t80_ibp_linear_sound_proof_size() {
    let env = make_env_ibp_linear();
    let proof = get_proof_term(&env, "NNVerify.ibp_linear_sound");
    let metrics = measure_cert_complexity(&proof);
    // T80 is a substantial proof about linear layer soundness
    assert!(
        metrics.term_size > 10,
        "T80 proof should be substantial, got {}",
        metrics.term_size
    );
}

// -- T81: ibp_relu_soundness ---------------------------------------------

#[test]
fn test_t81_ibp_relu_soundness_proof_size() {
    // T81 is registered by init_nn_verify_relu which is called by ibp_composition.
    let env2 = make_env_ibp_composition();
    let proof = get_proof_term(&env2, "NNVerify.ibp_relu_soundness");
    let metrics = measure_cert_complexity(&proof);
    assert!(metrics.term_size > 0, "T81 proof should be non-empty");
}

// -- T82: ibp_composition ------------------------------------------------

#[test]
fn test_t82_ibp_composition_proof_size() {
    let env = make_env_ibp_composition();
    let proof = get_proof_term(&env, "NNVerify.ibp_composition");
    let metrics = measure_cert_complexity(&proof);
    // T82 composes T80 + T81, should be moderate size
    assert!(
        metrics.term_size > 5,
        "T82 proof should have some structure, got {}",
        metrics.term_size
    );
    assert!(metrics.unique_constants > 0);
}

// -- Cross-theorem comparisons -------------------------------------------

#[test]
fn test_proof_size_ordering_t03_vs_t70() {
    let env = make_env_proofs();
    let t03_size = cert_term_size(&get_proof_term(&env, "NNVerify.interval_contains_refl"));
    let t70_size = cert_term_size(&get_proof_term(&env, "NNVerify.entailment_transitivity"));
    // T70 (transitivity) is more complex than T03 (identity/refl)
    assert!(
        t70_size > t03_size,
        "T70 ({}) should be larger than T03 ({})",
        t70_size,
        t03_size
    );
}

// -- Formal definition measurement -------------------------------------------

#[test]
fn test_proof_complexity_definitions_registered() {
    let mut env = Environment::new();
    env.init_nn_verify_proof_complexity()
        .expect("init_nn_verify_proof_complexity");

    // CertSize is the formal definition we need for the complexity question
    let cert_size_type = get_theorem_type(&env, "NNVerify.ProofComplexity.CertificateSize");
    let metrics = measure_cert_complexity(&cert_size_type);
    // CertificateSize : Nat -> Nat is a simple Pi type
    assert!(metrics.term_size > 0);
}

// -- Edge cases --------------------------------------------------------------

#[test]
fn test_cert_term_size_literal() {
    let e = Expr::nat_lit(42);
    assert_eq!(cert_term_size(&e), 1);
}

#[test]
fn test_cert_depth_literal() {
    let e = Expr::nat_lit(42);
    assert_eq!(cert_depth(&e), 1);
}

#[test]
fn test_measure_cert_complexity_single_const() {
    let e = Expr::const_(Name::from_string("Nat"), vec![]);
    let metrics = measure_cert_complexity(&e);
    assert_eq!(
        metrics,
        CertComplexityMetrics {
            term_size: 1,
            depth: 1,
            unique_constants: 1,
        }
    );
}
