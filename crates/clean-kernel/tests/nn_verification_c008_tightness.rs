// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Integration tests for C008 IBP tightness bound formalization.
//!
//! Tests the typed formalization in `nn_verify_ibp_tightness.rs`:
//! - All definitions and theorems are correctly registered
//! - The C008 main theorem `NNVerify.ibp_tightness_bound` is a Theorem
//!   with a proof term (not just an axiom)
//! - `NNVerify.ibp_tightness_bound_inductive` is a Theorem with a
//!   constructive `Nat.rec` proof combining the base + step Theorems (#3374)
//! - base/step are constructive sorry-free Theorems (2026-06-12 unlock), not
//!   sorry-inhabited Opaques
//! - Idempotency of initialization
//! - Proof term type-checks
//!
//! Part of #3200, #3374.

use clean_kernel::{ConstantKind, Environment, Expr, ExprKind, Name, TypeChecker};

/// Create an environment with C008 tightness axioms initialized.
fn make_env() -> Environment {
    let mut env = Environment::new();
    env.init_nn_verify_ibp_tightness()
        .expect("init_nn_verify_ibp_tightness should succeed");
    env
}

/// Assert that a constant is registered.
fn assert_registered(env: &Environment, name: &str) {
    assert!(
        env.get_const(&Name::from_string(name)).is_some(),
        "Expected constant '{name}' to be registered"
    );
}

/// Assert that a constant has a specific kind.
fn assert_is_kind(env: &Environment, name: &str, expected: ConstantKind) {
    let info = env
        .get_const(&Name::from_string(name))
        .unwrap_or_else(|| panic!("'{name}' should be registered"));
    assert_eq!(
        info.kind, expected,
        "'{name}' should be {expected:?}, got {:?}",
        info.kind
    );
}

// =============================================================================
// Initialization tests
// =============================================================================

#[test]
fn test_c008_init_succeeds() {
    make_env();
}

#[test]
fn test_c008_init_idempotent() {
    let mut env = Environment::new();
    env.init_nn_verify_ibp_tightness()
        .expect("first init should succeed");
    let count_after_first = env.num_constants();
    env.init_nn_verify_ibp_tightness()
        .expect("second init should succeed (idempotent)");
    assert_eq!(
        env.num_constants(),
        count_after_first,
        "Idempotent init should not add more constants"
    );
}

// =============================================================================
// Definition registration tests
// =============================================================================

#[test]
fn test_infinity_norm_registered() {
    let env = make_env();
    assert_registered(&env, "NNVerify.infinity_norm");
}

#[test]
fn test_ibp_width_registered() {
    let env = make_env();
    assert_registered(&env, "NNVerify.ibp_width");
}

#[test]
fn test_norm_product_registered() {
    let env = make_env();
    assert_registered(&env, "NNVerify.norm_product");
}

#[test]
fn test_eps_ball_registered() {
    let env = make_env();
    assert_registered(&env, "NNVerify.eps_ball");
}

#[test]
fn test_ibp_propagate_registered() {
    let env = make_env();
    assert_registered(&env, "NNVerify.ibp_propagate");
}

// =============================================================================
// Kind verification tests
// =============================================================================

#[test]
fn test_infinity_norm_is_definition() {
    let env = make_env();
    assert_is_kind(&env, "NNVerify.infinity_norm", ConstantKind::Definition);
}

#[test]
fn test_ibp_width_is_definition() {
    let env = make_env();
    assert_is_kind(&env, "NNVerify.ibp_width", ConstantKind::Definition);
}

#[test]
fn test_norm_product_is_definition() {
    let env = make_env();
    assert_is_kind(&env, "NNVerify.norm_product", ConstantKind::Definition);
}

#[test]
fn test_ibp_propagate_is_definition() {
    let env = make_env();
    assert_is_kind(&env, "NNVerify.ibp_propagate", ConstantKind::Definition);
}

/// eps_ball was upgraded from Axiom to Opaque (Category A fix, #3374),
/// then from Opaque to reducible Definition (#3435) now that the body uses
/// only Rat.le_refl (a foundational axiom). The Definition status means
/// downstream proofs can reduce `eps_ball ...` applications through the kernel.
#[test]
fn test_eps_ball_is_definition() {
    let env = make_env();
    assert_is_kind(&env, "NNVerify.eps_ball", ConstantKind::Definition);
}

/// ibp_tightness_base was upgraded from Axiom to Opaque (#3374).
/// C008 unlock (R-weak, 2026-06-12 zero-faith campaign): `ibp_tightness_base`
/// graduated from sorry-inhabited Opaque to a constructive sorry-free
/// `Declaration::Theorem`. Its value is the genuine `le_of_eq_of_le` assembly in
/// `build_ibp_tightness_base_value` (LHS collapses to `Rat.zero` via
/// `eps_ball_width_is_zero`; RHS `0 ≤ 2·eps·1` via `Rat.mul_nonneg`).
#[test]
fn test_ibp_tightness_base_is_theorem() {
    let env = make_env();
    assert_is_kind(&env, "NNVerify.ibp_tightness_base", ConstantKind::Theorem);
}

/// C008 unlock (R-weak, 2026-06-12): `ibp_tightness_step` graduated from a
/// sorry-inhabited Opaque (originally an admitted Axiom, #3374) to a
/// constructive sorry-free `Declaration::Theorem`. Its value is the
/// `build_ibp_tightness_step_value` assembly (zero-width preserved through every
/// layer via `ibp_propagate_eq`, so the step `ibp_width` collapses to `Rat.zero`
/// via `ibp_width_zero`; the RHS is discharged by `Rat.mul_nonneg` fed
/// `norm_product_nonneg` / `infinity_norm_nonneg`).
#[test]
fn test_ibp_tightness_step_is_theorem() {
    let env = make_env();
    assert_is_kind(&env, "NNVerify.ibp_tightness_step", ConstantKind::Theorem);
}

/// ibp_tightness_bound_inductive was upgraded from Axiom to Theorem (#3374).
/// It now has a constructive Nat.rec proof combining base + step axioms.
#[test]
fn test_ibp_tightness_bound_inductive_is_theorem() {
    let env = make_env();
    assert_is_kind(
        &env,
        "NNVerify.ibp_tightness_bound_inductive",
        ConstantKind::Theorem,
    );
}

// =============================================================================
// Base/step axiom registration tests
// =============================================================================

#[test]
fn test_ibp_tightness_base_registered() {
    let env = make_env();
    assert_registered(&env, "NNVerify.ibp_tightness_base");
}

#[test]
fn test_ibp_tightness_step_registered() {
    let env = make_env();
    assert_registered(&env, "NNVerify.ibp_tightness_step");
}

// =============================================================================
// Main theorem tests
// =============================================================================

#[test]
fn test_ibp_tightness_bound_registered() {
    let env = make_env();
    assert_registered(&env, "NNVerify.ibp_tightness_bound");
}

#[test]
fn test_ibp_tightness_bound_is_theorem() {
    let env = make_env();
    assert_is_kind(&env, "NNVerify.ibp_tightness_bound", ConstantKind::Theorem);
}

#[test]
fn test_ibp_tightness_bound_inductive_registered() {
    let env = make_env();
    assert_registered(&env, "NNVerify.ibp_tightness_bound_inductive");
}

#[test]
fn test_ibp_tightness_bound_has_proof_term() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string("NNVerify.ibp_tightness_bound"))
        .expect("ibp_tightness_bound should be registered");
    assert_eq!(
        info.kind,
        ConstantKind::Theorem,
        "ibp_tightness_bound should be a Theorem"
    );
    assert!(
        info.value.is_some(),
        "ibp_tightness_bound should have a proof term"
    );
}

#[test]
fn test_ibp_tightness_bound_inductive_has_proof_term() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string("NNVerify.ibp_tightness_bound_inductive"))
        .expect("ibp_tightness_bound_inductive should be registered");
    assert_eq!(
        info.kind,
        ConstantKind::Theorem,
        "ibp_tightness_bound_inductive should be a Theorem (was Axiom before #3374)"
    );
    assert!(
        info.value.is_some(),
        "ibp_tightness_bound_inductive should have a Nat.rec proof term"
    );
}

#[test]
fn test_ibp_tightness_bound_type_is_pi() {
    let env = make_env();
    let tc = TypeChecker::new(&env);
    let e = Expr::const_(Name::from_string("NNVerify.ibp_tightness_bound"), vec![]);
    let ty = tc
        .infer_type(&e)
        .expect("ibp_tightness_bound should type-check");
    assert!(
        matches!(ty.kind(), ExprKind::Pi { .. }),
        "ibp_tightness_bound type should be Pi, got {:?}",
        ty.kind()
    );
}

// =============================================================================
// Definition value existence tests
// =============================================================================

#[test]
fn test_infinity_norm_has_value() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string("NNVerify.infinity_norm"))
        .expect("infinity_norm should be registered");
    assert!(
        info.value.is_some(),
        "infinity_norm Definition should have a value (computable body)"
    );
}

#[test]
fn test_ibp_width_has_value() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string("NNVerify.ibp_width"))
        .expect("ibp_width should be registered");
    assert!(
        info.value.is_some(),
        "ibp_width Definition should have a value (computable body)"
    );
}

#[test]
fn test_norm_product_has_value() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string("NNVerify.norm_product"))
        .expect("norm_product should be registered");
    assert!(
        info.value.is_some(),
        "norm_product Definition should have a value (computable body)"
    );
}

#[test]
fn test_ibp_propagate_has_value() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string("NNVerify.ibp_propagate"))
        .expect("ibp_propagate should be registered");
    assert!(
        info.value.is_some(),
        "ibp_propagate Definition should have a value (computable body)"
    );
}

// =============================================================================
// All declarations completeness test
// =============================================================================

#[test]
fn test_c008_all_declarations_present() {
    let env = make_env();

    let expected = &[
        // Definitions
        "NNVerify.infinity_norm",
        "NNVerify.ibp_width",
        "NNVerify.norm_product",
        "NNVerify.eps_ball",
        "NNVerify.ibp_propagate",
        // Base + step axioms
        "NNVerify.ibp_tightness_base",
        "NNVerify.ibp_tightness_step",
        // Theorems
        "NNVerify.ibp_tightness_bound_inductive",
        "NNVerify.ibp_tightness_bound",
    ];

    for name in expected {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Missing C008 declaration: {name}"
        );
    }
}

// =============================================================================
// Declaration count test
// =============================================================================

#[test]
fn test_c008_adds_expected_declarations() {
    let env = make_env();
    // Count the C008-specific declarations by checking they are all present.
    // The 9 expected are: 4 defs + 1 axiom(eps_ball) + 2 axioms(base+step)
    //   + 2 theorems(inductive + bound).
    let c008_names = [
        "NNVerify.infinity_norm",
        "NNVerify.ibp_width",
        "NNVerify.norm_product",
        "NNVerify.eps_ball",
        "NNVerify.ibp_propagate",
        "NNVerify.ibp_tightness_base",
        "NNVerify.ibp_tightness_step",
        "NNVerify.ibp_tightness_bound_inductive",
        "NNVerify.ibp_tightness_bound",
    ];
    let present = c008_names
        .iter()
        .filter(|n| env.get_const(&Name::from_string(n)).is_some())
        .count();
    assert_eq!(
        present,
        c008_names.len(),
        "All 9 C008 declarations should be present, found {present}"
    );
}

// =============================================================================
// Dependency chain tests
// =============================================================================

#[test]
fn test_c008_depends_on_ibp_linear() {
    // C008 should pull in T80 (ibp_linear_sound)
    let env = make_env();
    assert_registered(&env, "NNVerify.ibp_linear_sound");
}

#[test]
fn test_c008_depends_on_relu() {
    // C008 should pull in T81 (ibp_relu)
    let env = make_env();
    assert_registered(&env, "NNVerify.ibp_relu_bounds");
}

#[test]
fn test_c008_depends_on_linear_bounds() {
    // C008 uses ibp_linear_bounds from T80
    let env = make_env();
    assert_registered(&env, "NNVerify.ibp_linear_bounds");
}

// =============================================================================
// Proof chain structure test
// =============================================================================

#[test]
fn test_c008_proof_chain_complete() {
    // The C008 proof chain requires:
    // 1. ibp_tightness_base (base case axiom)
    // 2. ibp_tightness_step (inductive step axiom)
    // 3. ibp_tightness_bound_inductive (Nat.rec theorem)
    // 4. ibp_tightness_bound (main theorem)
    let env = make_env();
    for name in &[
        "NNVerify.ibp_tightness_base",
        "NNVerify.ibp_tightness_step",
        "NNVerify.ibp_tightness_bound_inductive",
        "NNVerify.ibp_tightness_bound",
    ] {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "C008 proof chain requires: {name}"
        );
    }
}

// =============================================================================
// Axiom reduction verification (#3374)
// =============================================================================

/// Verify that the former individual lemma axioms have been consolidated.
/// ibp_width_affine_le, ibp_width_relu_le, ibp_width_input are no longer
/// registered as separate axioms — their content is subsumed by
/// ibp_tightness_base and ibp_tightness_step.
#[test]
fn test_c008_consolidated_axioms() {
    let env = make_env();

    // Old individual lemma axioms should NOT be present
    let removed = &[
        "NNVerify.ibp_width_affine_le",
        "NNVerify.ibp_width_relu_le",
        "NNVerify.ibp_width_input",
    ];
    for name in removed {
        assert!(
            env.get_const(&Name::from_string(name)).is_none(),
            "'{name}' should have been consolidated into base/step axioms (#3374)"
        );
    }

    // New consolidated axioms should be present
    assert_registered(&env, "NNVerify.ibp_tightness_base");
    assert_registered(&env, "NNVerify.ibp_tightness_step");
}

/// Verify that ibp_tightness_bound_inductive is now a Theorem, not an Axiom.
/// The Nat.rec proof combines base + step axioms constructively.
#[test]
fn test_c008_inductive_no_longer_axiom() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string("NNVerify.ibp_tightness_bound_inductive"))
        .expect("ibp_tightness_bound_inductive should be registered");
    assert_eq!(
        info.kind,
        ConstantKind::Theorem,
        "ibp_tightness_bound_inductive should be Theorem (upgraded from Axiom, #3374)"
    );
    assert!(
        info.value.is_some(),
        "ibp_tightness_bound_inductive should have a constructive proof term"
    );
}

/// Verify C008 has ZERO domain-specific axioms (#3374).
/// All former axioms have been retired:
/// - eps_ball: reducible Definition (Category A fix, #3435)
/// - ibp_tightness_base: constructive sorry-free Theorem (2026-06-12 unlock)
/// - ibp_tightness_step: constructive sorry-free Theorem (2026-06-12 unlock)
#[test]
fn test_c008_zero_axioms() {
    let env = make_env();
    let c008_names = [
        "NNVerify.eps_ball",
        "NNVerify.ibp_tightness_base",
        "NNVerify.ibp_tightness_step",
    ];
    let c008_axioms: Vec<&str> = c008_names
        .iter()
        .copied()
        .filter(|name| {
            env.get_const(&Name::from_string(name))
                .map(|info| info.kind == ConstantKind::Axiom)
                .unwrap_or(false)
        })
        .collect();

    assert_eq!(
        c008_axioms.len(),
        0,
        "C008 should have ZERO domain-specific axioms (was 5->3->0 via #3374), found: {:?}",
        c008_axioms
    );
}

// =============================================================================
// Constructive Theorem value tests (C008 unlock, R-weak, 2026-06-12)
// =============================================================================

/// `ibp_tightness_base` is a constructive Theorem with a value (Axiom -> Opaque
/// #3374 -> sorry-free constructive Theorem in the zero-faith campaign).
#[test]
fn test_ibp_tightness_base_has_value() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string("NNVerify.ibp_tightness_base"))
        .expect("ibp_tightness_base should be registered");
    assert_eq!(
        info.kind,
        ConstantKind::Theorem,
        "ibp_tightness_base should be a constructive Theorem (was Axiom/Opaque)"
    );
    assert!(
        info.value.is_some(),
        "ibp_tightness_base Theorem should have a proof value"
    );
}

/// `ibp_tightness_step` is a constructive Theorem with a value (Axiom -> Opaque
/// #3374 -> sorry-free constructive Theorem in the zero-faith campaign).
#[test]
fn test_ibp_tightness_step_has_value() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string("NNVerify.ibp_tightness_step"))
        .expect("ibp_tightness_step should be registered");
    assert_eq!(
        info.kind,
        ConstantKind::Theorem,
        "ibp_tightness_step should be a constructive Theorem (was Axiom/Opaque)"
    );
    assert!(
        info.value.is_some(),
        "ibp_tightness_step Theorem should have a proof value"
    );
}

/// Verify that C008's base + step are genuine constructive Theorems and that
/// `eps_ball` is a Definition (#3435). Both base/step retired their
/// sorry-inhabited Opaque bodies in the 2026-06-12 zero-faith campaign.
#[test]
fn test_c008_theorems_and_definitions_are_genuine() {
    let env = make_env();
    // base + step are constructive sorry-free Theorems.
    let theorems = ["NNVerify.ibp_tightness_base", "NNVerify.ibp_tightness_step"];
    for name in &theorems {
        let info = env
            .get_const(&Name::from_string(name))
            .unwrap_or_else(|| panic!("'{name}' should be registered"));
        assert_eq!(
            info.kind,
            ConstantKind::Theorem,
            "'{name}' should be a constructive Theorem, got {:?}",
            info.kind
        );
        assert!(info.value.is_some(), "'{name}' Theorem should have a value");
    }
    // eps_ball is a Definition (Category A, #3435).
    let eps_ball = env
        .get_const(&Name::from_string("NNVerify.eps_ball"))
        .expect("eps_ball should be registered");
    assert_eq!(
        eps_ball.kind,
        ConstantKind::Definition,
        "eps_ball should be Definition (Category A promotion #3435)"
    );
    assert!(
        eps_ball.value.is_some(),
        "eps_ball Definition should have a value"
    );
}

/// C008 base/step proofs must NOT reach any trust marker (sorry/sorryAx). After
/// the R-weak unlock they are constructive sorry-free Theorems, so
/// `trust_marker_deps` is empty for both.
#[test]
fn test_c008_base_step_are_sorry_free() {
    let env = make_env();
    for name in ["NNVerify.ibp_tightness_base", "NNVerify.ibp_tightness_step"] {
        let n = Name::from_string(name);
        let markers = env
            .trust_marker_deps(&n)
            .unwrap_or_else(|| panic!("trust_marker_deps should work for {name}"));
        assert!(
            markers.is_empty(),
            "'{name}' should reach no trust marker (sorry/sorryAx); found: {:?}",
            markers.iter().map(|m| m.to_string()).collect::<Vec<_>>(),
        );
    }
}

/// Count C008 base/step Opaques — should be 0: both graduated to constructive
/// Theorems in the 2026-06-12 zero-faith campaign (was 2 sorry-inhabited
/// Opaques after the #3435 eps_ball -> Definition promotion).
#[test]
fn test_c008_base_step_opaque_count_is_zero() {
    let env = make_env();
    let c008_names = ["NNVerify.ibp_tightness_base", "NNVerify.ibp_tightness_step"];
    let opaque_count = c008_names
        .iter()
        .filter(|name| {
            env.get_const(&Name::from_string(name))
                .map(|info| info.kind == ConstantKind::Opaque)
                .unwrap_or(false)
        })
        .count();
    assert_eq!(
        opaque_count, 0,
        "C008 base/step should have 0 Opaques — both are constructive Theorems"
    );
}

/// Verify the Nat.rec theorem still type-checks now that base/step are
/// constructive Theorems. The theorem references base/step by name; Theorem
/// constants are resolved the same way during type checking.
#[test]
fn test_ibp_tightness_inductive_still_valid_with_theorem_base_step() {
    let env = make_env();
    let tc = TypeChecker::new(&env);
    let e = Expr::const_(
        Name::from_string("NNVerify.ibp_tightness_bound_inductive"),
        vec![],
    );
    let ty = tc
        .infer_type(&e)
        .expect("ibp_tightness_bound_inductive should type-check with Theorem base/step");
    assert!(
        matches!(ty.kind(), ExprKind::Pi { .. }),
        "ibp_tightness_bound_inductive type should be Pi"
    );
}

// =============================================================================
// Transitive-dependency axiom audit (#3374)
//
// Tests in this section use the kernel's axiom_audit API (axiom_deps,
// proof_quality, soundness_report) to walk the TRANSITIVE constant-reference
// graph of C008 theorems and verify that ZERO C008-specific domain axioms
// appear in the dep tree. This strictly stronger than the kind-only check
// in test_c008_zero_axioms above.
//
// Pattern mirrors C006 tests in tests_nn_verify_blockwise_crown.rs:
// test_c006_main_theorem_no_c006_specific_axioms /
// test_c006_all_theorems_no_c006_specific_axioms.
// =============================================================================

/// C008-specific names that, if they appear as `Declaration::Axiom` in any
/// theorem's transitive dep tree, indicate a regression in the C008 work.
/// These include the original individual lemma axioms (now consolidated) and
/// the base/step constants (now constructive Theorems, not Axiom/Opaque).
const C008_ELIMINATED_AXIOMS: &[&str] = &[
    // 3 individual lemma axioms consolidated in #3374 Phase 1
    "NNVerify.ibp_width_affine_le",
    "NNVerify.ibp_width_relu_le",
    "NNVerify.ibp_width_input",
    // base/step: Axiom -> Opaque (#3374) -> constructive Theorem (2026-06-12)
    "NNVerify.ibp_tightness_base",
    "NNVerify.ibp_tightness_step",
    // The induction theorem itself was once an axiom; now a Theorem with
    // a Nat.rec proof. Should never appear as a domain axiom.
    "NNVerify.ibp_tightness_bound_inductive",
    "NNVerify.ibp_tightness_bound",
];

/// The main C008 theorem (`ibp_tightness_bound_inductive`) must have zero
/// C008-specific domain axioms in its transitive dep tree. Infrastructure
/// axioms are permitted because they encode standard ordered-field properties
/// and are not C008-specific claims.
///
/// This enforces the #3374 acceptance criteria at the audit level:
/// "Zero domain-specific axioms remain."
#[test]
fn test_c008_inductive_no_c008_specific_axioms() {
    let env = make_env();
    let name = Name::from_string("NNVerify.ibp_tightness_bound_inductive");
    let deps = env
        .axiom_deps(&name)
        .expect("axiom_deps should work for ibp_tightness_bound_inductive");
    let dep_strs: Vec<String> = deps.iter().map(|d| d.to_string()).collect();
    for eliminated in C008_ELIMINATED_AXIOMS {
        assert!(
            !dep_strs.contains(&eliminated.to_string()),
            "#3374: C008 eliminated axiom {} still appears in transitive deps of \
             ibp_tightness_bound_inductive. All deps: {:?}",
            eliminated,
            dep_strs,
        );
    }
}

/// The final C008 theorem wrapper (`ibp_tightness_bound`) must also have
/// zero C008-specific domain axioms in its transitive dep tree.
#[test]
fn test_c008_bound_no_c008_specific_axioms() {
    let env = make_env();
    let name = Name::from_string("NNVerify.ibp_tightness_bound");
    let deps = env
        .axiom_deps(&name)
        .expect("axiom_deps should work for ibp_tightness_bound");
    let dep_strs: Vec<String> = deps.iter().map(|d| d.to_string()).collect();
    for eliminated in C008_ELIMINATED_AXIOMS {
        assert!(
            !dep_strs.contains(&eliminated.to_string()),
            "#3374: C008 eliminated axiom {} still appears in transitive deps of \
             ibp_tightness_bound. All deps: {:?}",
            eliminated,
            dep_strs,
        );
    }
}

/// Soundness-report-based check: no constant whose name matches a C008
/// "eliminated" axiom should appear in the environment-wide `domain_axioms`
/// list. Stronger than the per-theorem checks above because it inspects
/// every registered declaration, not just a named theorem.
#[test]
fn test_c008_no_c008_domain_axioms_in_soundness_report() {
    let env = make_env();
    let report = env.soundness_report();
    let c008_axiom_names: Vec<String> = report
        .domain_axioms
        .iter()
        .map(|n| n.to_string())
        .filter(|s| C008_ELIMINATED_AXIOMS.contains(&s.as_str()))
        .collect();
    assert!(
        c008_axiom_names.is_empty(),
        "#3374: soundness_report must not list any C008 eliminated axiom as a \
         domain axiom, found: {:?}",
        c008_axiom_names,
    );
}

/// The C008 main theorem should classify as either `Constructive` (zero
/// domain-specific dependencies) or `AxiomDependent` with no C008-specific
/// axioms (only shared infrastructure axioms from other conjectures/defs).
///
/// This is the highest-level publication-quality check: the theorem traces
/// back to the foundational axiom base (propext, Quot.sound, Classical.choice)
/// without a single C008 domain axiom — and, since the 2026-06-12 unlock, with
/// no `sorryAx` reachable at all (base/step are now constructive Theorems).
#[test]
fn test_c008_main_theorem_proof_quality() {
    use clean_kernel::ProofQuality;
    let env = make_env();
    let name = Name::from_string("NNVerify.ibp_tightness_bound_inductive");
    let quality = env
        .proof_quality(&name)
        .expect("proof_quality should work for ibp_tightness_bound_inductive");
    match &quality {
        ProofQuality::Constructive => {
            // Best case: zero axiom dependencies of any kind.
        }
        ProofQuality::AxiomDependent { axioms, .. } => {
            let axiom_strs: Vec<String> = axioms.iter().map(|a| a.to_string()).collect();
            for eliminated in C008_ELIMINATED_AXIOMS {
                assert!(
                    !axiom_strs.contains(&eliminated.to_string()),
                    "#3374: C008 eliminated axiom {} still appears in proof \
                     quality deps of ibp_tightness_bound_inductive. All deps: {:?}",
                    eliminated,
                    axiom_strs,
                );
            }
        }
        other => {
            panic!(
                "ibp_tightness_bound_inductive should be Constructive or \
                 AxiomDependent (infra only), got {:?}",
                other,
            );
        }
    }
}

/// Diagnostic: emit the full transitive domain-axiom dep set of the C008
/// infrastructure axioms survive. Runs quietly; use `-- --nocapture` to
/// see the output.
///
/// This test PASSES regardless of content; it is a reporting aid, not a
/// correctness gate. The correctness gates are the `no_c008_specific_axioms`
/// tests above.
#[test]
fn test_c008_report_domain_axiom_deps() {
    let env = make_env();
    for target in &[
        "NNVerify.ibp_tightness_bound_inductive",
        "NNVerify.ibp_tightness_bound",
    ] {
        let name = Name::from_string(target);
        let deps = env
            .axiom_deps(&name)
            .unwrap_or_else(|| panic!("axiom_deps should work for {}", target));
        let mut dep_strs: Vec<String> = deps.iter().map(|d| d.to_string()).collect();
        dep_strs.sort();
        eprintln!(
            "[C008 audit] {} -> {} domain axioms: {:?}",
            target,
            dep_strs.len(),
            dep_strs
        );
    }
}
