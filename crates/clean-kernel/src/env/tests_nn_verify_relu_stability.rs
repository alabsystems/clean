// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for C012: ReLU activation pattern stability declarations.

use crate::env::types::ConstantKind;
use crate::env::Environment;
use crate::expr::{Expr, ExprKind};
use crate::name::Name;
use crate::tc::TypeChecker;

fn make_env() -> Environment {
    let mut env = Environment::new();
    env.init_nn_verify_relu_stability()
        .expect("init_nn_verify_relu_stability");
    env
}

// =========================================================================
// Definition registration tests
// =========================================================================

#[test]
fn test_network_type_registered() {
    let env = make_env();
    assert!(
        env.get_const(&Name::from_string("NNVerify.C012.Network"))
            .is_some(),
        "NNVerify.C012.Network should be registered",
    );
}

#[test]
fn test_pre_activation_registered() {
    let env = make_env();
    assert!(
        env.get_const(&Name::from_string("NNVerify.C012.pre_activation"))
            .is_some(),
        "NNVerify.C012.pre_activation should be registered",
    );
}

#[test]
fn test_activation_pattern_registered() {
    let env = make_env();
    assert!(
        env.get_const(&Name::from_string("NNVerify.C012.activation_pattern"))
            .is_some(),
        "NNVerify.C012.activation_pattern should be registered",
    );
}

#[test]
fn test_stability_radius_registered() {
    let env = make_env();
    assert!(
        env.get_const(&Name::from_string("NNVerify.C012.stability_radius"))
            .is_some(),
        "NNVerify.C012.stability_radius should be registered",
    );
}

#[test]
fn test_perturbation_ball_registered() {
    let env = make_env();
    assert!(
        env.get_const(&Name::from_string("NNVerify.C012.perturbation_ball"))
            .is_some(),
        "NNVerify.C012.perturbation_ball should be registered",
    );
}

#[test]
fn test_crown_relaxation_gap_registered() {
    let env = make_env();
    assert!(
        env.get_const(&Name::from_string("NNVerify.C012.crown_relaxation_gap"))
            .is_some(),
        "NNVerify.C012.crown_relaxation_gap should be registered",
    );
}

#[test]
fn test_pattern_stable_registered() {
    let env = make_env();
    assert!(
        env.get_const(&Name::from_string("NNVerify.C012.pattern_stable"))
            .is_some(),
        "NNVerify.C012.pattern_stable should be registered",
    );
}

#[test]
fn test_single_lp_form_registered() {
    let env = make_env();
    assert!(
        env.get_const(&Name::from_string("NNVerify.C012.single_lp_form"))
            .is_some(),
        "NNVerify.C012.single_lp_form should be registered",
    );
}

// =========================================================================
// Theorem registration tests
// =========================================================================

#[test]
fn test_pattern_stable_criterion_registered() {
    let env = make_env();
    // Core axiom
    assert!(
        env.get_const(&Name::from_string(
            "NNVerify.C012.pattern_stable_criterion_core"
        ))
        .is_some(),
        "C012a core axiom should be registered",
    );
    // Theorem
    assert!(
        env.get_const(&Name::from_string("NNVerify.C012.pattern_stable_criterion"))
            .is_some(),
        "C012a: pattern_stable_criterion theorem should be registered",
    );
}

#[test]
fn test_crown_exact_under_stable_registered() {
    let env = make_env();
    // Core axiom
    assert!(
        env.get_const(&Name::from_string(
            "NNVerify.C012.crown_exact_under_stable_core"
        ))
        .is_some(),
        "C012b core axiom should be registered",
    );
    // Theorem
    assert!(
        env.get_const(&Name::from_string("NNVerify.C012.crown_exact_under_stable"))
            .is_some(),
        "C012b: crown_exact_under_stable theorem should be registered",
    );
}

#[test]
fn test_lp_reduction_registered() {
    let env = make_env();
    // `lp_reduction` is now a hypothesis-wrapped theorem. The backing
    // `lp_reduction_core` Opaque remains removed.
    assert!(
        env.get_const(&Name::from_string("NNVerify.C012.lp_reduction"))
            .is_some(),
        "C012c: lp_reduction theorem should be registered",
    );
    assert!(
        env.get_const(&Name::from_string("NNVerify.C012.lp_reduction_core"))
            .is_none(),
        "C012c: lp_reduction_core was removed in #3579 (Branch A demasquerade)",
    );
}

// =========================================================================
// Type-checking tests
// =========================================================================

#[test]
fn test_network_type_checks() {
    let env = make_env();
    let net = Expr::const_(Name::from_string("NNVerify.C012.Network"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&net).expect("infer Network type");
    // Network : Type, so its type is Sort(1)
    assert!(
        matches!(ty.kind(), ExprKind::Sort(..)),
        "Network should be a Type (Sort level)",
    );
}

#[test]
fn test_pre_activation_type_checks() {
    let env = make_env();
    let e = Expr::const_(Name::from_string("NNVerify.C012.pre_activation"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&e).expect("infer pre_activation type");
    assert!(
        matches!(ty.kind(), ExprKind::Pi(..)),
        "pre_activation should have Pi type",
    );
}

#[test]
fn test_stability_radius_type_checks() {
    let env = make_env();
    let e = Expr::const_(Name::from_string("NNVerify.C012.stability_radius"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&e).expect("infer stability_radius type");
    assert!(
        matches!(ty.kind(), ExprKind::Pi(..)),
        "stability_radius should have Pi type",
    );
}

#[test]
fn test_pattern_stable_criterion_type_checks() {
    let env = make_env();
    let thm = Expr::const_(
        Name::from_string("NNVerify.C012.pattern_stable_criterion"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&thm)
        .expect("infer pattern_stable_criterion type");
    assert!(
        matches!(ty.kind(), ExprKind::Pi(..)),
        "C012a should have Pi type (universally quantified)",
    );
}

#[test]
fn test_crown_exact_under_stable_type_checks() {
    let env = make_env();
    let thm = Expr::const_(
        Name::from_string("NNVerify.C012.crown_exact_under_stable"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&thm)
        .expect("infer crown_exact_under_stable type");
    assert!(
        matches!(ty.kind(), ExprKind::Pi(..)),
        "C012b should have Pi type (universally quantified)",
    );
}

#[test]
fn test_lp_reduction_type_checks() {
    let env = make_env();
    let thm = Expr::const_(Name::from_string("NNVerify.C012.lp_reduction"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&thm).expect("infer lp_reduction type");
    assert!(
        matches!(ty.kind(), ExprKind::Pi(..)),
        "C012c should have Pi type (universally quantified)",
    );
}

// =========================================================================
// Idempotence and naming convention tests
// =========================================================================

#[test]
fn test_idempotent() {
    let mut env = Environment::new();
    env.init_nn_verify_relu_stability().expect("first init");
    env.init_nn_verify_relu_stability()
        .expect("second init should be idempotent");
}

#[test]
fn test_naming_convention() {
    let env = make_env();
    // Post-#3579: `lp_reduction_core` was removed in the Branch A
    // demasquerade. The surviving C012 names are the 13 below.
    let names = [
        "NNVerify.C012.Network",
        "NNVerify.C012.pre_activation",
        "NNVerify.C012.activation_pattern",
        "NNVerify.C012.stability_radius",
        "NNVerify.C012.perturbation_ball",
        "NNVerify.C012.crown_relaxation_gap",
        "NNVerify.C012.pattern_stable",
        "NNVerify.C012.single_lp_form",
        "NNVerify.C012.pattern_stable_criterion_core",
        "NNVerify.C012.pattern_stable_criterion",
        "NNVerify.C012.crown_exact_under_stable_core",
        "NNVerify.C012.crown_exact_under_stable",
        "NNVerify.C012.lp_reduction",
    ];
    for name in &names {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{} should be registered",
            name,
        );
        assert!(
            name.starts_with("NNVerify."),
            "all names must start with NNVerify. prefix: {}",
            name,
        );
    }
}

/// Verify the C012 declaration layout: 8 defs, 2 core Opaques
/// (`pattern_stable_criterion_core`, `crown_exact_under_stable_core`),
/// 2 Theorem wrappers (`pattern_stable_criterion`,
/// `crown_exact_under_stable`), and 1 hypothesis-wrapped Theorem
/// (`lp_reduction`). Total 13.
#[test]
fn test_declaration_count() {
    let env = make_env();
    let all_names = [
        "NNVerify.C012.Network",
        "NNVerify.C012.pre_activation",
        "NNVerify.C012.activation_pattern",
        "NNVerify.C012.stability_radius",
        "NNVerify.C012.perturbation_ball",
        "NNVerify.C012.crown_relaxation_gap",
        "NNVerify.C012.pattern_stable",
        "NNVerify.C012.single_lp_form",
        "NNVerify.C012.pattern_stable_criterion_core",
        "NNVerify.C012.pattern_stable_criterion",
        "NNVerify.C012.crown_exact_under_stable_core",
        "NNVerify.C012.crown_exact_under_stable",
        "NNVerify.C012.lp_reduction",
    ];
    let count = all_names
        .iter()
        .filter(|n| env.get_const(&Name::from_string(n)).is_some())
        .count();
    assert_eq!(
        count, 13,
        "expected 13 C012 declarations post-#3579 (lp_reduction_core removed)",
    );
    assert!(
        env.get_const(&Name::from_string("NNVerify.C012.lp_reduction_core"))
            .is_none(),
        "lp_reduction_core must stay unregistered after #3579",
    );
}

// =============================================================================
// Helpers for #3579 demasquerade-guard tests (mirror #3568 C007 shape).
// =============================================================================

/// Returns true iff the innermost body (after stripping lambdas) is the
/// canonical synthetic sorry term.
fn innermost_body(env_value: &Expr) -> &Expr {
    let mut cursor = env_value;
    while let ExprKind::Lam(_, _, body) = cursor.kind() {
        cursor = body;
    }
    cursor
}

fn innermost_body_is_synthetic_sorry(env_value: &Expr) -> bool {
    innermost_body(env_value).is_synthetic_sorry()
}

fn count_outer_pis(ty: &Expr) -> usize {
    let mut cursor = ty;
    let mut count = 0;
    while let ExprKind::Pi(_, _, body) = cursor.kind() {
        count += 1;
        cursor = body;
    }
    count
}

// =============================================================================
// C012 lp_reduction / single_lp_form guards
// =============================================================================

/// Guards the C012 axiom retirement: `NNVerify.C012.lp_reduction` is a
/// `Declaration::Theorem` whose strengthened type includes an explicit
/// local `single_lp_form` premise. The proof returns that local premise;
/// it does not use `True.intro`, `Eq.refl`, or a global C012 axiom.
#[test]
fn test_c012_lp_reduction_is_hypothesis_wrapped_theorem() {
    let env = make_env();
    let ci = env
        .get_const(&Name::from_string("NNVerify.C012.lp_reduction"))
        .expect("lp_reduction should be registered");
    assert_eq!(
        ci.kind,
        ConstantKind::Theorem,
        "lp_reduction must be a theorem after hypothesis-wrapped axiom \
         retirement, got {:?}",
        ci.kind,
    );
    let value = ci
        .value
        .as_ref()
        .expect("lp_reduction theorem should carry a proof value");
    assert!(
        matches!(innermost_body(value).kind(), ExprKind::BVar(0)),
        "lp_reduction proof should return the innermost local single-LP \
         hypothesis, got {:?}",
        innermost_body(value).kind(),
    );
}

/// Guards the #3579 co-demotion: `NNVerify.C012.single_lp_form` is a
/// `Declaration::Opaque`, NOT a reducible `Declaration::Definition`.
///
/// This is the load-bearing half of Branch A. If `single_lp_form` stays
/// reducible, any future `lp_reduction : ... -> single_lp_form n net x0
/// eps` proof could once again be discharged by `True.intro` via delta-
/// reduction of the argument-discarding carrier. Opaques are not delta-
/// unfolded during `def_eq`, so this test pins the kernel property that
/// keeps the demasquerade intact. Replaces the #3465
/// `test_c012_single_lp_form_is_reducible_definition` test (which pinned
/// the opposite property).
#[test]
fn test_c012_single_lp_form_is_opaque_not_reducible_definition() {
    let env = make_env();
    let ci = env
        .get_const(&Name::from_string("NNVerify.C012.single_lp_form"))
        .expect("single_lp_form should be registered");
    assert_eq!(
        ci.kind,
        ConstantKind::Opaque,
        "#3579 Branch A: single_lp_form must be Opaque (closes the \
         delta-reduction path single_lp_form n net x0 eps -> True), got \
         {:?}",
        ci.kind,
    );
    // The stored body is unchanged from #3465 (`fun _ _ _ _ => True`) —
    // only the declaration kind flipped. Confirm it still carries a
    // value (Opaques require a body; unlike Axioms).
    assert!(
        ci.value.is_some(),
        "#3579 single_lp_form Opaque should still carry its placeholder \
         `fun _ _ _ _ => True` body",
    );
}

/// `lp_reduction` carries the strengthened Pi type:
/// `n -> net -> x0 -> eps -> pattern_stable ... -> single_lp_form ... ->
/// single_lp_form ...`.
#[test]
fn test_c012_lp_reduction_strengthened_type_checks() {
    let env = make_env();
    let thm = Expr::const_(Name::from_string("NNVerify.C012.lp_reduction"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&thm)
        .expect("lp_reduction theorem should infer a type");
    assert!(
        matches!(ty.kind(), ExprKind::Pi(..)),
        "lp_reduction type should be Pi (universally quantified), got {:?}",
        ty.kind(),
    );
    assert_eq!(
        count_outer_pis(&ty),
        6,
        "lp_reduction should have 6 outer binders after adding the local \
         single-LP hypothesis",
    );
}

/// Site count: the 2 remaining `sorry_inhabit_pi` sites in
/// C012 are `pattern_stable_criterion_core` and
/// `crown_exact_under_stable_core`. `lp_reduction_core` is gone (the
/// backing Opaque was removed). `lp_reduction` is a theorem whose proof
/// returns a local hypothesis, so it is not sorry-inhabited.
#[test]
fn test_c012_sorry_inhabit_pi_site_count_after_lp_reduction_retirement() {
    let env = make_env();

    // `lp_reduction_core` must be gone.
    assert!(
        env.get_const(&Name::from_string("NNVerify.C012.lp_reduction_core"))
            .is_none(),
        "#3579 removed `lp_reduction_core`; re-registering it would \
         reopen the masquerade path",
    );

    // `lp_reduction` is a hypothesis-wrapped theorem; its proof is not sorry.
    let lp_reduction_ci = env
        .get_const(&Name::from_string("NNVerify.C012.lp_reduction"))
        .expect("lp_reduction should be registered");
    let lp_reduction_value = lp_reduction_ci
        .value
        .as_ref()
        .expect("lp_reduction theorem should carry a proof value");
    assert!(
        !innermost_body_is_synthetic_sorry(lp_reduction_value),
        "lp_reduction theorem proof should not be sorry-inhabited",
    );

    let pattern_stable_criterion_core = env
        .get_const(&Name::from_string(
            "NNVerify.C012.pattern_stable_criterion_core",
        ))
        .and_then(|ci| ci.value.clone())
        .expect("pattern_stable_criterion_core should have a value");
    assert!(
        innermost_body_is_synthetic_sorry(&pattern_stable_criterion_core),
        "pattern_stable_criterion_core should still be sorry-inhabited \
         (not remediated by #3579; only the lp_reduction masquerade was \
         addressed)",
    );

    let crown_exact_under_stable_core = env
        .get_const(&Name::from_string(
            "NNVerify.C012.crown_exact_under_stable_core",
        ))
        .and_then(|ci| ci.value.clone())
        .expect("crown_exact_under_stable_core should have a value");
    assert!(
        innermost_body_is_synthetic_sorry(&crown_exact_under_stable_core),
        "crown_exact_under_stable_core should still be sorry-inhabited \
         (not remediated by #3579)",
    );
}
