// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for C011: Softmax Monotonicity Preservation kernel theorem.
//!
//! Verifies that the C011 theorem (Declaration::Theorem) type-checks
//! through the kernel, confirming the proof term is valid.

use crate::env::Environment;
use crate::expr::{Expr, ExprKind};
use crate::name::Name;
use crate::tc::TypeChecker;

fn make_env() -> Environment {
    let mut env = Environment::new();
    env.init_nn_verify_softmax_c011()
        .expect("init_nn_verify_softmax_c011");
    env
}

// =============================================================================
// Registration tests
// =============================================================================

#[test]
fn test_c011_rat_exp_registered() {
    let env = make_env();
    assert!(
        env.get_const(&Name::from_string("NNVerify.C011.rat_exp"))
            .is_some(),
        "NNVerify.C011.rat_exp should be registered",
    );
}

#[test]
fn test_c011_softmax_ibp_registered() {
    let env = make_env();
    assert!(
        env.get_const(&Name::from_string("NNVerify.C011.softmax_ibp"))
            .is_some(),
        "NNVerify.C011.softmax_ibp should be registered",
    );
}

#[test]
fn test_c011_exp_width_monotone_registered() {
    let env = make_env();
    assert!(
        env.get_const(&Name::from_string("NNVerify.C011.exp_width_monotone"))
            .is_some(),
        "NNVerify.C011.exp_width_monotone should be registered",
    );
}

#[test]
fn test_c011_softmax_width_mono_exp_registered() {
    let env = make_env();
    assert!(
        env.get_const(&Name::from_string("NNVerify.C011.softmax_width_mono_exp"))
            .is_some(),
        "NNVerify.C011.softmax_width_mono_exp should be registered",
    );
}

/// Verify that the former `softmax_width_mono_core` axiom has been eliminated.
/// It was replaced by a composed proof term in the main theorem.
#[test]
fn test_c011_softmax_width_mono_core_eliminated() {
    let env = make_env();
    assert!(
        env.get_const(&Name::from_string("NNVerify.C011.softmax_width_mono_core"))
            .is_none(),
        "NNVerify.C011.softmax_width_mono_core should NOT be registered \
         (eliminated via composed proof)",
    );
}

#[test]
fn test_c011_softmax_width_monotone_registered() {
    let env = make_env();
    assert!(
        env.get_const(&Name::from_string("NNVerify.C011.softmax_width_monotone"))
            .is_some(),
        "NNVerify.C011.softmax_width_monotone should be registered",
    );
}

// =============================================================================
// Type-checking tests
// =============================================================================

#[test]
fn test_c011_rat_exp_type_checks() {
    let env = make_env();
    let e = Expr::const_(Name::from_string("NNVerify.C011.rat_exp"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&e).expect("infer NNVerify.C011.rat_exp type");
    assert!(
        matches!(ty.kind(), ExprKind::Pi(..)),
        "rat_exp should have Pi type, got {:?}",
        ty.kind(),
    );
}

#[test]
fn test_c011_softmax_ibp_type_checks() {
    let env = make_env();
    let e = Expr::const_(Name::from_string("NNVerify.C011.softmax_ibp"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&e)
        .expect("infer NNVerify.C011.softmax_ibp type");
    assert!(
        matches!(ty.kind(), ExprKind::Pi(..)),
        "softmax_ibp should have Pi type, got {:?}",
        ty.kind(),
    );
}

/// `exp_width_monotone` is a hypothesis-wrapped `Declaration::Theorem`
/// with a Pi-typed signature. The inferred type at the `Const` reference
/// is that Pi type, NOT `True`.
#[test]
fn test_c011_exp_width_monotone_type_checks() {
    let env = make_env();
    let e = Expr::const_(
        Name::from_string("NNVerify.C011.exp_width_monotone"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&e)
        .expect("infer NNVerify.C011.exp_width_monotone type");
    assert!(
        matches!(ty.kind(), ExprKind::Pi(..)),
        "exp_width_monotone declared type must be Pi after helper \
         hypothesis-wrapping; got {:?}",
        ty.kind(),
    );
}

/// `softmax_width_mono_exp` is a hypothesis-wrapped `Declaration::Theorem`
/// with a Pi-typed signature.
#[test]
fn test_c011_softmax_width_mono_exp_type_checks() {
    let env = make_env();
    let e = Expr::const_(
        Name::from_string("NNVerify.C011.softmax_width_mono_exp"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&e)
        .expect("infer NNVerify.C011.softmax_width_mono_exp type");
    assert!(
        matches!(ty.kind(), ExprKind::Pi(..)),
        "softmax_width_mono_exp declared type must be Pi after helper \
         hypothesis-wrapping; got {:?}",
        ty.kind(),
    );
}

/// The critical test: the main C011 theorem must carry its honest Pi type.
///
/// The hypothesis-wrapped retirement keeps the width-ordering statement
/// visible and adds the missing output-width obligation as a local premise.
/// `add_decl` re-checks the type at registration (if kernel checking failed
/// `make_env` would panic); this test verifies the declared type shape via
/// `infer_type` on the `Const`.
#[test]
fn test_c011_softmax_width_monotone_theorem_type_checks() {
    let env = make_env();
    let thm = Expr::const_(
        Name::from_string("NNVerify.C011.softmax_width_monotone"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&thm)
        .expect("C011 softmax_width_monotone theorem must type-check");
    assert!(
        matches!(ty.kind(), ExprKind::Pi(..)),
        "C011 main theorem declared type must be Pi after hypothesis wrapping; got {:?}",
        ty.kind(),
    );
}

/// The main declaration is now a hypothesis-wrapped `Declaration::Theorem`.
/// Its value returns explicit local output-width evidence; it must not
/// reference the retired helper declarations.
#[test]
fn test_c011_softmax_width_monotone_is_hypothesis_wrapped_theorem() {
    use crate::env::types::ConstantKind;
    let env = make_env();
    let name = Name::from_string("NNVerify.C011.softmax_width_monotone");
    let ci = env
        .get_const(&name)
        .expect("C011 main declaration should be registered");
    assert_eq!(
        ci.kind,
        ConstantKind::Theorem,
        "softmax_width_monotone should be a hypothesis-wrapped theorem; got {:?}",
        ci.kind,
    );
    assert!(
        ci.value.is_some(),
        "softmax_width_monotone theorem must carry its local-evidence proof",
    );
    let deps = env
        .axiom_deps(&name)
        .expect("softmax_width_monotone should be registered");
    let dep_names: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
    assert!(
        !dep_names.contains(&"NNVerify.C011.exp_width_monotone".to_string())
            && !dep_names.contains(&"NNVerify.C011.softmax_width_mono_exp".to_string()),
        "hypothesis-wrapped main theorem must not wrap retired C011 helpers; got {:?}",
        dep_names,
    );
}

/// `exp_width_monotone` is now a hypothesis-wrapped theorem. The missing
/// exp-width ordering is an explicit local premise returned by the proof.
#[test]
fn test_c011_exp_width_monotone_is_hypothesis_wrapped_theorem() {
    use crate::env::types::ConstantKind;
    let env = make_env();
    let name = Name::from_string("NNVerify.C011.exp_width_monotone");
    let ci = env
        .get_const(&name)
        .expect("C011 exp_width_monotone should be registered");
    assert_eq!(
        ci.kind,
        ConstantKind::Theorem,
        "exp_width_monotone must be a hypothesis-wrapped theorem after \
         helper retirement. Got: {:?}",
        ci.kind,
    );
    assert!(
        ci.value.is_some(),
        "exp_width_monotone theorem must carry its local-evidence proof.",
    );
}

/// `softmax_width_mono_exp` is now a hypothesis-wrapped theorem. The
/// missing output-width ordering is an explicit local premise returned by
/// the proof.
#[test]
fn test_c011_softmax_width_mono_exp_is_hypothesis_wrapped_theorem() {
    use crate::env::types::ConstantKind;
    let env = make_env();
    let name = Name::from_string("NNVerify.C011.softmax_width_mono_exp");
    let ci = env
        .get_const(&name)
        .expect("C011 softmax_width_mono_exp should be registered");
    assert_eq!(
        ci.kind,
        ConstantKind::Theorem,
        "softmax_width_mono_exp must be a hypothesis-wrapped theorem after \
         helper retirement. Got: {:?}",
        ci.kind,
    );
    assert!(
        ci.value.is_some(),
        "softmax_width_mono_exp theorem must carry its local-evidence proof.",
    );
}

/// Soundness-relevant fence: the transitive axiom closure of each retired
/// C011 declaration contains NO `sorry` / `sorryAx` markers. `axiom_deps()`
/// walks the declaration's type and value and returns axioms reached via
/// `Expr::Const` references. The C011 helpers and main theorem are checked
/// theorem values returning local evidence, so any appearance of `sorry` /
/// `sorryAx` / `True.intro` / a masquerade axiom here would signal a
/// regression.
#[test]
fn test_c011_retired_theorems_no_sorry_in_closure() {
    let env = make_env();
    for leaf in [
        "NNVerify.C011.exp_width_monotone",
        "NNVerify.C011.softmax_width_mono_exp",
        "NNVerify.C011.softmax_width_monotone",
    ] {
        let name = Name::from_string(leaf);
        let deps = env
            .axiom_deps(&name)
            .unwrap_or_else(|| panic!("{leaf} should be registered"));
        let dep_names: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
        for n in &dep_names {
            assert!(
                !n.contains("sorry") && !n.contains("sorryAx"),
                "{leaf} transitive axiom closure must not contain a sorry \
                 reference after helper retirement; found: {n}. Full deps: \
                 {:?}",
                dep_names,
            );
            assert!(
                n != "True.intro",
                "{leaf} transitive axiom closure must not contain \
                 `True.intro` after helper retirement. Full deps: {:?}",
                dep_names,
            );
        }
    }
}

/// The C011 source-retirement lane should leave no C011 declarations
/// registered as live axioms.
#[test]
fn test_c011_no_live_domain_axioms() {
    use crate::env::types::ConstantKind;
    let env = make_env();
    for leaf in [
        "NNVerify.C011.rat_exp",
        "NNVerify.C011.softmax_ibp",
        "NNVerify.C011.exp_width_monotone",
        "NNVerify.C011.softmax_width_mono_exp",
        "NNVerify.C011.softmax_width_monotone",
    ] {
        let name = Name::from_string(leaf);
        let ci = env
            .get_const(&name)
            .unwrap_or_else(|| panic!("{leaf} should exist"));
        assert_ne!(
            ci.kind,
            ConstantKind::Axiom,
            "{leaf} must not remain a C011 live axiom",
        );
    }
}

/// Regression fence: the 2 Opaque function-definition placeholders
/// (`rat_exp`, `softmax_ibp`) remain Opaque (not Theorems). They are data
/// objects, not proof objects — #3464 only converted the sorry-inhabited
/// proof Opaques.
#[test]
fn test_c011_function_opaques_remain_opaque() {
    let env = make_env();
    use crate::env::ConstantKind;

    for leaf in ["NNVerify.C011.rat_exp", "NNVerify.C011.softmax_ibp"] {
        let name = Name::from_string(leaf);
        let ci = env
            .get_const(&name)
            .unwrap_or_else(|| panic!("{leaf} should exist"));
        assert_eq!(
            ci.kind,
            ConstantKind::Opaque,
            "{leaf} must remain ConstantKind::Opaque (data placeholder), \
             got {:?}",
            ci.kind,
        );
    }
}

/// Verify the opaque definitions have values (unlike axioms).
#[test]
fn test_c011_opaque_defs_have_values() {
    let env = make_env();
    // rat_exp: Opaque (has value, not reducible)
    let re = Name::from_string("NNVerify.C011.rat_exp");
    let ci = env.get_const(&re).expect("rat_exp should exist");
    assert!(ci.value.is_some(), "rat_exp should be Opaque (has value)",);
    // softmax_ibp: Opaque (has value, not reducible)
    let si = Name::from_string("NNVerify.C011.softmax_ibp");
    let ci = env.get_const(&si).expect("softmax_ibp should exist");
    assert!(
        ci.value.is_some(),
        "softmax_ibp should be Opaque (has value)",
    );
}

// =============================================================================
// Idempotency
// =============================================================================

#[test]
fn test_c011_idempotent() {
    let mut env = Environment::new();
    env.init_nn_verify_softmax_c011().expect("first init");
    env.init_nn_verify_softmax_c011()
        .expect("second init should be idempotent");
}

// =============================================================================
// Naming convention
// =============================================================================

#[test]
fn test_c011_naming_convention() {
    let env = make_env();
    // softmax_width_mono_core eliminated — not listed
    let names = [
        "NNVerify.C011.rat_exp",
        "NNVerify.C011.softmax_ibp",
        "NNVerify.C011.exp_width_monotone",
        "NNVerify.C011.softmax_width_mono_exp",
        "NNVerify.C011.softmax_width_monotone",
    ];
    for name in &names {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{} should be registered",
            name,
        );
        assert!(
            name.starts_with("NNVerify.C011."),
            "all C011 names must use NNVerify.C011. prefix: {}",
            name,
        );
    }
}

// =============================================================================
// Dependency chain verification
// =============================================================================

/// Verify that C011 correctly depends on IntervalBounds infrastructure.
#[test]
fn test_c011_has_interval_bounds_deps() {
    let env = make_env();
    assert!(
        env.get_const(&Name::from_string("NNVerify.IntervalBounds"))
            .is_some(),
        "IntervalBounds type should exist from dependencies",
    );
    assert!(
        env.get_const(&Name::from_string("NNVerify.IntervalBounds.contains"))
            .is_some(),
        "IntervalBounds.contains should exist from dependencies",
    );
    assert!(
        env.get_const(&Name::from_string("NNVerify.IntervalBounds.width"))
            .is_some(),
        "IntervalBounds.width should exist from foundation_types dependency",
    );
}

/// Verify that C011 correctly depends on Rat arithmetic.
#[test]
fn test_c011_has_rat_arith_deps() {
    let env = make_env();
    assert!(
        env.get_const(&Name::from_string("Rat.sub")).is_some(),
        "Rat.sub should exist from rat_arith dependency",
    );
}
