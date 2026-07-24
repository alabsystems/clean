// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for C006: Block-wise CROWN = monolithic for transformers.
//!
//! Validates that all C006 declarations (axioms + theorem) are registered
//! correctly, type-check, and follow the C008 helper-axiom pattern.

use crate::env::types::ConstantKind;
use crate::env::Environment;
use crate::expr::{Expr, ExprKind};
use crate::name::Name;
use crate::tc::TypeChecker;

fn make_env() -> Environment {
    let mut env = Environment::new();
    env.init_nn_verify_blockwise_crown()
        .expect("init_nn_verify_blockwise_crown");
    env
}

// =============================================================================
// Registration tests
// =============================================================================

#[test]
fn test_ibp_transfer_registered() {
    let env = make_env();
    assert!(
        env.get_const(&Name::from_string("NNVerify.Block.ibp_transfer"))
            .is_some(),
        "NNVerify.Block.ibp_transfer should be registered",
    );
}

#[test]
fn test_block_compose_registered() {
    let env = make_env();
    assert!(
        env.get_const(&Name::from_string("NNVerify.Block.compose"))
            .is_some(),
        "NNVerify.Block.compose should be registered",
    );
}

#[test]
fn test_monolithic_crown_registered() {
    let env = make_env();
    assert!(
        env.get_const(&Name::from_string("NNVerify.Block.monolithic_crown"))
            .is_some(),
        "NNVerify.Block.monolithic_crown should be registered",
    );
}

#[test]
fn test_blockwise_base_registered() {
    let env = make_env();
    assert!(
        env.get_const(&Name::from_string("NNVerify.C006.blockwise_base"))
            .is_some(),
        "NNVerify.C006.blockwise_base should be registered",
    );
}

#[test]
fn test_blockwise_step_registered() {
    let env = make_env();
    assert!(
        env.get_const(&Name::from_string("NNVerify.C006.blockwise_step"))
            .is_some(),
        "NNVerify.C006.blockwise_step should be registered",
    );
}

#[test]
fn test_blockwise_nat_induction_registered() {
    let env = make_env();
    assert!(
        env.get_const(&Name::from_string("NNVerify.C006.blockwise_nat_induction"))
            .is_some(),
        "NNVerify.C006.blockwise_nat_induction should be registered",
    );
}

#[test]
fn test_blockwise_equals_monolithic_registered() {
    let env = make_env();
    assert!(
        env.get_const(&Name::from_string(
            "NNVerify.C006.blockwise_equals_monolithic"
        ))
        .is_some(),
        "NNVerify.C006.blockwise_equals_monolithic should be registered",
    );
}

#[test]
fn test_follows_from_c004_registered() {
    let env = make_env();
    assert!(
        env.get_const(&Name::from_string("NNVerify.C006.follows_from_c004"))
            .is_some(),
        "NNVerify.C006.follows_from_c004 should be registered",
    );
}

// =============================================================================
// Idempotency
// =============================================================================

#[test]
fn test_idempotent() {
    let mut env = Environment::new();
    env.init_nn_verify_blockwise_crown().expect("first init");
    env.init_nn_verify_blockwise_crown()
        .expect("second init should be idempotent");
}

// =============================================================================
// Naming convention
// =============================================================================

#[test]
fn test_nn_verify_naming_convention() {
    let env = make_env();
    let nn_names = [
        "NNVerify.Block.ibp_transfer",
        "NNVerify.Block.compose",
        "NNVerify.Block.monolithic_crown",
        "NNVerify.C006.blockwise_base",
        "NNVerify.C006.blockwise_step",
        "NNVerify.C006.blockwise_nat_induction",
        "NNVerify.C006.blockwise_equals_monolithic",
        "NNVerify.C006.follows_from_c004",
    ];
    for name in &nn_names {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{} should be registered with NNVerify.* prefix",
            name,
        );
        assert!(
            name.starts_with("NNVerify."),
            "all names must start with NNVerify. prefix: {}",
            name,
        );
    }
}

// =============================================================================
// Type-checking tests
// =============================================================================

#[test]
fn test_ibp_transfer_type_checks() {
    let env = make_env();
    let transfer = Expr::const_(Name::from_string("NNVerify.Block.ibp_transfer"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&transfer)
        .expect("infer Block.ibp_transfer type");
    assert!(
        matches!(ty.kind(), ExprKind::Pi(..)),
        "Block.ibp_transfer should have Pi type",
    );
}

#[test]
fn test_block_compose_type_checks() {
    let env = make_env();
    let compose = Expr::const_(Name::from_string("NNVerify.Block.compose"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&compose).expect("infer Block.compose type");
    assert!(
        matches!(ty.kind(), ExprKind::Pi(..)),
        "Block.compose should have Pi type",
    );
}

#[test]
fn test_monolithic_crown_type_checks() {
    let env = make_env();
    let mono = Expr::const_(Name::from_string("NNVerify.Block.monolithic_crown"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&mono)
        .expect("infer Block.monolithic_crown type");
    assert!(
        matches!(ty.kind(), ExprKind::Pi(..)),
        "Block.monolithic_crown should have Pi type",
    );
}

#[test]
fn test_blockwise_base_type_checks() {
    let env = make_env();
    let base = Expr::const_(Name::from_string("NNVerify.C006.blockwise_base"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&base)
        .expect("infer C006.blockwise_base type");
    assert!(
        matches!(ty.kind(), ExprKind::Pi(..)),
        "C006.blockwise_base should have Pi type",
    );
}

#[test]
fn test_blockwise_step_type_checks() {
    let env = make_env();
    let step = Expr::const_(Name::from_string("NNVerify.C006.blockwise_step"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&step)
        .expect("infer C006.blockwise_step type");
    assert!(
        matches!(ty.kind(), ExprKind::Pi(..)),
        "C006.blockwise_step should have Pi type (universally quantified)",
    );
}

#[test]
fn test_blockwise_equals_monolithic_type_checks() {
    let env = make_env();
    let thm = Expr::const_(
        Name::from_string("NNVerify.C006.blockwise_equals_monolithic"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&thm)
        .expect("infer C006.blockwise_equals_monolithic type");
    assert!(
        matches!(ty.kind(), ExprKind::Pi(..)),
        "C006.blockwise_equals_monolithic should have Pi type (universally quantified)",
    );
}

#[test]
fn test_follows_from_c004_type_checks() {
    let env = make_env();
    let thm = Expr::const_(Name::from_string("NNVerify.C006.follows_from_c004"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&thm)
        .expect("infer C006.follows_from_c004 type");
    assert!(
        matches!(ty.kind(), ExprKind::Pi(..)),
        "C006.follows_from_c004 should have Pi type",
    );
}

// =============================================================================
// C004 dependency
// =============================================================================

#[test]
fn test_c004_dependency_loaded() {
    // C006 depends on C004 — verify C004 declarations are present
    let env = make_env();
    assert!(
        env.get_const(&Name::from_string("NNVerify.C004.crown_equals_ibp"))
            .is_some(),
        "C004.crown_equals_ibp should be loaded as a C006 dependency",
    );
}

// =============================================================================
// Proof structure validation
// =============================================================================

// 2026-04-19 MASQUERADE DEMOTION (#3489-#3493): the original C006 theorem
// cluster was demoted to `Declaration::Axiom` because its Eq.refl/Nat.rec
// proof closed over placeholder carriers. The headline, base, and
// nat_induction names are now hypothesis-wrapped theorems over the Phase-1
// indexed carriers; step is now a hypothesis-wrapped theorem over the same
// pointwise mono-step evidence used by the headline theorem.
#[test]
fn test_main_result_is_hypothesis_wrapped_theorem() {
    let env = make_env();
    let ci = env
        .get_const(&Name::from_string(
            "NNVerify.C006.blockwise_equals_monolithic",
        ))
        .expect("theorem should exist");
    assert_eq!(
        ci.kind,
        ConstantKind::Theorem,
        "main result is a hypothesis-wrapped Declaration::Theorem after Phase 2",
    );
}

#[test]
fn test_main_result_has_proof_value() {
    let env = make_env();
    let ci = env
        .get_const(&Name::from_string(
            "NNVerify.C006.blockwise_equals_monolithic",
        ))
        .expect("theorem should exist");
    assert!(
        ci.value.is_some(),
        "hypothesis-wrapped theorem must carry the Nat.rec proof value",
    );
}

#[test]
fn test_blockwise_base_is_hypothesis_wrapped_theorem() {
    let env = make_env();
    let ci = env
        .get_const(&Name::from_string("NNVerify.C006.blockwise_base"))
        .expect("blockwise_base should be registered");
    assert_eq!(
        ci.kind,
        ConstantKind::Theorem,
        "blockwise_base is now a hypothesis-wrapped Declaration::Theorem"
    );
    assert!(
        ci.value.is_some(),
        "blockwise_base theorem must carry its And.intro proof value"
    );
}

#[test]
fn test_blockwise_step_is_hypothesis_wrapped_theorem() {
    let env = make_env();
    let ci = env
        .get_const(&Name::from_string("NNVerify.C006.blockwise_step"))
        .expect("blockwise_step should be registered");
    assert_eq!(
        ci.kind,
        ConstantKind::Theorem,
        "blockwise_step is now a hypothesis-wrapped Declaration::Theorem",
    );
    assert!(
        ci.value.is_some(),
        "blockwise_step theorem must carry a proof value",
    );
}

#[test]
fn test_blockwise_nat_induction_is_hypothesis_wrapped_theorem() {
    let env = make_env();
    let ci = env
        .get_const(&Name::from_string("NNVerify.C006.blockwise_nat_induction"))
        .expect("blockwise_nat_induction should be registered");
    assert_eq!(
        ci.kind,
        ConstantKind::Theorem,
        "blockwise_nat_induction is now a hypothesis-wrapped Declaration::Theorem",
    );
    assert!(
        ci.value.is_some(),
        "blockwise_nat_induction theorem must carry a proof value",
    );
}

#[test]
fn test_base_and_step_are_distinct() {
    // Base theorem and step axiom must have different types (base has no k parameter)
    let env = make_env();
    let base_ci = env
        .get_const(&Name::from_string("NNVerify.C006.blockwise_base"))
        .expect("base axiom should exist");
    let step_ci = env
        .get_const(&Name::from_string("NNVerify.C006.blockwise_step"))
        .expect("step axiom should exist");
    assert_ne!(
        format!("{:?}", base_ci.type_),
        format!("{:?}", step_ci.type_),
        "base and step axioms must have distinct types",
    );
}

#[test]
fn test_helper_and_main_types_diverge_after_hypothesis_promotion() {
    // Phase 2 adds the missing pointwise `crown_block = mono_step`
    // hypothesis to the headline theorem. The nat_induction theorem now takes
    // explicit all-k induction evidence, so the two types must now differ.
    let env = make_env();
    let helper_ci = env
        .get_const(&Name::from_string("NNVerify.C006.blockwise_nat_induction"))
        .expect("helper theorem should exist");
    let thm_ci = env
        .get_const(&Name::from_string(
            "NNVerify.C006.blockwise_equals_monolithic",
        ))
        .expect("main axiom should exist");
    assert_ne!(
        format!("{:?}", helper_ci.type_),
        format!("{:?}", thm_ci.type_),
        "hypothesis-wrapped main theorem must not share the old axiom type",
    );
}

#[test]
fn test_old_inductive_name_not_registered() {
    // The old monolithic `_inductive` name should not exist in the new design
    let env = make_env();
    assert!(
        env.get_const(&Name::from_string(
            "NNVerify.C006.blockwise_equals_monolithic_inductive"
        ))
        .is_none(),
        "old _inductive name should not be registered in new decomposed design",
    );
}

// =============================================================================
// Constructive proof validation (#3309)
// =============================================================================

#[test]
fn test_nat_induction_is_theorem_after_hypothesis_wrapping() {
    // The old hypothesis-free Nat.rec proof was not restored. The theorem now
    // requires explicit local induction evidence and returns its instance at k.
    let env = make_env();
    let ci = env
        .get_const(&Name::from_string("NNVerify.C006.blockwise_nat_induction"))
        .expect("induction combinator should exist");
    assert_eq!(
        ci.kind,
        ConstantKind::Theorem,
        "blockwise_nat_induction is now a hypothesis-wrapped Declaration::Theorem"
    );
}

#[test]
fn test_nat_induction_has_proof_value() {
    let env = make_env();
    let ci = env
        .get_const(&Name::from_string("NNVerify.C006.blockwise_nat_induction"))
        .expect("induction combinator should exist");
    assert!(
        ci.value.is_some(),
        "blockwise_nat_induction theorem carries the local-evidence proof value"
    );
}

#[test]
fn test_registration_shape_after_demotion() {
    // 2026-04-19 masquerade demotion (#3489-#3493) + 2026-04-20 carrier
    // cleanup (#3500 Branch A) + 2026-04-20 Phase-1 faithful carriers
    // (#3638):
    //   Opaques: ibp_transfer, follows_from_c004,
    //            per_block_crown_matches_mono (Phase-1 True-valued Prop).
    //   Definitions (reducible): compose, monolithic_crown (new indexed
    //            Nat.rec bodies — distinct step cases structurally block
    //            the δ-collapse alias path), mono_step (Phase-1 helper).
    //   Axiom: blockwise_step = 1.
    //   Theorems: blockwise_base, blockwise_nat_induction, and
    //             blockwise_equals_monolithic
    //             (hypothesis-wrapped).
    let env = make_env();

    // Opaques (value-carrying but non-reducible).
    let opaque_names = [
        "NNVerify.Block.ibp_transfer",
        "NNVerify.C006.follows_from_c004",
        "NNVerify.C006.per_block_crown_matches_mono",
    ];
    for name in &opaque_names {
        let ci = env
            .get_const(&Name::from_string(name))
            .unwrap_or_else(|| panic!("{} should exist", name));
        assert_eq!(
            ci.kind,
            ConstantKind::Opaque,
            "{} should be Opaque (post-#3638 Phase 1)",
            name,
        );
    }

    // Reducible Definitions (Phase-1 faithful carriers + mono_step helper).
    let definition_names = [
        "NNVerify.Block.compose",
        "NNVerify.Block.monolithic_crown",
        "NNVerify.C006.mono_step",
    ];
    for name in &definition_names {
        let ci = env
            .get_const(&Name::from_string(name))
            .unwrap_or_else(|| panic!("{} should exist", name));
        assert_eq!(
            ci.kind,
            ConstantKind::Definition,
            "{} should be a reducible Definition (#3638 Phase 1)",
            name,
        );
        assert!(
            ci.is_reducible,
            "{} should be reducible — Phase-1 indexed Nat.rec bodies \
             carry real iota content that downstream proof terms unfold",
            name,
        );
    }

    let step = env
        .get_const(&Name::from_string("NNVerify.C006.blockwise_step"))
        .expect("blockwise_step theorem should exist");
    assert_eq!(
        step.kind,
        ConstantKind::Theorem,
        "blockwise_step should be the hypothesis-wrapped step theorem",
    );
    assert!(
        step.value.is_some(),
        "blockwise_step should carry a proof value",
    );

    let base = env
        .get_const(&Name::from_string("NNVerify.C006.blockwise_base"))
        .expect("base theorem should exist");
    assert_eq!(
        base.kind,
        ConstantKind::Theorem,
        "blockwise_base should be the Phase-3 hypothesis-wrapped theorem",
    );

    let nat_ind = env
        .get_const(&Name::from_string("NNVerify.C006.blockwise_nat_induction"))
        .expect("nat induction theorem should exist");
    assert_eq!(
        nat_ind.kind,
        ConstantKind::Theorem,
        "blockwise_nat_induction should be the local-evidence theorem",
    );
    assert!(
        nat_ind.value.is_some(),
        "blockwise_nat_induction should carry a proof value",
    );
    assert!(
        base.value.is_some(),
        "blockwise_base should carry a proof value",
    );

    let main = env
        .get_const(&Name::from_string(
            "NNVerify.C006.blockwise_equals_monolithic",
        ))
        .expect("main theorem should exist");
    assert_eq!(
        main.kind,
        ConstantKind::Theorem,
        "blockwise_equals_monolithic should be the Phase-2 theorem",
    );
    assert!(
        main.value.is_some(),
        "blockwise_equals_monolithic should carry a proof value",
    );
}

/// Regression guard: the C006 faithful carriers `Block.compose` and
/// `Block.monolithic_crown` must be reducible Definitions post-#3638.
/// Their bodies are indexed `@Nat.rec` over `fun i => IB (block_dim i)`
/// with syntactically distinct step cases (`cb i ih` vs
/// `mono_step … i ih`). Reverting to a shared `zero_ib` body would
/// re-open the alias-collapse masquerade that #3500 Branch A blocked
/// via Opacity — the Phase-1 design replaces that guard with a
/// structural one in the body itself.
#[test]
fn test_3638_carriers_are_reducible_faithful_definitions() {
    let env = make_env();
    for name in &["NNVerify.Block.compose", "NNVerify.Block.monolithic_crown"] {
        let ci = env
            .get_const(&Name::from_string(name))
            .unwrap_or_else(|| panic!("{} should exist", name));
        assert_eq!(
            ci.kind,
            ConstantKind::Definition,
            "{} must be Definition post-#3638 (was Opaque pre-Phase-1)",
            name,
        );
        assert!(
            ci.is_reducible,
            "{} must be reducible — indexed Nat.rec body requires iota \
             unfolding at call sites for downstream proofs",
            name,
        );
        assert!(
            ci.value.is_some(),
            "{} must carry its indexed Nat.rec body",
            name,
        );
    }
}

/// #3638 Phase 1 guard: `Block.compose` and `Block.monolithic_crown`
/// step-case bodies are **structurally distinct**. The former uses the
/// free variable `cb` (`crown_block` from the outer lambda); the latter
/// uses the `Const` reference `NNVerify.C006.mono_step`. This is the
/// Phase-1 demasquerade of Rule M1 (alias-collapse): the two carriers
/// cannot δ-reduce to the same term because their step bodies have
/// different head symbols.
#[test]
fn test_3638_carriers_have_distinct_step_bodies() {
    let env = make_env();
    let compose = env
        .get_const(&Name::from_string("NNVerify.Block.compose"))
        .expect("compose should exist");
    let monolithic = env
        .get_const(&Name::from_string("NNVerify.Block.monolithic_crown"))
        .expect("monolithic_crown should exist");
    let compose_value = compose.value.as_ref().expect("compose value present");
    let monolithic_value = monolithic
        .value
        .as_ref()
        .expect("monolithic_crown value present");
    // The full bodies are Nat.rec applications wrapped in seven lambdas.
    // Syntactic distinctness at the full-body level is enough to block
    // δ-collapse to a shared placeholder.
    assert_ne!(
        compose_value, monolithic_value,
        "#3638 Phase 1: Block.compose and Block.monolithic_crown must \
         have syntactically distinct bodies. If they match, the \
         masquerade Rule M1 (alias-collapse) has been re-introduced."
    );
}

/// #3638 Phase 1 guard: `C006.mono_step` is a reducible Definition
/// (required so `Block.monolithic_crown`'s step case iota-unfolds
/// through to the placeholder body during kernel type-checking).
#[test]
fn test_3638_mono_step_is_reducible_definition() {
    let env = make_env();
    let ci = env
        .get_const(&Name::from_string("NNVerify.C006.mono_step"))
        .expect("mono_step should be registered");
    assert_eq!(
        ci.kind,
        ConstantKind::Definition,
        "mono_step must be a Definition (Phase-1 reducible helper)"
    );
    assert!(
        ci.is_reducible,
        "mono_step must be reducible so Block.monolithic_crown's step \
         case unfolds through to the placeholder body"
    );
}

/// #3638 Phase 1 guard: `C006.per_block_crown_matches_mono` is
/// registered as a proposition-valued Opaque (True-valued Phase-1 body;
/// Phase 4 upgrades to the real `forall i X, cb i X = mono_step … i X`
/// proposition).
#[test]
fn test_3638_per_block_hypothesis_is_opaque_prop() {
    let env = make_env();
    let ci = env
        .get_const(&Name::from_string(
            "NNVerify.C006.per_block_crown_matches_mono",
        ))
        .expect("per_block_crown_matches_mono should be registered");
    assert_eq!(
        ci.kind,
        ConstantKind::Opaque,
        "per_block_crown_matches_mono must be Opaque (Prop-valued \
         placeholder hypothesis)"
    );
    assert!(
        ci.value.is_some(),
        "per_block_crown_matches_mono should carry its True-valued \
         Phase-1 body"
    );
}

// =============================================================================
// Proof quality validation using axiom_audit API (#3375)
// =============================================================================

// 2026-04-19 masquerade demotion (#3489-#3493) + 2026-04-20 carrier
// cleanup (#3500 Branch A): the former `#3375 zero-domain-axioms` tests
// were replaced after the C006 theorems were demoted to
// `Declaration::Axiom`. The shard audit
// (reports/audit/2026-04-19-clean-native-shard-audit.md entries 5-8)
// established that the Eq.refl/Nat.rec proof terms closed only because
// `Block.compose` and `Block.monolithic_crown` were reducible
// Definitions whose body is `zero_ib`. The Branch A carrier co-demotion
// in #3500 additionally flipped both placeholder carriers to
// `Declaration::Opaque` with the same body, closing the δ-reduction
// path so no downstream theorem can collapse the two aliases together.
// The new tests assert the honest axiom shape and the Opaque carrier
// invariant.

#[test]
fn test_c006_core_claim_kinds_after_step_retirement() {
    let env = make_env();
    for name_str in [
        "NNVerify.C006.blockwise_step",
        "NNVerify.C006.blockwise_nat_induction",
    ] {
        let name = Name::from_string(name_str);
        let ci = env
            .get_const(&name)
            .unwrap_or_else(|| panic!("{} should exist", name_str));
        assert_eq!(
            ci.kind,
            ConstantKind::Theorem,
            "{} must be a hypothesis-wrapped Declaration::Theorem",
            name_str,
        );
        assert!(ci.value.is_some(), "{} must carry a proof value", name_str,);
    }
}

#[test]
fn test_blockwise_step_theorem_has_no_c006_axiom_deps() {
    let env = make_env();
    let deps = env
        .axiom_deps(&Name::from_string("NNVerify.C006.blockwise_step"))
        .expect("axiom_deps should work for blockwise_step");
    let dep_strs: Vec<String> = deps.iter().map(|d| d.to_string()).collect();
    for forbidden in [
        "NNVerify.C006.blockwise_base",
        "NNVerify.C006.blockwise_step",
        "NNVerify.C006.blockwise_nat_induction",
        "NNVerify.C006.blockwise_equals_monolithic",
    ] {
        assert!(
            !dep_strs.contains(&forbidden.to_string()),
            "hypothesis-wrapped step theorem must not depend on {forbidden}; deps: {dep_strs:?}",
        );
    }
}

#[test]
fn test_blockwise_base_theorem_has_no_c006_axiom_deps() {
    let env = make_env();
    let deps = env
        .axiom_deps(&Name::from_string("NNVerify.C006.blockwise_base"))
        .expect("axiom_deps should work for blockwise_base");
    let dep_strs: Vec<String> = deps.iter().map(|d| d.to_string()).collect();
    for forbidden in [
        "NNVerify.C006.blockwise_base",
        "NNVerify.C006.blockwise_step",
        "NNVerify.C006.blockwise_nat_induction",
        "NNVerify.C006.blockwise_equals_monolithic",
    ] {
        assert!(
            !dep_strs.contains(&forbidden.to_string()),
            "Phase-3 base theorem must not depend on {forbidden}; deps: {dep_strs:?}",
        );
    }
}

#[test]
fn test_c006_claims_carry_a_type_signature() {
    // Demoted axioms still need well-formed type signatures so downstream
    // callers (follows_from_c004, other gamma-crown theorems) can refer to
    // them. Sanity-check that every former theorem still has an inferable
    // Pi type.
    let env = make_env();
    let claim_names = [
        "NNVerify.C006.blockwise_base",
        "NNVerify.C006.blockwise_step",
        "NNVerify.C006.blockwise_nat_induction",
        "NNVerify.C006.blockwise_equals_monolithic",
    ];
    for name_str in &claim_names {
        let name = Name::from_string(name_str);
        let const_expr = Expr::const_(name.clone(), vec![]);
        let tc = TypeChecker::with_mode(&env, env.mode());
        let ty = tc
            .infer_type(&const_expr)
            .unwrap_or_else(|e| panic!("{} type-inference failed: {:?}", name_str, e));
        assert!(
            matches!(ty.kind(), ExprKind::Pi(..)),
            "{} should have a Pi type (universally quantified claim)",
            name_str,
        );
    }
}

// =============================================================================
// #3489 — strengthened `blockwise_base` theorem: value characterization
// =============================================================================
//
// The `blockwise_base` theorem was strengthened from a bare
// `compose 0 = monolithic 0` alias identity (which closes with Eq.refl
// **only** because compose and monolithic_crown are reducibly defined with
// identical bodies) to the value characterization
//
//     And (compose 0 ... B = zero_ib (block_dim 0))
//         (monolithic_crown 0 ... B = zero_ib (block_dim 0))
//
// These tests pin the new structure so the audit finding in
// `reports/audit/2026-04-19-clean-native-shard-audit.md` (entry 5) can be
// closed and would be detected if it regressed.

/// Walk an expression tree and return true if any sub-expression is a
/// `Const` with the given name.
fn expr_mentions_const(e: &Expr, needle: &str) -> bool {
    match e.kind() {
        ExprKind::Const(n, _) => n.to_string() == needle,
        ExprKind::App(f, a) => expr_mentions_const(f, needle) || expr_mentions_const(a, needle),
        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
            expr_mentions_const(ty, needle) || expr_mentions_const(body, needle)
        }
        ExprKind::Let(_, ty, val, body, _) => {
            expr_mentions_const(ty, needle)
                || expr_mentions_const(val, needle)
                || expr_mentions_const(body, needle)
        }
        ExprKind::Proj(_, _, inner) => expr_mentions_const(inner, needle),
        ExprKind::MData(_, inner) => expr_mentions_const(inner, needle),
        _ => false,
    }
}

#[test]
fn test_phase2_main_theorem_type_mentions_pointwise_mono_step_hypothesis() {
    let env = make_env();
    let ci = env
        .get_const(&Name::from_string(
            "NNVerify.C006.blockwise_equals_monolithic",
        ))
        .expect("main theorem should exist");
    assert!(
        expr_mentions_const(&ci.type_, "NNVerify.C006.mono_step"),
        "Phase-2 main theorem type must include the pointwise \
         `crown_block = mono_step` hypothesis",
    );
}

#[test]
fn test_phase2_main_theorem_proof_uses_induction_and_hypothesis_chain() {
    let env = make_env();
    let ci = env
        .get_const(&Name::from_string(
            "NNVerify.C006.blockwise_equals_monolithic",
        ))
        .expect("main theorem should exist");
    let value = ci.value.as_ref().expect("main theorem proof value");
    for needle in [
        "Nat.rec",
        "Eq.trans",
        "congrArg",
        "NNVerify.C006.mono_step",
        "NNVerify.Block.compose",
        "NNVerify.Block.monolithic_crown",
    ] {
        assert!(
            expr_mentions_const(value, needle),
            "Phase-2 proof should mention {needle}",
        );
    }
    for forbidden in [
        "NNVerify.C006.blockwise_base",
        "NNVerify.C006.blockwise_step",
        "NNVerify.C006.blockwise_nat_induction",
    ] {
        assert!(
            !expr_mentions_const(value, forbidden),
            "Phase-2 proof must not wrap old C006 axiom {forbidden}",
        );
    }
}

#[test]
fn test_blockwise_step_proof_uses_local_hypothesis_chain() {
    let env = make_env();
    let ci = env
        .get_const(&Name::from_string("NNVerify.C006.blockwise_step"))
        .expect("blockwise_step should exist");
    assert!(
        expr_mentions_const(&ci.type_, "NNVerify.C006.mono_step"),
        "step theorem type must include the pointwise `crown_block = mono_step` hypothesis",
    );
    let value = ci.value.as_ref().expect("blockwise_step proof value");
    for needle in [
        "Eq.trans",
        "congrArg",
        "NNVerify.C006.mono_step",
        "NNVerify.Block.compose",
        "NNVerify.Block.monolithic_crown",
    ] {
        assert!(
            expr_mentions_const(value, needle),
            "step proof should mention {needle}",
        );
    }
    for forbidden in [
        "NNVerify.C006.blockwise_base",
        "NNVerify.C006.blockwise_step",
        "NNVerify.C006.blockwise_nat_induction",
        "NNVerify.C006.blockwise_equals_monolithic",
    ] {
        assert!(
            !expr_mentions_const(value, forbidden),
            "step proof must not wrap old C006 axiom/theorem {forbidden}",
        );
    }
}

#[test]
fn test_phase3_base_theorem_proof_uses_and_intro() {
    let env = make_env();
    let ci = env
        .get_const(&Name::from_string("NNVerify.C006.blockwise_base"))
        .expect("blockwise_base should exist");
    let value = ci.value.as_ref().expect("blockwise_base proof value");
    assert!(
        expr_mentions_const(value, "And.intro"),
        "Phase-3 base proof should combine the two zero-interval equalities with And.intro",
    );
    for forbidden in [
        "NNVerify.C006.blockwise_step",
        "NNVerify.C006.blockwise_nat_induction",
        "NNVerify.C006.blockwise_equals_monolithic",
    ] {
        assert!(
            !expr_mentions_const(value, forbidden),
            "Phase-3 base proof must not wrap old C006 axiom {forbidden}",
        );
    }
}

#[test]
fn test_phase2_main_theorem_has_no_c006_axiom_deps() {
    let env = make_env();
    let deps = env
        .axiom_deps(&Name::from_string(
            "NNVerify.C006.blockwise_equals_monolithic",
        ))
        .expect("axiom_deps should work for main theorem");
    let dep_strs: Vec<String> = deps.iter().map(|d| d.to_string()).collect();
    for forbidden in [
        "NNVerify.C006.blockwise_base",
        "NNVerify.C006.blockwise_step",
        "NNVerify.C006.blockwise_nat_induction",
        "NNVerify.C006.blockwise_equals_monolithic",
    ] {
        assert!(
            !dep_strs.contains(&forbidden.to_string()),
            "Phase-2 main theorem must not depend on {forbidden}; deps: {dep_strs:?}",
        );
    }
}

#[test]
fn test_3489_base_type_mentions_and_constructor() {
    // The strengthened statement is a conjunction, so its type must mention
    // the `And` inductive type. The prior statement was a plain `Eq`, which
    // would NOT satisfy this assertion — this is the direct regression guard
    // for the #3489 audit finding.
    let env = make_env();
    let ci = env
        .get_const(&Name::from_string("NNVerify.C006.blockwise_base"))
        .expect("blockwise_base should exist");
    assert!(
        expr_mentions_const(&ci.type_, "And"),
        "#3489: blockwise_base type must use `And` to express the conjunction \
         of compose-zero_ib and monolithic-zero_ib equalities, got type: {:?}",
        ci.type_,
    );
}

#[test]
fn test_3489_base_type_mentions_interval_bounds_mk() {
    // The strengthened statement's RHS on each conjunct is an explicit
    // `IntervalBounds.mk` application (the zero_ib builder). The prior
    // alias-only statement referenced neither `IntervalBounds.mk` nor `Fin`
    // inside its Eq comparands — it only mentioned `Block.compose` and
    // `Block.monolithic_crown`. Finding `IntervalBounds.mk` therefore confirms
    // the strengthened value-characterization is present.
    let env = make_env();
    let ci = env
        .get_const(&Name::from_string("NNVerify.C006.blockwise_base"))
        .expect("blockwise_base should exist");
    assert!(
        expr_mentions_const(&ci.type_, "NNVerify.IntervalBounds.mk"),
        "#3489: blockwise_base type must mention the explicit \
         `NNVerify.IntervalBounds.mk` constructor (zero_ib RHS), type: {:?}",
        ci.type_,
    );
}

// #3519 (2026-04-19, auditor round 6 F3): the old unwrapped
// `blockwise_base` proof-shape tests were deleted when `blockwise_base` and
// `blockwise_nat_induction` were demoted to Axioms. Phase 3 restores a
// hypothesis-wrapped base theorem, and the 2026-04-27 pass restores a
// local-evidence induction theorem; their live contracts are pinned by
// `test_blockwise_base_is_hypothesis_wrapped_theorem`,
// `test_blockwise_base_theorem_has_no_c006_axiom_deps`, and
// `test_phase3_base_theorem_proof_uses_and_intro`, plus
// `test_nat_induction_is_theorem_after_hypothesis_wrapping` and
// `test_nat_induction_has_proof_value`.
//
// The strengthened *statement* (the And-of-equalities type) is still pinned
// by `test_3489_base_type_mentions_interval_bounds_mk` above. If a future
// pass replaces the placeholder CROWN/IBP carriers with substantive content
// and re-promotes these constants to Theorems, revival proof-shape tests
// should live alongside the new Declaration::Theorem registrations.
