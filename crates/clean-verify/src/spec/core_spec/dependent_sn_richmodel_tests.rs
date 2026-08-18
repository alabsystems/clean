// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Kernel-check pins for the Brick-2 rich-model dependent judgment
//! (`dependent_sn_richmodel.rs`). Confirms `ctx_lookup`, `TypingCtx` (+ its
//! generated recursor/constructors) and the two non-vacuity witnesses register
//! and re-verify against the live kernel environment.

use crate::Specification;

fn build_spec() -> Specification {
    crate::test_utils::build_substitution_spec_with_stack()
}

/// The dependent judgment, its lookup, recursor, constructors and witnesses all
/// register.
#[test]
fn test_dependent_richmodel_registered() {
    let spec = build_spec();
    for name in [
        "ctx_lookup",
        "TypingCtx",
        "TypingCtx.rec",
        "TypingCtx.var",
        "TypingCtx.sort",
        "TypingCtx.pi",
        "TypingCtx.lam",
        "TypingCtx.app",
        "TypingCtx.const",
        // Let increment (task #28): the trailing dependent let rule.
        "TypingCtx.let_",
        "typingctx_sort_witness",
        "typingctx_var_witness",
    ] {
        assert!(
            spec.definitions().contains_key(name),
            "{name} should be registered by the dependent_sn_richmodel stage"
        );
    }
}

/// The non-vacuity witnesses re-typecheck against the live kernel environment —
/// the real witness that `TypingCtx` (with the new `var`/`const` rules) is a
/// genuine, inhabited, kernel-sound inductive.
#[test]
fn test_dependent_richmodel_witnesses_reverify() {
    let spec = build_spec();
    for name in ["typingctx_sort_witness", "typingctx_var_witness"] {
        spec.verify_definition(name).unwrap_or_else(|e| {
            panic!("{name} should re-typecheck in the spec environment: {e:?}")
        });
    }
}

/// BATCH 4 FVRel bisimulation framework: the FVRel/FVRelL inductives, their
/// generated recursors, and the structural pass-through + list lemmas all
/// register and re-verify against the live kernel environment.
#[test]
fn test_fvrel_framework_registered_and_reverifies() {
    let spec = build_spec();
    // Inductives + generated recursors/constructors.
    for name in [
        "FVRel",
        "FVRel.rec",
        "FVRel.bvar_bound",
        "FVRel.bvar_free",
        "FVRel.app",
        "FVRel.lam",
        "FVRel.pi",
        // Let increment (task #28): the trailing let_ congruence.
        "FVRel.let_",
        "FVRelL",
        "FVRelL.rec",
        "FVRelL.nil",
        "FVRelL.cons",
        // Batch 5: dichotomy + existential witness inductives.
        "NatLtLeDichotomy",
        "NatLtLeDichotomy.rec",
        "FVRelHeadWitness",
        "FVRelHeadWitness.rec",
        "DeltaBisimWitness",
        "DeltaBisimWitness.rec",
        // Batch 6: iota bisimulation witness inductive.
        "IotaBisimWitness",
        "IotaBisimWitness.rec",
        // Batch 6b: Nat trichotomy witness inductive.
        "NatTrichotomy",
        "NatTrichotomy.rec",
        // Batch 6d: FVRel inversion witness inductives.
        "FVRelAppInv",
        "FVRelAppInv.rec",
        "FVRelLamInv",
        "FVRelLamInv.rec",
        "FVRelPiInv",
        "FVRelPiInv.rec",
        // Let increment (task #28): the let_ inversion witness inductive.
        "FVRelLetInv",
        "FVRelLetInv.rec",
        // Batch 6e: beta bisimulation witness inductive.
        "BetaBisimWitness",
        "BetaBisimWitness.rec",
        // Batch 6f: union bisimulation witness inductive.
        "WhnfBisimWitness",
        "WhnfBisimWitness.rec",
        // Priority batch: CandModel accessors, RedAbstraction, Models, pi SN-closure.
        "CandModel",
        "CandModel.rec",
        "cm_Red",
        "RedAbstraction",
        // Let increment (task #28): the zeta weak-head-expansion closure law.
        "RedLet",
        // Nat.rec increment (task #30): the object-level-iota expansion closure law.
        "RedNatRec",
        "Models",
        "WhnfStepPiInv",
        "WhnfStepPiInv.rec",
    ] {
        assert!(
            spec.definitions().contains_key(name),
            "{name} should be registered by the FVRel batch"
        );
    }
    // DerivedProved lemmas: each carries a closed value and re-typechecks.
    for name in [
        "fvRel_symm",
        "fvRel_const_name",
        "fvRel_kapp_fn",
        "fvRelL_append",
        "fvRelL_tail",
        "fvRelL_length",
        "fvRelL_drop",
        "fvRelL_take",
        "fvRelL_apply_spine",
        "fvRel_kapp_args",
        // Batch 5: dichotomy totality + (A) arithmetic + (B) existential lemmas.
        "nat_lt_le_dichotomy",
        "fvRel_refl",
        "fvRel_mono",
        "fvRelL_head_some",
        "fvRel_delta_bisim",
        // Batch 6: iota bisimulation arm.
        "fvRel_iota_bisim",
        // Batch 6a: FVRel arithmetic bridges + fvRel_lift.
        "le_sub_zero",
        "lt_sub_succ",
        "lt_add_weaken_right",
        "le_add_right_mono",
        "fvRel_lift",
        // Batch 6b: trichotomy totality + Lt->Le bridges + instantiate_bvar0.
        "nat_trichotomy",
        "lt_implies_le",
        "lt_to_le_succ",
        "fvRel_instantiate_bvar0",
        // Batch 6c: ordering bridges + fvRel_instantiate_at.
        "lt_of_lt_of_le",
        "lt_succ_to_le",
        "nat_succ_sub1_of_lt",
        "fvRel_instantiate_at",
        // Batch 6d: FVRel inversion lemmas.
        "fvRel_app_inv",
        "fvRel_lam_inv",
        "fvRel_pi_inv",
        // Let increment (task #28): the let_ inversion.
        "fvRel_let_inv",
        // Batch 6e: beta bisimulation arm.
        "fvRel_beta_bisim",
        // Batch 6f: union bisimulation + SN transport (framework complete).
        "fvRel_bisim",
        "whnfAcc_of_fvRel",
        "whnfAcc_of_instantiate_bvar0",
        // Priority batch: bvar discriminations, CandModel CR accessors +
        // redAbstraction_holds, red_var / whnfAcc_sort, the pi SN-closure, and the
        // psubst_cancel arithmetic sub-tower + Models environment.
        "app_ne_bvar",
        "lam_ne_bvar",
        "pi_ne_bvar",
        // Let increment (task #28): let_ != bvar discrimination.
        "let_ne_bvar",
        "CR1",
        "CR2",
        "CR3",
        "redAbstraction_holds",
        // Let increment (task #28): the redLet field projection.
        "redLet_holds",
        // Nat.rec increment (task #30): the redNatRec field projection.
        "redNatRec_holds",
        "no_whnf_step_bvar",
        "red_var",
        "whnfAcc_sort",
        "whnfStep_pi_inv",
        "whnfAcc_pi",
        "upn_zero_apply",
        "upn_succ_apply",
        "upn_apply_lt",
        "upn_apply_ge",
        "lift_at_bvar_lt",
        "nat_succ_sub_of_le",
        "models_idsubst",
        "psubst_cancel_gen",
        "psubst_cancel",
        "models_extend",
        // Brick 2: the 4 remaining CandModel field accessors + the 6 Tait
        // adequacy cases + fundamental_general + the top theorem.
        "red_sort",
        "pi_elim",
        "pi_intro",
        "redConst",
        "fundamental_var",
        "fundamental_sort",
        "fundamental_pi",
        "fundamental_lam",
        "fundamental_app",
        "fundamental_const",
        // Let increment (task #28): the let adequacy case.
        "fundamental_let",
        "fundamental_general",
        "whnf_terminates_well_typed_dependent",
    ] {
        let def = spec
            .definitions()
            .get(name)
            .unwrap_or_else(|| panic!("{name} should be registered"));
        assert!(!def.is_axiom, "{name} must not be an axiom");
        assert!(def.value_src.is_some(), "{name} must carry a proof term");
        assert!(
            def.axiom_deps.is_empty(),
            "{name} must declare empty axiom closure: {:?}",
            def.axiom_deps
        );
        spec.verify_definition(name)
            .unwrap_or_else(|e| panic!("{name} should re-typecheck in the spec env: {e:?}"));
    }
}

/// CENSUS-NEUTRALITY PIN: the rich judgment adds ZERO kernel axioms — it lowers to
/// Inductive/Constructor/Recursor only. Guards the design-doc claim that the
/// dependent judgment is census-neutral until a `CandModel` is asserted.
#[test]
fn test_dependent_richmodel_witnesses_not_axioms() {
    let spec = build_spec();
    for name in ["typingctx_sort_witness", "typingctx_var_witness"] {
        let def = spec
            .definitions()
            .get(name)
            .unwrap_or_else(|| panic!("{name} should be registered"));
        assert!(!def.is_axiom, "{name} must not be an axiom");
        assert!(
            def.value_src.is_some(),
            "{name} must carry a closed proof term"
        );
        assert!(
            def.axiom_deps.is_empty(),
            "{name} must declare an empty axiom closure: {:?}",
            def.axiom_deps
        );
    }
}
