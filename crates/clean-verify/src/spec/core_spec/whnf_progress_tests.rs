// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Fail-closed pins for the MODEL-side WHNF progress / exit-shape brick
//! (`whnf_progress.rs`, Front-2 recursive-grounding FIRST BRICK).
//!
//! The theorem `whnf_progress_bd` must be a real `DerivedProved` closed term
//! with an EMPTY non-foundational computed closure, its statement must target
//! EXACTLY the const-free bvar-free fragment and the iota-free
//! `beta_reduces_bd` step relation, and the honestly-named `stuck` residual
//! must be present in the witness (the naive 2-shape progress is false here).

use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec_axiom_closure::{computed_axiom_closure, foundational_rule_names};
use crate::test_utils::run_with_stack;
use crate::Specification;
use clean_kernel::{ConstantKind, Name, Reducibility, TypeChecker};

/// Build the substitution subset of the spec (the `add_whnf_progress` stage is
/// in the Substitution bundle, right after `add_beta_bd_sn`; see `bundles.rs`).
fn build_progress_test_spec() -> Specification {
    run_with_stack(|| {
        Specification::new_substitution_test_spec().expect("substitution test spec should build")
    })
}

/// The three inductives (const-free unit, stuck-head predicate, progress
/// witness) register with constructor + recursor surfaces.
#[test]
fn test_whnf_progress_inductives_registered() {
    let spec = build_progress_test_spec();
    for name in [
        "ConstFreeUnit",
        "ConstFreeUnit.triv",
        "ConstFreeUnit.rec",
        "whnf_stuck_head",
        "whnf_stuck_head.sort",
        "whnf_stuck_head.pi",
        "whnf_stuck_head.app",
        "whnf_stuck_head.proj",
        "whnf_stuck_head.projw",
        "whnf_stuck_head.lit",
        "whnf_stuck_head.rec",
        "whnf_progress_result",
        "whnf_progress_result.done",
        "whnf_progress_result.step",
        "whnf_progress_result.stuck",
        "whnf_progress_result.stuck_proj",
        "whnf_progress_result.rec",
        "whnf_noredex_class",
        "whnf_noredex_class.done",
        "whnf_noredex_class.stuck",
        "whnf_noredex_class.stuck_proj",
        "whnf_noredex_class.rec",
        "const_free",
        "LiftP",
        "LiftP.up",
        "LiftP.rec",
        "liftp_composite_smoke",
        "whnf_env_step",
        "whnf_env_step.beta",
        "whnf_env_step.delta",
        "whnf_env_step.app_left",
        "whnf_env_step.proj",
        "whnf_env_step.rec",
        "whnf_progress_result_env",
        "whnf_progress_result_env.done",
        "whnf_progress_result_env.step",
        "whnf_progress_result_env.stuck",
        "whnf_progress_result_env.stuck_proj",
        "whnf_progress_result_env.rec",
        "const_delta_fires",
        "whnf_progress_env_constfree",
        "opt_defined",
        "has_defval",
        "consts_defined",
        "const_progress_env",
        "opt_none_discr",
        "opt_none_ne_some_t",
        "whnf_progress_env_bd",
        "env_fixpoint_classifies_bd",
        "whnf_red_step",
        "whnf_red_step.beta",
        "whnf_red_step.delta",
        "whnf_red_step.iota",
        "whnf_red_step.app_left",
        "whnf_red_step.proj",
        "env_step_to_red",
        "whnf_progress_result_red",
        "whnf_progress_result_red.done",
        "whnf_progress_result_red.step",
        "whnf_progress_result_red.stuck",
        "whnf_progress_result_red.stuck_proj",
        "whnf_progress_result_red.rec",
        "whnf_progress_red_bd",
        "red_fixpoint_classifies_bd",
        "natrec_fires_red_zero",
        "natrec_fires_red_succ",
        "opt_app_lift",
        "opt_proj_lift",
        "reduce_app_head",
        "reduce_once",
        "loop_dispatch",
        "whnf_fuel",
        "env_step_star",
        "env_step_star.refl",
        "env_step_star.tail",
        "env_step_star_head",
        "whnf_fuel_no_redex",
        "whnf_fuel_monotone",
        "whnf_fuel_reaches",
        "apply_spine_append_one",
        "delta_lift_app",
        "reduce_app_lift_sound",
        "reduce_proj_lift_sound",
        "reduce_once_sound",
        "whnf_fuel_reaches_sound",
        "def_env_good",
        "reduce_app_none_inv",
        "delta_none_app",
        "reduce_once_none_delta_none",
        "app_head_stuck",
        "opt_proj_lift",
        "proj_lift_none_inv",
        "reduce_proj_lift_sound",
        "proj_lift_closed",
        "proj_lift_defined",
        "noredex_proj_class",
        "noredex_proj_stuck",
        "app_stuck_class_combined",
        "opt_app_ilift",
        "reduce_app_head_red",
        "reduce_once_red",
        "whnf_fuel_red",
        "reduce_app_ilift_sound",
        "reduce_proj_lift_sound_red",
        "reduce_once_red_sound",
        "red_step_star",
        "red_step_star.refl",
        "red_step_star.tail",
        "red_step_star.rec",
        "red_step_star_head",
        "whnf_fuel_red_no_redex",
        "whnf_fuel_red_monotone",
        "whnf_fuel_red_reaches",
        "whnf_fuel_red_reaches_sound",
        "red_app_none_head_inv",
        "red_app_none_iota_inv",
        "reduce_once_red_none_delta_none",
        "reduce_once_red_none_iota_none",
        "OrType",
        "OrType.inl",
        "OrType.inr",
        "OrType.rec",
        "opt_meta_defined",
        "red_closed_at",
        "consts_defined_red",
        "red_env_good",
        "red_closed_le",
        "red_closed_list",
        "list_tail_red_closed",
        "list_take_red_closed",
        "list_drop_red_closed",
        "list_head_red_closed",
        "list_append_red_closed",
        "apply_spine_red_closed",
        "kapp_red_closed",
        "opt_bind_some_inv_t",
        "iota_reduct_some_inv_t",
        "iota_reduct_red_closed",
        "consts_defined_red_list",
        "lift_bvar_dispatch",
        "lift_bvar_defined_red",
        "lift_at_defined_red",
        "inst_bvar_geq_defined_red",
        "inst_bvar_defined_red",
        "inst_defined_red",
        "list_tail_defined_red",
        "list_take_defined_red",
        "list_drop_defined_red",
        "list_head_defined_red",
        "list_append_defined_red",
        "apply_spine_defined_red",
        "kapp_defined_red",
        "iota_reduct_defined_red",
        "reduce_app_ilift_closed",
        "reduce_proj_lift_closed",
        "reduce_once_red_preserves_closed",
        "reduce_app_ilift_defined",
        "reduce_proj_lift_defined",
        "reduce_once_red_preserves_defined",
        "silent_head_class_red",
        "silent_head_class_red.lam",
        "silent_head_class_red.neutral",
        "silent_head_class_red.stuck",
        "silent_head_class_red.rec",
        "silent_head_class_of_none_red",
        "reduce_once_red_none_classifies",
        "whnf_fuel_red_classifies",
        "is_neutral_red",
        "is_neutral_red.const",
        "is_neutral_red.app",
        "is_neutral_red.rec",
        "is_whnf_red",
        "is_whnf_red.neutral",
        "is_whnf_red.rec",
        "whnf_stuck_head_red",
        "whnf_stuck_head_red.projw",
        "whnf_stuck_head_red.rec",
        "whnf_noredex_class_red",
        "whnf_noredex_class_red.done",
        "whnf_noredex_class_red.rec",
        "silent_head_class_red_gen",
        "silent_head_class_red_gen.rec",
        "noredex_proj_class_red",
        "silent_head_class_of_none_red_gen",
        "reduce_once_red_none_classifies_gen",
        "whnf_fuel_red_classifies_gen",
        "whnf_fuel_red_le",
        "whnf_fuel_red_unique",
        "whnf_red_step_star",
        "whnf_red_step_star.refl",
        "whnf_red_step_star.step",
        "whnf_red_step_star.rec",
        "whnf_red_join_witness",
        "whnf_red_join_witness.intro",
        "whnf_red_join_witness.rec",
        "beta_bd_star_to_whnf_red_star",
        "whnf_red_beta_confluent",
        "beta_reduces_bd_to_par_cd",
        "whnf_red_step_to_par_cd",
        "whnf_red_step_star_to_par_cd_star",
        "whnf_red_step_star_confluent_via_cd",
        "whnf_red_step_star_snoc",
        "red_step_star_to_whnf_red_step_star",
        "whnf_fuel_red_join",
        "whnf_red_step_to_par_cd_star",
        "whnf_red_conv",
        "whnf_red_conv.refl",
        "whnf_red_conv.fwd",
        "whnf_red_conv.bwd",
        "whnf_red_conv.rec",
        "whnf_red_conv_join",
        "whnf_red_conv_trans",
        "whnf_red_conv_symm",
        "whnf_red_star_to_conv",
        "whnf_fuel_red_conv",
        "le_zero_eq_zero",
        "nat_sub_succ_le",
        "nat_sub_zero_eq",
        "lift_at_red_closed_id",
        "inst_bvar_dispatch",
        "inst_bvar_geq_dispatch",
        "inst_bvar_red_closed",
        "inst_red_closed",
        "inst_red_closed_zero",
        "reduce_once_none_classifies",
        "inst_closed_id",
        "nat_both_zero_add",
        "reduce_app_lift_closed",
        "reduce_once_preserves_closed",
        "reduce_app_lift_defined",
        "reduce_once_preserves_defined",
        "whnf_fuel_classifies",
    ] {
        assert!(
            spec.definitions().contains_key(name),
            "{name} should be registered by the whnf_progress stage"
        );
    }

    // CURRENT-KEXPR EXECUTABLE PARITY: prove the new projection/literal lanes
    // compute, rather than merely checking that their definitions registered.
    // The first case crosses both nested recursors: reduce a let under a
    // projection, then lift that projection reduct through an application.
    let computation_cases = [
        (
            "projection/app recursion",
            "reduce_once DefEnv.empty (KExpr.app (KExpr.proj Name.anonymous Nat.zero (KExpr.let_ (KExpr.sort Level.zero) (KExpr.sort Level.zero) (KExpr.bvar Nat.zero))) (KExpr.lit Nat.zero))",
            "OptionType.some KExpr (KExpr.app (KExpr.proj Name.anonymous Nat.zero (KExpr.sort Level.zero)) (KExpr.lit Nat.zero))",
        ),
        (
            "projection over literal fixpoint",
            "reduce_once DefEnv.empty (KExpr.proj Name.anonymous Nat.zero (KExpr.lit Nat.zero))",
            "OptionType.none KExpr",
        ),
        (
            "literal fixpoint",
            "reduce_once DefEnv.empty (KExpr.lit Nat.zero)",
            "OptionType.none KExpr",
        ),
        (
            "literal-head artificial reduct lift",
            "reduce_app_head (KExpr.sort Level.zero) (KExpr.lit Nat.zero) (OptionType.some KExpr (KExpr.bvar Nat.zero))",
            "OptionType.some KExpr (KExpr.app (KExpr.bvar Nat.zero) (KExpr.sort Level.zero))",
        ),
    ];
    let tc = TypeChecker::with_mode(spec.env(), spec.env().mode());
    for (label, lhs_src, rhs_src) in computation_cases {
        let lhs = spec
            .elaborate_source(lhs_src, &format!("{label} lhs"))
            .unwrap_or_else(|err| panic!("{label} lhs should elaborate: {err}"));
        let rhs = spec
            .elaborate_source(rhs_src, &format!("{label} rhs"))
            .unwrap_or_else(|err| panic!("{label} rhs should elaborate: {err}"));
        assert!(
            tc.is_def_eq(&lhs, &rhs),
            "{label} must compute definitionally: {lhs_src} != {rhs_src}"
        );
    }

    // The soundness consumer must accept the computed projection reduct and
    // return exactly the projection congruence step, closing the semantic lane.
    let projection_sound = spec
        .elaborate_source(
            "reduce_once_sound DefEnv.empty (KExpr.proj Name.anonymous Nat.zero (KExpr.let_ (KExpr.sort Level.zero) (KExpr.sort Level.zero) (KExpr.bvar Nat.zero))) (KExpr.proj Name.anonymous Nat.zero (KExpr.sort Level.zero)) (Eq.refl (OptionType KExpr) (OptionType.some KExpr (KExpr.proj Name.anonymous Nat.zero (KExpr.sort Level.zero))))",
            "reduce_once_sound projection computation",
        )
        .expect("reduce_once_sound should accept the computed projection reduct");
    let projection_sound_type = tc
        .infer_type(&projection_sound)
        .expect("projection soundness proof should have an inferred type");
    let expected_projection_step = spec
        .elaborate_source(
            "whnf_env_step DefEnv.empty (KExpr.proj Name.anonymous Nat.zero (KExpr.let_ (KExpr.sort Level.zero) (KExpr.sort Level.zero) (KExpr.bvar Nat.zero))) (KExpr.proj Name.anonymous Nat.zero (KExpr.sort Level.zero))",
            "expected projection congruence step",
        )
        .expect("expected projection congruence step should elaborate");
    assert!(
        tc.is_def_eq(&projection_sound_type, &expected_projection_step),
        "reduce_once_sound projection result must be the matching whnf_env_step"
    );

    // Exact constructor-surface audit for every canonical relation/result
    // consumed by X14/X15, plus their lifted red counterparts. This makes a
    // future constructor addition fail closed until each recursor/lift is
    // extended deliberately.
    let constructor_surfaces: [(&str, &[&str]); 5] = [
        (
            "whnf_env_step.",
            &["app_left", "beta", "delta", "proj", "rec"],
        ),
        (
            "whnf_progress_result_env.",
            &["done", "rec", "step", "stuck", "stuck_proj"],
        ),
        (
            "whnf_noredex_class.",
            &["done", "rec", "stuck", "stuck_proj"],
        ),
        (
            "whnf_red_step.",
            &["app_left", "beta", "delta", "iota", "proj", "rec"],
        ),
        (
            "whnf_progress_result_red.",
            &["done", "rec", "step", "stuck", "stuck_proj"],
        ),
    ];
    for (prefix, expected) in constructor_surfaces {
        let mut actual: Vec<&str> = spec
            .definitions()
            .keys()
            .filter_map(|name| name.strip_prefix(prefix))
            .collect();
        actual.sort_unstable();
        assert_eq!(
            actual, expected,
            "{prefix} constructor/recursor surface changed; audit every X14/X15 consumer"
        );
    }

    // FAIL-CLOSED X13b PIN: the full env-aware theorem must remain a genuine
    // kernel-checked proof over the exact bvar-free/defined-constant surface.
    // In particular, app (proj S i (const n [])) a requires BOTH contextual
    // lifts: const δ, then whnf_env_step.proj, then whnf_env_step.app_left.
    let theorem = spec
        .definitions()
        .get("whnf_progress_env_bd")
        .expect("whnf_progress_env_bd should be registered");
    assert!(
        !theorem.is_axiom,
        "whnf_progress_env_bd must not be an axiom"
    );
    assert_eq!(theorem.category, AxiomCategory::DerivedLemma);
    assert_eq!(theorem.proof_status, ProofStatus::DerivedProved);
    assert!(
        theorem.value_src.is_some(),
        "whnf_progress_env_bd must carry a closed proof term"
    );
    assert!(
        theorem.axiom_deps.is_empty(),
        "whnf_progress_env_bd must declare zero axiom debt: {:?}",
        theorem.axiom_deps
    );
    assert_eq!(
        theorem.type_src,
        "forall (env : DefEnv) (e : KExpr), Eq Nat (bvar_ceiling e) Nat.zero -> \
         consts_defined env e -> whnf_progress_result_env env e"
    );

    let dependencies = theorem
        .dependencies
        .as_ref()
        .expect("whnf_progress_env_bd must pin its direct dependency surface");
    let value_src = theorem
        .value_src
        .as_deref()
        .expect("whnf_progress_env_bd must retain its proof source");
    for required in [
        "whnf_env_step.app_left",
        "whnf_env_step.proj",
        "whnf_progress_result_env.stuck_proj",
        "is_whnf.proj",
        "is_whnf.lit",
        "whnf_stuck_head.projw",
        "whnf_stuck_head.lit",
    ] {
        assert!(
            dependencies.contains(required),
            "whnf_progress_env_bd dependency surface must retain {required}"
        );
        assert!(
            value_src.contains(required),
            "whnf_progress_env_bd proof source must exercise {required}"
        );
    }

    let foundational = foundational_rule_names(&spec);
    let closure = computed_axiom_closure(&spec, "whnf_progress_env_bd");
    let debt: Vec<&String> = closure.difference(&foundational).collect();
    assert!(
        debt.is_empty(),
        "whnf_progress_env_bd must have foundational-only computed closure, got: {debt:?}"
    );
    spec.verify_definition("whnf_progress_env_bd")
        .expect("whnf_progress_env_bd should re-typecheck in the live kernel environment");

    // MERGE-PARITY REGRESSION: X14/X15 were originally authored before the
    // env-aware progress witness gained its honest stuck-projection arm. Both
    // lifts must eliminate that arm explicitly rather than silently narrowing
    // the canonical progress surface back to application-only residuals.
    for (theorem_name, projection_constructor) in [
        (
            "env_fixpoint_classifies_bd",
            "whnf_noredex_class.stuck_proj",
        ),
        (
            "whnf_progress_red_bd",
            "whnf_progress_result_red.stuck_proj",
        ),
    ] {
        let theorem = spec
            .definitions()
            .get(theorem_name)
            .unwrap_or_else(|| panic!("{theorem_name} should be registered"));
        assert_eq!(theorem.proof_status, ProofStatus::DerivedProved);
        assert!(
            theorem.axiom_deps.is_empty(),
            "{theorem_name} must retain zero declared axiom debt"
        );
        assert!(
            theorem
                .dependencies
                .as_ref()
                .is_some_and(|deps| deps.contains(projection_constructor)),
            "{theorem_name} must pin {projection_constructor} in its dependency surface"
        );
        assert!(
            theorem
                .value_src
                .as_deref()
                .is_some_and(|value| value.contains(projection_constructor)),
            "{theorem_name} must explicitly discharge the stuck-projection minor"
        );
        spec.verify_definition(theorem_name)
            .unwrap_or_else(|err| panic!("{theorem_name} should re-typecheck: {err}"));
    }

    // The env-to-red embedding is a structural recursion over all four
    // canonical env-step constructors. Contextual env steps may contain δ
    // steps, so they must map to matching recursive red constructors rather
    // than being narrowed to the beta-only relation.
    let embedding = spec
        .definitions()
        .get("env_step_to_red")
        .expect("env_step_to_red should be registered");
    assert_eq!(embedding.proof_status, ProofStatus::DerivedProved);
    assert!(embedding.axiom_deps.is_empty());
    let embedding_deps = embedding
        .dependencies
        .as_ref()
        .expect("env_step_to_red must pin its constructor surface");
    let embedding_value = embedding
        .value_src
        .as_deref()
        .expect("env_step_to_red must retain its proof term");
    for required in [
        "whnf_red_step.beta",
        "whnf_red_step.delta",
        "whnf_red_step.app_left",
        "whnf_red_step.proj",
    ] {
        assert!(
            embedding_deps.contains(required),
            "env_step_to_red must pin {required}"
        );
        assert!(
            embedding_value.contains(required),
            "env_step_to_red must explicitly construct {required}"
        );
    }
    spec.verify_definition("env_step_to_red")
        .expect("the complete env-to-red embedding should re-typecheck");
}

/// FAIL-CLOSED PIN: `whnf_progress_bd` is a genuine DerivedProved closed term
/// (not an axiom, carries a proof value) with an EMPTY declared axiom closure.
#[test]
fn test_whnf_progress_bd_derived_proved_zero_axiom_deps() {
    let spec = build_progress_test_spec();
    let def = spec
        .definitions()
        .get("whnf_progress_bd")
        .expect("whnf_progress_bd should be registered by the whnf_progress stage");
    assert!(!def.is_axiom, "whnf_progress_bd must not be an axiom");
    assert_eq!(
        def.category,
        AxiomCategory::DerivedLemma,
        "whnf_progress_bd must be a DerivedLemma"
    );
    assert_eq!(
        def.proof_status,
        ProofStatus::DerivedProved,
        "whnf_progress_bd must be DerivedProved (closed, kernel-checked term)"
    );
    assert!(
        def.value_src.is_some(),
        "whnf_progress_bd must carry a closed proof term"
    );
    assert!(
        def.axiom_deps.is_empty(),
        "whnf_progress_bd must declare an empty axiom closure (FOUNDATIONAL only): {:?}",
        def.axiom_deps
    );
}

/// HONESTY PIN: the theorem targets EXACTLY the const-free bvar-free fragment
/// and the iota-free `beta_reduces_bd` step relation, and the witness carries
/// the explicit `stuck` residual (with a description that names the counter-
/// example refuting the naive 2-shape progress).
#[test]
fn test_whnf_progress_bd_targets_exact_fragment_and_relation() {
    let spec = build_progress_test_spec();

    let thm = spec
        .definitions()
        .get("whnf_progress_bd")
        .expect("whnf_progress_bd should be registered");
    assert_eq!(
        thm.type_src,
        "forall (e : KExpr), Eq Nat (bvar_ceiling e) Nat.zero -> const_free e -> \
         whnf_progress_result e",
        "the statement must be exactly const-free + bvar-free (ceiling zero) progress"
    );
    assert!(
        thm.description.contains("beta_reduces_bd")
            && thm.description.contains("FALSE")
            && thm.description.contains("stuck"),
        "the description must name the iota-free relation, the falseness of the naive \
         2-shape progress, and the stuck residual: {}",
        thm.description
    );

    // The witness must expose the stuck constructor over whnf_stuck_head, and
    // the step constructor over beta_reduces_bd (never the full whnf_step /
    // beta_reduces, whose iota arm breaks the termination alignment).
    let witness = spec
        .definitions()
        .get("whnf_progress_result.stuck")
        .expect("whnf_progress_result.stuck should be registered");
    assert!(
        witness.elaborated_type.is_some(),
        "whnf_progress_result.stuck should carry its elaborated constructor type"
    );
    let step = spec
        .definitions()
        .get("whnf_progress_result.step")
        .expect("whnf_progress_result.step should be registered");
    let step_ty = step
        .elaborated_type
        .as_ref()
        .map(std::string::ToString::to_string)
        .unwrap_or_default();
    assert!(
        step_ty.contains("beta_reduces_bd"),
        "the progress step must be over the iota-free beta_reduces_bd: {step_ty}"
    );
}

/// REGISTRATION PIN: `const_whnf` must stay a semireducible kernel Definition.
/// An Opaque registration would make the folded predicate unusable by a proof
/// of its computed `delta_reduct = none` equation; a fully reducible registration
/// would be a stronger transparency policy than this one-step alias needs.
#[test]
fn test_const_whnf_is_semireducible_definition() {
    let spec = build_progress_test_spec();
    let def = spec
        .definitions()
        .get("const_whnf")
        .expect("const_whnf should be registered");
    assert!(
        !def.is_axiom,
        "const_whnf must remain a Definition, not regress to a helper axiom"
    );

    let info = spec
        .env()
        .get_const(&Name::from_string("const_whnf"))
        .expect("const_whnf should be present in the kernel environment");
    assert!(
        matches!(info.reducibility, Reducibility::Regular(_)),
        "const_whnf must remain semireducible, got {:?}",
        info.reducibility
    );
    assert!(
        !info.is_reducible,
        "const_whnf must not become fully reducible"
    );
    assert_eq!(
        info.kind,
        ConstantKind::Definition,
        "const_whnf must remain a kernel Definition"
    );
}

/// KERNEL-GROUND-TRUTH HONESTY PIN: the computed transitive axiom closure of
/// `whnf_progress_bd` rests ONLY on the spec's self-declared FoundationalRule
/// primitives. `const_whnf` is a semireducible Definition, not a helper axiom,
/// and this lane only touches it through the unused `is_neutral.const`; the
/// closure must also avoid `delta_reduces` / `iota_reduces`. Empty residual ⇔
/// `DerivedProved` is not an overclaim.
#[test]
fn test_whnf_progress_bd_computed_closure_is_foundational_only() {
    let spec = build_progress_test_spec();
    let foundational = foundational_rule_names(&spec);
    let closure = computed_axiom_closure(&spec, "whnf_progress_bd");
    let debt: Vec<&String> = closure.difference(&foundational).collect();
    assert!(
        debt.is_empty(),
        "whnf_progress_bd must have an empty non-foundational computed closure, got: {debt:?}"
    );
    assert!(
        !closure.contains("const_whnf"),
        "whnf_progress_bd must not classify const_whnf as an axiom dependency"
    );
}

/// The theorem re-verifies against the live kernel environment (the stored
/// elaborated proof term type-checks at its declared type).
#[test]
fn test_whnf_progress_bd_reverifies_in_kernel() {
    let spec = build_progress_test_spec();
    spec.verify_definition("whnf_progress_bd")
        .expect("whnf_progress_bd should re-typecheck in the spec environment");
}

/// REGRESSION: the no-redex composition theorem must eliminate every
/// `whnf_progress_result` constructor. In particular, projections over stuck
/// heads are a genuine no-step residual and cannot be omitted or represented
/// by the application-only `stuck` constructor.
#[test]
fn test_step_fixpoint_classifies_bd_covers_stuck_projection() {
    let spec = build_progress_test_spec();

    for name in [
        "whnf_noredex_class.stuck_proj",
        "step_fixpoint_classifies_bd",
    ] {
        assert!(
            spec.definitions().contains_key(name),
            "{name} should be registered by the whnf_progress stage"
        );
    }

    let theorem = spec
        .definitions()
        .get("step_fixpoint_classifies_bd")
        .expect("composition theorem should be registered");
    assert_eq!(theorem.proof_status, ProofStatus::DerivedProved);
    assert!(
        theorem
            .dependencies
            .as_ref()
            .is_some_and(|deps| deps.contains("whnf_noredex_class.stuck_proj")),
        "the theorem dependency surface must retain the stuck-projection constructor"
    );
    assert!(
        theorem
            .value_src
            .as_deref()
            .is_some_and(|value| value.contains("whnf_noredex_class.stuck_proj")),
        "the recursor proof must discharge the stuck-projection minor"
    );
    spec.verify_definition("step_fixpoint_classifies_bd")
        .expect("the complete composition proof should re-typecheck in the live kernel");
}

/// Deep pins for the X16 executable-loop capstones and the MIR reflection
/// cluster (audit M9/M10): statement-substring pins so a silent statement
/// rewrite fails loudly, DerivedProved status, foundational-only computed
/// closures, and a live kernel re-typecheck — one spec build for all of them.
#[test]
fn test_x16_capstones_and_mir_deep_pins() {
    let spec = build_progress_test_spec();
    let foundational = foundational_rule_names(&spec);

    let statement_pins: [(&str, &[&str]); 18] = [
        (
            "whnf_fuel_classifies",
            &[
                "def_env_good env",
                "(whnf_fuel env fuel e) (OptionType.some KExpr r)",
                "whnf_noredex_class r",
                "Eq Nat (bvar_ceiling e) Nat.zero",
                "consts_defined env e",
            ],
        ),
        // Relational confluence of whnf_red_step (β/ζ core). Pin the join
        // conclusion so a silent weakening of the confluence statement fails.
        (
            "whnf_red_conv_join",
            &[
                "whnf_red_conv renv a b",
                "par_strips_witness_cd_star renv a b",
            ],
        ),
        (
            "whnf_fuel_red_join",
            &[
                "(whnf_fuel_red renv fuel e) (OptionType.some KExpr r)",
                "whnf_red_step_star renv e e2",
                "par_strips_witness_cd_star renv r e2",
            ],
        ),
        (
            "whnf_red_step_star_confluent_via_cd",
            &[
                "whnf_red_step_star renv e e1",
                "whnf_red_step_star renv e e2",
                "par_strips_witness_cd_star renv e1 e2",
            ],
        ),
        (
            "whnf_red_beta_confluent",
            &[
                "beta_reduces_bd_star e e1",
                "beta_reduces_bd_star e e2",
                "whnf_red_join_witness renv e1 e2",
            ],
        ),
        (
            "beta_bd_star_to_whnf_red_star",
            &["beta_reduces_bd_star e e2", "whnf_red_step_star renv e e2"],
        ),
        // The PARAMETRIC (arbitrary-renv) 3-way capstones — the classification
        // and fuel-loop capstone generalized beyond the fixed the_red_env.
        // Pin `renv` (not the_red_env) so a silent re-pinning is caught too.
        (
            "whnf_fuel_red_classifies_gen",
            &[
                "red_env_good renv",
                "(whnf_fuel_red renv fuel e) (OptionType.some KExpr r)",
                "whnf_noredex_class_red renv r",
                "red_closed_at e Nat.zero",
                "consts_defined_red renv e",
            ],
        ),
        (
            "reduce_once_red_none_classifies_gen",
            &[
                "(reduce_once_red renv e) (OptionType.none KExpr)",
                "whnf_noredex_class_red renv e",
                "consts_defined_red renv e",
            ],
        ),
        // The 3-way (β/ζ+δ+ι) executable-loop capstones (X17c-2c). Deep-pin the
        // statements so a silent weakening of the classification or the
        // fuel-loop capstone fails loudly, matching the X16 capstone discipline.
        (
            "whnf_fuel_red_classifies",
            &[
                "red_env_good the_red_env",
                "(whnf_fuel_red the_red_env fuel e) (OptionType.some KExpr r)",
                "whnf_noredex_class r",
                "red_closed_at e Nat.zero",
                "consts_defined_red the_red_env e",
            ],
        ),
        (
            "reduce_once_red_none_classifies",
            &[
                "(reduce_once_red the_red_env e) (OptionType.none KExpr)",
                "red_closed_at e Nat.zero",
                "consts_defined_red the_red_env e",
                "whnf_noredex_class e",
            ],
        ),
        (
            "reduce_once_red_sound",
            &[
                "(reduce_once_red renv e) (OptionType.some KExpr e2)",
                "whnf_red_step renv e e2",
            ],
        ),
        (
            "reduce_once_sound",
            &[
                "(reduce_once env e) (OptionType.some KExpr e2)",
                "whnf_env_step env e e2",
            ],
        ),
        (
            "whnf_fuel_reaches_sound",
            &["env_step_star", "whnf_fuel env fuel e"],
        ),
        (
            "reduce_once_none_classifies",
            &[
                "(reduce_once env e) (OptionType.none KExpr)",
                "consts_defined env e",
                "whnf_noredex_class e",
            ],
        ),
        (
            "reduce_once_preserves_closed",
            &["def_env_good env", "Eq Nat (bvar_ceiling e2) Nat.zero"],
        ),
        (
            "reduce_once_preserves_defined",
            &["def_env_good env", "consts_defined env e2"],
        ),
        ("mir_reaches_smoke", &[]),
        ("mir_payload_reflection_whnf_inner", &[]),
    ];

    for (name, pins) in statement_pins {
        let def = spec
            .definitions()
            .get(name)
            .unwrap_or_else(|| panic!("{name} should be registered"));
        assert_eq!(
            def.proof_status,
            ProofStatus::DerivedProved,
            "{name} must be DerivedProved"
        );
        for pin in pins {
            assert!(
                def.type_src.contains(pin),
                "{name} statement must contain {pin:?} — a statement rewrite must fail this pin"
            );
        }
        let closure = computed_axiom_closure(&spec, name);
        let debt: Vec<&String> = closure.difference(&foundational).collect();
        assert!(
            debt.is_empty(),
            "{name} must have an empty non-foundational computed closure, got: {debt:?}"
        );
        spec.verify_definition(name)
            .unwrap_or_else(|e| panic!("{name} should re-typecheck in the live kernel: {e:?}"));
    }

    // The audit-C1 rewrite made the two public classification lemmas thin
    // projections of the combined proof — pin that routing so a silent
    // re-inlining (or a statement-weakening rewrite of the combined lemma)
    // is caught.
    for name in ["app_head_stuck", "reduce_once_none_classifies"] {
        let def = spec.definitions().get(name).expect("pinned above");
        assert!(
            def.value_src
                .as_deref()
                .is_some_and(|v| v.contains("app_stuck_class_combined")),
            "{name} must route through app_stuck_class_combined"
        );
    }
}
