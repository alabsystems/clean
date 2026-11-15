// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **Crystal E4's census** -- `KernelAcceptsIn`, the env-indexed algorithmic
//! successor of `KernelInfersIn` (`src/spec/core_spec/acceptance_cdp_in.rs`),
//! and the inventory rows it closes (`data/crystal_e4_conversion_inventory.json`).
//!
//! The stage also registers the TYPED-CONVERSION successors `KernelAcceptsTcIn`
//! / `TypingTcIn` (one `Bool`-indexed family per side, typing and conversion),
//! which carry proof irrelevance, lambda eta, unit-like and structure eta, and
//! the Nat literal / constructor correspondence.
//!
//! "Proved" here means kernel-checked on registration, re-checked by
//! `verify_definition`, domain AND foundational axiom closure EMPTY. The census
//! also asserts what the statements say (the soundness target, the successor
//! embedding, the non-seed environments) and that forged callers are REFUSED
//! by the kernel -- a witness whose premise the checker would accept for any
//! output would be no witness.

use clean_kernel::name::Name;
use clean_verify::spec::Specification;
use clean_verify::spec_axiom_closure::computed_axiom_closure;
use clean_verify::test_utils::build_spec_with_stack;

/// The count this census mints. Quote it; do not type it somewhere else.
const ACCEPTS_IN_PROOFS: usize = 70;

pub(crate) fn assert_kernel_checked_axiom_free(spec: &Specification, name: &str) {
    let def = spec
        .definitions()
        .get(name)
        .unwrap_or_else(|| panic!("{name} must be registered"));
    assert!(
        !def.is_axiom && def.value_src.is_some() && def.elaborated_value.is_some(),
        "{name} must carry a checked value, not be an axiom"
    );
    spec.verify_definition(name)
        .unwrap_or_else(|e| panic!("{name} must re-check against its declared type: {e:?}"));
    let kernel_name = Name::from_string(name);
    let domain = spec
        .env()
        .axiom_deps(&kernel_name)
        .expect("domain closure computes");
    assert!(domain.is_empty(), "{name}: domain axiom closure {domain:?}");
    let foundational = spec
        .env()
        .foundational_axiom_deps(&kernel_name)
        .expect("foundational closure computes");
    assert!(
        foundational.is_empty(),
        "{name}: foundational axiom closure {foundational:?}"
    );
    let computed = computed_axiom_closure(spec, name);
    assert!(computed.is_empty(), "{name}: computed closure {computed:?}");
}

pub(crate) fn type_src(spec: &Specification, name: &str) -> String {
    spec.definitions()
        .get(name)
        .map(|d| d.type_src.clone())
        .unwrap_or_else(|| panic!("{name} must be registered"))
}

/// Every proof the stage registers is kernel-checked with an empty axiom
/// closure, and the headline statements say exactly what the inventory cites.
#[test]
fn kernel_accepts_in_registers_axiom_free_and_says_what_it_claims() {
    let spec = build_spec_with_stack();
    let names = clean_verify::spec::ACCEPTS_IN_PROOF_NAMES;
    assert_eq!(names.len(), ACCEPTS_IN_PROOFS);
    for name in names {
        assert_kernel_checked_axiom_free(&spec, name);
    }
    // Soundness lands in TypingProjIn: TypingCDPCtxConvIn plus the projection
    // rule, into which the old projection-aware family embeds.
    assert_eq!(
        type_src(&spec, "kernel_accepts_in_sound"),
        "forall (R : RedEnv) (tenv : KDeclEnv) (G : ListType KExpr) (e : KExpr) (T : KExpr), \
         KernelAcceptsIn R tenv G e T -> TypingProjIn R tenv G e T"
    );
    assert_eq!(
        type_src(&spec, "typing_cdp_to_proj_in"),
        "forall (R : RedEnv) (tenv : KDeclEnv) (G : ListType KExpr) (e : KExpr) (T : KExpr), \
         TypingCDPCtxConvIn R tenv G e T -> TypingProjIn R tenv G e T"
    );
    // The successor embeds the old env-indexed algorithmic relation.
    assert_eq!(
        type_src(&spec, "kernel_infers_in_to_accepts_in"),
        "forall (R : RedEnv) (tenv : KDeclEnv) (G : ListType KExpr) (e : KExpr) (T : KExpr), \
         KernelInfersIn R tenv G e T -> KernelAcceptsIn R tenv G e T"
    );
    // The two witnesses run in supplied environments, never the reflected seed,
    // and each carries a constructive inequality with the seed.
    for (witness, env) in [
        ("kernel_accepts_in_prepass_pi", "accepts_prepass_env"),
        ("accepts_prepass_pi_sound", "accepts_prepass_env"),
        (
            "kernel_accepts_in_proj_pi",
            "projection_metadata_control_env",
        ),
        ("accepts_proj_pi_sound", "projection_metadata_control_env"),
        (
            "kernel_accepts_in_proj_field_zero",
            "projection_metadata_control_env",
        ),
        (
            "accepts_proj_field_zero_sound",
            "projection_metadata_control_env",
        ),
        ("kernel_accepts_in_proj_dependent_field", "accepts_dep_env"),
        ("accepts_proj_dependent_field_sound", "accepts_dep_env"),
    ] {
        let src = type_src(&spec, witness);
        assert!(src.contains(env), "{witness} must run at {env}: {src}");
        assert!(
            !src.contains("the_red_env"),
            "{witness} must not be seed-pinned"
        );
    }
    for inequality in ["accepts_prepass_env_not_seed", "accepts_proj_env_not_seed"] {
        assert!(type_src(&spec, inequality).ends_with("the_red_env -> Empty"));
    }
    // The typed-conversion successor: one Bool-indexed family per side, the
    // algorithmic one sound into the declarative one, and both old relations
    // embedded, so every earlier witness still lands in the new target.
    assert_eq!(
        type_src(&spec, "kernel_accepts_tc_in_sound"),
        "forall (R : RedEnv) (tenv : KDeclEnv) (b : Bool) (G : ListType CtxEntryIn) (x : KExpr) (y : KExpr), \
         KernelAcceptsTcIn R tenv b G x y -> TypingTcIn R tenv b G x y"
    );
    assert_eq!(
        type_src(&spec, "kernel_accepts_in_to_tc_in"),
        "forall (R : RedEnv) (tenv : KDeclEnv) (G : ListType KExpr) (e : KExpr) (T : KExpr), \
         KernelAcceptsIn R tenv G e T -> KernelAcceptsTcIn R tenv Bool.true (lctx_decls G) e T"
    );
    assert_eq!(
        type_src(&spec, "typing_proj_in_to_tc_in"),
        "forall (R : RedEnv) (tenv : KDeclEnv) (G : ListType KExpr) (e : KExpr) (T : KExpr), \
         TypingProjIn R tenv G e T -> TypingTcIn R tenv Bool.true (lctx_decls G) e T"
    );
    // Each typed-conversion witness relates two DIFFERENT terms, which no
    // DefEqCDPIn derivation can: the arm is load-bearing, not decoration.
    for (witness, head) in [
        (
            "kernel_accepts_tc_in_proof_irrel",
            "KernelAcceptsTcIn R tenv Bool.false accepts_tc_prop_context (KExpr.bvar (Nat.succ Nat.zero)) (KExpr.bvar Nat.zero)",
        ),
        (
            "kernel_accepts_tc_in_unit_like",
            "KernelAcceptsTcIn accepts_unit_env tenv Bool.false accepts_unit_context (KExpr.bvar Nat.zero) (KExpr.bvar (Nat.succ Nat.zero))",
        ),
        ("kernel_accepts_tc_in_eta", "accepts_tc_fun_context (KExpr.bvar Nat.zero)"),
        ("kernel_accepts_tc_in_struct_eta", "accepts_struct_t (KExpr.bvar Nat.zero)"),
        // Not a conversion: a let body typed only through its local's VALUE.
        (
            "kernel_accepts_tc_in_let_zeta",
            "KernelAcceptsTcIn R tenv Bool.true (ListType.nil CtxEntryIn) (KExpr.let_",
        ),
    ] {
        let src = type_src(&spec, witness);
        assert!(src.contains(head), "{witness} must state {head}: {src}");
        assert!(!src.contains("the_red_env"), "{witness} must not be seed-pinned");
    }
    // The environment-generic witnesses quantify the environment; the two that
    // need metadata run at supplied, non-seed environments.
    for witness in [
        "kernel_accepts_tc_in_proof_irrel",
        "kernel_accepts_tc_in_eta",
        "kernel_accepts_tc_in_let_zeta",
        "kernel_accepts_tc_in_lit_two",
        "accepts_tc_offset_peel",
        "accepts_tc_iota_major_literal",
        "kernel_accepts_tc_in_quot_lift",
        "kernel_accepts_tc_in_quot_ind",
        "kernel_accepts_tc_in_quot_lift_extra_arg",
    ] {
        assert!(
            type_src(&spec, witness).starts_with("forall (R : RedEnv) (tenv : KDeclEnv)"),
            "{witness} must hold at every environment"
        );
    }
    for (witness, env) in [
        ("kernel_accepts_tc_in_unit_like", "accepts_unit_env"),
        ("accepts_unit_like_sound", "accepts_unit_env"),
        (
            "kernel_accepts_tc_in_struct_eta",
            "projection_metadata_control_env",
        ),
        (
            "accepts_struct_eta_sound",
            "projection_metadata_control_env",
        ),
    ] {
        assert!(
            type_src(&spec, witness).contains(env),
            "{witness} must run at {env}"
        );
    }
    assert!(type_src(&spec, "accepts_unit_env_not_seed").ends_with("the_red_env -> Empty"));
    // The quotient witnesses relate a Quot.lift / Quot.ind redex to its
    // function argument applied to the quoted value: argument 3 (#2) applied
    // to the major's LAST argument (#0), never the proof #1 or another slot.
    for witness in [
        "kernel_accepts_tc_in_quot_lift",
        "kernel_accepts_tc_in_quot_ind",
    ] {
        let src = type_src(&spec, witness);
        assert!(
            src.ends_with(
                "(KExpr.app (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))) (KExpr.bvar Nat.zero))"
            ),
            "{witness} must conclude at argument 3 applied to the quoted value: {src}"
        );
        assert!(
            !src.contains("the_red_env"),
            "{witness} must not be seed-pinned"
        );
    }
    // The literal and quotient rules key on REFLECTED names: each alias's value
    // is the kcre name the validated interning table assigns.
    for (alias, real) in clean_verify::spec::ACCEPTS_TC_NAT_NAME_ALIASES
        .iter()
        .chain(clean_verify::spec::ACCEPTS_TC_QUOT_NAME_ALIASES)
    {
        let atom = clean_verify::red_env_reflect::committed_name_atom(real)
            .unwrap_or_else(|e| panic!("{real} must be interned: {e}"));
        let value = spec
            .definitions()
            .get(*alias)
            .and_then(|d| d.value_src.clone())
            .unwrap_or_else(|| panic!("{alias} must be registered with a value"));
        assert_eq!(
            value.trim(),
            format!("def {alias} : Name := {atom}"),
            "{alias} must be the reflected {real}"
        );
    }
    // The dependent witness's type IS a projection of the preceding field.
    assert!(type_src(&spec, "kernel_accepts_in_proj_dependent_field")
        .ends_with("(KExpr.proj Name.anonymous Nat.zero (KExpr.bvar Nat.zero))"));
    for inductive in [
        "KernelAcceptsIn",
        "TypingProjIn",
        "ProjStructIn",
        "ProjParamsIn",
        "ProjFieldIn",
        "KernelAcceptsTcIn",
        "TypingTcIn",
        "UnitLikeIn",
        "StructCtorIn",
        "RecKAdmitIn",
        "CtxEntryIn",
    ] {
        assert!(
            spec.env()
                .get_const(&Name::from_string(inductive))
                .is_some(),
            "{inductive} must be registered"
        );
    }
}

/// Forged callers are refused by the kernel: a wrong result, a starved run,
/// a projection trace moved to the reflected seed, a dependent field given its
/// undependent domain, an out-of-bounds field, and the old one-name projection
/// congruence stretched across two names. For the typed-conversion arms: proof
/// irrelevance at a proposition that lives in `Type`, eta at a non-function,
/// unit-like at a one-field structure and at the seed, structure eta at a
/// subject whose type is not the structure, a literal given the wrong
/// predecessor, and a let-local value read off a DECLARATION entry. For the
/// quotient rules: a `Quot.mk` major with two arguments (the deployed and Lean
/// rules need three), a `Quot.ind` head claimed through the `Quot.lift` rule, and
/// the proof argument returned in place of the function. Each guard the arm reads is shown to be load-bearing.
/// (K-like reduction's forged callers: `accepts_tc_native_fold_census`.)
#[test]
fn kernel_accepts_in_witnesses_refuse_forged_callers() {
    let mut spec = build_spec_with_stack();
    for &(name, source) in FORGED {
        let kernel_name = Name::from_string(name);
        assert!(spec.env().get_const(&kernel_name).is_none(), "{name}");
        let error = spec
            .add_recursive_def(source, "Forged KernelAcceptsIn caller: must not register.")
            .expect_err("a forged caller must be refused");
        assert!(
            format!("{error:?}").contains("mismatch"),
            "{name} must be refused by a type mismatch, got {error:?}"
        );
        assert!(spec.env().get_const(&kernel_name).is_none(), "{name}");
        assert!(!spec.definitions().contains_key(name), "{name}");
    }
}

/// Kernel-refused callers; each must fail by a type mismatch and leave no trace.
const FORGED: &[(&str, &str)] = &[
    (
        "accepts_forged_prepass_result",
        r"def accepts_forged_prepass_result : par_reduces_cdp_star accepts_prepass_env accepts_prepass_redex (KExpr.sort Level.zero) :=
semantic_join_cdp_old_star accepts_prepass_env accepts_prepass_redex (KExpr.sort Level.zero)
  (whnf_fuel_red_wh3_par_in accepts_prepass_env (Nat.succ (Nat.succ (Nat.succ Nat.zero)))
accepts_prepass_redex (KExpr.sort Level.zero) accepts_prepass_computes)",
    ),
    (
        "accepts_forged_prepass_starved",
        r"def accepts_forged_prepass_starved : par_reduces_cdp_star accepts_prepass_env accepts_prepass_redex (KExpr.sort (Level.succ Level.zero)) :=
semantic_join_cdp_old_star accepts_prepass_env accepts_prepass_redex (KExpr.sort (Level.succ Level.zero))
  (whnf_fuel_red_wh3_par_in accepts_prepass_env (Nat.succ (Nat.succ Nat.zero))
accepts_prepass_redex (KExpr.sort (Level.succ Level.zero)) accepts_prepass_starved)",
    ),
    (
        "accepts_forged_seed_projection",
        r"def accepts_forged_seed_projection : par_reduces_cdp_star the_red_env accepts_proj_redex (KExpr.sort (Level.succ Level.zero)) :=
par_cdp_to_star the_red_env accepts_proj_redex (KExpr.sort (Level.succ Level.zero))
  (par_reduces_cdp.projection_beta the_red_env Name.anonymous Nat.zero
accepts_proj_subject (KExpr.sort (Level.succ Level.zero)) accepts_proj_computes)",
    ),
    (
        "accepts_forged_dependent_domain",
        r"def accepts_forged_dependent_domain : ProjFieldIn accepts_dep_env Name.anonymous (KExpr.bvar Nat.zero) Nat.zero (Nat.succ Nat.zero)
  (KExpr.pi (KExpr.sort (Level.succ Level.zero)) (KExpr.pi (KExpr.bvar Nat.zero) (KExpr.const Name.anonymous (ListType.nil Level))))
  (KExpr.sort (Level.succ Level.zero)) := accepts_dep_field_one_walk",
    ),
    (
        "accepts_forged_field_bound",
        r"def accepts_forged_field_bound : ProjStructIn projection_metadata_control_env Name.anonymous (Nat.succ Nat.zero) projection_metadata_control_type
  projection_metadata_control_ind projection_metadata_control_ctor :=
ProjStructIn.mk projection_metadata_control_env Name.anonymous (Nat.succ Nat.zero) projection_metadata_control_type
  projection_metadata_control_ind projection_metadata_control_cn projection_metadata_control_ctor
  (Eq.refl (OptionType Name) (OptionType.some Name Name.anonymous))
  (Eq.refl (OptionType KIndMeta) (OptionType.some KIndMeta projection_metadata_control_ind))
  (Eq.refl (ListType Name) (ListType.cons Name projection_metadata_control_cn (ListType.nil Name)))
  (Eq.refl (OptionType KCtorMeta) (OptionType.some KCtorMeta projection_metadata_control_ctor))
  (Eq.refl Bool Bool.true) (Eq.refl Bool Bool.true) (Eq.refl Bool Bool.true)",
    ),
    (
        "accepts_forged_one_name_congruence",
        r"def accepts_forged_one_name_congruence : DefEqCDPIn projection_metadata_control_env accepts_proj_redex
  (KExpr.proj accepts_proj_other_name Nat.zero accepts_proj_subject) :=
DefEqCDPIn.proj projection_metadata_control_env Name.anonymous Nat.zero accepts_proj_subject accepts_proj_subject
  (DefEqCDPIn.refl projection_metadata_control_env accepts_proj_subject)",
    ),
    (
        "accepts_tc_forged_proof_irrel_type",
        r"def accepts_tc_forged_proof_irrel_type : forall (R : RedEnv) (tenv : KDeclEnv), KernelAcceptsTcIn R tenv Bool.false (ListType.cons CtxEntryIn (CtxEntryIn.decl (KExpr.bvar (Nat.succ Nat.zero))) (ListType.cons CtxEntryIn (CtxEntryIn.decl (KExpr.bvar Nat.zero)) (ListType.cons CtxEntryIn (CtxEntryIn.decl (KExpr.sort (Level.succ Level.zero))) (ListType.nil CtxEntryIn)))) (KExpr.bvar (Nat.succ Nat.zero)) (KExpr.bvar Nat.zero) :=
fun (R : RedEnv) (tenv : KDeclEnv) =>
KernelAcceptsTcIn.proof_irrel R tenv (ListType.cons CtxEntryIn (CtxEntryIn.decl (KExpr.bvar (Nat.succ Nat.zero))) (ListType.cons CtxEntryIn (CtxEntryIn.decl (KExpr.bvar Nat.zero)) (ListType.cons CtxEntryIn (CtxEntryIn.decl (KExpr.sort (Level.succ Level.zero))) (ListType.nil CtxEntryIn))))
  (KExpr.bvar (Nat.succ Nat.zero)) (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))) (KExpr.bvar (Nat.succ (Nat.succ Nat.zero)))
  (KExpr.sort (Level.succ Level.zero)) (KExpr.bvar Nat.zero) (KExpr.bvar (Nat.succ (Nat.succ Nat.zero)))
  (KernelAcceptsTcIn.bvar R tenv (ListType.cons CtxEntryIn (CtxEntryIn.decl (KExpr.bvar (Nat.succ Nat.zero))) (ListType.cons CtxEntryIn (CtxEntryIn.decl (KExpr.bvar Nat.zero)) (ListType.cons CtxEntryIn (CtxEntryIn.decl (KExpr.sort (Level.succ Level.zero))) (ListType.nil CtxEntryIn)))) (Nat.succ Nat.zero) (CtxEntryIn.decl (KExpr.bvar Nat.zero)) (Eq.refl (OptionType CtxEntryIn) (OptionType.some CtxEntryIn (CtxEntryIn.decl (KExpr.bvar Nat.zero)))))
  (KernelAcceptsTcIn.cdp R tenv (ListType.cons CtxEntryIn (CtxEntryIn.decl (KExpr.bvar (Nat.succ Nat.zero))) (ListType.cons CtxEntryIn (CtxEntryIn.decl (KExpr.bvar Nat.zero)) (ListType.cons CtxEntryIn (CtxEntryIn.decl (KExpr.sort (Level.succ Level.zero))) (ListType.nil CtxEntryIn)))) (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))) (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))) (DefEqCDPIn.refl R (KExpr.bvar (Nat.succ (Nat.succ Nat.zero)))))
  (KernelAcceptsTcIn.bvar R tenv (ListType.cons CtxEntryIn (CtxEntryIn.decl (KExpr.bvar (Nat.succ Nat.zero))) (ListType.cons CtxEntryIn (CtxEntryIn.decl (KExpr.bvar Nat.zero)) (ListType.cons CtxEntryIn (CtxEntryIn.decl (KExpr.sort (Level.succ Level.zero))) (ListType.nil CtxEntryIn)))) (Nat.succ (Nat.succ Nat.zero)) (CtxEntryIn.decl (KExpr.sort (Level.succ Level.zero))) (Eq.refl (OptionType CtxEntryIn) (OptionType.some CtxEntryIn (CtxEntryIn.decl (KExpr.sort (Level.succ Level.zero))))))
  (KernelAcceptsTcIn.cdp R tenv (ListType.cons CtxEntryIn (CtxEntryIn.decl (KExpr.bvar (Nat.succ Nat.zero))) (ListType.cons CtxEntryIn (CtxEntryIn.decl (KExpr.bvar Nat.zero)) (ListType.cons CtxEntryIn (CtxEntryIn.decl (KExpr.sort (Level.succ Level.zero))) (ListType.nil CtxEntryIn)))) (KExpr.sort (Level.succ Level.zero)) (KExpr.sort Level.zero) (DefEqCDPIn.refl R (KExpr.sort Level.zero)))
  (KernelAcceptsTcIn.bvar R tenv (ListType.cons CtxEntryIn (CtxEntryIn.decl (KExpr.bvar (Nat.succ Nat.zero))) (ListType.cons CtxEntryIn (CtxEntryIn.decl (KExpr.bvar Nat.zero)) (ListType.cons CtxEntryIn (CtxEntryIn.decl (KExpr.sort (Level.succ Level.zero))) (ListType.nil CtxEntryIn)))) Nat.zero (CtxEntryIn.decl (KExpr.bvar (Nat.succ Nat.zero))) (Eq.refl (OptionType CtxEntryIn) (OptionType.some CtxEntryIn (CtxEntryIn.decl (KExpr.bvar (Nat.succ Nat.zero))))))
  (KernelAcceptsTcIn.cdp R tenv (ListType.cons CtxEntryIn (CtxEntryIn.decl (KExpr.bvar (Nat.succ Nat.zero))) (ListType.cons CtxEntryIn (CtxEntryIn.decl (KExpr.bvar Nat.zero)) (ListType.cons CtxEntryIn (CtxEntryIn.decl (KExpr.sort (Level.succ Level.zero))) (ListType.nil CtxEntryIn)))) (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))) (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))) (DefEqCDPIn.refl R (KExpr.bvar (Nat.succ (Nat.succ Nat.zero)))))",
    ),
    (
        "accepts_tc_forged_eta_non_function",
        r"def accepts_tc_forged_eta_non_function : forall (R : RedEnv) (tenv : KDeclEnv), KernelAcceptsTcIn R tenv Bool.false (ListType.cons CtxEntryIn (CtxEntryIn.decl (KExpr.sort Level.zero)) (ListType.nil CtxEntryIn)) (KExpr.bvar Nat.zero) (KExpr.lam (KExpr.sort Level.zero) (KExpr.app (KExpr.bvar (Nat.succ Nat.zero)) (KExpr.bvar Nat.zero))) :=
fun (R : RedEnv) (tenv : KDeclEnv) =>
KernelAcceptsTcIn.eta R tenv (ListType.cons CtxEntryIn (CtxEntryIn.decl (KExpr.sort Level.zero)) (ListType.nil CtxEntryIn)) (KExpr.bvar Nat.zero) (KExpr.sort Level.zero) (KExpr.sort Level.zero) (KExpr.sort Level.zero)
  (KernelAcceptsTcIn.bvar R tenv (ListType.cons CtxEntryIn (CtxEntryIn.decl (KExpr.sort Level.zero)) (ListType.nil CtxEntryIn)) Nat.zero (CtxEntryIn.decl (KExpr.sort Level.zero)) (Eq.refl (OptionType CtxEntryIn) (OptionType.some CtxEntryIn (CtxEntryIn.decl (KExpr.sort Level.zero)))))
  (KernelAcceptsTcIn.cdp R tenv (ListType.cons CtxEntryIn (CtxEntryIn.decl (KExpr.sort Level.zero)) (ListType.nil CtxEntryIn)) (KExpr.sort Level.zero) (KExpr.pi (KExpr.sort Level.zero) (KExpr.sort Level.zero)) (DefEqCDPIn.refl R (KExpr.sort Level.zero)))",
    ),
    (
        "accepts_tc_forged_unit_like_one_field",
        r"def accepts_tc_forged_unit_like_one_field : UnitLikeIn projection_metadata_control_env projection_metadata_control_type :=
UnitLikeIn.mk projection_metadata_control_env projection_metadata_control_type Name.anonymous projection_metadata_control_ind projection_metadata_control_cn projection_metadata_control_ctor
  (Eq.refl (OptionType Name) (OptionType.some Name Name.anonymous))
  (Eq.refl (OptionType KIndMeta) (OptionType.some KIndMeta projection_metadata_control_ind))
  (Eq.refl (ListType Name) (ListType.cons Name projection_metadata_control_cn (ListType.nil Name)))
  (Eq.refl Bool Bool.true)
  (Eq.refl (OptionType KCtorMeta) (OptionType.some KCtorMeta projection_metadata_control_ctor))
  (Eq.refl Bool Bool.true)",
    ),
    (
        "accepts_tc_forged_seed_unit_like",
        r"def accepts_tc_forged_seed_unit_like : UnitLikeIn the_red_env accepts_unit_type :=
UnitLikeIn.mk the_red_env accepts_unit_type Name.anonymous accepts_unit_ind accepts_unit_cn accepts_unit_ctor
  (Eq.refl (OptionType Name) (OptionType.some Name Name.anonymous))
  (Eq.refl (OptionType KIndMeta) (OptionType.some KIndMeta accepts_unit_ind))
  (Eq.refl (ListType Name) (ListType.cons Name accepts_unit_cn (ListType.nil Name)))
  (Eq.refl Bool Bool.true)
  (Eq.refl (OptionType KCtorMeta) (OptionType.some KCtorMeta accepts_unit_ctor))
  (Eq.refl Bool Bool.true)",
    ),
    (
        "accepts_tc_forged_struct_eta_foreign_subject",
        r"def accepts_tc_forged_struct_eta_foreign_subject : forall (tenv : KDeclEnv), KernelAcceptsTcIn projection_metadata_control_env tenv Bool.false (ListType.cons CtxEntryIn (CtxEntryIn.decl (KExpr.sort (Level.succ Level.zero))) (ListType.nil CtxEntryIn)) accepts_struct_t (KExpr.bvar Nat.zero) :=
fun (tenv : KDeclEnv) =>
KernelAcceptsTcIn.struct_eta projection_metadata_control_env tenv (ListType.cons CtxEntryIn (CtxEntryIn.decl (KExpr.sort (Level.succ Level.zero))) (ListType.nil CtxEntryIn))
  accepts_struct_t (KExpr.bvar Nat.zero) (KExpr.sort (Level.succ Level.zero)) (KExpr.sort (Level.succ Level.zero))
  projection_metadata_control_ind projection_metadata_control_ctor accepts_struct_ctor
  (KernelAcceptsTcIn.bvar projection_metadata_control_env tenv (ListType.cons CtxEntryIn (CtxEntryIn.decl (KExpr.sort (Level.succ Level.zero))) (ListType.nil CtxEntryIn)) Nat.zero (CtxEntryIn.decl (KExpr.sort (Level.succ Level.zero))) (Eq.refl (OptionType CtxEntryIn) (OptionType.some CtxEntryIn (CtxEntryIn.decl (KExpr.sort (Level.succ Level.zero))))))
  (KernelAcceptsTcIn.cdp projection_metadata_control_env tenv (ListType.cons CtxEntryIn (CtxEntryIn.decl (KExpr.sort (Level.succ Level.zero))) (ListType.nil CtxEntryIn)) (KExpr.sort (Level.succ Level.zero)) (KExpr.sort (Level.succ Level.zero)) (DefEqCDPIn.refl projection_metadata_control_env (KExpr.sort (Level.succ Level.zero))))
  (Eq.refl (OptionType Name) (OptionType.some Name Name.anonymous))
  (accepts_struct_fields tenv)",
    ),
    (
        "accepts_tc_forged_lit_pred",
        r"def accepts_tc_forged_lit_pred : forall (R : RedEnv) (tenv : KDeclEnv) (G : ListType CtxEntryIn), KernelAcceptsTcIn R tenv Bool.false G (literal_nat (Nat.succ (Nat.succ Nat.zero))) (KExpr.app (KExpr.const accepts_tc_nat_succ_name (ListType.nil Level)) (literal_nat Nat.zero)) :=
fun (R : RedEnv) (tenv : KDeclEnv) (G : ListType CtxEntryIn) => KernelAcceptsTcIn.lit_succ R tenv G (Nat.succ Nat.zero)",
    ),
    (
        "accepts_tc_forged_zeta_on_decl",
        r"def accepts_tc_forged_zeta_on_decl : forall (R : RedEnv) (tenv : KDeclEnv), KernelAcceptsTcIn R tenv Bool.false (ListType.cons CtxEntryIn (CtxEntryIn.decl (KExpr.sort (Level.succ (Level.succ Level.zero)))) (ListType.nil CtxEntryIn)) (KExpr.bvar Nat.zero) (KExpr.sort (Level.succ Level.zero)) :=
fun (R : RedEnv) (tenv : KDeclEnv) =>
KernelAcceptsTcIn.zeta_local R tenv (ListType.cons CtxEntryIn (CtxEntryIn.decl (KExpr.sort (Level.succ (Level.succ Level.zero)))) (ListType.nil CtxEntryIn)) Nat.zero (KExpr.sort (Level.succ (Level.succ Level.zero))) (KExpr.sort (Level.succ Level.zero))
  (Eq.refl (OptionType CtxEntryIn) (OptionType.some CtxEntryIn (CtxEntryIn.defn (KExpr.sort (Level.succ (Level.succ Level.zero))) (KExpr.sort (Level.succ Level.zero)))))",
    ),
    (
        "accepts_tc_forged_quot_short_mk",
        r"def accepts_tc_forged_quot_short_mk : forall (R : RedEnv) (tenv : KDeclEnv) (G : ListType CtxEntryIn), KernelAcceptsTcIn R tenv Bool.false G (KExpr.app (KExpr.app (KExpr.app (KExpr.app (KExpr.app (KExpr.app (KExpr.const accepts_tc_quot_lift_name (ListType.cons Level Level.zero (ListType.cons Level Level.zero (ListType.nil Level)))) (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero))))))) (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))))) (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ Nat.zero))))) (KExpr.bvar (Nat.succ (Nat.succ Nat.zero)))) (KExpr.bvar (Nat.succ Nat.zero))) (KExpr.app (KExpr.app (KExpr.const accepts_tc_quot_mk_name (ListType.cons Level Level.zero (ListType.nil Level))) (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero))))))) (KExpr.bvar Nat.zero))) (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))) (KExpr.bvar Nat.zero)) :=
fun (R : RedEnv) (tenv : KDeclEnv) (G : ListType CtxEntryIn) =>
KernelAcceptsTcIn.quot_lift R tenv G (ListType.cons Level Level.zero (ListType.cons Level Level.zero (ListType.nil Level))) (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))))) (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero))))) (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))) (KExpr.bvar (Nat.succ Nat.zero)) (ListType.cons Level Level.zero (ListType.nil Level)) (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))))) (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero))))) (KExpr.bvar Nat.zero)",
    ),
    (
        "accepts_tc_forged_quot_ind_head",
        r"def accepts_tc_forged_quot_ind_head : forall (R : RedEnv) (tenv : KDeclEnv) (G : ListType CtxEntryIn), KernelAcceptsTcIn R tenv Bool.false G (KExpr.app (KExpr.app (KExpr.app (KExpr.app (KExpr.app (KExpr.app (KExpr.const accepts_tc_quot_ind_name (ListType.cons Level Level.zero (ListType.cons Level Level.zero (ListType.nil Level)))) (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero))))))) (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))))) (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ Nat.zero))))) (KExpr.bvar (Nat.succ (Nat.succ Nat.zero)))) (KExpr.bvar (Nat.succ Nat.zero))) (KExpr.app (KExpr.app (KExpr.app (KExpr.const accepts_tc_quot_mk_name (ListType.cons Level Level.zero (ListType.nil Level))) (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero))))))) (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))))) (KExpr.bvar Nat.zero))) (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))) (KExpr.bvar Nat.zero)) :=
fun (R : RedEnv) (tenv : KDeclEnv) (G : ListType CtxEntryIn) =>
KernelAcceptsTcIn.quot_lift R tenv G (ListType.cons Level Level.zero (ListType.cons Level Level.zero (ListType.nil Level))) (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))))) (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero))))) (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))) (KExpr.bvar (Nat.succ Nat.zero)) (ListType.cons Level Level.zero (ListType.nil Level)) (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))))) (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero))))) (KExpr.bvar Nat.zero)",
    ),
    (
        "accepts_tc_forged_quot_wrong_function",
        r"def accepts_tc_forged_quot_wrong_function : forall (R : RedEnv) (tenv : KDeclEnv) (G : ListType CtxEntryIn), KernelAcceptsTcIn R tenv Bool.false G (KExpr.app (KExpr.app (KExpr.app (KExpr.app (KExpr.app (KExpr.app (KExpr.const accepts_tc_quot_lift_name (ListType.cons Level Level.zero (ListType.cons Level Level.zero (ListType.nil Level)))) (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero))))))) (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))))) (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ Nat.zero))))) (KExpr.bvar (Nat.succ (Nat.succ Nat.zero)))) (KExpr.bvar (Nat.succ Nat.zero))) (KExpr.app (KExpr.app (KExpr.app (KExpr.const accepts_tc_quot_mk_name (ListType.cons Level Level.zero (ListType.nil Level))) (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero))))))) (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))))) (KExpr.bvar Nat.zero))) (KExpr.app (KExpr.bvar (Nat.succ Nat.zero)) (KExpr.bvar Nat.zero)) :=
fun (R : RedEnv) (tenv : KDeclEnv) (G : ListType CtxEntryIn) =>
KernelAcceptsTcIn.quot_lift R tenv G (ListType.cons Level Level.zero (ListType.cons Level Level.zero (ListType.nil Level))) (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))))) (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero))))) (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))) (KExpr.bvar (Nat.succ Nat.zero)) (ListType.cons Level Level.zero (ListType.nil Level)) (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))))) (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero))))) (KExpr.bvar Nat.zero)",
    ),
];
