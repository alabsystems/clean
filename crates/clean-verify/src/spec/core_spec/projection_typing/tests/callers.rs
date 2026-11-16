// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Concrete model callers. These do not assert declaration admission or Rust refinement.

use super::{assert_absent, checks, run_with_stack, shared_spec};
use clean_kernel::Name;

const NIL: &str = "(@ListType.nil KExpr)";
const S0: &str = "(KExpr.sort Level.zero)";
const S1: &str = "(KExpr.sort (Level.succ Level.zero))";
const S2: &str = "(KExpr.sort (Level.succ (Level.succ Level.zero)))";

#[test]
fn projection_typing_actual_resolver_and_transparent_computations() {
    run_with_stack(|| {
        let spec = shared_spec();
        for (source, expected) in [
            ("projection_resolve dp_R dp_one dp_family_name dp_one dp_family",
                "@OptionType.some ProjectionMetadataResult dp_result"),
            ("projection_resolve dp_R dp_one dp_family_name dp_two dp_family",
                "@OptionType.none ProjectionMetadataResult"),
            ("projection_resolve dp_R dp_one dp_nat_name dp_one dp_family",
                "@OptionType.none ProjectionMetadataResult"),
            ("dp_inferred_field1", "@OptionType.some KExpr dp_domain"),
            ("projection_post_whnf_reduct dp_R dp_domain", "@OptionType.some KExpr dp_nat"),
            ("projection_post_whnf_reduct dp_R (KExpr.proj dp_family_name dp_one dp_subject)",
                "@OptionType.some KExpr dp_zero"),
            ("raw_pi_spine dp_args (kconst_type dp_ctor_signature)", "@OptionType.some KExpr dp_family"),
            ("raw_pi_spine (list_take dp_one dp_args) (kconst_type dp_ctor_signature)",
                "@OptionType.some KExpr (KExpr.pi dp_nat dp_family)"),
            ("kdecl_type_at dp_tenv dp_ctor_name (@ListType.cons Level Level.zero (@ListType.nil Level))",
                "@OptionType.none KExpr"),
            ("cgen_tenv Name.anonymous", "@OptionType.some KConstSig cgen_signature"),
            ("projection_post_whnf_reduct the_red_env cgen_projection", "@OptionType.some KExpr (KExpr.sort Level.zero)"),
        ] {
            checks::computes(spec, source, expected);
        }
        checks::computes(spec,
            "projection_field_prefix dp_R dp_one dp_family_name dp_subject dp_two Nat.zero (projection_meta_start dp_result)",
            &format!("@OptionType.some (ListType KExpr) (@ListType.cons KExpr {S1} (@ListType.cons KExpr dp_domain {NIL}))"));
        checks::computes(spec,
            &format!("semantic_typing_cdp_generation the_red_env cgen_tenv {NIL} (KExpr.app (KExpr.const Name.anonymous (@ListType.nil Level)) {S0}) {S0}"),
            &format!("SemanticTypingCDPAppReturn the_red_env cgen_tenv {NIL} (KExpr.const Name.anonymous (@ListType.nil Level)) {S0} {S0}"));
        checks::computes(spec,
            &format!("RawPiHeadCanonicalCDP dp_R dp_tenv {NIL} dp_ctor (kconst_type dp_ctor_signature)"),
            &format!("forall (V : KExpr), TypingCDPCtxConvIn dp_R dp_tenv {NIL} dp_ctor V -> DefEqCDPIn dp_R (kconst_type dp_ctor_signature) V"));
        checks::not_def_eq(spec, "dp_nat", "dp_domain");
        checks::not_def_eq(spec, "cgen_projection", S0);
    });
}

#[test]
fn projection_typing_dependent_field_derives_from_old_whole() {
    run_with_stack(|| {
        let spec = shared_spec();
        let old_selected = format!("TypingCtxConvIn dp_R dp_tenv {NIL} dp_zero dp_nat");
        let new_selected = format!("TypingCDPCtxConvIn dp_R dp_tenv {NIL} dp_zero dp_domain");
        checks::caller(spec,
            &format!("dp_field1_connected dp_family dp_domain dp_actual_whole dp_inferred_field1_run ({old_selected}) (fun (typed : {old_selected}) (_converted : DefEqCDPIn dp_R dp_nat dp_domain) => typed)"),
            &old_selected);
        checks::caller(
            spec,
            "dp_cdp_field1_from_whole dp_family dp_domain dp_actual_whole dp_inferred_field1_run",
            &new_selected,
        );
        checks::caller(spec, "dp_cdp_field1_typed", &new_selected);
        checks::caller(
            spec,
            "dp_cdp_whole_typed",
            &format!("TypingCDPCtxConvIn dp_R dp_tenv {NIL} dp_subject dp_family"),
        );
        checks::caller(spec, "dp_cdp_field1_from_whole",
            &format!("forall (T D : KExpr), TypingCtxConvIn dp_R dp_tenv {NIL} dp_subject T -> @Eq (OptionType KExpr) dp_inferred_field1 (@OptionType.some KExpr D) -> TypingCDPCtxConvIn dp_R dp_tenv {NIL} dp_zero D"));
        // Generic observed T does not change the fixed dp_family resolver.
        checks::computes(spec, "dp_result",
            "ProjectionMetadataResult.mk dp_family dp_ind_meta dp_ctor_name dp_ctor_meta (kconst_type dp_ctor_signature)");
        checks::caller(spec, "typing_cdp_open_var_embeds dp_R dp_tenv (@ListType.nil KExpr)",
            &format!("TypingCDPCtxConvIn dp_R dp_tenv (@ListType.cons KExpr (KExpr.bvar Nat.zero) {NIL}) (KExpr.bvar Nat.zero) (KExpr.bvar (Nat.succ Nat.zero))"));
        for (kind, literal, ty) in [
            ("nat", "literal_nat", "literal_nat_type"),
            ("string", "literal_string", "literal_string_type"),
        ] {
            checks::caller(
                spec,
                &format!("typing_cdp_{kind}_literal_embeds dp_R dp_tenv {NIL} dp_two"),
                &format!("TypingCDPCtxConvIn dp_R dp_tenv {NIL} ({literal} dp_two) {ty}"),
            );
        }
    });
}

#[test]
fn projection_typing_generation_consumes_new_whole_derivations() {
    run_with_stack(|| {
        let spec = shared_spec();
        let function = "(KExpr.const Name.anonymous (@ListType.nil Level))";
        let app = format!("(KExpr.app {function} {S0})");
        let signature = format!("(KExpr.pi {S1} cgen_projection)");
        checks::caller(spec,
            &format!("typingcdpctxconv_in_generation the_red_env cgen_tenv {NIL} {app} {S0} cgen_app_typed"),
            &format!("SemanticTypingCDPAppReturn the_red_env cgen_tenv {NIL} {function} {S0} {S0}"));
        checks::caller(spec,
            &format!("typingcdpctxconv_in_generation the_red_env cgen_tenv {NIL} {function} {signature} cgen_constant_typed"),
            &format!("SemanticTypingCDPConstantReturn the_red_env cgen_tenv Name.anonymous (@ListType.nil Level) {signature}"));
        checks::caller(spec, "cgen_actual_pi_generation",
            &format!("SemanticTypingCDPPiReturn the_red_env cgen_tenv {NIL} {S0} {S0} (KExpr.sort (Level.imax (Level.succ Level.zero) (Level.succ Level.zero)))"));
        let app_return =
            format!("SemanticTypingCDPAppReturn the_red_env cgen_tenv {NIL} {function} {S0} {S0}");
        checks::caller(spec,
            &format!("typingcdpctxconv_in_app_gen the_red_env cgen_tenv {NIL} {function} {S0} {S0} cgen_app_typed ({app_return}) (fun (A B : KExpr) (hf : TypingCDPCtxConvIn the_red_env cgen_tenv {NIL} {function} (KExpr.pi A B)) (ha : TypingCDPCtxConvIn the_red_env cgen_tenv {NIL} {S0} A) (result : DefEqCDPIn the_red_env (instantiate B {S0}) {S0}) => @SemanticTypingCDPAppReturn.intro the_red_env cgen_tenv {NIL} {function} {S0} {S0} A B hf ha result)"),
            &app_return);
    });
}

#[test]
fn projection_typing_instantiation_uses_real_conversion_and_keeps_capture() {
    run_with_stack(|| {
        let spec = shared_spec();
        let source = format!("(KExpr.app (KExpr.lam {S0} (KExpr.bvar Nat.zero)) dp_domain)");
        checks::caller(
            spec,
            "dp_cdp_instantiate_beta_projection",
            &format!("DefEqCDPIn dp_R {source} dp_nat"),
        );
        checks::caller(spec,
            &format!("def_eq_cdp_in_instantiate_congr dp_R (KExpr.app (KExpr.lam {S0} (KExpr.bvar Nat.zero)) (KExpr.bvar Nat.zero)) (KExpr.bvar Nat.zero) dp_domain dp_nat (def_eq_cdp_in_beta dp_R {S0} (KExpr.bvar Nat.zero) (KExpr.bvar Nat.zero)) (@DefEqCDPIn.symm dp_R dp_nat dp_domain dp_field1_domain_conversion)"),
            &format!("DefEqCDPIn dp_R {source} dp_nat"));
        checks::caller(
            spec,
            "dp_cdp_const_app_argument",
            &format!("TypingCDPCtxConvIn dp_R dp_tenv {NIL} dp_nat {S1}"),
        );
        checks::caller(
            spec,
            "dp_cdp_const_app_codomain",
            "DefEqCDPIn dp_R (KExpr.pi dp_nat dp_family) (KExpr.pi dp_domain dp_family)",
        );
        let input = format!(
            "instantiate (KExpr.lam {S0} (KExpr.bvar (Nat.succ Nat.zero))) (KExpr.bvar Nat.zero)"
        );
        let output = format!("KExpr.lam {S0} (KExpr.bvar (Nat.succ Nat.zero))");
        checks::computes(spec, &input, &output);
        checks::not_def_eq(
            spec,
            &output,
            &format!("KExpr.lam {S0} (KExpr.bvar Nat.zero)"),
        );
    });
}

#[test]
fn projection_typing_spines_derive_arguments_from_new_whole() {
    run_with_stack(|| {
        let spec = shared_spec();
        let arguments = format!("TypedRawPiSpineCDP dp_R dp_tenv {NIL} (kconst_type dp_ctor_signature) dp_args dp_family");
        checks::caller(
            spec,
            "dp_cdp_full_through_projection",
            &format!("TypingCDPCtxConvIn dp_R dp_tenv {NIL} dp_subject dp_family"),
        );
        checks::caller(spec,
            &format!("typingcdpctxconv_in_const_spine dp_R dp_faithful dp_cdp_const_app_rigid dp_tenv {NIL} dp_ctor_name (@ListType.nil Level) (kconst_type dp_ctor_signature) dp_args dp_family dp_family dp_ctor_lookup dp_raw_spine_run dp_cdp_full_through_projection"),
            &format!("SemanticTypedSpineCDPReturn dp_R dp_tenv {NIL} dp_ctor (kconst_type dp_ctor_signature) dp_args dp_family dp_family"));
        checks::caller(spec,
            &format!("typingcdpctxconv_in_const_spine_gen dp_R dp_faithful dp_cdp_const_app_rigid dp_tenv {NIL} dp_ctor_name (@ListType.nil Level) (kconst_type dp_ctor_signature) dp_args dp_family dp_family dp_ctor_lookup dp_raw_spine_run dp_cdp_full_through_projection ({arguments}) (fun (_head : TypingCDPCtxConvIn dp_R dp_tenv {NIL} dp_ctor (kconst_type dp_ctor_signature)) (args : {arguments}) (_convert : DefEqCDPIn dp_R dp_family dp_family) => args)"),
            &arguments);
        checks::caller(spec, "dp_cdp_partial_arguments",
            &format!("TypedRawPiSpineCDP dp_R dp_tenv {NIL} (kconst_type dp_ctor_signature) (@ListType.cons KExpr dp_nat {NIL}) (KExpr.pi dp_nat dp_family)"));
        checks::caller(
            spec,
            "dp_cdp_partial_conversion",
            "DefEqCDPIn dp_R (KExpr.pi dp_nat dp_family) (KExpr.pi dp_domain dp_family)",
        );

        let context = format!("(@ListType.cons KExpr {S2} {NIL})");
        let one_arg = format!("(@ListType.cons KExpr (KExpr.bvar Nat.zero) {NIL})");
        let identity_type = "(typed_spine_identity_type (Level.succ (Level.succ Level.zero)))";
        let residual = "(KExpr.pi (KExpr.bvar Nat.zero) (KExpr.bvar (Nat.succ Nat.zero)))";
        checks::computes(
            spec,
            &format!("raw_pi_spine {one_arg} {identity_type}"),
            &format!("@OptionType.some KExpr {residual}"),
        );
        checks::not_def_eq(
            spec,
            residual,
            "KExpr.pi (KExpr.bvar Nat.zero) (KExpr.bvar Nat.zero)",
        );
        checks::caller(spec,
            &format!("typingcdpctxconv_in_const_spine faithful_red_env faithful_red_env_faithful (ctor_metadata_rigid_empty faithful_red_env) typed_spine_identity_tenv {context} Name.anonymous (@ListType.nil Level) {identity_type} {one_arg} {residual} {residual} typed_spine_identity_lookup cdp_spine_capture_run cdp_spine_capture_whole"),
            &format!("SemanticTypedSpineCDPReturn faithful_red_env typed_spine_identity_tenv {context} (KExpr.const Name.anonymous (@ListType.nil Level)) {identity_type} {one_arg} {residual} {residual}"));
        checks::caller(spec, "cdp_spine_capture_arguments",
            &format!("TypedRawPiSpineCDP faithful_red_env typed_spine_identity_tenv {context} {identity_type} {one_arg} {residual}"));
    });
}

#[test]
fn projection_typing_old_judgments_and_no_projection_constructor() {
    run_with_stack(|| {
        let spec = shared_spec();
        checks::caller(spec, "TypingCtxConvIn.conv",
            "forall (R : RedEnv) (tenv : KDeclEnv) (G : ListType KExpr) (e A B : KExpr), TypingCtxConvIn R tenv G e A -> DefEqIn R A B -> TypingCtxConvIn R tenv G e B");
        checks::caller(spec, "TypingCDPCtxConvIn.conv",
            "forall (R : RedEnv) (tenv : KDeclEnv) (G : ListType KExpr) (e A B : KExpr), TypingCDPCtxConvIn R tenv G e A -> DefEqCDPIn R A B -> TypingCDPCtxConvIn R tenv G e B");
        checks::caller(
            spec,
            "DefEqIn.raw",
            "forall (R : RedEnv) (a b : KExpr), par_reduces_cd R a b -> DefEqIn R a b",
        );
        checks::caller(spec, "SemanticJoin.mk",
            "forall (R : RedEnv) (a b x y : KExpr), par_reduces_cd_star R a x -> par_reduces_cd_star R b y -> KExprUniverseEq x y -> SemanticJoin R a b");
        let expected = [
            "var",
            "sort",
            "pi",
            "lam",
            "app",
            "const",
            "conv",
            "let_",
            "lit_nat",
            "lit_string",
        ];
        for name in ["TypingCtxConvIn", "TypingCDPCtxConvIn"] {
            let kernel_name = Name::from_string(name);
            let metadata = spec
                .env()
                .get_inductive(&kernel_name)
                .expect("actual typing carrier");
            assert_eq!((metadata.num_params, metadata.num_indices), (2, 3));
            let constructors = expected
                .iter()
                .map(|arm| Name::from_string(&format!("{name}.{arm}")))
                .collect::<Vec<_>>();
            assert_eq!(metadata.constructor_names, constructors);
            assert_absent(spec, &format!("{name}.proj"));
            assert_absent(spec, &format!("{name}.projection"));
        }
    });
}
