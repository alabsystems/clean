// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Additive projection typing prerequisites: domain.

use super::DeclarationInput;

pub(super) const DECLARATIONS: &[DeclarationInput] = &[
    DeclarationInput::Data("dp_one", r"Nat", r"Nat.succ Nat.zero"),
    DeclarationInput::Data("dp_two", r"Nat", r"Nat.succ dp_one"),
    DeclarationInput::Data("dp_family_name", r"Name", r"Name.anonymous"),
    DeclarationInput::Data(
        "dp_ctor_name",
        r"Name",
        r"Name.str (Name.str Name.anonymous Nat.zero) Nat.zero",
    ),
    DeclarationInput::Data(
        "dp_nat_name",
        r"Name",
        r"Name.str (Name.str Name.anonymous Nat.zero) dp_one",
    ),
    DeclarationInput::Data(
        "dp_zero_name",
        r"Name",
        r"Name.str (Name.str Name.anonymous Nat.zero) dp_two",
    ),
    DeclarationInput::Data(
        "dp_family",
        r"KExpr",
        r"KExpr.const dp_family_name (@ListType.nil Level)",
    ),
    DeclarationInput::Data(
        "dp_nat",
        r"KExpr",
        r"KExpr.const dp_nat_name (@ListType.nil Level)",
    ),
    DeclarationInput::Data(
        "dp_zero",
        r"KExpr",
        r"KExpr.const dp_zero_name (@ListType.nil Level)",
    ),
    DeclarationInput::Data(
        "dp_ctor",
        r"KExpr",
        r"KExpr.const dp_ctor_name (@ListType.nil Level)",
    ),
    DeclarationInput::Data(
        "dp_family_signature",
        r"KConstSig",
        r"KConstSig.mk (@ListType.nil Name) (KExpr.sort (Level.succ (Level.succ Level.zero)))",
    ),
    DeclarationInput::Data(
        "dp_ctor_signature",
        r"KConstSig",
        r"projection_fixture_dep_pair",
    ),
    DeclarationInput::Data(
        "dp_ind_meta",
        r"KIndMeta",
        r"KIndMeta.mk dp_family_signature Nat.zero Nat.zero (@ListType.cons Name dp_ctor_name (@ListType.nil Name)) (@ListType.cons Name dp_family_name (@ListType.nil Name))",
    ),
    DeclarationInput::Data(
        "dp_ctor_meta",
        r"KCtorMeta",
        r"KCtorMeta.mk dp_ctor_signature dp_family_name Nat.zero dp_two Nat.zero",
    ),
    DeclarationInput::Data(
        "dp_metadata",
        r"IndCtorEnv",
        r"IndCtorEnv.addCtor (IndCtorEnv.addInd IndCtorEnv.empty dp_family_name dp_ind_meta) dp_ctor_name dp_ctor_meta",
    ),
    DeclarationInput::Data(
        "dp_R",
        r"RedEnv",
        r"RedEnv.mk faithful_rec_env faithful_def_env dp_metadata",
    ),
    DeclarationInput::Data(
        "dp_tenv",
        r"forall (n : Name), OptionType KConstSig",
        r"fun (n : Name) => @Bool.rec (fun (_ : Bool) => OptionType KConstSig)
  (@Bool.rec (fun (_ : Bool) => OptionType KConstSig)
   (@Bool.rec (fun (_ : Bool) => OptionType KConstSig)
    (@Bool.rec (fun (_ : Bool) => OptionType KConstSig)
     (@OptionType.none KConstSig) (@OptionType.some KConstSig dp_ctor_signature) (name_eqb n dp_ctor_name))
    (@OptionType.some KConstSig (KConstSig.mk (@ListType.nil Name) dp_nat)) (name_eqb n dp_zero_name))
   (@OptionType.some KConstSig (KConstSig.mk (@ListType.nil Name) (KExpr.sort (Level.succ Level.zero)))) (name_eqb n dp_nat_name))
  (@OptionType.some KConstSig dp_family_signature) (name_eqb n dp_family_name)",
    ),
    DeclarationInput::Data(
        "dp_args",
        r"ListType KExpr",
        r"@ListType.cons KExpr dp_nat (@ListType.cons KExpr dp_zero (@ListType.nil KExpr))",
    ),
    DeclarationInput::Data("dp_subject", r"KExpr", r"apply_spine dp_args dp_ctor"),
    DeclarationInput::Data(
        "dp_domain",
        r"KExpr",
        r"KExpr.proj dp_family_name Nat.zero dp_subject",
    ),
    DeclarationInput::Data(
        "dp_result",
        r"ProjectionMetadataResult",
        r"ProjectionMetadataResult.mk dp_family dp_ind_meta dp_ctor_name dp_ctor_meta (kconst_type dp_ctor_signature)",
    ),
    DeclarationInput::Data(
        "dp_inferred_field1",
        r"OptionType KExpr",
        r"opt_bind (ListType KExpr) KExpr
 (projection_field_prefix dp_R dp_one dp_family_name dp_subject dp_two Nat.zero (projection_meta_start dp_result))
 (fun (domains : ListType KExpr) => list_head (list_drop dp_one domains))",
    ),
    DeclarationInput::Proof(
        "dp_disjoint",
        r"RecEnvDefEnvDisjoint dp_R",
        r"@RecEnvDefEnvDisjoint.rec faithful_red_env
  (fun (_ : RecEnvDefEnvDisjoint faithful_red_env) => RecEnvDefEnvDisjoint dp_R)
  (fun (h : forall (n : Name) (v : KExpr), @Eq (OptionType KExpr) (defval_for (red_def faithful_red_env) n) (@OptionType.some KExpr v) -> @Eq (OptionType RecMeta) (recmeta_for (red_rec faithful_red_env) n) (@OptionType.none RecMeta)) => @RecEnvDefEnvDisjoint.mk dp_R h)
  faithful_red_env_defenv_disjoint",
    ),
    DeclarationInput::Proof(
        "dp_ctor_no_def",
        r"RecEnvCtorNoDefVal dp_R",
        r"@RecEnvCtorNoDefVal.rec faithful_red_env
  (fun (_ : RecEnvCtorNoDefVal faithful_red_env) => RecEnvCtorNoDefVal dp_R)
  (fun (h : forall (rn cn : Name) (rule : RecRule) (e : KExpr), @Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (@OptionType.some Name cn) -> @Eq (OptionType RecRule) (recrule_for (red_rec faithful_red_env) rn cn) (@OptionType.some RecRule rule) -> @Eq (OptionType KExpr) (defval_for (red_def faithful_red_env) cn) (@OptionType.none KExpr)) => @RecEnvCtorNoDefVal.mk dp_R h)
  faithful_red_env_ctor_no_defval",
    ),
    DeclarationInput::Proof(
        "dp_faithful",
        r"RedEnvFaithful dp_R",
        r"@RedEnvFaithful.mk dp_R
 faithful_red_env_reduct_not_redex faithful_rec_env_ctor_no_recmeta
 faithful_rec_env_closed faithful_rec_env_lift_closed faithful_def_env_closed faithful_def_env_lift_closed dp_disjoint dp_ctor_no_def",
    ),
    DeclarationInput::Proof(
        "dp_resolve_run",
        r"@Eq (OptionType ProjectionMetadataResult)
 (projection_resolve dp_R dp_one dp_family_name dp_one dp_family)
 (@OptionType.some ProjectionMetadataResult dp_result)",
        r"@Eq.refl (OptionType ProjectionMetadataResult) (@OptionType.some ProjectionMetadataResult dp_result)",
    ),
    DeclarationInput::Proof(
        "dp_resolution",
        r"ProjectionResolution dp_R dp_one dp_family_name dp_one dp_family dp_result",
        r"projection_resolve_trace dp_R dp_one dp_family_name dp_one dp_family dp_result dp_resolve_run",
    ),
    DeclarationInput::Proof(
        "dp_agreement",
        r"ProjectionMetadataAgreement dp_tenv dp_family_name dp_result",
        r"@ProjectionMetadataAgreement.mk dp_tenv dp_family_name dp_result
 (@Eq.refl (OptionType KConstSig) (@OptionType.some KConstSig dp_family_signature))
 (@Eq.refl (OptionType KConstSig) (@OptionType.some KConstSig dp_ctor_signature))
 (@Eq.refl (ListType Name) (@ListType.nil Name)) (@Eq.refl Name dp_family_name)
 (@Eq.refl Nat Nat.zero) (@Eq.refl Nat Nat.zero)",
    ),
    DeclarationInput::Proof(
        "dp_ctor_lookup",
        r"@Eq (OptionType KExpr) (kdecl_type_at dp_tenv dp_ctor_name (@ListType.nil Level)) (@OptionType.some KExpr (kconst_type dp_ctor_signature))",
        r"projection_metadata_ctor_lookup dp_R dp_one dp_tenv dp_family_name dp_result dp_agreement
  (projection_resolution_telescope dp_R dp_one dp_family_name dp_one dp_family dp_result dp_resolution)",
    ),
    DeclarationInput::Proof(
        "dp_field_domains",
        r"@Eq (OptionType (ListType KExpr))
 (projection_field_prefix dp_R dp_one dp_family_name dp_subject dp_two Nat.zero (projection_meta_start dp_result))
 (@OptionType.some (ListType KExpr) (@ListType.cons KExpr (KExpr.sort (Level.succ Level.zero)) (@ListType.cons KExpr dp_domain (@ListType.nil KExpr))))",
        r"@Eq.refl (OptionType (ListType KExpr)) (@OptionType.some (ListType KExpr) (@ListType.cons KExpr (KExpr.sort (Level.succ Level.zero)) (@ListType.cons KExpr dp_domain (@ListType.nil KExpr))))",
    ),
    DeclarationInput::Proof(
        "dp_raw_spine_run",
        r"@Eq (OptionType KExpr) (raw_pi_spine dp_args (projection_meta_ctor_type dp_result)) (@OptionType.some KExpr dp_family)",
        r"@Eq.refl (OptionType KExpr) (@OptionType.some KExpr dp_family)",
    ),
    DeclarationInput::Proof(
        "dp_raw_field1_prefix",
        r"@Eq (OptionType KExpr) (raw_pi_spine (list_take dp_one dp_args) (projection_meta_ctor_type dp_result)) (@OptionType.some KExpr (KExpr.pi dp_nat dp_family))",
        r"@Eq.refl (OptionType KExpr) (@OptionType.some KExpr (KExpr.pi dp_nat dp_family))",
    ),
    DeclarationInput::Proof(
        "dp_selected_field1",
        r"@Eq (OptionType KExpr) (list_head (list_drop dp_one dp_args)) (@OptionType.some KExpr dp_zero)",
        r"@Eq.refl (OptionType KExpr) (@OptionType.some KExpr dp_zero)",
    ),
    DeclarationInput::Proof(
        "dp_select_field0",
        r"@Eq (OptionType KExpr) (projection_post_whnf_reduct dp_R dp_domain) (@OptionType.some KExpr dp_nat)",
        r"@Eq.refl (OptionType KExpr) (@OptionType.some KExpr dp_nat)",
    ),
    DeclarationInput::Proof(
        "dp_select_field1",
        r"@Eq (OptionType KExpr) (projection_post_whnf_reduct dp_R (KExpr.proj dp_family_name dp_one dp_subject)) (@OptionType.some KExpr dp_zero)",
        r"@Eq.refl (OptionType KExpr) (@OptionType.some KExpr dp_zero)",
    ),
    DeclarationInput::Proof(
        "dp_field1_domain_conversion",
        r"DefEqCDPIn dp_R dp_nat dp_domain",
        r"@DefEqCDPIn.symm dp_R dp_domain dp_nat
  (@DefEqCDPIn.raw dp_R dp_domain dp_nat
   (@par_reduces_cdp.projection_beta dp_R dp_family_name Nat.zero dp_subject dp_nat dp_select_field0))",
    ),
    DeclarationInput::Proof(
        "dp_whole_spine",
        r"forall (T : KExpr)
 (whole : TypingCtxConvIn dp_R dp_tenv (@ListType.nil KExpr) dp_subject T), SemanticTypedSpineReturn dp_R dp_tenv (@ListType.nil KExpr) dp_ctor (projection_meta_ctor_type dp_result) dp_args dp_family T",
        r"fun (T : KExpr)
 (whole : TypingCtxConvIn dp_R dp_tenv (@ListType.nil KExpr) dp_subject T) => projection_resolved_ctor_spine dp_R dp_faithful dp_tenv (@ListType.nil KExpr) dp_one dp_family_name dp_one dp_family dp_result
 dp_resolution dp_agreement dp_args dp_family T dp_raw_spine_run whole",
    ),
    DeclarationInput::Proof(
        "dp_field1_from_whole",
        r"forall (T : KExpr)
 (whole : TypingCtxConvIn dp_R dp_tenv (@ListType.nil KExpr) dp_subject T)
 (C : Type) (consume : TypingCtxConvIn dp_R dp_tenv (@ListType.nil KExpr) dp_zero dp_nat -> DefEqCDPIn dp_R dp_nat dp_domain -> C), C",
        r"fun (T : KExpr)
 (whole : TypingCtxConvIn dp_R dp_tenv (@ListType.nil KExpr) dp_subject T)
 (C : Type) (consume : TypingCtxConvIn dp_R dp_tenv (@ListType.nil KExpr) dp_zero dp_nat -> DefEqCDPIn dp_R dp_nat dp_domain -> C) => consume
  (semantic_typed_spine_select_at dp_R dp_tenv (@ListType.nil KExpr) dp_ctor (projection_meta_ctor_type dp_result) dp_args dp_family T
   (dp_whole_spine T whole) dp_one dp_zero dp_nat dp_family dp_selected_field1 dp_raw_field1_prefix)
  dp_field1_domain_conversion",
    ),
    DeclarationInput::Proof(
        "dp_actual_whole",
        r"TypingCtxConvIn dp_R dp_tenv (@ListType.nil KExpr) dp_subject dp_family",
        r"@TypingCtxConvIn.app dp_R dp_tenv (@ListType.nil KExpr) (KExpr.app dp_ctor dp_nat) dp_zero dp_nat dp_family
  (@TypingCtxConvIn.app dp_R dp_tenv (@ListType.nil KExpr) dp_ctor dp_nat (KExpr.sort (Level.succ Level.zero)) (KExpr.pi (KExpr.bvar Nat.zero) dp_family)
   (@TypingCtxConvIn.const dp_R dp_tenv (@ListType.nil KExpr) dp_ctor_name (@ListType.nil Level) (kconst_type dp_ctor_signature) dp_ctor_lookup)
   (@TypingCtxConvIn.const dp_R dp_tenv (@ListType.nil KExpr) dp_nat_name (@ListType.nil Level) (KExpr.sort (Level.succ Level.zero)) (@Eq.refl (OptionType KExpr) (@OptionType.some KExpr (KExpr.sort (Level.succ Level.zero))))))
  (@TypingCtxConvIn.const dp_R dp_tenv (@ListType.nil KExpr) dp_zero_name (@ListType.nil Level) dp_nat (@Eq.refl (OptionType KExpr) (@OptionType.some KExpr dp_nat)))",
    ),
    DeclarationInput::Proof(
        "dp_actual_selected",
        r"TypingCtxConvIn dp_R dp_tenv (@ListType.nil KExpr) dp_zero dp_nat",
        r"dp_field1_from_whole dp_family dp_actual_whole (TypingCtxConvIn dp_R dp_tenv (@ListType.nil KExpr) dp_zero dp_nat)
  (fun (typed : TypingCtxConvIn dp_R dp_tenv (@ListType.nil KExpr) dp_zero dp_nat) (_converted : DefEqCDPIn dp_R dp_nat dp_domain) => typed)",
    ),
    DeclarationInput::Proof(
        "dp_actual_domain_conversion",
        r"DefEqCDPIn dp_R dp_nat dp_domain",
        r"dp_field1_from_whole dp_family dp_actual_whole (DefEqCDPIn dp_R dp_nat dp_domain)
  (fun (_typed : TypingCtxConvIn dp_R dp_tenv (@ListType.nil KExpr) dp_zero dp_nat) (converted : DefEqCDPIn dp_R dp_nat dp_domain) => converted)",
    ),
    DeclarationInput::Proof(
        "dp_invalid_field_refused",
        r"@Eq (OptionType ProjectionMetadataResult) (projection_resolve dp_R dp_one dp_family_name dp_two dp_family) (@OptionType.none ProjectionMetadataResult)",
        r"@Eq.refl (OptionType ProjectionMetadataResult) (@OptionType.none ProjectionMetadataResult)",
    ),
    DeclarationInput::Proof(
        "dp_wrong_family_refused",
        r"@Eq (OptionType ProjectionMetadataResult) (projection_resolve dp_R dp_one dp_nat_name dp_one dp_family) (@OptionType.none ProjectionMetadataResult)",
        r"@Eq.refl (OptionType ProjectionMetadataResult) (@OptionType.none ProjectionMetadataResult)",
    ),
    DeclarationInput::Proof(
        "dp_inferred_field1_run",
        r"@Eq (OptionType KExpr) dp_inferred_field1 (@OptionType.some KExpr dp_domain)",
        r"Eq.cong (OptionType (ListType KExpr)) (OptionType KExpr)
  (fun (fields : OptionType (ListType KExpr)) => opt_bind (ListType KExpr) KExpr fields
   (fun (domains : ListType KExpr) => list_head (list_drop dp_one domains)))
  (projection_field_prefix dp_R dp_one dp_family_name dp_subject dp_two Nat.zero (projection_meta_start dp_result))
  (@OptionType.some (ListType KExpr) (@ListType.cons KExpr (KExpr.sort (Level.succ Level.zero)) (@ListType.cons KExpr dp_domain (@ListType.nil KExpr)))) dp_field_domains",
    ),
    DeclarationInput::Proof(
        "dp_field1_connected",
        r"forall (T D : KExpr)
 (whole : TypingCtxConvIn dp_R dp_tenv (@ListType.nil KExpr) dp_subject T)
 (domain_run : @Eq (OptionType KExpr) dp_inferred_field1 (@OptionType.some KExpr D))
 (C : Type) (consume : TypingCtxConvIn dp_R dp_tenv (@ListType.nil KExpr) dp_zero dp_nat -> DefEqCDPIn dp_R dp_nat D -> C), C",
        r"fun (T D : KExpr)
 (whole : TypingCtxConvIn dp_R dp_tenv (@ListType.nil KExpr) dp_subject T)
 (domain_run : @Eq (OptionType KExpr) dp_inferred_field1 (@OptionType.some KExpr D))
 (C : Type) (consume : TypingCtxConvIn dp_R dp_tenv (@ListType.nil KExpr) dp_zero dp_nat -> DefEqCDPIn dp_R dp_nat D -> C) => dp_field1_from_whole T whole C
  (fun (selected : TypingCtxConvIn dp_R dp_tenv (@ListType.nil KExpr) dp_zero dp_nat)
   (converted : DefEqCDPIn dp_R dp_nat dp_domain) => consume selected
   (Eq.substType KExpr (fun (target : KExpr) => DefEqCDPIn dp_R dp_nat target) dp_domain D
    (Eq.symm KExpr D dp_domain (option_some_inj KExpr D dp_domain
     (Eq.trans (OptionType KExpr) (@OptionType.some KExpr D) dp_inferred_field1 (@OptionType.some KExpr dp_domain)
      (Eq.symm (OptionType KExpr) dp_inferred_field1 (@OptionType.some KExpr D) domain_run) dp_inferred_field1_run))) converted))",
    ),
    DeclarationInput::Proof(
        "dp_actual_connected",
        r"forall (C : Type)
 (consume : TypingCtxConvIn dp_R dp_tenv (@ListType.nil KExpr) dp_zero dp_nat -> DefEqCDPIn dp_R dp_nat dp_domain -> C), C",
        r"fun (C : Type)
 (consume : TypingCtxConvIn dp_R dp_tenv (@ListType.nil KExpr) dp_zero dp_nat -> DefEqCDPIn dp_R dp_nat dp_domain -> C) => dp_field1_connected dp_family dp_domain dp_actual_whole dp_inferred_field1_run C consume",
    ),
];

#[cfg(test)]
pub(super) const NEGATIVE_CONTROLS: &[(&str, &str, &str)] = &[
    (
        "dp_reject_raw_domain",
        r"@Eq KExpr dp_nat dp_domain",
        r"@Eq.refl KExpr dp_nat",
    ),
    (
        "dp_reject_wrong_selected_field",
        r"@Eq (OptionType KExpr)
 (projection_post_whnf_reduct dp_R (KExpr.proj dp_family_name dp_one dp_subject))
 (@OptionType.some KExpr dp_nat)",
        r"@Eq.refl (OptionType KExpr) (@OptionType.some KExpr dp_nat)",
    ),
    (
        "dp_reject_invalid_field_success",
        r"@Eq (OptionType ProjectionMetadataResult)
 (projection_resolve dp_R dp_one dp_family_name dp_two dp_family)
 (@OptionType.some ProjectionMetadataResult dp_result)",
        r"@Eq.refl (OptionType ProjectionMetadataResult) (@OptionType.some ProjectionMetadataResult dp_result)",
    ),
    (
        "dp_reject_old_conversion_cast",
        r"DefEqIn dp_R dp_nat dp_domain",
        r"dp_field1_domain_conversion",
    ),
];

#[cfg(test)]
pub(super) const PROOF_ROOTS: &[&str] = &[
    "dp_disjoint",
    "dp_ctor_no_def",
    "dp_faithful",
    "dp_resolve_run",
    "dp_resolution",
    "dp_agreement",
    "dp_ctor_lookup",
    "dp_field_domains",
    "dp_raw_spine_run",
    "dp_raw_field1_prefix",
    "dp_selected_field1",
    "dp_select_field0",
    "dp_select_field1",
    "dp_field1_domain_conversion",
    "dp_whole_spine",
    "dp_field1_from_whole",
    "dp_actual_whole",
    "dp_actual_selected",
    "dp_actual_domain_conversion",
    "dp_invalid_field_refused",
    "dp_wrong_family_refused",
    "dp_inferred_field1_run",
    "dp_field1_connected",
    "dp_actual_connected",
];

#[cfg(test)]
pub(super) const DATA_NAMES: &[&str] = &[
    "dp_one",
    "dp_two",
    "dp_family_name",
    "dp_ctor_name",
    "dp_nat_name",
    "dp_zero_name",
    "dp_family",
    "dp_nat",
    "dp_zero",
    "dp_ctor",
    "dp_family_signature",
    "dp_ctor_signature",
    "dp_ind_meta",
    "dp_ctor_meta",
    "dp_metadata",
    "dp_R",
    "dp_tenv",
    "dp_args",
    "dp_subject",
    "dp_domain",
    "dp_result",
    "dp_inferred_field1",
];

#[cfg(test)]
pub(super) const INDUCTIVE_NAMES: &[&str] = &[];
