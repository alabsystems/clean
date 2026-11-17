// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Existing-fragment constructor return coherence: prod_admission.

use super::DeclarationInput;

pub(super) const DECLARATIONS: &[DeclarationInput] = &[
    DeclarationInput::Data("rpa_one", r"Nat", r"Nat.succ Nat.zero"),
    DeclarationInput::Data("rpa_two", r"Nat", r"Nat.succ rpa_one"),
    DeclarationInput::Data("rpa_three", r"Nat", r"Nat.succ rpa_two"),
    DeclarationInput::Data("rpa_four", r"Nat", r"Nat.succ rpa_three"),
    DeclarationInput::Data("rpa_u1", r"Level", r"Level.succ Level.zero"),
    DeclarationInput::Data("rpa_u2", r"Level", r"Level.succ rpa_u1"),
    DeclarationInput::Data("rpa_S", r"KExpr", r"KExpr.sort rpa_u1"),
    DeclarationInput::Data(
        "rpa_ind_ty",
        r"KExpr",
        r"kconst_type kcre_prod_type_signature",
    ),
    DeclarationInput::Data(
        "rpa_return",
        r"KExpr",
        r"KExpr.app (KExpr.app (KExpr.bvar rpa_four) (KExpr.bvar rpa_three)) (KExpr.bvar rpa_two)",
    ),
    DeclarationInput::Data(
        "rpa_y_pi",
        r"KExpr",
        r"KExpr.pi (KExpr.bvar rpa_one) rpa_return",
    ),
    DeclarationInput::Data(
        "rpa_x_pi",
        r"KExpr",
        r"KExpr.pi (KExpr.bvar rpa_one) rpa_y_pi",
    ),
    DeclarationInput::Data("rpa_b_pi", r"KExpr", r"KExpr.pi rpa_S rpa_x_pi"),
    DeclarationInput::Data("rpa_ctor_ty", r"KExpr", r"KExpr.pi rpa_S rpa_b_pi"),
    DeclarationInput::Data(
        "rpa_G0",
        r"ListType KExpr",
        r"@ListType.cons KExpr rpa_ind_ty (@ListType.nil KExpr)",
    ),
    DeclarationInput::Data(
        "rpa_G1",
        r"ListType KExpr",
        r"@ListType.cons KExpr rpa_S rpa_G0",
    ),
    DeclarationInput::Data(
        "rpa_G2",
        r"ListType KExpr",
        r"@ListType.cons KExpr rpa_S rpa_G1",
    ),
    DeclarationInput::Data(
        "rpa_G3",
        r"ListType KExpr",
        r"@ListType.cons KExpr (KExpr.bvar rpa_one) rpa_G2",
    ),
    DeclarationInput::Data(
        "rpa_G4",
        r"ListType KExpr",
        r"@ListType.cons KExpr (KExpr.bvar rpa_one) rpa_G3",
    ),
    DeclarationInput::Data("rpa_y_level", r"Level", r"Level.imax rpa_u1 rpa_u1"),
    DeclarationInput::Data("rpa_x_level", r"Level", r"Level.imax rpa_u1 rpa_y_level"),
    DeclarationInput::Data("rpa_b_level", r"Level", r"Level.imax rpa_u2 rpa_x_level"),
    DeclarationInput::Data("rpa_ctor_level", r"Level", r"Level.imax rpa_u2 rpa_b_level"),
    DeclarationInput::Data(
        "rpa_ctors",
        r"CtorDecls",
        r"CtorDecls.cons (CtorDecl.mk rpa_one rpa_ctor_ty) CtorDecls.nil",
    ),
    DeclarationInput::Data(
        "rpa_env",
        r"KEnv",
        r"KEnv.addInductive KEnv.empty Nat.zero rpa_two rpa_ind_ty rpa_ctors",
    ),
    DeclarationInput::Data(
        "rpa_source_name",
        r"forall (id : Nat), Name",
        r"fun (id : Nat) => @Nat.rec (fun (_ : Nat) => Name) kcre_prod_type_name
  (fun (j : Nat) (_ih : Name) => @Nat.rec (fun (_ : Nat) => Name) kcre_prod_mk_name
   (fun (_k : Nat) (_prev : Name) => Name.anonymous) j) id",
    ),
    DeclarationInput::Proof(
        "rpa_family_typed",
        r"Typing rpa_ind_ty (KExpr.sort (Level.imax rpa_u2 (Level.imax rpa_u2 rpa_u2)))",
        r"Typing.pi rpa_S (KExpr.pi rpa_S rpa_S) rpa_u2 (Level.imax rpa_u2 rpa_u2)
  (Typing.sort rpa_u1) (Typing.pi rpa_S rpa_S rpa_u2 rpa_u2 (Typing.sort rpa_u1) (Typing.sort rpa_u1))",
    ),
    DeclarationInput::Proof(
        "rpa_self_typed",
        r"CtxTyping rpa_G4 (KExpr.bvar rpa_four) rpa_ind_ty",
        r"CtxTyping.var rpa_G4 rpa_four rpa_ind_ty
  (CtxLookup.there (KExpr.bvar rpa_one) rpa_G3 rpa_three rpa_ind_ty
   (CtxLookup.there (KExpr.bvar rpa_one) rpa_G2 rpa_two rpa_ind_ty
    (CtxLookup.there rpa_S rpa_G1 rpa_one rpa_ind_ty
     (CtxLookup.there rpa_S rpa_G0 Nat.zero rpa_ind_ty
      (CtxLookup.here rpa_ind_ty (@ListType.nil KExpr))))))",
    ),
    DeclarationInput::Proof(
        "rpa_A_typed",
        r"CtxTyping rpa_G4 (KExpr.bvar rpa_three) rpa_S",
        r"CtxTyping.var rpa_G4 rpa_three rpa_S
  (CtxLookup.there (KExpr.bvar rpa_one) rpa_G3 rpa_two rpa_S
   (CtxLookup.there (KExpr.bvar rpa_one) rpa_G2 rpa_one rpa_S
    (CtxLookup.there rpa_S rpa_G1 Nat.zero rpa_S (CtxLookup.here rpa_S rpa_G0))))",
    ),
    DeclarationInput::Proof(
        "rpa_B_typed",
        r"CtxTyping rpa_G4 (KExpr.bvar rpa_two) rpa_S",
        r"CtxTyping.var rpa_G4 rpa_two rpa_S
  (CtxLookup.there (KExpr.bvar rpa_one) rpa_G3 rpa_one rpa_S
   (CtxLookup.there (KExpr.bvar rpa_one) rpa_G2 Nat.zero rpa_S (CtxLookup.here rpa_S rpa_G1)))",
    ),
    DeclarationInput::Proof(
        "rpa_return_typed",
        r"CtxTyping rpa_G4 rpa_return rpa_S",
        r"CtxTyping.app rpa_G4 (KExpr.app (KExpr.bvar rpa_four) (KExpr.bvar rpa_three)) (KExpr.bvar rpa_two)
  rpa_S rpa_S
  (CtxTyping.app rpa_G4 (KExpr.bvar rpa_four) (KExpr.bvar rpa_three)
   rpa_S (KExpr.pi rpa_S rpa_S) rpa_self_typed rpa_A_typed) rpa_B_typed",
    ),
    DeclarationInput::Proof(
        "rpa_x_domain_typed",
        r"CtxTyping rpa_G2 (KExpr.bvar rpa_one) rpa_S",
        r"CtxTyping.var rpa_G2 rpa_one rpa_S
  (CtxLookup.there rpa_S rpa_G1 Nat.zero rpa_S (CtxLookup.here rpa_S rpa_G0))",
    ),
    DeclarationInput::Proof(
        "rpa_y_domain_typed",
        r"CtxTyping rpa_G3 (KExpr.bvar rpa_one) rpa_S",
        r"CtxTyping.var rpa_G3 rpa_one rpa_S
  (CtxLookup.there (KExpr.bvar rpa_one) rpa_G2 Nat.zero rpa_S (CtxLookup.here rpa_S rpa_G1))",
    ),
    DeclarationInput::Proof(
        "rpa_ctor_typed",
        r"CtxTyping rpa_G0 rpa_ctor_ty (KExpr.sort rpa_ctor_level)",
        r"CtxTyping.pi rpa_G0 rpa_S rpa_b_pi rpa_u2 rpa_b_level (CtxTyping.sort rpa_G0 rpa_u1)
  (CtxTyping.pi rpa_G1 rpa_S rpa_x_pi rpa_u2 rpa_x_level (CtxTyping.sort rpa_G1 rpa_u1)
   (CtxTyping.pi rpa_G2 (KExpr.bvar rpa_one) rpa_y_pi rpa_u1 rpa_y_level rpa_x_domain_typed
    (CtxTyping.pi rpa_G3 (KExpr.bvar rpa_one) rpa_return rpa_u1 rpa_u1 rpa_y_domain_typed rpa_return_typed)))",
    ),
    DeclarationInput::Proof(
        "rpa_fields_bounded",
        r"FieldsBounded rpa_u1 rpa_G0 rpa_two rpa_ctor_ty",
        r"@FieldsBounded.param rpa_u1 rpa_G0 rpa_one rpa_S rpa_b_pi rpa_u2 (CtxTyping.sort rpa_G0 rpa_u1)
  (@FieldsBounded.param rpa_u1 rpa_G1 Nat.zero rpa_S rpa_x_pi rpa_u2 (CtxTyping.sort rpa_G1 rpa_u1)
   (@FieldsBounded.field rpa_u1 rpa_G2 (KExpr.bvar rpa_one) rpa_y_pi rpa_u1 rpa_x_domain_typed (@Eq.refl Bool Bool.true)
    (@FieldsBounded.field rpa_u1 rpa_G3 (KExpr.bvar rpa_one) rpa_return rpa_u1 rpa_y_domain_typed (@Eq.refl Bool Bool.true)
     (@FieldsBounded.done_app rpa_u1 rpa_G4 (KExpr.app (KExpr.bvar rpa_four) (KExpr.bvar rpa_three)) (KExpr.bvar rpa_two)))))",
    ),
    DeclarationInput::Proof(
        "rpa_ctors_typed",
        r"CtorsWellTyped rpa_u1 rpa_two rpa_ind_ty rpa_ctors",
        r"@CtorsWellTyped.cons rpa_u1 rpa_two rpa_ind_ty rpa_one rpa_ctor_ty rpa_ctor_level CtorDecls.nil
  rpa_ctor_typed rpa_fields_bounded (@CtorsWellTyped.nil rpa_u1 rpa_two rpa_ind_ty)",
    ),
    DeclarationInput::Proof(
        "rpa_well_formed",
        r"WellFormedCtorDecls KEnv.empty Nat.zero rpa_two rpa_ind_ty rpa_ctors",
        r"@WellFormedCtorDecls.mk KEnv.empty Nat.zero rpa_two rpa_ind_ty rpa_ctors rpa_u1
  (@Eq.refl Bool Bool.true) (@Eq.refl KExpr rpa_S) (@Eq.refl Bool Bool.true) rpa_ctors_typed",
    ),
    DeclarationInput::Proof(
        "rpa_positive",
        r"StrictlyPositiveCtorDecls rpa_ind_ty rpa_ctors",
        r"@Eq.refl Bool Bool.true",
    ),
    DeclarationInput::Proof(
        "rpa_extension",
        r"InductiveExtension KEnv.empty rpa_env",
        r"@InductiveExtension.mk KEnv.empty Nat.zero rpa_two rpa_ind_ty rpa_ctors
  (Level.imax rpa_u2 (Level.imax rpa_u2 rpa_u2)) (@Eq.refl Bool Bool.true)
  rpa_family_typed rpa_positive rpa_well_formed",
    ),
    DeclarationInput::Proof(
        "rpa_env_sound",
        r"EnvSound rpa_env",
        r"DefinitionalExtension.inductive_ KEnv.empty rpa_env rpa_extension",
    ),
    DeclarationInput::Proof(
        "rpa_uniform_from_admission",
        r"@Eq Bool (return_args_wf_from (count_pi rpa_ctor_ty) rpa_two (return_type rpa_ctor_ty)) Bool.true",
        r"ac_sound_last_inductive_selected KEnv.empty Nat.zero rpa_two rpa_ind_ty rpa_ctors rpa_env_sound
  Nat.zero rpa_one rpa_ctor_ty (@Eq.refl (OptionType CtorDecl) (@OptionType.some CtorDecl (CtorDecl.mk rpa_one rpa_ctor_ty)))",
    ),
    DeclarationInput::Proof(
        "rpa_family_name",
        r"@Eq Name (rpa_source_name Nat.zero) kcre_prod_type_name",
        r"@Eq.refl Name kcre_prod_type_name",
    ),
    DeclarationInput::Proof(
        "rpa_ctor_name",
        r"@Eq Name (rpa_source_name rpa_one) kcre_prod_mk_name",
        r"@Eq.refl Name kcre_prod_mk_name",
    ),
    DeclarationInput::Proof(
        "rpa_names_distinct",
        r"@Eq Bool (name_eqb (rpa_source_name Nat.zero) (rpa_source_name rpa_one)) Bool.false",
        r"@Eq.refl Bool Bool.false",
    ),
    DeclarationInput::Proof(
        "rpa_family_signature",
        r"@Eq KConstSig
  (KConstSig.mk (@ListType.nil Name) rpa_ind_ty) kcre_prod_type_signature",
        r"@Eq.refl KConstSig kcre_prod_type_signature",
    ),
    DeclarationInput::Proof(
        "rpa_close_self",
        r"@Eq KExpr
  (instantiate rpa_ctor_ty (KExpr.const (rpa_source_name Nat.zero) (@ListType.nil Level)))
  (kconst_type kcre_prod_mk_signature)",
        r"@Eq.refl KExpr (kconst_type kcre_prod_mk_signature)",
    ),
    DeclarationInput::Proof(
        "rpa_ctor_signature",
        r"@Eq KConstSig
  (KConstSig.mk (@ListType.nil Name) (instantiate rpa_ctor_ty (KExpr.const (rpa_source_name Nat.zero) (@ListType.nil Level))))
  (kctor_sig kcre_prod_ctor_meta)",
        r"@Eq.refl KConstSig (kctor_sig kcre_prod_ctor_meta)",
    ),
    DeclarationInput::Proof(
        "rpa_family_metadata",
        r"@Eq KIndMeta kcre_prod_ind_meta
  (KIndMeta.mk kcre_prod_type_signature rpa_two Nat.zero (@ListType.cons Name (rpa_source_name rpa_one) (@ListType.nil Name))
   (@ListType.cons Name (rpa_source_name Nat.zero) (@ListType.nil Name)))",
        r"@Eq.refl KIndMeta kcre_prod_ind_meta",
    ),
    DeclarationInput::Proof(
        "rpa_ctor_metadata",
        r"@Eq KCtorMeta kcre_prod_ctor_meta
  (KCtorMeta.mk kcre_prod_mk_signature (rpa_source_name Nat.zero) rpa_two rpa_two Nat.zero)",
        r"@Eq.refl KCtorMeta kcre_prod_ctor_meta",
    ),
    DeclarationInput::Proof(
        "rpa_family_lookup",
        r"@Eq (OptionType KIndMeta)
  (kind_for kcre_ind_ctor_env (rpa_source_name Nat.zero)) (@OptionType.some KIndMeta kcre_prod_ind_meta)",
        r"@Eq.refl (OptionType KIndMeta) (@OptionType.some KIndMeta kcre_prod_ind_meta)",
    ),
    DeclarationInput::Proof(
        "rpa_ctor_lookup",
        r"@Eq (OptionType KCtorMeta)
  (kctor_for kcre_ind_ctor_env (rpa_source_name rpa_one)) (@OptionType.some KCtorMeta kcre_prod_ctor_meta)",
        r"@Eq.refl (OptionType KCtorMeta) (@OptionType.some KCtorMeta kcre_prod_ctor_meta)",
    ),
    DeclarationInput::Proof(
        "rpa_family_decl_lookup",
        r"@Eq (OptionType KConstSig)
  (kcre_ind_ctor_tenv (rpa_source_name Nat.zero)) (@OptionType.some KConstSig kcre_prod_type_signature)",
        r"@Eq.refl (OptionType KConstSig) (@OptionType.some KConstSig kcre_prod_type_signature)",
    ),
    DeclarationInput::Proof(
        "rpa_ctor_decl_lookup",
        r"@Eq (OptionType KConstSig)
  (kcre_ind_ctor_tenv (rpa_source_name rpa_one)) (@OptionType.some KConstSig kcre_prod_mk_signature)",
        r"@Eq.refl (OptionType KConstSig) (@OptionType.some KConstSig kcre_prod_mk_signature)",
    ),
    DeclarationInput::Proof(
        "rpa_connected_admission",
        r"forall (C : Type)
 (consume : EnvSound rpa_env ->
  @Eq Bool (return_args_wf_from (count_pi rpa_ctor_ty) rpa_two (return_type rpa_ctor_ty)) Bool.true ->
  @Eq KConstSig (KConstSig.mk (@ListType.nil Name) (instantiate rpa_ctor_ty (KExpr.const (rpa_source_name Nat.zero) (@ListType.nil Level)))) (kctor_sig kcre_prod_ctor_meta) ->
  @Eq (OptionType KCtorMeta) (kctor_for kcre_ind_ctor_env (rpa_source_name rpa_one)) (@OptionType.some KCtorMeta kcre_prod_ctor_meta) -> C), C",
        r"fun (C : Type)
 (consume : EnvSound rpa_env ->
  @Eq Bool (return_args_wf_from (count_pi rpa_ctor_ty) rpa_two (return_type rpa_ctor_ty)) Bool.true ->
  @Eq KConstSig (KConstSig.mk (@ListType.nil Name) (instantiate rpa_ctor_ty (KExpr.const (rpa_source_name Nat.zero) (@ListType.nil Level)))) (kctor_sig kcre_prod_ctor_meta) ->
  @Eq (OptionType KCtorMeta) (kctor_for kcre_ind_ctor_env (rpa_source_name rpa_one)) (@OptionType.some KCtorMeta kcre_prod_ctor_meta) -> C) => consume rpa_env_sound rpa_uniform_from_admission rpa_ctor_signature rpa_ctor_lookup",
    ),
];

#[cfg(test)]
pub(super) const NEGATIVE_CONTROLS: &[(&str, &str, &str)] = &[
    (
        "rpa_bad_admission_parameter_count",
        r"WellFormedCtorDecls KEnv.empty Nat.zero rpa_one rpa_ind_ty rpa_ctors",
        r"rpa_well_formed",
    ),
    (
        "rpa_bad_self_substitution_target",
        r"@Eq KExpr
  (instantiate rpa_ctor_ty (KExpr.const (rpa_source_name rpa_one) (@ListType.nil Level)))
  (kconst_type kcre_prod_mk_signature)",
        r"rpa_close_self",
    ),
    (
        "rpa_bad_metadata_field_count",
        r"@Eq KCtorMeta kcre_prod_ctor_meta
  (KCtorMeta.mk kcre_prod_mk_signature (rpa_source_name Nat.zero) rpa_two rpa_one Nat.zero)",
        r"rpa_ctor_metadata",
    ),
];

#[cfg(test)]
pub(super) const PROOF_ROOTS: &[&str] = &[
    "rpa_family_typed",
    "rpa_self_typed",
    "rpa_A_typed",
    "rpa_B_typed",
    "rpa_return_typed",
    "rpa_x_domain_typed",
    "rpa_y_domain_typed",
    "rpa_ctor_typed",
    "rpa_fields_bounded",
    "rpa_ctors_typed",
    "rpa_well_formed",
    "rpa_positive",
    "rpa_extension",
    "rpa_env_sound",
    "rpa_uniform_from_admission",
    "rpa_family_name",
    "rpa_ctor_name",
    "rpa_names_distinct",
    "rpa_family_signature",
    "rpa_close_self",
    "rpa_ctor_signature",
    "rpa_family_metadata",
    "rpa_ctor_metadata",
    "rpa_family_lookup",
    "rpa_ctor_lookup",
    "rpa_family_decl_lookup",
    "rpa_ctor_decl_lookup",
    "rpa_connected_admission",
];

#[cfg(test)]
pub(super) const DATA_NAMES: &[&str] = &[
    "rpa_one",
    "rpa_two",
    "rpa_three",
    "rpa_four",
    "rpa_u1",
    "rpa_u2",
    "rpa_S",
    "rpa_ind_ty",
    "rpa_return",
    "rpa_y_pi",
    "rpa_x_pi",
    "rpa_b_pi",
    "rpa_ctor_ty",
    "rpa_G0",
    "rpa_G1",
    "rpa_G2",
    "rpa_G3",
    "rpa_G4",
    "rpa_y_level",
    "rpa_x_level",
    "rpa_b_level",
    "rpa_ctor_level",
    "rpa_ctors",
    "rpa_env",
    "rpa_source_name",
];

#[cfg(test)]
pub(super) const INDUCTIVE_NAMES: &[&str] = &[];

#[cfg(test)]
pub(super) const PROP_PROOF_ROOTS: &[&str] = &[
    "rpa_positive",
    "rpa_uniform_from_admission",
    "rpa_family_name",
    "rpa_ctor_name",
    "rpa_names_distinct",
    "rpa_family_signature",
    "rpa_close_self",
    "rpa_ctor_signature",
    "rpa_family_metadata",
    "rpa_ctor_metadata",
    "rpa_family_lookup",
    "rpa_ctor_lookup",
    "rpa_family_decl_lookup",
    "rpa_ctor_decl_lookup",
];

#[cfg(test)]
pub(super) const TYPE_PROOF_ROOTS: &[&str] = &[
    "rpa_family_typed",
    "rpa_self_typed",
    "rpa_A_typed",
    "rpa_B_typed",
    "rpa_return_typed",
    "rpa_x_domain_typed",
    "rpa_y_domain_typed",
    "rpa_ctor_typed",
    "rpa_fields_bounded",
    "rpa_ctors_typed",
    "rpa_well_formed",
    "rpa_extension",
    "rpa_env_sound",
    "rpa_connected_admission",
];
