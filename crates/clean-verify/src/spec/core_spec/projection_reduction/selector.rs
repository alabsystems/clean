// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Raw post-WHNF constructor-field selection and current-reduction transport.

use super::DeclarationInput;

pub(super) const DECLARATIONS: &[DeclarationInput] = &[
    DeclarationInput::Data(
        "projection_post_whnf_field",
        r"forall (R : RedEnv) (idx : Nat) (subject : KExpr), OptionType KExpr",
        r"fun (R : RedEnv) (idx : Nat) (subject : KExpr) => opt_bind Name KExpr (kexpr_const_name (kapp_fn subject)) (fun (n : Name) =>
  opt_bind KCtorMeta KExpr (kctor_for (red_ind_ctor R) n) (fun (cm : KCtorMeta) =>
   list_head (list_drop (Nat.add (kctor_num_params cm) idx) (kapp_args subject))))",
    ),
    DeclarationInput::Data(
        "projection_post_whnf_reduct",
        r"forall (R : RedEnv) (e : KExpr), OptionType KExpr",
        r"fun (R : RedEnv) (e : KExpr) => match e with
| KExpr.sort u => @OptionType.none KExpr
| KExpr.bvar i => @OptionType.none KExpr
| KExpr.app f a => @OptionType.none KExpr
| KExpr.lam A b => @OptionType.none KExpr
| KExpr.pi A B => @OptionType.none KExpr
| KExpr.const n us => @OptionType.none KExpr
| KExpr.let_ A v b => @OptionType.none KExpr
| KExpr.proj S i subject => projection_post_whnf_field R i subject
| KExpr.lit n => @OptionType.none KExpr",
    ),
    DeclarationInput::Proof(
        "projection_post_whnf_proj",
        r"forall (R : RedEnv) (S : Name) (idx : Nat) (subject : KExpr), @Eq (OptionType KExpr) (projection_post_whnf_reduct R (KExpr.proj S idx subject))
  (projection_post_whnf_field R idx subject)",
        r"fun (R : RedEnv) (S : Name) (idx : Nat) (subject : KExpr) => @Eq.refl (OptionType KExpr) (projection_post_whnf_field R idx subject)",
    ),
    DeclarationInput::Proof(
        "projection_post_whnf_field_intro",
        r"forall (R : RedEnv) (idx : Nat) (subject : KExpr)
 (n : Name) (cm : KCtorMeta) (a : KExpr)
 (head : @Eq (OptionType Name) (kexpr_const_name (kapp_fn subject)) (@OptionType.some Name n))
 (found : @Eq (OptionType KCtorMeta) (kctor_for (red_ind_ctor R) n) (@OptionType.some KCtorMeta cm))
 (selected : @Eq (OptionType KExpr)
  (list_head (list_drop (Nat.add (kctor_num_params cm) idx) (kapp_args subject))) (@OptionType.some KExpr a)), @Eq (OptionType KExpr) (projection_post_whnf_field R idx subject) (@OptionType.some KExpr a)",
        r"fun (R : RedEnv) (idx : Nat) (subject : KExpr)
 (n : Name) (cm : KCtorMeta) (a : KExpr)
 (head : @Eq (OptionType Name) (kexpr_const_name (kapp_fn subject)) (@OptionType.some Name n))
 (found : @Eq (OptionType KCtorMeta) (kctor_for (red_ind_ctor R) n) (@OptionType.some KCtorMeta cm))
 (selected : @Eq (OptionType KExpr)
  (list_head (list_drop (Nat.add (kctor_num_params cm) idx) (kapp_args subject))) (@OptionType.some KExpr a)) => opt_bind_some_intro Name KExpr (kexpr_const_name (kapp_fn subject))
  (fun (q : Name) => opt_bind KCtorMeta KExpr (kctor_for (red_ind_ctor R) q)
   (fun (qc : KCtorMeta) => list_head (list_drop (Nat.add (kctor_num_params qc) idx) (kapp_args subject)))) n a head
  (opt_bind_some_intro KCtorMeta KExpr (kctor_for (red_ind_ctor R) n)
   (fun (qc : KCtorMeta) => list_head (list_drop (Nat.add (kctor_num_params qc) idx) (kapp_args subject))) cm a found selected)",
    ),
    DeclarationInput::Proof(
        "projection_post_whnf_field_inv_type",
        r"forall (R : RedEnv) (idx : Nat) (subject a : KExpr)
 (C : Type)
 (run : @Eq (OptionType KExpr) (projection_post_whnf_field R idx subject) (@OptionType.some KExpr a))
 (next : forall (n : Name) (cm : KCtorMeta),
  @Eq (OptionType Name) (kexpr_const_name (kapp_fn subject)) (@OptionType.some Name n) ->
  @Eq (OptionType KCtorMeta) (kctor_for (red_ind_ctor R) n) (@OptionType.some KCtorMeta cm) ->
  @Eq (OptionType KExpr)
   (list_head (list_drop (Nat.add (kctor_num_params cm) idx) (kapp_args subject))) (@OptionType.some KExpr a) -> C), C",
        r"fun (R : RedEnv) (idx : Nat) (subject a : KExpr)
 (C : Type)
 (run : @Eq (OptionType KExpr) (projection_post_whnf_field R idx subject) (@OptionType.some KExpr a))
 (next : forall (n : Name) (cm : KCtorMeta),
  @Eq (OptionType Name) (kexpr_const_name (kapp_fn subject)) (@OptionType.some Name n) ->
  @Eq (OptionType KCtorMeta) (kctor_for (red_ind_ctor R) n) (@OptionType.some KCtorMeta cm) ->
  @Eq (OptionType KExpr)
   (list_head (list_drop (Nat.add (kctor_num_params cm) idx) (kapp_args subject))) (@OptionType.some KExpr a) -> C) => opt_bind_some_inv_type Name KExpr (kexpr_const_name (kapp_fn subject))
  (fun (q : Name) => opt_bind KCtorMeta KExpr (kctor_for (red_ind_ctor R) q)
   (fun (qc : KCtorMeta) => list_head (list_drop (Nat.add (kctor_num_params qc) idx) (kapp_args subject)))) a C run
  (fun (n : Name)
   (head : @Eq (OptionType Name) (kexpr_const_name (kapp_fn subject)) (@OptionType.some Name n))
   (rest : @Eq (OptionType KExpr)
    (opt_bind KCtorMeta KExpr (kctor_for (red_ind_ctor R) n)
     (fun (qc : KCtorMeta) => list_head (list_drop (Nat.add (kctor_num_params qc) idx) (kapp_args subject))))
    (@OptionType.some KExpr a)) =>
   opt_bind_some_inv_type KCtorMeta KExpr (kctor_for (red_ind_ctor R) n)
    (fun (qc : KCtorMeta) => list_head (list_drop (Nat.add (kctor_num_params qc) idx) (kapp_args subject))) a C rest
    (fun (cm : KCtorMeta)
     (found : @Eq (OptionType KCtorMeta) (kctor_for (red_ind_ctor R) n) (@OptionType.some KCtorMeta cm))
     (selected : @Eq (OptionType KExpr)
      (list_head (list_drop (Nat.add (kctor_num_params cm) idx) (kapp_args subject))) (@OptionType.some KExpr a)) =>
     next n cm head found selected))",
    ),
    DeclarationInput::Proof(
        "projection_post_whnf_transport",
        r"forall (R : RedEnv) (rigid : CtorMetadataRigid R (red_ind_ctor R))
 (S : Name) (idx : Nat) (subject subject2 : KExpr) (step : par_reduces_cd R subject subject2)
 (a : KExpr)
 (run : @Eq (OptionType KExpr) (projection_post_whnf_reduct R (KExpr.proj S idx subject)) (@OptionType.some KExpr a))
 (C : Type)
 (next : forall (b : KExpr),
  @Eq (OptionType KExpr) (projection_post_whnf_reduct R (KExpr.proj S idx subject2)) (@OptionType.some KExpr b) ->
  par_reduces_cd R a b -> C), C",
        r"fun (R : RedEnv) (rigid : CtorMetadataRigid R (red_ind_ctor R))
 (S : Name) (idx : Nat) (subject subject2 : KExpr) (step : par_reduces_cd R subject subject2)
 (a : KExpr)
 (run : @Eq (OptionType KExpr) (projection_post_whnf_reduct R (KExpr.proj S idx subject)) (@OptionType.some KExpr a))
 (C : Type)
 (next : forall (b : KExpr),
  @Eq (OptionType KExpr) (projection_post_whnf_reduct R (KExpr.proj S idx subject2)) (@OptionType.some KExpr b) ->
  par_reduces_cd R a b -> C) => projection_post_whnf_field_inv_type R idx subject a C run
  (fun (n : Name) (cm : KCtorMeta)
   (head : @Eq (OptionType Name) (kexpr_const_name (kapp_fn subject)) (@OptionType.some Name n))
   (found : @Eq (OptionType KCtorMeta) (kctor_for (red_ind_ctor R) n) (@OptionType.some KCtorMeta cm))
   (selected : @Eq (OptionType KExpr)
    (list_head (list_drop (Nat.add (kctor_num_params cm) idx) (kapp_args subject))) (@OptionType.some KExpr a)) =>
   ctor_metadata_selected_field R rigid n cm found subject subject2 step head idx a C selected
    (fun (b : KExpr) (same : @Eq KExpr (kapp_fn subject2) (kapp_fn subject))
     (selected2 : @Eq (OptionType KExpr)
      (list_head (list_drop (Nat.add (kctor_num_params cm) idx) (kapp_args subject2))) (@OptionType.some KExpr b))
     (field_step : par_reduces_cd R a b) =>
     next b
      (projection_post_whnf_field_intro R idx subject2 n cm b
       (Eq.trans (OptionType Name) (kexpr_const_name (kapp_fn subject2))
        (kexpr_const_name (kapp_fn subject)) (@OptionType.some Name n)
        (Eq.cong KExpr (OptionType Name) kexpr_const_name (kapp_fn subject2) (kapp_fn subject) same) head)
       found selected2) field_step))",
    ),
    DeclarationInput::Proof(
        "projection_post_whnf_prod_before_zero",
        r"@Eq (OptionType KExpr)
 (projection_post_whnf_reduct the_red_env (KExpr.proj kcre_prod_type_name Nat.zero ctor_spine_prod_before))
 (@OptionType.some KExpr ctor_spine_prod_redex)",
        r"@Eq.refl (OptionType KExpr) (@OptionType.some KExpr ctor_spine_prod_redex)",
    ),
    DeclarationInput::Proof(
        "projection_post_whnf_prod_after_zero",
        r"@Eq (OptionType KExpr)
 (projection_post_whnf_reduct the_red_env (KExpr.proj kcre_prod_type_name Nat.zero kcre_witness_prod_value))
 (@OptionType.some KExpr rfnz_zero)",
        r"@Eq.refl (OptionType KExpr) (@OptionType.some KExpr rfnz_zero)",
    ),
    DeclarationInput::Proof(
        "projection_post_whnf_prod_before_one",
        r"@Eq (OptionType KExpr)
 (projection_post_whnf_reduct the_red_env (KExpr.proj kcre_prod_type_name (Nat.succ Nat.zero) ctor_spine_prod_before))
 (@OptionType.some KExpr (KExpr.app rfnz_succ rfnz_zero))",
        r"@Eq.refl (OptionType KExpr) (@OptionType.some KExpr (KExpr.app rfnz_succ rfnz_zero))",
    ),
    DeclarationInput::Proof(
        "projection_post_whnf_prod_after_one",
        r"@Eq (OptionType KExpr)
 (projection_post_whnf_reduct the_red_env (KExpr.proj kcre_prod_type_name (Nat.succ Nat.zero) kcre_witness_prod_value))
 (@OptionType.some KExpr (KExpr.app rfnz_succ rfnz_zero))",
        r"@Eq.refl (OptionType KExpr) (@OptionType.some KExpr (KExpr.app rfnz_succ rfnz_zero))",
    ),
    DeclarationInput::Proof(
        "projection_post_whnf_prod_transport_zero",
        r"par_reduces_cd the_red_env ctor_spine_prod_redex rfnz_zero",
        r"projection_post_whnf_transport the_red_env reflected_ctor_metadata_rigid kcre_prod_type_name Nat.zero
  ctor_spine_prod_before kcre_witness_prod_value ctor_spine_prod_step ctor_spine_prod_redex
  projection_post_whnf_prod_before_zero (par_reduces_cd the_red_env ctor_spine_prod_redex rfnz_zero)
  (fun (b : KExpr)
   (run2 : @Eq (OptionType KExpr)
    (projection_post_whnf_reduct the_red_env (KExpr.proj kcre_prod_type_name Nat.zero kcre_witness_prod_value)) (@OptionType.some KExpr b))
   (field_step : par_reduces_cd the_red_env ctor_spine_prod_redex b) =>
   Eq.substType KExpr (fun (v : KExpr) => par_reduces_cd the_red_env ctor_spine_prod_redex v) b rfnz_zero
    (option_some_inj KExpr b rfnz_zero
     (Eq.trans (OptionType KExpr) (@OptionType.some KExpr b)
      (projection_post_whnf_reduct the_red_env (KExpr.proj kcre_prod_type_name Nat.zero kcre_witness_prod_value))
      (@OptionType.some KExpr rfnz_zero)
      (Eq.symm (OptionType KExpr)
       (projection_post_whnf_reduct the_red_env (KExpr.proj kcre_prod_type_name Nat.zero kcre_witness_prod_value))
       (@OptionType.some KExpr b) run2) projection_post_whnf_prod_after_zero)) field_step)",
    ),
    DeclarationInput::Proof(
        "projection_post_whnf_prod_transport_one",
        r"par_reduces_cd the_red_env (KExpr.app rfnz_succ rfnz_zero) (KExpr.app rfnz_succ rfnz_zero)",
        r"projection_post_whnf_transport the_red_env reflected_ctor_metadata_rigid kcre_prod_type_name (Nat.succ Nat.zero)
  ctor_spine_prod_before kcre_witness_prod_value ctor_spine_prod_step (KExpr.app rfnz_succ rfnz_zero)
  projection_post_whnf_prod_before_one (par_reduces_cd the_red_env (KExpr.app rfnz_succ rfnz_zero) (KExpr.app rfnz_succ rfnz_zero))
  (fun (b : KExpr)
   (run2 : @Eq (OptionType KExpr)
    (projection_post_whnf_reduct the_red_env (KExpr.proj kcre_prod_type_name (Nat.succ Nat.zero) kcre_witness_prod_value)) (@OptionType.some KExpr b))
   (field_step : par_reduces_cd the_red_env (KExpr.app rfnz_succ rfnz_zero) b) =>
   Eq.substType KExpr (fun (v : KExpr) => par_reduces_cd the_red_env (KExpr.app rfnz_succ rfnz_zero) v) b (KExpr.app rfnz_succ rfnz_zero)
    (option_some_inj KExpr b (KExpr.app rfnz_succ rfnz_zero)
     (Eq.trans (OptionType KExpr) (@OptionType.some KExpr b)
      (projection_post_whnf_reduct the_red_env (KExpr.proj kcre_prod_type_name (Nat.succ Nat.zero) kcre_witness_prod_value))
      (@OptionType.some KExpr (KExpr.app rfnz_succ rfnz_zero))
      (Eq.symm (OptionType KExpr)
       (projection_post_whnf_reduct the_red_env (KExpr.proj kcre_prod_type_name (Nat.succ Nat.zero) kcre_witness_prod_value))
       (@OptionType.some KExpr b) run2) projection_post_whnf_prod_after_one)) field_step)",
    ),
    DeclarationInput::Proof(
        "projection_post_whnf_missing_metadata",
        r"@Eq (OptionType KExpr)
 (projection_post_whnf_reduct (RedEnv.mk RecEnv.empty DefEnv.empty IndCtorEnv.empty)
  (KExpr.proj kcre_prod_type_name Nat.zero kcre_witness_prod_value)) (@OptionType.none KExpr)",
        r"@Eq.refl (OptionType KExpr) (@OptionType.none KExpr)",
    ),
    DeclarationInput::Proof(
        "projection_post_whnf_missing_argument",
        r"@Eq (OptionType KExpr)
 (projection_post_whnf_reduct the_red_env
  (KExpr.proj kcre_prod_type_name (Nat.succ (Nat.succ Nat.zero)) kcre_witness_prod_value)) (@OptionType.none KExpr)",
        r"@Eq.refl (OptionType KExpr) (@OptionType.none KExpr)",
    ),
    DeclarationInput::Proof(
        "projection_post_whnf_outer_app_refused",
        r"@Eq (OptionType KExpr)
 (projection_post_whnf_reduct the_red_env kcre_witness_prod_value) (@OptionType.none KExpr)",
        r"@Eq.refl (OptionType KExpr) (@OptionType.none KExpr)",
    ),
    DeclarationInput::Proof(
        "projection_post_whnf_outer_sort_refused",
        r"forall (R : RedEnv) (u : Level), @Eq (OptionType KExpr)
 (projection_post_whnf_reduct R (KExpr.sort u)) (@OptionType.none KExpr)",
        r"fun (R : RedEnv) (u : Level) => @Eq.refl (OptionType KExpr) (@OptionType.none KExpr)",
    ),
    DeclarationInput::Proof(
        "projection_post_whnf_nonconstant_head_refused",
        r"@Eq (OptionType KExpr)
 (projection_post_whnf_reduct the_red_env (KExpr.proj kcre_prod_type_name Nat.zero ctor_spine_prod_redex)) (@OptionType.none KExpr)",
        r"@Eq.refl (OptionType KExpr) (@OptionType.none KExpr)",
    ),
    DeclarationInput::Proof(
        "projection_post_whnf_struct_name_ignored",
        r"forall (R : RedEnv) (S T : Name) (idx : Nat) (subject : KExpr), @Eq (OptionType KExpr) (projection_post_whnf_reduct R (KExpr.proj S idx subject))
  (projection_post_whnf_reduct R (KExpr.proj T idx subject))",
        r"fun (R : RedEnv) (S T : Name) (idx : Nat) (subject : KExpr) => @Eq.refl (OptionType KExpr) (projection_post_whnf_field R idx subject)",
    ),
    DeclarationInput::Proof(
        "projection_post_whnf_prod_universe_arity_ignored",
        r"@Eq (OptionType KExpr)
 (projection_post_whnf_reduct the_red_env (KExpr.proj kcre_prod_type_name Nat.zero
  (apply_spine (kapp_args kcre_witness_prod_value)
   (KExpr.const kcre_prod_mk_name (@ListType.cons Level Level.zero (@ListType.nil Level))))))
 (@OptionType.some KExpr rfnz_zero)",
        r"@Eq.refl (OptionType KExpr) (@OptionType.some KExpr rfnz_zero)",
    ),
    DeclarationInput::Data(
        "projection_post_whnf_zero_fields_env",
        r"RedEnv",
        r"RedEnv.mk RecEnv.empty DefEnv.empty
 (IndCtorEnv.addCtor IndCtorEnv.empty kcre_prod_mk_name
  (KCtorMeta.mk (kctor_sig kcre_prod_ctor_meta) kcre_prod_type_name (kctor_num_params kcre_prod_ctor_meta) Nat.zero Nat.zero))",
    ),
    DeclarationInput::Proof(
        "projection_post_whnf_declared_field_count_ignored",
        r"@Eq (OptionType KExpr)
 (projection_post_whnf_reduct projection_post_whnf_zero_fields_env
  (KExpr.proj kcre_prod_type_name Nat.zero kcre_witness_prod_value)) (@OptionType.some KExpr rfnz_zero)",
        r"@Eq.refl (OptionType KExpr) (@OptionType.some KExpr rfnz_zero)",
    ),
];
