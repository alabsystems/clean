// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Semantic-universe compatibility of actual raw field selection.

use super::DeclarationInput;

pub(super) const DECLARATIONS: &[DeclarationInput] = &[
    DeclarationInput::Proof(
        "projection_post_whnf_universe_compat",
        r"forall (R : RedEnv) (S : Name) (idx : Nat)
 (subject subject2 : KExpr) (related : KExprUniverseEq subject subject2) (a : KExpr)
 (run : Eq (OptionType KExpr) (projection_post_whnf_reduct R (KExpr.proj S idx subject)) (OptionType.some KExpr a))
 (C : Type)
 (next : forall (b : KExpr),
  Eq (OptionType KExpr) (projection_post_whnf_reduct R (KExpr.proj S idx subject2)) (OptionType.some KExpr b) ->
  KExprUniverseEq a b -> C), C",
        r"fun (R : RedEnv) (S : Name) (idx : Nat)
 (subject subject2 : KExpr) (related : KExprUniverseEq subject subject2) (a : KExpr)
 (run : Eq (OptionType KExpr) (projection_post_whnf_reduct R (KExpr.proj S idx subject)) (OptionType.some KExpr a))
 (C : Type)
 (next : forall (b : KExpr),
  Eq (OptionType KExpr) (projection_post_whnf_reduct R (KExpr.proj S idx subject2)) (OptionType.some KExpr b) ->
  KExprUniverseEq a b -> C) => projection_post_whnf_field_inv_type R idx subject a C run
  (fun (n : Name) (cm : KCtorMeta)
   (head : Eq (OptionType Name) (kexpr_const_name (kapp_fn subject)) (OptionType.some Name n))
   (found : Eq (OptionType KCtorMeta) (kctor_for (red_ind_ctor R) n) (OptionType.some KCtorMeta cm))
   (selected : Eq (OptionType KExpr)
    (list_head (list_drop (Nat.add (kctor_num_params cm) idx) (kapp_args subject))) (OptionType.some KExpr a)) =>
   kexprListUniverseEq_head_some
    (list_drop (Nat.add (kctor_num_params cm) idx) (kapp_args subject))
    (list_drop (Nat.add (kctor_num_params cm) idx) (kapp_args subject2)) a C
    (kexprListUniverseEq_drop (Nat.add (kctor_num_params cm) idx) (kapp_args subject) (kapp_args subject2)
     (kexprUniverseEq_kapp_args subject subject2 related)) selected
    (fun (b : KExpr)
     (selected2 : Eq (OptionType KExpr)
      (list_head (list_drop (Nat.add (kctor_num_params cm) idx) (kapp_args subject2))) (OptionType.some KExpr b))
     (field_related : KExprUniverseEq a b) =>
     next b
      (projection_post_whnf_field_intro R idx subject2 n cm b
       (Eq.trans (OptionType Name) (kexpr_const_name (kapp_fn subject2))
        (kexpr_const_name (kapp_fn subject)) (OptionType.some Name n)
        (Eq.symm (OptionType Name) (kexpr_const_name (kapp_fn subject)) (kexpr_const_name (kapp_fn subject2))
         (kexprUniverseEq_const_name (kapp_fn subject) (kapp_fn subject2)
          (kexprUniverseEq_kapp_fn subject subject2 related))) head)
       found selected2) field_related))",
    ),
    DeclarationInput::Data(
        "projection_universe_subject",
        r"forall (u : Level), KExpr",
        r"fun (u : Level) => KExpr.app (KExpr.app ctor_spine_prod_prefix (KExpr.sort u)) rfnz_zero",
    ),
    DeclarationInput::Proof(
        "projection_universe_subject_related",
        r"forall (u : Level), KExprUniverseEq (projection_universe_subject (Level.imax u Level.zero)) (projection_universe_subject Level.zero)",
        r"fun (u : Level) => KExprUniverseEq.app
  (KExpr.app ctor_spine_prod_prefix (KExpr.sort (Level.imax u Level.zero)))
  (KExpr.app ctor_spine_prod_prefix (KExpr.sort Level.zero)) rfnz_zero rfnz_zero
  (KExprUniverseEq.app ctor_spine_prod_prefix ctor_spine_prod_prefix
   (KExpr.sort (Level.imax u Level.zero)) (KExpr.sort Level.zero)
   (kexprUniverseEq_refl ctor_spine_prod_prefix) (kexprUniverseEq_imax_zero u))
  (kexprUniverseEq_refl rfnz_zero)",
    ),
    DeclarationInput::Proof(
        "projection_universe_source_select",
        r"forall (u : Level), Eq (OptionType KExpr)
 (projection_post_whnf_reduct the_red_env
  (KExpr.proj kcre_prod_type_name Nat.zero (projection_universe_subject (Level.imax u Level.zero))))
 (OptionType.some KExpr (KExpr.sort (Level.imax u Level.zero)))",
        r"fun (u : Level) => Eq.refl (OptionType KExpr) (OptionType.some KExpr (KExpr.sort (Level.imax u Level.zero)))",
    ),
    DeclarationInput::Proof(
        "projection_universe_target_select",
        r"Eq (OptionType KExpr)
 (projection_post_whnf_reduct the_red_env (KExpr.proj kcre_prod_type_name Nat.zero (projection_universe_subject Level.zero)))
 (OptionType.some KExpr (KExpr.sort Level.zero))",
        r"Eq.refl (OptionType KExpr) (OptionType.some KExpr (KExpr.sort Level.zero))",
    ),
    DeclarationInput::Proof(
        "projection_universe_selected_compat",
        r"forall (u : Level), KExprUniverseEq (KExpr.sort (Level.imax u Level.zero)) (KExpr.sort Level.zero)",
        r"fun (u : Level) => projection_post_whnf_universe_compat the_red_env kcre_prod_type_name Nat.zero
  (projection_universe_subject (Level.imax u Level.zero)) (projection_universe_subject Level.zero)
  (projection_universe_subject_related u) (KExpr.sort (Level.imax u Level.zero)) (projection_universe_source_select u)
  (KExprUniverseEq (KExpr.sort (Level.imax u Level.zero)) (KExpr.sort Level.zero))
  (fun (b : KExpr)
   (run2 : Eq (OptionType KExpr)
    (projection_post_whnf_reduct the_red_env (KExpr.proj kcre_prod_type_name Nat.zero (projection_universe_subject Level.zero)))
    (OptionType.some KExpr b))
   (field_related : KExprUniverseEq (KExpr.sort (Level.imax u Level.zero)) b) =>
   Eq.substType KExpr (fun (v : KExpr) => KExprUniverseEq (KExpr.sort (Level.imax u Level.zero)) v) b (KExpr.sort Level.zero)
    (option_some_inj KExpr b (KExpr.sort Level.zero)
     (Eq.trans (OptionType KExpr) (OptionType.some KExpr b)
      (projection_post_whnf_reduct the_red_env (KExpr.proj kcre_prod_type_name Nat.zero (projection_universe_subject Level.zero)))
      (OptionType.some KExpr (KExpr.sort Level.zero))
      (Eq.symm (OptionType KExpr)
       (projection_post_whnf_reduct the_red_env (KExpr.proj kcre_prod_type_name Nat.zero (projection_universe_subject Level.zero)))
       (OptionType.some KExpr b) run2) projection_universe_target_select)) field_related)",
    ),
    DeclarationInput::Proof(
        "projection_universe_nonzero_caller",
        r"KExprUniverseEq (KExpr.sort (Level.imax (Level.succ (Level.param Name.anonymous)) Level.zero)) (KExpr.sort Level.zero)",
        r"projection_universe_selected_compat (Level.succ (Level.param Name.anonymous))",
    ),
    DeclarationInput::Proof(
        "projection_universe_not_syntactic",
        r"forall (u : Level)
 (same : Eq KExpr (KExpr.sort (Level.imax u Level.zero)) (KExpr.sort Level.zero)), Empty",
        r"fun (u : Level)
 (same : Eq KExpr (KExpr.sort (Level.imax u Level.zero)) (KExpr.sort Level.zero)) => level_imax_ne_zero u Level.zero (kexpr_sort_inj (Level.imax u Level.zero) Level.zero same)",
    ),
];
