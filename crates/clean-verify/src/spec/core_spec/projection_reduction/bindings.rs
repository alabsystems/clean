// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Capture-avoiding substitution and lifting of successful field selection.

use super::DeclarationInput;

pub(super) const DECLARATIONS: &[DeclarationInput] = &[
    DeclarationInput::Proof(
        "projection_post_whnf_field_inv",
        r"forall (R : RedEnv) (idx : Nat) (subject a : KExpr)
 (C : Prop)
 (run : Eq (OptionType KExpr) (projection_post_whnf_field R idx subject) (OptionType.some KExpr a))
 (next : forall (n : Name) (cm : KCtorMeta),
  Eq (OptionType Name) (kexpr_const_name (kapp_fn subject)) (OptionType.some Name n) ->
  Eq (OptionType KCtorMeta) (kctor_for (red_ind_ctor R) n) (OptionType.some KCtorMeta cm) ->
  Eq (OptionType KExpr)
   (list_head (list_drop (Nat.add (kctor_num_params cm) idx) (kapp_args subject))) (OptionType.some KExpr a) -> C), C",
        r"fun (R : RedEnv) (idx : Nat) (subject a : KExpr)
 (C : Prop)
 (run : Eq (OptionType KExpr) (projection_post_whnf_field R idx subject) (OptionType.some KExpr a))
 (next : forall (n : Name) (cm : KCtorMeta),
  Eq (OptionType Name) (kexpr_const_name (kapp_fn subject)) (OptionType.some Name n) ->
  Eq (OptionType KCtorMeta) (kctor_for (red_ind_ctor R) n) (OptionType.some KCtorMeta cm) ->
  Eq (OptionType KExpr)
   (list_head (list_drop (Nat.add (kctor_num_params cm) idx) (kapp_args subject))) (OptionType.some KExpr a) -> C) => LiftP.rec C (fun (_ : LiftP C) => C) (fun (h : C) => h)
  (projection_post_whnf_field_inv_type R idx subject a (LiftP C) run
   (fun (n : Name) (cm : KCtorMeta)
    (head : Eq (OptionType Name) (kexpr_const_name (kapp_fn subject)) (OptionType.some Name n))
    (found : Eq (OptionType KCtorMeta) (kctor_for (red_ind_ctor R) n) (OptionType.some KCtorMeta cm))
    (selected : Eq (OptionType KExpr)
     (list_head (list_drop (Nat.add (kctor_num_params cm) idx) (kapp_args subject))) (OptionType.some KExpr a)) =>
    LiftP.up C (next n cm head found selected)))",
    ),
    DeclarationInput::Proof(
        "projection_selected_map_head",
        r"forall (f : KExpr -> KExpr) (xs : ListType KExpr) (a : KExpr)
 (selected : Eq (OptionType KExpr) (list_head xs) (OptionType.some KExpr a)), Eq (OptionType KExpr) (list_head (list_map f xs)) (OptionType.some KExpr (f a))",
        r"fun (f : KExpr -> KExpr) (xs : ListType KExpr) (a : KExpr)
 (selected : Eq (OptionType KExpr) (list_head xs) (OptionType.some KExpr a)) => Eq.trans (OptionType KExpr) (list_head (list_map f xs)) (opt_map f (list_head xs)) (OptionType.some KExpr (f a))
  (list_map_head f xs)
  (Eq.cong (OptionType KExpr) (OptionType KExpr) (fun (o : OptionType KExpr) => opt_map f o)
   (list_head xs) (OptionType.some KExpr a) selected)",
    ),
    DeclarationInput::Proof(
        "projection_post_whnf_field_instantiate_at",
        r"forall (R : RedEnv) (idx : Nat) (subject a v : KExpr) (d : Nat)
 (run : Eq (OptionType KExpr) (projection_post_whnf_field R idx subject) (OptionType.some KExpr a)), Eq (OptionType KExpr) (projection_post_whnf_field R idx (instantiate_at subject v d))
  (OptionType.some KExpr (instantiate_at a v d))",
        r"fun (R : RedEnv) (idx : Nat) (subject a v : KExpr) (d : Nat)
 (run : Eq (OptionType KExpr) (projection_post_whnf_field R idx subject) (OptionType.some KExpr a)) => projection_post_whnf_field_inv R idx subject a
  (Eq (OptionType KExpr) (projection_post_whnf_field R idx (instantiate_at subject v d))
   (OptionType.some KExpr (instantiate_at a v d))) run
  (fun (n : Name) (cm : KCtorMeta)
   (head : Eq (OptionType Name) (kexpr_const_name (kapp_fn subject)) (OptionType.some Name n))
   (found : Eq (OptionType KCtorMeta) (kctor_for (red_ind_ctor R) n) (OptionType.some KCtorMeta cm))
   (selected : Eq (OptionType KExpr)
    (list_head (list_drop (Nat.add (kctor_num_params cm) idx) (kapp_args subject))) (OptionType.some KExpr a)) =>
   projection_post_whnf_field_intro R idx (instantiate_at subject v d) n cm (instantiate_at a v d)
    (Eq.trans (OptionType Name) (kexpr_const_name (kapp_fn (instantiate_at subject v d)))
     (kexpr_const_name (kapp_fn subject)) (OptionType.some Name n)
     (kexpr_const_name_instantiate_const v d n subject head) head) found
    (Eq.trans (OptionType KExpr)
     (list_head (list_drop (Nat.add (kctor_num_params cm) idx) (kapp_args (instantiate_at subject v d))))
     (list_head (list_map (fun (x : KExpr) => instantiate_at x v d)
      (list_drop (Nat.add (kctor_num_params cm) idx) (kapp_args subject))))
     (OptionType.some KExpr (instantiate_at a v d))
     (Eq.cong (ListType KExpr) (OptionType KExpr) (fun (xs : ListType KExpr) => list_head xs)
      (list_drop (Nat.add (kctor_num_params cm) idx) (kapp_args (instantiate_at subject v d)))
      (list_map (fun (x : KExpr) => instantiate_at x v d) (list_drop (Nat.add (kctor_num_params cm) idx) (kapp_args subject)))
      (kapp_drop_inst v d n subject (Nat.add (kctor_num_params cm) idx) head))
     (projection_selected_map_head (fun (x : KExpr) => instantiate_at x v d)
      (list_drop (Nat.add (kctor_num_params cm) idx) (kapp_args subject)) a selected)))",
    ),
    DeclarationInput::Proof(
        "projection_post_whnf_instantiate_at",
        r"forall (R : RedEnv) (S : Name) (idx : Nat) (subject a v : KExpr) (d : Nat)
 (run : Eq (OptionType KExpr) (projection_post_whnf_reduct R (KExpr.proj S idx subject)) (OptionType.some KExpr a)), Eq (OptionType KExpr) (projection_post_whnf_reduct R (instantiate_at (KExpr.proj S idx subject) v d))
  (OptionType.some KExpr (instantiate_at a v d))",
        r"fun (R : RedEnv) (S : Name) (idx : Nat) (subject a v : KExpr) (d : Nat)
 (run : Eq (OptionType KExpr) (projection_post_whnf_reduct R (KExpr.proj S idx subject)) (OptionType.some KExpr a)) => Eq.trans (OptionType KExpr)
  (projection_post_whnf_reduct R (instantiate_at (KExpr.proj S idx subject) v d))
  (projection_post_whnf_reduct R (KExpr.proj S idx (instantiate_at subject v d)))
  (OptionType.some KExpr (instantiate_at a v d))
  (Eq.cong KExpr (OptionType KExpr) (fun (e : KExpr) => projection_post_whnf_reduct R e)
   (instantiate_at (KExpr.proj S idx subject) v d) (KExpr.proj S idx (instantiate_at subject v d))
   (instantiate_at_proj S idx subject v d))
  (projection_post_whnf_field_instantiate_at R idx subject a v d run)",
    ),
    DeclarationInput::Proof(
        "projection_post_whnf_field_lift_at",
        r"forall (R : RedEnv) (idx : Nat) (subject a : KExpr) (cutoff amount : Nat)
 (run : Eq (OptionType KExpr) (projection_post_whnf_field R idx subject) (OptionType.some KExpr a)), Eq (OptionType KExpr) (projection_post_whnf_field R idx (lift_at subject cutoff amount))
  (OptionType.some KExpr (lift_at a cutoff amount))",
        r"fun (R : RedEnv) (idx : Nat) (subject a : KExpr) (cutoff amount : Nat)
 (run : Eq (OptionType KExpr) (projection_post_whnf_field R idx subject) (OptionType.some KExpr a)) => projection_post_whnf_field_inv R idx subject a
  (Eq (OptionType KExpr) (projection_post_whnf_field R idx (lift_at subject cutoff amount))
   (OptionType.some KExpr (lift_at a cutoff amount))) run
  (fun (n : Name) (cm : KCtorMeta)
   (head : Eq (OptionType Name) (kexpr_const_name (kapp_fn subject)) (OptionType.some Name n))
   (found : Eq (OptionType KCtorMeta) (kctor_for (red_ind_ctor R) n) (OptionType.some KCtorMeta cm))
   (selected : Eq (OptionType KExpr)
    (list_head (list_drop (Nat.add (kctor_num_params cm) idx) (kapp_args subject))) (OptionType.some KExpr a)) =>
   projection_post_whnf_field_intro R idx (lift_at subject cutoff amount) n cm (lift_at a cutoff amount)
    (Eq.trans (OptionType Name) (kexpr_const_name (kapp_fn (lift_at subject cutoff amount)))
     (kexpr_const_name (kapp_fn subject)) (OptionType.some Name n)
     (kexpr_const_name_lift cutoff amount subject) head) found
    (Eq.trans (OptionType KExpr)
     (list_head (list_drop (Nat.add (kctor_num_params cm) idx) (kapp_args (lift_at subject cutoff amount))))
     (list_head (list_map (fun (x : KExpr) => lift_at x cutoff amount)
      (list_drop (Nat.add (kctor_num_params cm) idx) (kapp_args subject))))
     (OptionType.some KExpr (lift_at a cutoff amount))
     (Eq.cong (ListType KExpr) (OptionType KExpr) (fun (xs : ListType KExpr) => list_head xs)
      (list_drop (Nat.add (kctor_num_params cm) idx) (kapp_args (lift_at subject cutoff amount)))
      (list_map (fun (x : KExpr) => lift_at x cutoff amount) (list_drop (Nat.add (kctor_num_params cm) idx) (kapp_args subject)))
      (kapp_drop_lift cutoff amount subject (Nat.add (kctor_num_params cm) idx)))
     (projection_selected_map_head (fun (x : KExpr) => lift_at x cutoff amount)
      (list_drop (Nat.add (kctor_num_params cm) idx) (kapp_args subject)) a selected)))",
    ),
    DeclarationInput::Proof(
        "projection_post_whnf_lift_at",
        r"forall (R : RedEnv) (S : Name) (idx : Nat) (subject a : KExpr) (cutoff amount : Nat)
 (run : Eq (OptionType KExpr) (projection_post_whnf_reduct R (KExpr.proj S idx subject)) (OptionType.some KExpr a)), Eq (OptionType KExpr) (projection_post_whnf_reduct R (lift_at (KExpr.proj S idx subject) cutoff amount))
  (OptionType.some KExpr (lift_at a cutoff amount))",
        r"fun (R : RedEnv) (S : Name) (idx : Nat) (subject a : KExpr) (cutoff amount : Nat)
 (run : Eq (OptionType KExpr) (projection_post_whnf_reduct R (KExpr.proj S idx subject)) (OptionType.some KExpr a)) => Eq.trans (OptionType KExpr)
  (projection_post_whnf_reduct R (lift_at (KExpr.proj S idx subject) cutoff amount))
  (projection_post_whnf_reduct R (KExpr.proj S idx (lift_at subject cutoff amount)))
  (OptionType.some KExpr (lift_at a cutoff amount))
  (Eq.cong KExpr (OptionType KExpr) (fun (e : KExpr) => projection_post_whnf_reduct R e)
   (lift_at (KExpr.proj S idx subject) cutoff amount) (KExpr.proj S idx (lift_at subject cutoff amount))
   (lift_at_proj S idx subject cutoff amount))
  (projection_post_whnf_field_lift_at R idx subject a cutoff amount run)",
    ),
    DeclarationInput::Data(
        "projection_binding_field",
        r"KExpr",
        r"KExpr.lam rfnz_nat (KExpr.bvar (Nat.succ Nat.zero))",
    ),
    DeclarationInput::Data(
        "projection_binding_subject",
        r"KExpr",
        r"KExpr.app (KExpr.app
  (KExpr.app (KExpr.app projection_prod_ctor (KExpr.pi rfnz_nat rfnz_nat)) rfnz_nat)
  projection_binding_field) rfnz_zero",
    ),
    DeclarationInput::Proof(
        "projection_binding_select",
        r"Eq (OptionType KExpr)
 (projection_post_whnf_reduct the_red_env (KExpr.proj kcre_prod_type_name Nat.zero projection_binding_subject))
 (OptionType.some KExpr projection_binding_field)",
        r"Eq.refl (OptionType KExpr) (OptionType.some KExpr projection_binding_field)",
    ),
    DeclarationInput::Proof(
        "projection_binding_substitution_computes",
        r"Eq KExpr
 (instantiate_at projection_binding_field (KExpr.bvar (Nat.succ Nat.zero)) Nat.zero)
 (KExpr.lam rfnz_nat (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))))",
        r"Eq.refl KExpr (KExpr.lam rfnz_nat (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))))",
    ),
    DeclarationInput::Proof(
        "projection_binding_lifting_computes",
        r"Eq KExpr
 (lift_at projection_binding_field Nat.zero (Nat.succ (Nat.succ Nat.zero)))
 (KExpr.lam rfnz_nat (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ Nat.zero)))))",
        r"Eq.refl KExpr (KExpr.lam rfnz_nat (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ Nat.zero)))))",
    ),
    DeclarationInput::Proof(
        "projection_binding_substitution_caller",
        r"Eq (OptionType KExpr)
 (projection_post_whnf_reduct the_red_env
  (instantiate_at (KExpr.proj kcre_prod_type_name Nat.zero projection_binding_subject)
   (KExpr.bvar (Nat.succ Nat.zero)) Nat.zero))
 (OptionType.some KExpr (KExpr.lam rfnz_nat (KExpr.bvar (Nat.succ (Nat.succ Nat.zero)))))",
        r"Eq.trans (OptionType KExpr)
  (projection_post_whnf_reduct the_red_env
   (instantiate_at (KExpr.proj kcre_prod_type_name Nat.zero projection_binding_subject)
    (KExpr.bvar (Nat.succ Nat.zero)) Nat.zero))
  (OptionType.some KExpr (instantiate_at projection_binding_field (KExpr.bvar (Nat.succ Nat.zero)) Nat.zero))
  (OptionType.some KExpr (KExpr.lam rfnz_nat (KExpr.bvar (Nat.succ (Nat.succ Nat.zero)))))
  (projection_post_whnf_instantiate_at the_red_env kcre_prod_type_name Nat.zero projection_binding_subject
   projection_binding_field (KExpr.bvar (Nat.succ Nat.zero)) Nat.zero projection_binding_select)
  (Eq.cong KExpr (OptionType KExpr) (fun (e : KExpr) => OptionType.some KExpr e)
   (instantiate_at projection_binding_field (KExpr.bvar (Nat.succ Nat.zero)) Nat.zero)
   (KExpr.lam rfnz_nat (KExpr.bvar (Nat.succ (Nat.succ Nat.zero)))) projection_binding_substitution_computes)",
    ),
    DeclarationInput::Proof(
        "projection_binding_lifting_caller",
        r"Eq (OptionType KExpr)
 (projection_post_whnf_reduct the_red_env
  (lift_at (KExpr.proj kcre_prod_type_name Nat.zero projection_binding_subject) Nat.zero (Nat.succ (Nat.succ Nat.zero))))
 (OptionType.some KExpr (KExpr.lam rfnz_nat (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ Nat.zero))))))",
        r"Eq.trans (OptionType KExpr)
  (projection_post_whnf_reduct the_red_env
   (lift_at (KExpr.proj kcre_prod_type_name Nat.zero projection_binding_subject) Nat.zero (Nat.succ (Nat.succ Nat.zero))))
  (OptionType.some KExpr (lift_at projection_binding_field Nat.zero (Nat.succ (Nat.succ Nat.zero))))
  (OptionType.some KExpr (KExpr.lam rfnz_nat (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ Nat.zero))))))
  (projection_post_whnf_lift_at the_red_env kcre_prod_type_name Nat.zero projection_binding_subject
   projection_binding_field Nat.zero (Nat.succ (Nat.succ Nat.zero)) projection_binding_select)
  (Eq.cong KExpr (OptionType KExpr) (fun (e : KExpr) => OptionType.some KExpr e)
   (lift_at projection_binding_field Nat.zero (Nat.succ (Nat.succ Nat.zero)))
   (KExpr.lam rfnz_nat (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ Nat.zero))))) projection_binding_lifting_computes)",
    ),
];
