// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Existing-fragment constructor return coherence: return_spine.

use super::DeclarationInput;

pub(super) const DECLARATIONS: &[DeclarationInput] = &[
    DeclarationInput::Data(
        "arc_return_spine",
        r"forall (d : Nat) (np : Nat), KExpr",
        r"fun (d : Nat) (np : Nat) => @Nat.rec (fun (_p : Nat) => KExpr) (KExpr.bvar d) (fun (p : Nat) (spine : KExpr) => KExpr.app spine (KExpr.bvar (Nat.sub d (Nat.succ p)))) np",
    ),
    DeclarationInput::Proof(
        "arc_is_bvar_eq_sound",
        r"forall (k : Nat) (e : KExpr), @Eq Bool (is_bvar_eq k e) Bool.true -> @Eq KExpr e (KExpr.bvar k)",
        r"fun (k : Nat) (e : KExpr) =>
 @KExpr.rec (fun (e0 : KExpr) => forall (k : Nat), @Eq Bool (is_bvar_eq k e0) Bool.true -> @Eq KExpr e0 (KExpr.bvar k))
 (fun (u : Level)
  (k : Nat) (h : @Eq Bool (is_bvar_eq k (KExpr.sort u)) Bool.true) =>
  bool_false_ne_true (@Eq KExpr (KExpr.sort u) (KExpr.bvar k)) h)
 (fun (i : Nat)
  (k : Nat) (h : @Eq Bool (is_bvar_eq k (KExpr.bvar i)) Bool.true) =>
  Eq.cong Nat KExpr KExpr.bvar i k (nat_eqb_eq i k h))
 (fun (f : KExpr)
  (a : KExpr)
  (_ih_f : forall (k : Nat), @Eq Bool (is_bvar_eq k f) Bool.true -> @Eq KExpr f (KExpr.bvar k))
  (_ih_a : forall (k : Nat), @Eq Bool (is_bvar_eq k a) Bool.true -> @Eq KExpr a (KExpr.bvar k))
  (k : Nat) (h : @Eq Bool (is_bvar_eq k (KExpr.app f a)) Bool.true) =>
  bool_false_ne_true (@Eq KExpr (KExpr.app f a) (KExpr.bvar k)) h)
 (fun (A : KExpr)
  (b : KExpr)
  (_ih_A : forall (k : Nat), @Eq Bool (is_bvar_eq k A) Bool.true -> @Eq KExpr A (KExpr.bvar k))
  (_ih_b : forall (k : Nat), @Eq Bool (is_bvar_eq k b) Bool.true -> @Eq KExpr b (KExpr.bvar k))
  (k : Nat) (h : @Eq Bool (is_bvar_eq k (KExpr.lam A b)) Bool.true) =>
  bool_false_ne_true (@Eq KExpr (KExpr.lam A b) (KExpr.bvar k)) h)
 (fun (A : KExpr)
  (B : KExpr)
  (_ih_A : forall (k : Nat), @Eq Bool (is_bvar_eq k A) Bool.true -> @Eq KExpr A (KExpr.bvar k))
  (_ih_B : forall (k : Nat), @Eq Bool (is_bvar_eq k B) Bool.true -> @Eq KExpr B (KExpr.bvar k))
  (k : Nat) (h : @Eq Bool (is_bvar_eq k (KExpr.pi A B)) Bool.true) =>
  bool_false_ne_true (@Eq KExpr (KExpr.pi A B) (KExpr.bvar k)) h)
 (fun (n : Name)
  (us : ListType Level)
  (k : Nat) (h : @Eq Bool (is_bvar_eq k (KExpr.const n us)) Bool.true) =>
  bool_false_ne_true (@Eq KExpr (KExpr.const n us) (KExpr.bvar k)) h)
 (fun (A : KExpr)
  (v : KExpr)
  (b : KExpr)
  (_ih_A : forall (k : Nat), @Eq Bool (is_bvar_eq k A) Bool.true -> @Eq KExpr A (KExpr.bvar k))
  (_ih_v : forall (k : Nat), @Eq Bool (is_bvar_eq k v) Bool.true -> @Eq KExpr v (KExpr.bvar k))
  (_ih_b : forall (k : Nat), @Eq Bool (is_bvar_eq k b) Bool.true -> @Eq KExpr b (KExpr.bvar k))
  (k : Nat) (h : @Eq Bool (is_bvar_eq k (KExpr.let_ A v b)) Bool.true) =>
  bool_false_ne_true (@Eq KExpr (KExpr.let_ A v b) (KExpr.bvar k)) h)
 (fun (S : Name)
  (i : Nat)
  (sub : KExpr)
  (_ih_sub : forall (k : Nat), @Eq Bool (is_bvar_eq k sub) Bool.true -> @Eq KExpr sub (KExpr.bvar k))
  (k : Nat) (h : @Eq Bool (is_bvar_eq k (KExpr.proj S i sub)) Bool.true) =>
  bool_false_ne_true (@Eq KExpr (KExpr.proj S i sub) (KExpr.bvar k)) h)
 (fun (n : Nat)
  (k : Nat) (h : @Eq Bool (is_bvar_eq k (KExpr.lit n)) Bool.true) =>
  bool_false_ne_true (@Eq KExpr (KExpr.lit n) (KExpr.bvar k)) h) e k",
    ),
    DeclarationInput::Proof(
        "arc_return_guard_spine",
        r"forall (d : Nat) (np : Nat) (e : KExpr), @Eq Bool (return_args_wf_from d np e) Bool.true -> @Eq KExpr e (arc_return_spine d np)",
        r"fun (d : Nat) (np : Nat) (e : KExpr) =>
 @KExpr.rec (fun (e0 : KExpr) => forall (np : Nat), @Eq Bool (return_args_wf_from d np e0) Bool.true -> @Eq KExpr e0 (arc_return_spine d np))
 (fun (u : Level)
  (np : Nat) (h : @Eq Bool (return_args_wf_from d np (KExpr.sort u)) Bool.true) =>
  bool_false_ne_true (@Eq KExpr (KExpr.sort u) (arc_return_spine d np)) h)
 (fun (i : Nat)
  (np : Nat) (h : @Eq Bool (return_args_wf_from d np (KExpr.bvar i)) Bool.true) =>
Eq.subst Nat (fun (p : Nat) => @Eq KExpr (KExpr.bvar i) (arc_return_spine d p))
 Nat.zero np
 (Eq.symm Nat np Nat.zero
  (nat_is_zero_eq np (band_eq_true_right (nat_eqb i d) (nat_is_zero np) h)))
 (Eq.cong Nat KExpr KExpr.bvar i d
  (nat_eqb_eq i d (band_eq_true_left (nat_eqb i d) (nat_is_zero np) h))))
 (fun (f : KExpr)
  (a : KExpr)
  (_ih_f : forall (np : Nat), @Eq Bool (return_args_wf_from d np f) Bool.true -> @Eq KExpr f (arc_return_spine d np))
  (_ih_a : forall (np : Nat), @Eq Bool (return_args_wf_from d np a) Bool.true -> @Eq KExpr a (arc_return_spine d np))
  (np : Nat) => @Nat.rec
 (fun (p : Nat) => @Eq Bool (return_args_wf_from d p (KExpr.app f a)) Bool.true ->
  @Eq KExpr (KExpr.app f a) (arc_return_spine d p))
 (fun (h : @Eq Bool (return_args_wf_from d Nat.zero (KExpr.app f a)) Bool.true) =>
  bool_false_ne_true (@Eq KExpr (KExpr.app f a) (arc_return_spine d Nat.zero))
   (band_eq_true_left Bool.false
    (Bool.and (return_arg_ok d Nat.zero a) (return_args_wf_from d Nat.zero f)) h))
 (fun (p : Nat)
  (_prev : @Eq Bool (return_args_wf_from d p (KExpr.app f a)) Bool.true ->
   @Eq KExpr (KExpr.app f a) (arc_return_spine d p))
  (h : @Eq Bool (return_args_wf_from d (Nat.succ p) (KExpr.app f a)) Bool.true) =>
  Eq.trans KExpr (KExpr.app f a) (KExpr.app (arc_return_spine d p) a)
   (KExpr.app (arc_return_spine d p) (KExpr.bvar (Nat.sub d (Nat.succ p))))
   (Eq.cong KExpr KExpr (fun (g : KExpr) => KExpr.app g a) f (arc_return_spine d p)
    (_ih_f p
     (Eq.subst Nat (fun (q : Nat) => @Eq Bool (return_args_wf_from d q f) Bool.true)
      (Nat.sub (Nat.succ p) (Nat.succ Nat.zero)) p
      (Eq.trans Nat (Nat.sub (Nat.succ p) (Nat.succ Nat.zero)) (Nat.sub p Nat.zero) p
       (nat_sub_succ_succ p Nat.zero) (nat_sub_zero_right p))
      (band_eq_true_right (return_arg_ok d (Nat.succ p) a)
       (return_args_wf_from d (Nat.sub (Nat.succ p) (Nat.succ Nat.zero)) f)
       (band_eq_true_right Bool.true
        (Bool.and (return_arg_ok d (Nat.succ p) a)
         (return_args_wf_from d (Nat.sub (Nat.succ p) (Nat.succ Nat.zero)) f)) h)))))
   (Eq.cong KExpr KExpr (fun (arg : KExpr) => KExpr.app (arc_return_spine d p) arg)
    a (KExpr.bvar (Nat.sub d (Nat.succ p)))
    (arc_is_bvar_eq_sound (Nat.sub d (Nat.succ p)) a
     (band_eq_true_left (return_arg_ok d (Nat.succ p) a)
      (return_args_wf_from d (Nat.sub (Nat.succ p) (Nat.succ Nat.zero)) f)
      (band_eq_true_right Bool.true
       (Bool.and (return_arg_ok d (Nat.succ p) a)
        (return_args_wf_from d (Nat.sub (Nat.succ p) (Nat.succ Nat.zero)) f)) h))))) np)
 (fun (A : KExpr)
  (b : KExpr)
  (_ih_A : forall (np : Nat), @Eq Bool (return_args_wf_from d np A) Bool.true -> @Eq KExpr A (arc_return_spine d np))
  (_ih_b : forall (np : Nat), @Eq Bool (return_args_wf_from d np b) Bool.true -> @Eq KExpr b (arc_return_spine d np))
  (np : Nat) (h : @Eq Bool (return_args_wf_from d np (KExpr.lam A b)) Bool.true) =>
  bool_false_ne_true (@Eq KExpr (KExpr.lam A b) (arc_return_spine d np)) h)
 (fun (A : KExpr)
  (B : KExpr)
  (_ih_A : forall (np : Nat), @Eq Bool (return_args_wf_from d np A) Bool.true -> @Eq KExpr A (arc_return_spine d np))
  (_ih_B : forall (np : Nat), @Eq Bool (return_args_wf_from d np B) Bool.true -> @Eq KExpr B (arc_return_spine d np))
  (np : Nat) (h : @Eq Bool (return_args_wf_from d np (KExpr.pi A B)) Bool.true) =>
  bool_false_ne_true (@Eq KExpr (KExpr.pi A B) (arc_return_spine d np)) h)
 (fun (n : Name)
  (us : ListType Level)
  (np : Nat) (h : @Eq Bool (return_args_wf_from d np (KExpr.const n us)) Bool.true) =>
  bool_false_ne_true (@Eq KExpr (KExpr.const n us) (arc_return_spine d np)) h)
 (fun (A : KExpr)
  (v : KExpr)
  (b : KExpr)
  (_ih_A : forall (np : Nat), @Eq Bool (return_args_wf_from d np A) Bool.true -> @Eq KExpr A (arc_return_spine d np))
  (_ih_v : forall (np : Nat), @Eq Bool (return_args_wf_from d np v) Bool.true -> @Eq KExpr v (arc_return_spine d np))
  (_ih_b : forall (np : Nat), @Eq Bool (return_args_wf_from d np b) Bool.true -> @Eq KExpr b (arc_return_spine d np))
  (np : Nat) (h : @Eq Bool (return_args_wf_from d np (KExpr.let_ A v b)) Bool.true) =>
  bool_false_ne_true (@Eq KExpr (KExpr.let_ A v b) (arc_return_spine d np)) h)
 (fun (S : Name)
  (i : Nat)
  (sub : KExpr)
  (_ih_sub : forall (np : Nat), @Eq Bool (return_args_wf_from d np sub) Bool.true -> @Eq KExpr sub (arc_return_spine d np))
  (np : Nat) (h : @Eq Bool (return_args_wf_from d np (KExpr.proj S i sub)) Bool.true) =>
  bool_false_ne_true (@Eq KExpr (KExpr.proj S i sub) (arc_return_spine d np)) h)
 (fun (n : Nat)
  (np : Nat) (h : @Eq Bool (return_args_wf_from d np (KExpr.lit n)) Bool.true) =>
  bool_false_ne_true (@Eq KExpr (KExpr.lit n) (arc_return_spine d np)) h) e np",
    ),
    DeclarationInput::Proof(
        "arc_admitted_selected_arity",
        r"forall (env : KEnv) (family : Nat) (np : Nat) (ty : KExpr) (ctors : CtorDecls)
(wf : WellFormedCtorDecls env family np ty ctors) (i : Nat) (id : Nat) (ct : KExpr)
(found : @Eq (OptionType CtorDecl) (ac_ctor_at ctors i) (@OptionType.some CtorDecl (CtorDecl.mk id ct))),
 Le np (count_pi ct)",
        r"fun (env : KEnv) (family : Nat) (np : Nat) (ty : KExpr) (ctors : CtorDecls)
(wf : WellFormedCtorDecls env family np ty ctors) (i : Nat) (id : Nat) (ct : KExpr)
(found : @Eq (OptionType CtorDecl) (ac_ctor_at ctors i) (@OptionType.some CtorDecl (CtorDecl.mk id ct))) =>
ugeq_nat_leb_sound np (count_pi ct)
 (band_eq_true_left (nat_leb np (count_pi ct))
  (return_args_wf_from (count_pi ct) np (return_type ct))
  (ac_selected_return_guard np ctors i (CtorDecl.mk id ct)
   (ac_well_formed_returns env family np ty ctors wf) found))
",
    ),
    DeclarationInput::Proof(
        "arc_admitted_selected_spine",
        r"forall (env : KEnv) (family : Nat) (np : Nat) (ty : KExpr) (ctors : CtorDecls)
(wf : WellFormedCtorDecls env family np ty ctors) (i : Nat) (id : Nat) (ct : KExpr)
(found : @Eq (OptionType CtorDecl) (ac_ctor_at ctors i) (@OptionType.some CtorDecl (CtorDecl.mk id ct))),
 @Eq KExpr (return_type ct) (arc_return_spine (count_pi ct) np)",
        r"fun (env : KEnv) (family : Nat) (np : Nat) (ty : KExpr) (ctors : CtorDecls)
(wf : WellFormedCtorDecls env family np ty ctors) (i : Nat) (id : Nat) (ct : KExpr)
(found : @Eq (OptionType CtorDecl) (ac_ctor_at ctors i) (@OptionType.some CtorDecl (CtorDecl.mk id ct))) =>
arc_return_guard_spine (count_pi ct) np (return_type ct)
 (ac_well_formed_selected_return env family np ty ctors wf i id ct found)
",
    ),
    DeclarationInput::Proof(
        "arc_sound_selected_spine",
        r"forall (env : KEnv) (family : Nat) (np : Nat) (ty : KExpr) (ctors : CtorDecls)
(sound : EnvSound (KEnv.addInductive env family np ty ctors)) (i : Nat) (id : Nat) (ct : KExpr)
(found : @Eq (OptionType CtorDecl) (ac_ctor_at ctors i) (@OptionType.some CtorDecl (CtorDecl.mk id ct))),
@Eq KExpr (return_type ct) (arc_return_spine (count_pi ct) np)",
        r"fun (env : KEnv) (family : Nat) (np : Nat) (ty : KExpr) (ctors : CtorDecls)
(sound : EnvSound (KEnv.addInductive env family np ty ctors)) (i : Nat) (id : Nat) (ct : KExpr)
(found : @Eq (OptionType CtorDecl) (ac_ctor_at ctors i) (@OptionType.some CtorDecl (CtorDecl.mk id ct))) =>
arc_return_guard_spine (count_pi ct) np (return_type ct)
 (ac_sound_last_inductive_selected env family np ty ctors sound i id ct found)",
    ),
    DeclarationInput::Proof(
        "arc_prod_spine_from_admission",
        r"@Eq KExpr (return_type rpa_ctor_ty) (arc_return_spine rpa_four rpa_two)",
        r"arc_sound_selected_spine KEnv.empty Nat.zero rpa_two rpa_ind_ty rpa_ctors rpa_env_sound
 Nat.zero rpa_one rpa_ctor_ty
 (@Eq.refl (OptionType CtorDecl) (@OptionType.some CtorDecl (CtorDecl.mk rpa_one rpa_ctor_ty)))",
    ),
    DeclarationInput::Proof(
        "arc_prod_close_canonical",
        r"@Eq KExpr (instantiate_at (return_type rpa_ctor_ty) (KExpr.const (rpa_source_name Nat.zero) (@ListType.nil Level)) rpa_four) (KExpr.app (KExpr.app (KExpr.const (rpa_source_name Nat.zero) (@ListType.nil Level)) (KExpr.bvar rpa_three)) (KExpr.bvar rpa_two))",
        r"Eq.trans KExpr (instantiate_at (return_type rpa_ctor_ty) (KExpr.const (rpa_source_name Nat.zero) (@ListType.nil Level)) rpa_four)
 (instantiate_at (arc_return_spine rpa_four rpa_two) (KExpr.const (rpa_source_name Nat.zero) (@ListType.nil Level)) rpa_four)
 (KExpr.app (KExpr.app (KExpr.const (rpa_source_name Nat.zero) (@ListType.nil Level)) (KExpr.bvar rpa_three)) (KExpr.bvar rpa_two))
 (Eq.cong KExpr KExpr (fun (e : KExpr) => instantiate_at e (KExpr.const (rpa_source_name Nat.zero) (@ListType.nil Level)) rpa_four)
  (return_type rpa_ctor_ty) (arc_return_spine rpa_four rpa_two) arc_prod_spine_from_admission)
 (@Eq.refl KExpr (KExpr.app (KExpr.app (KExpr.const (rpa_source_name Nat.zero) (@ListType.nil Level)) (KExpr.bvar rpa_three)) (KExpr.bvar rpa_two)))",
    ),
    DeclarationInput::Proof(
        "arc_prod_source_return",
        r"@Eq KExpr (return_type (kconst_type kcre_prod_mk_signature)) (KExpr.app (KExpr.app (KExpr.const (rpa_source_name Nat.zero) (@ListType.nil Level)) (KExpr.bvar rpa_three)) (KExpr.bvar rpa_two))",
        r"Eq.trans KExpr (return_type (kconst_type kcre_prod_mk_signature))
 (instantiate_at (return_type rpa_ctor_ty) (KExpr.const (rpa_source_name Nat.zero) (@ListType.nil Level)) rpa_four)
 (KExpr.app (KExpr.app (KExpr.const (rpa_source_name Nat.zero) (@ListType.nil Level)) (KExpr.bvar rpa_three)) (KExpr.bvar rpa_two))
 (Eq.symm KExpr
  (return_type (instantiate rpa_ctor_ty (KExpr.const (rpa_source_name Nat.zero) (@ListType.nil Level))))
 (return_type (kconst_type kcre_prod_mk_signature))
  (Eq.cong KExpr KExpr return_type
   (instantiate rpa_ctor_ty (KExpr.const (rpa_source_name Nat.zero) (@ListType.nil Level)))
   (kconst_type kcre_prod_mk_signature) rpa_close_self))
 arc_prod_close_canonical",
    ),
    DeclarationInput::Proof(
        "arc_raw_underflow_guard_passes",
        r"@Eq Bool (return_args_wf_from Nat.zero (Nat.succ Nat.zero) (arc_return_spine Nat.zero (Nat.succ Nat.zero))) Bool.true",
        r"@Eq.refl Bool Bool.true",
    ),
    DeclarationInput::Proof(
        "arc_underflow_arity_refuses",
        r"@Eq Bool (nat_leb (Nat.succ Nat.zero) Nat.zero) Bool.false",
        r"@Eq.refl Bool Bool.false",
    ),
];

#[cfg(test)]
pub(super) const NEGATIVE_CONTROLS: &[(&str, &str, &str)] = &[
    (
        "arc_forged_reversed_parameters",
        r"@Eq KExpr (return_type (kconst_type kcre_prod_mk_signature)) (KExpr.app (KExpr.app (KExpr.const (rpa_source_name Nat.zero) (@ListType.nil Level)) (KExpr.bvar rpa_two)) (KExpr.bvar rpa_three))",
        r"arc_prod_source_return",
    ),
    (
        "arc_forged_constructor_as_family",
        r"@Eq KExpr (return_type (kconst_type kcre_prod_mk_signature)) (KExpr.app (KExpr.app (KExpr.const kcre_prod_mk_name (@ListType.nil Level)) (KExpr.bvar rpa_three)) (KExpr.bvar rpa_two))",
        r"arc_prod_source_return",
    ),
];

#[cfg(test)]
pub(super) const PROOF_ROOTS: &[&str] = &[
    "arc_is_bvar_eq_sound",
    "arc_return_guard_spine",
    "arc_admitted_selected_arity",
    "arc_admitted_selected_spine",
    "arc_sound_selected_spine",
    "arc_prod_spine_from_admission",
    "arc_prod_close_canonical",
    "arc_prod_source_return",
    "arc_raw_underflow_guard_passes",
    "arc_underflow_arity_refuses",
];

#[cfg(test)]
pub(super) const DATA_NAMES: &[&str] = &["arc_return_spine"];

#[cfg(test)]
pub(super) const INDUCTIVE_NAMES: &[&str] = &[];

#[cfg(test)]
pub(super) const PROP_PROOF_ROOTS: &[&str] = &[
    "arc_is_bvar_eq_sound",
    "arc_return_guard_spine",
    "arc_admitted_selected_arity",
    "arc_admitted_selected_spine",
    "arc_sound_selected_spine",
    "arc_prod_spine_from_admission",
    "arc_prod_close_canonical",
    "arc_prod_source_return",
    "arc_raw_underflow_guard_passes",
    "arc_underflow_arity_refuses",
];

#[cfg(test)]
pub(super) const TYPE_PROOF_ROOTS: &[&str] = &[];
