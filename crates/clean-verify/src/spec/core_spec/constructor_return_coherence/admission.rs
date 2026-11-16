// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Existing-fragment constructor return coherence: admission.

use super::DeclarationInput;

pub(super) const DECLARATIONS: &[DeclarationInput] = &[
    DeclarationInput::Data(
        "ac_env_returns_b",
        r"forall (env : KEnv), Bool",
        r"fun (env : KEnv) => @KEnv.rec (fun (_ : KEnv) => Bool) Bool.true
 (fun (_env : KEnv) (_kind : ConstExtensionKind) (_id : Nat) (_ty value : KExpr) (ih : Bool) => ih)
 (fun (_env : KEnv) (_id np : Nat) (_ty : KExpr) (ctors : CtorDecls) (ih : Bool) => Bool.and ih (ctor_decls_wf_b np ctors)) env",
    ),
    DeclarationInput::Data(
        "ac_ctor_at",
        r"forall (ctors : CtorDecls) (i : Nat), OptionType CtorDecl",
        r"fun (ctors : CtorDecls) (i : Nat) => @CtorDecls.rec (fun (_ : CtorDecls) => Nat -> OptionType CtorDecl)
 (fun (_i : Nat) => @OptionType.none CtorDecl)
 (fun (c : CtorDecl) (_rest : CtorDecls) (ih : Nat -> OptionType CtorDecl) (j : Nat) =>
  @Nat.rec (fun (_ : Nat) => OptionType CtorDecl) (@OptionType.some CtorDecl c)
   (fun (k : Nat) (_prev : OptionType CtorDecl) => ih k) j) ctors i",
    ),
    DeclarationInput::Data(
        "ac_bad_ct",
        r"KExpr",
        r"KExpr.pi (KExpr.sort (Level.succ Level.zero))
 (KExpr.pi (KExpr.bvar Nat.zero) (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))) (KExpr.sort Level.zero)))",
    ),
    DeclarationInput::Data(
        "ac_bad_ctors",
        r"CtorDecls",
        r"CtorDecls.cons (CtorDecl.mk (Nat.succ Nat.zero) ac_bad_ct) CtorDecls.nil",
    ),
    DeclarationInput::Data(
        "ac_bad_env",
        r"KEnv",
        r"KEnv.addInductive KEnv.empty Nat.zero (Nat.succ Nat.zero)
 (KExpr.pi (KExpr.sort (Level.succ Level.zero)) (KExpr.sort (Level.succ (Level.succ Level.zero)))) ac_bad_ctors",
    ),
    DeclarationInput::Proof(
        "ac_well_formed_returns",
        r"forall (env : KEnv) (family np : Nat) (ty : KExpr) (ctors : CtorDecls)
 (h : WellFormedCtorDecls env family np ty ctors), @Eq Bool (ctor_decls_wf_b np ctors) Bool.true",
        r"fun (env : KEnv) (family np : Nat) (ty : KExpr) (ctors : CtorDecls)
 (h : WellFormedCtorDecls env family np ty ctors) => @WellFormedCtorDecls.rec env family np ty ctors
 (fun (_h : WellFormedCtorDecls env family np ty ctors) => @Eq Bool (ctor_decls_wf_b np ctors) Bool.true)
 (fun (u : Level) (_fresh : FreshCtorDecls env family ctors)
  (_formed : @Eq KExpr (return_type ty) (KExpr.sort u))
  (shape : @Eq Bool (ctor_decls_wf_b np ctors) Bool.true)
  (_typed : CtorsWellTyped u np ty ctors) => shape) h",
    ),
    DeclarationInput::Proof(
        "ac_const_preserves",
        r"forall (env out : KEnv) (ext : ConstantExtension env out)
 (good : @Eq Bool (ac_env_returns_b env) Bool.true), @Eq Bool (ac_env_returns_b out) Bool.true",
        r"fun (env out : KEnv) (ext : ConstantExtension env out)
 (good : @Eq Bool (ac_env_returns_b env) Bool.true) => @ConstantExtension.rec env
 (fun (target : KEnv) (_h : ConstantExtension env target) => @Eq Bool (ac_env_returns_b target) Bool.true)
 (fun (kind : ConstExtensionKind) (id : Nat) (ty value : KExpr) (u : Level)
  (_fresh : FreshDeclName env id) (_ht : Typing ty (KExpr.sort u)) (_hv : Typing value ty) => good) out ext",
    ),
    DeclarationInput::Proof(
        "ac_inductive_preserves",
        r"forall (env out : KEnv) (ext : InductiveExtension env out)
 (good : @Eq Bool (ac_env_returns_b env) Bool.true), @Eq Bool (ac_env_returns_b out) Bool.true",
        r"fun (env out : KEnv) (ext : InductiveExtension env out)
 (good : @Eq Bool (ac_env_returns_b env) Bool.true) => @InductiveExtension.rec env
 (fun (target : KEnv) (_h : InductiveExtension env target) => @Eq Bool (ac_env_returns_b target) Bool.true)
 (fun (id np : Nat) (ty : KExpr) (ctors : CtorDecls) (u : Level)
  (_fresh : FreshDeclName env id) (_ht : Typing ty (KExpr.sort u))
  (_positive : StrictlyPositiveCtorDecls ty ctors) (wf : WellFormedCtorDecls env id np ty ctors) =>
  env_freshness_and_intro (ac_env_returns_b env) (ctor_decls_wf_b np ctors) good
   (ac_well_formed_returns env id np ty ctors wf)) out ext",
    ),
    DeclarationInput::Proof(
        "ac_extension_preserves",
        r"forall (env out : KEnv) (ext : DefinitionalExtension env out), @Eq Bool (ac_env_returns_b env) Bool.true -> @Eq Bool (ac_env_returns_b out) Bool.true",
        r"fun (env out : KEnv) (ext : DefinitionalExtension env out) => @DefinitionalExtension.rec
 (fun (src dst : KEnv) (_h : DefinitionalExtension src dst) => @Eq Bool (ac_env_returns_b src) Bool.true -> @Eq Bool (ac_env_returns_b dst) Bool.true)
 (fun (src : KEnv) (good : @Eq Bool (ac_env_returns_b src) Bool.true) => good)
 (fun (src dst : KEnv) (h : ConstantExtension src dst) => ac_const_preserves src dst h)
 (fun (src dst : KEnv) (h : InductiveExtension src dst) => ac_inductive_preserves src dst h)
 (fun (src mid dst : KEnv) (_a : DefinitionalExtension src mid) (_b : DefinitionalExtension mid dst)
  (iha : @Eq Bool (ac_env_returns_b src) Bool.true -> @Eq Bool (ac_env_returns_b mid) Bool.true)
  (ihb : @Eq Bool (ac_env_returns_b mid) Bool.true -> @Eq Bool (ac_env_returns_b dst) Bool.true)
  (good : @Eq Bool (ac_env_returns_b src) Bool.true) => ihb (iha good)) env out ext",
    ),
    DeclarationInput::Proof(
        "ac_env_sound_returns",
        r"forall (env : KEnv) (sound : EnvSound env), @Eq Bool (ac_env_returns_b env) Bool.true",
        r"fun (env : KEnv) (sound : EnvSound env) => ac_extension_preserves KEnv.empty env sound (@Eq.refl Bool Bool.true)",
    ),
    DeclarationInput::Proof(
        "ac_selected_return_guard",
        r"forall (np : Nat) (ctors : CtorDecls), forall (i : Nat) (c : CtorDecl),
 @Eq Bool (ctor_decls_wf_b np ctors) Bool.true ->
 @Eq (OptionType CtorDecl) (ac_ctor_at ctors i) (@OptionType.some CtorDecl c) ->
 @Eq Bool (ctor_wf_b np c) Bool.true",
        r"fun (np : Nat) (ctors : CtorDecls) => @CtorDecls.rec
 (fun (cs : CtorDecls) => forall (i : Nat) (c : CtorDecl), @Eq Bool (ctor_decls_wf_b np cs) Bool.true -> @Eq (OptionType CtorDecl) (ac_ctor_at cs i) (@OptionType.some CtorDecl c) -> @Eq Bool (ctor_wf_b np c) Bool.true)
 (fun (i : Nat) (c : CtorDecl) (_good : @Eq Bool (ctor_decls_wf_b np CtorDecls.nil) Bool.true)
  (bad : @Eq (OptionType CtorDecl) (ac_ctor_at CtorDecls.nil i) (@OptionType.some CtorDecl c)) =>
  option_none_ne_some CtorDecl c (@Eq Bool (ctor_wf_b np c) Bool.true) bad)
 (fun (head : CtorDecl) (rest : CtorDecls)
  (ih : forall (i : Nat) (c : CtorDecl), @Eq Bool (ctor_decls_wf_b np rest) Bool.true -> @Eq (OptionType CtorDecl) (ac_ctor_at rest i) (@OptionType.some CtorDecl c) -> @Eq Bool (ctor_wf_b np c) Bool.true)
  (i : Nat) => @Nat.rec
  (fun (j : Nat) => forall (c : CtorDecl), @Eq Bool (ctor_decls_wf_b np (CtorDecls.cons head rest)) Bool.true -> @Eq (OptionType CtorDecl) (ac_ctor_at (CtorDecls.cons head rest) j) (@OptionType.some CtorDecl c) -> @Eq Bool (ctor_wf_b np c) Bool.true)
  (fun (c : CtorDecl) (good : @Eq Bool (ctor_decls_wf_b np (CtorDecls.cons head rest)) Bool.true)
   (found : @Eq (OptionType CtorDecl) (ac_ctor_at (CtorDecls.cons head rest) Nat.zero) (@OptionType.some CtorDecl c)) =>
   Eq.substType CtorDecl (fun (d : CtorDecl) => @Eq Bool (ctor_wf_b np d) Bool.true) head c
    (option_some_inj CtorDecl head c found) (band_eq_true_left (ctor_wf_b np head) (ctor_decls_wf_b np rest) good))
  (fun (j : Nat) (_prev : forall (c : CtorDecl), @Eq Bool (ctor_decls_wf_b np (CtorDecls.cons head rest)) Bool.true -> @Eq (OptionType CtorDecl) (ac_ctor_at (CtorDecls.cons head rest) j) (@OptionType.some CtorDecl c) -> @Eq Bool (ctor_wf_b np c) Bool.true)
   (c : CtorDecl) (good : @Eq Bool (ctor_decls_wf_b np (CtorDecls.cons head rest)) Bool.true)
   (found : @Eq (OptionType CtorDecl) (ac_ctor_at (CtorDecls.cons head rest) (Nat.succ j)) (@OptionType.some CtorDecl c)) =>
   ih j c (band_eq_true_right (ctor_wf_b np head) (ctor_decls_wf_b np rest) good) found) i) ctors",
    ),
    DeclarationInput::Proof(
        "ac_well_formed_selected_return",
        r"forall (env : KEnv) (family np : Nat) (ty : KExpr) (ctors : CtorDecls)
 (wf : WellFormedCtorDecls env family np ty ctors) (i id : Nat) (ct : KExpr)
 (found : @Eq (OptionType CtorDecl) (ac_ctor_at ctors i) (@OptionType.some CtorDecl (CtorDecl.mk id ct))), @Eq Bool (return_args_wf_from (count_pi ct) np (return_type ct)) Bool.true",
        r"fun (env : KEnv) (family np : Nat) (ty : KExpr) (ctors : CtorDecls)
 (wf : WellFormedCtorDecls env family np ty ctors) (i id : Nat) (ct : KExpr)
 (found : @Eq (OptionType CtorDecl) (ac_ctor_at ctors i) (@OptionType.some CtorDecl (CtorDecl.mk id ct))) => band_eq_true_right (nat_leb np (count_pi ct)) (return_args_wf_from (count_pi ct) np (return_type ct))
  (ac_selected_return_guard np ctors i (CtorDecl.mk id ct) (ac_well_formed_returns env family np ty ctors wf) found)",
    ),
    DeclarationInput::Proof(
        "ac_sound_last_inductive_selected",
        r"forall (env : KEnv) (family np : Nat) (ty : KExpr) (ctors : CtorDecls)
 (sound : EnvSound (KEnv.addInductive env family np ty ctors)) (i id : Nat) (ct : KExpr)
 (found : @Eq (OptionType CtorDecl) (ac_ctor_at ctors i) (@OptionType.some CtorDecl (CtorDecl.mk id ct))), @Eq Bool (return_args_wf_from (count_pi ct) np (return_type ct)) Bool.true",
        r"fun (env : KEnv) (family np : Nat) (ty : KExpr) (ctors : CtorDecls)
 (sound : EnvSound (KEnv.addInductive env family np ty ctors)) (i id : Nat) (ct : KExpr)
 (found : @Eq (OptionType CtorDecl) (ac_ctor_at ctors i) (@OptionType.some CtorDecl (CtorDecl.mk id ct))) => band_eq_true_right (nat_leb np (count_pi ct)) (return_args_wf_from (count_pi ct) np (return_type ct))
  (ac_selected_return_guard np ctors i (CtorDecl.mk id ct)
   (band_eq_true_right (ac_env_returns_b env) (ctor_decls_wf_b np ctors)
    (ac_env_sound_returns (KEnv.addInductive env family np ty ctors) sound)) found)",
    ),
    DeclarationInput::Proof(
        "ac_existing_admitted_caller",
        r"@Eq Bool (return_args_wf_from Nat.zero Nat.zero (KExpr.bvar Nat.zero)) Bool.true",
        r"ac_sound_last_inductive_selected KEnv.empty Nat.zero Nat.zero env_freshness_type (env_freshness_ctors env_freshness_one)
 env_freshness_first_sound Nat.zero env_freshness_one (KExpr.bvar Nat.zero)
 (@Eq.refl (OptionType CtorDecl) (@OptionType.some CtorDecl (CtorDecl.mk env_freshness_one (KExpr.bvar Nat.zero))))",
    ),
    DeclarationInput::Proof(
        "ac_nonuniform_environment_refused",
        r"forall (sound : EnvSound ac_bad_env), Empty",
        r"fun (sound : EnvSound ac_bad_env) => Eq.substType Bool (fun (b : Bool) => @Bool.rec (fun (_ : Bool) => Type) Nat Empty b)
 Bool.false Bool.true (ac_env_sound_returns ac_bad_env sound) Nat.zero",
    ),
    DeclarationInput::Proof(
        "ac_nonuniform_guard_false",
        r"@Eq Bool (ctor_return_wf_b (Nat.succ Nat.zero) ac_bad_ct) Bool.false",
        r"@Eq.refl Bool Bool.false",
    ),
    DeclarationInput::Proof(
        "ac_uniform_parameter_guard_true",
        r"@Eq Bool
 (ctor_return_wf_b (Nat.succ Nat.zero)
  (KExpr.pi (KExpr.sort (Level.succ Level.zero)) (KExpr.pi (KExpr.bvar Nat.zero)
   (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))) (KExpr.bvar (Nat.succ Nat.zero)))))) Bool.true",
        r"@Eq.refl Bool Bool.true",
    ),
];

#[cfg(test)]
pub(super) const NEGATIVE_CONTROLS: &[(&str, &str, &str)] = &[
    (
        "ac_reject_bad_return",
        r"@Eq Bool (ctor_return_wf_b (Nat.succ Nat.zero) ac_bad_ct) Bool.true",
        r"@Eq.refl Bool Bool.true",
    ),
    (
        "ac_reject_fake_admission",
        r"EnvSound ac_bad_env",
        r"env_freshness_first_sound",
    ),
    (
        "ac_reject_wrong_slot",
        r"@Eq (OptionType CtorDecl)
 (ac_ctor_at (env_freshness_ctors env_freshness_one) (Nat.succ Nat.zero))
 (@OptionType.some CtorDecl (CtorDecl.mk env_freshness_one (KExpr.bvar Nat.zero)))",
        r"@Eq.refl (OptionType CtorDecl) (@OptionType.some CtorDecl (CtorDecl.mk env_freshness_one (KExpr.bvar Nat.zero)))",
    ),
];

#[cfg(test)]
pub(super) const PROOF_ROOTS: &[&str] = &[
    "ac_well_formed_returns",
    "ac_const_preserves",
    "ac_inductive_preserves",
    "ac_extension_preserves",
    "ac_env_sound_returns",
    "ac_selected_return_guard",
    "ac_well_formed_selected_return",
    "ac_sound_last_inductive_selected",
    "ac_existing_admitted_caller",
    "ac_nonuniform_environment_refused",
    "ac_nonuniform_guard_false",
    "ac_uniform_parameter_guard_true",
];

#[cfg(test)]
pub(super) const DATA_NAMES: &[&str] = &[
    "ac_env_returns_b",
    "ac_ctor_at",
    "ac_bad_ct",
    "ac_bad_ctors",
    "ac_bad_env",
];

#[cfg(test)]
pub(super) const INDUCTIVE_NAMES: &[&str] = &[];

#[cfg(test)]
pub(super) const PROP_PROOF_ROOTS: &[&str] = &[
    "ac_well_formed_returns",
    "ac_const_preserves",
    "ac_inductive_preserves",
    "ac_extension_preserves",
    "ac_env_sound_returns",
    "ac_selected_return_guard",
    "ac_well_formed_selected_return",
    "ac_sound_last_inductive_selected",
    "ac_existing_admitted_caller",
    "ac_nonuniform_guard_false",
    "ac_uniform_parameter_guard_true",
];

#[cfg(test)]
pub(super) const TYPE_PROOF_ROOTS: &[&str] = &["ac_nonuniform_environment_refused"];
