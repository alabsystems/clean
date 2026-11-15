// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Witnesses for the typed-conversion arms, each needing the arm it witnesses:
//! two DISTINCT variables made convertible by proof irrelevance and by a
//! unit-like type, a variable made convertible with its eta expansion, a
//! constructor application made convertible with a variable by structure eta
//! (the same term is `expand_eta_struct` of that variable, so it also witnesses
//! the recursor-major expansion), a let body that type-checks only through
//! its let-local's VALUE, and a Nat literal reaching constructor form.
//!
//! The proof-irrelevance, eta, let and literal witnesses hold at EVERY environment.
//! The unit-like witness runs at `accepts_unit_env` (a zero-field structure) and
//! the structure-eta witness at `projection_metadata_control_env` (a one-field
//! structure); both carry a constructive inequality with the reflected seed.

use super::DeclarationInput;

pub(super) const DECLARATIONS: &[DeclarationInput] = &[
    // ── proof irrelevance: G = [#1, #0, Sort 0], so #2 : Prop and #1, #0 : #2.
    DeclarationInput::Data(
        r"def accepts_tc_prop_context : ListType CtxEntryIn := ListType.cons CtxEntryIn (CtxEntryIn.decl (KExpr.bvar (Nat.succ Nat.zero))) (ListType.cons CtxEntryIn (CtxEntryIn.decl (KExpr.bvar Nat.zero)) (ListType.cons CtxEntryIn (CtxEntryIn.decl (KExpr.sort Level.zero)) (ListType.nil CtxEntryIn)))",
    ),
    DeclarationInput::Proof(
        "kernel_accepts_tc_in_proof_irrel",
        r"forall (R : RedEnv) (tenv : KDeclEnv), KernelAcceptsTcIn R tenv Bool.false accepts_tc_prop_context (KExpr.bvar (Nat.succ Nat.zero)) (KExpr.bvar Nat.zero)",
        r"fun (R : RedEnv) (tenv : KDeclEnv) =>
KernelAcceptsTcIn.proof_irrel R tenv accepts_tc_prop_context
  (KExpr.bvar (Nat.succ Nat.zero)) (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))) (KExpr.bvar (Nat.succ (Nat.succ Nat.zero)))
  (KExpr.sort Level.zero) (KExpr.bvar Nat.zero) (KExpr.bvar (Nat.succ (Nat.succ Nat.zero)))
  (KernelAcceptsTcIn.bvar R tenv accepts_tc_prop_context (Nat.succ Nat.zero) (CtxEntryIn.decl (KExpr.bvar Nat.zero))
    (Eq.refl (OptionType CtxEntryIn) (OptionType.some CtxEntryIn (CtxEntryIn.decl (KExpr.bvar Nat.zero)))))
  (KernelAcceptsTcIn.cdp R tenv accepts_tc_prop_context (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))) (KExpr.bvar (Nat.succ (Nat.succ Nat.zero)))
    (DefEqCDPIn.refl R (KExpr.bvar (Nat.succ (Nat.succ Nat.zero)))))
  (KernelAcceptsTcIn.bvar R tenv accepts_tc_prop_context (Nat.succ (Nat.succ Nat.zero)) (CtxEntryIn.decl (KExpr.sort Level.zero))
    (Eq.refl (OptionType CtxEntryIn) (OptionType.some CtxEntryIn (CtxEntryIn.decl (KExpr.sort Level.zero)))))
  (KernelAcceptsTcIn.cdp R tenv accepts_tc_prop_context (KExpr.sort Level.zero) (KExpr.sort Level.zero)
    (DefEqCDPIn.refl R (KExpr.sort Level.zero)))
  (KernelAcceptsTcIn.bvar R tenv accepts_tc_prop_context Nat.zero (CtxEntryIn.decl (KExpr.bvar (Nat.succ Nat.zero)))
    (Eq.refl (OptionType CtxEntryIn) (OptionType.some CtxEntryIn (CtxEntryIn.decl (KExpr.bvar (Nat.succ Nat.zero))))))
  (KernelAcceptsTcIn.cdp R tenv accepts_tc_prop_context (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))) (KExpr.bvar (Nat.succ (Nat.succ Nat.zero)))
    (DefEqCDPIn.refl R (KExpr.bvar (Nat.succ (Nat.succ Nat.zero)))))",
    ),
    DeclarationInput::Proof(
        "accepts_tc_proof_irrel_sound",
        r"forall (R : RedEnv) (tenv : KDeclEnv), TypingTcIn R tenv Bool.false accepts_tc_prop_context (KExpr.bvar (Nat.succ Nat.zero)) (KExpr.bvar Nat.zero)",
        r"fun (R : RedEnv) (tenv : KDeclEnv) =>
kernel_accepts_tc_in_sound R tenv Bool.false accepts_tc_prop_context (KExpr.bvar (Nat.succ Nat.zero)) (KExpr.bvar Nat.zero)
  (kernel_accepts_tc_in_proof_irrel R tenv)",
    ),
    // ── lambda eta: G = [Pi (Sort 0) (Sort 0)], f = #0.
    DeclarationInput::Data(
        r"def accepts_tc_fun_context : ListType CtxEntryIn := ListType.cons CtxEntryIn (CtxEntryIn.decl (KExpr.pi (KExpr.sort Level.zero) (KExpr.sort Level.zero))) (ListType.nil CtxEntryIn)",
    ),
    DeclarationInput::Proof(
        "kernel_accepts_tc_in_eta",
        r"forall (R : RedEnv) (tenv : KDeclEnv), KernelAcceptsTcIn R tenv Bool.false accepts_tc_fun_context (KExpr.bvar Nat.zero)
  (KExpr.lam (KExpr.sort Level.zero) (KExpr.app (KExpr.bvar (Nat.succ Nat.zero)) (KExpr.bvar Nat.zero)))",
        r"fun (R : RedEnv) (tenv : KDeclEnv) =>
KernelAcceptsTcIn.eta R tenv accepts_tc_fun_context (KExpr.bvar Nat.zero)
  (KExpr.pi (KExpr.sort Level.zero) (KExpr.sort Level.zero)) (KExpr.sort Level.zero) (KExpr.sort Level.zero)
  (KernelAcceptsTcIn.bvar R tenv accepts_tc_fun_context Nat.zero (CtxEntryIn.decl (KExpr.pi (KExpr.sort Level.zero) (KExpr.sort Level.zero)))
    (Eq.refl (OptionType CtxEntryIn) (OptionType.some CtxEntryIn (CtxEntryIn.decl (KExpr.pi (KExpr.sort Level.zero) (KExpr.sort Level.zero))))))
  (KernelAcceptsTcIn.cdp R tenv accepts_tc_fun_context (KExpr.pi (KExpr.sort Level.zero) (KExpr.sort Level.zero))
    (KExpr.pi (KExpr.sort Level.zero) (KExpr.sort Level.zero))
    (DefEqCDPIn.refl R (KExpr.pi (KExpr.sort Level.zero) (KExpr.sort Level.zero))))",
    ),
    DeclarationInput::Proof(
        "accepts_tc_eta_sound",
        r"forall (R : RedEnv) (tenv : KDeclEnv), TypingTcIn R tenv Bool.false accepts_tc_fun_context (KExpr.bvar Nat.zero)
  (KExpr.lam (KExpr.sort Level.zero) (KExpr.app (KExpr.bvar (Nat.succ Nat.zero)) (KExpr.bvar Nat.zero)))",
        r"fun (R : RedEnv) (tenv : KDeclEnv) =>
kernel_accepts_tc_in_sound R tenv Bool.false accepts_tc_fun_context (KExpr.bvar Nat.zero)
  (KExpr.lam (KExpr.sort Level.zero) (KExpr.app (KExpr.bvar (Nat.succ Nat.zero)) (KExpr.bvar Nat.zero)))
  (kernel_accepts_tc_in_eta R tenv)",
    ),
    // ── unit-like: a zero-field structure `const anon []` with constructor `str anon 2`.
    DeclarationInput::Data(
        r"def accepts_unit_cn : Name := Name.str Name.anonymous (Nat.succ (Nat.succ Nat.zero))",
    ),
    DeclarationInput::Data(
        r"def accepts_unit_ind : KIndMeta := KIndMeta.mk (KConstSig.mk (ListType.nil Name) (KExpr.sort (Level.succ Level.zero))) Nat.zero Nat.zero
 (ListType.cons Name accepts_unit_cn (ListType.nil Name)) (ListType.cons Name Name.anonymous (ListType.nil Name))",
    ),
    DeclarationInput::Data(
        r"def accepts_unit_ctor : KCtorMeta := KCtorMeta.mk (KConstSig.mk (ListType.nil Name) (KExpr.const Name.anonymous (ListType.nil Level))) Name.anonymous Nat.zero Nat.zero Nat.zero",
    ),
    DeclarationInput::Data(
        r"def accepts_unit_env : RedEnv := RedEnv.mk RecEnv.empty DefEnv.empty
 (IndCtorEnv.addCtor (IndCtorEnv.addInd IndCtorEnv.empty Name.anonymous accepts_unit_ind) accepts_unit_cn accepts_unit_ctor)",
    ),
    DeclarationInput::Data(
        r"def accepts_unit_type : KExpr := KExpr.const Name.anonymous (ListType.nil Level)",
    ),
    DeclarationInput::Data(
        r"def accepts_unit_context : ListType CtxEntryIn := ListType.cons CtxEntryIn (CtxEntryIn.decl accepts_unit_type) (ListType.cons CtxEntryIn (CtxEntryIn.decl accepts_unit_type) (ListType.nil CtxEntryIn))",
    ),
    DeclarationInput::Proof(
        "accepts_unit_like",
        r"UnitLikeIn accepts_unit_env accepts_unit_type",
        r"UnitLikeIn.mk accepts_unit_env accepts_unit_type Name.anonymous accepts_unit_ind accepts_unit_cn accepts_unit_ctor
  (Eq.refl (OptionType Name) (OptionType.some Name Name.anonymous))
  (Eq.refl (OptionType KIndMeta) (OptionType.some KIndMeta accepts_unit_ind))
  (Eq.refl (ListType Name) (ListType.cons Name accepts_unit_cn (ListType.nil Name)))
  (Eq.refl Bool Bool.true)
  (Eq.refl (OptionType KCtorMeta) (OptionType.some KCtorMeta accepts_unit_ctor))
  (Eq.refl Bool Bool.true)",
    ),
    DeclarationInput::Proof(
        "kernel_accepts_tc_in_unit_like",
        r"forall (tenv : KDeclEnv), KernelAcceptsTcIn accepts_unit_env tenv Bool.false accepts_unit_context (KExpr.bvar Nat.zero) (KExpr.bvar (Nat.succ Nat.zero))",
        r"fun (tenv : KDeclEnv) =>
KernelAcceptsTcIn.unit_like accepts_unit_env tenv accepts_unit_context
  (KExpr.bvar Nat.zero) accepts_unit_type accepts_unit_type (KExpr.bvar (Nat.succ Nat.zero)) accepts_unit_type
  (KernelAcceptsTcIn.bvar accepts_unit_env tenv accepts_unit_context Nat.zero (CtxEntryIn.decl accepts_unit_type)
    (Eq.refl (OptionType CtxEntryIn) (OptionType.some CtxEntryIn (CtxEntryIn.decl accepts_unit_type))))
  (KernelAcceptsTcIn.cdp accepts_unit_env tenv accepts_unit_context accepts_unit_type accepts_unit_type
    (DefEqCDPIn.refl accepts_unit_env accepts_unit_type))
  accepts_unit_like
  (KernelAcceptsTcIn.bvar accepts_unit_env tenv accepts_unit_context (Nat.succ Nat.zero) (CtxEntryIn.decl accepts_unit_type)
    (Eq.refl (OptionType CtxEntryIn) (OptionType.some CtxEntryIn (CtxEntryIn.decl accepts_unit_type))))
  (KernelAcceptsTcIn.cdp accepts_unit_env tenv accepts_unit_context accepts_unit_type accepts_unit_type
    (DefEqCDPIn.refl accepts_unit_env accepts_unit_type))",
    ),
    DeclarationInput::Proof(
        "accepts_unit_like_sound",
        r"forall (tenv : KDeclEnv), TypingTcIn accepts_unit_env tenv Bool.false accepts_unit_context (KExpr.bvar Nat.zero) (KExpr.bvar (Nat.succ Nat.zero))",
        r"fun (tenv : KDeclEnv) =>
kernel_accepts_tc_in_sound accepts_unit_env tenv Bool.false accepts_unit_context (KExpr.bvar Nat.zero) (KExpr.bvar (Nat.succ Nat.zero))
  (kernel_accepts_tc_in_unit_like tenv)",
    ),
    DeclarationInput::Proof(
        "accepts_unit_env_not_seed",
        r"Eq RedEnv accepts_unit_env the_red_env -> Empty",
        r"fun (same : Eq RedEnv accepts_unit_env the_red_env) =>
option_none_ne_some_type KIndMeta accepts_unit_ind Empty
  (Eq.trans (OptionType KIndMeta) (OptionType.none KIndMeta)
    (kind_for (red_ind_ctor the_red_env) Name.anonymous)
    (OptionType.some KIndMeta accepts_unit_ind)
    (Eq.symm (OptionType KIndMeta)
      (kind_for (red_ind_ctor the_red_env) Name.anonymous) (OptionType.none KIndMeta)
      accepts_proj_seed_has_no_anonymous_inductive)
    (Eq.symm (OptionType KIndMeta) (OptionType.some KIndMeta accepts_unit_ind)
      (kind_for (red_ind_ctor the_red_env) Name.anonymous)
      (Eq.cong RedEnv (OptionType KIndMeta)
        (fun (R : RedEnv) => kind_for (red_ind_ctor R) Name.anonymous)
        accepts_unit_env the_red_env same)))",
    ),
    // ── structure eta at the one-field structure of projection_metadata_control_env:
    // t = cn (proj anon 0 #0) is expand_eta_struct of #0, so t == #0.
    DeclarationInput::Data(
        r"def accepts_struct_context : ListType CtxEntryIn := ListType.cons CtxEntryIn (CtxEntryIn.decl projection_metadata_control_type) (ListType.nil CtxEntryIn)",
    ),
    DeclarationInput::Data(
        r"def accepts_struct_t : KExpr := KExpr.app (KExpr.const projection_metadata_control_cn (ListType.nil Level)) (KExpr.proj Name.anonymous Nat.zero (KExpr.bvar Nat.zero))",
    ),
    DeclarationInput::Proof(
        "accepts_struct_ctor",
        r"StructCtorIn projection_metadata_control_env accepts_struct_t projection_metadata_control_ind projection_metadata_control_ctor",
        r"StructCtorIn.mk projection_metadata_control_env accepts_struct_t projection_metadata_control_cn
  projection_metadata_control_ind projection_metadata_control_ctor
  (Eq.refl (OptionType Name) (OptionType.some Name projection_metadata_control_cn))
  (Eq.refl (OptionType KCtorMeta) (OptionType.some KCtorMeta projection_metadata_control_ctor))
  (Eq.refl (OptionType KIndMeta) (OptionType.some KIndMeta projection_metadata_control_ind))
  (Eq.refl Bool Bool.true) (Eq.refl Bool Bool.true) (Eq.refl Bool Bool.true)",
    ),
    DeclarationInput::Proof(
        "accepts_struct_fields",
        r"forall (tenv : KDeclEnv) (i : Nat), Eq Bool (nat_leb (Nat.succ i) (kctor_num_fields projection_metadata_control_ctor)) Bool.true ->
 KernelAcceptsTcIn projection_metadata_control_env tenv Bool.false accepts_struct_context
  (KExpr.proj (kctor_parent projection_metadata_control_ctor) i (KExpr.bvar Nat.zero))
  (accepts_kexpr_nth (kapp_args accepts_struct_t) (Nat.add (kctor_num_params projection_metadata_control_ctor) i))",
        r"fun (tenv : KDeclEnv) (i : Nat) =>
Nat.rec (fun (j : Nat) => Eq Bool (nat_leb (Nat.succ j) (kctor_num_fields projection_metadata_control_ctor)) Bool.true ->
    KernelAcceptsTcIn projection_metadata_control_env tenv Bool.false accepts_struct_context
      (KExpr.proj (kctor_parent projection_metadata_control_ctor) j (KExpr.bvar Nat.zero))
      (accepts_kexpr_nth (kapp_args accepts_struct_t) (Nat.add (kctor_num_params projection_metadata_control_ctor) j)))
  (fun (_hi : Eq Bool (nat_leb (Nat.succ Nat.zero) (kctor_num_fields projection_metadata_control_ctor)) Bool.true) =>
    KernelAcceptsTcIn.cdp projection_metadata_control_env tenv accepts_struct_context
      (KExpr.proj Name.anonymous Nat.zero (KExpr.bvar Nat.zero)) (KExpr.proj Name.anonymous Nat.zero (KExpr.bvar Nat.zero))
      (DefEqCDPIn.refl projection_metadata_control_env (KExpr.proj Name.anonymous Nat.zero (KExpr.bvar Nat.zero))))
  (fun (j : Nat)
    (_ih : Eq Bool (nat_leb (Nat.succ j) (kctor_num_fields projection_metadata_control_ctor)) Bool.true ->
      KernelAcceptsTcIn projection_metadata_control_env tenv Bool.false accepts_struct_context
        (KExpr.proj (kctor_parent projection_metadata_control_ctor) j (KExpr.bvar Nat.zero))
        (accepts_kexpr_nth (kapp_args accepts_struct_t) (Nat.add (kctor_num_params projection_metadata_control_ctor) j)))
    (hi : Eq Bool (nat_leb (Nat.succ (Nat.succ j)) (kctor_num_fields projection_metadata_control_ctor)) Bool.true) =>
    bool_false_ne_true_t
      (KernelAcceptsTcIn projection_metadata_control_env tenv Bool.false accepts_struct_context
        (KExpr.proj (kctor_parent projection_metadata_control_ctor) (Nat.succ j) (KExpr.bvar Nat.zero))
        (accepts_kexpr_nth (kapp_args accepts_struct_t) (Nat.add (kctor_num_params projection_metadata_control_ctor) (Nat.succ j))))
      hi)
  i",
    ),
    DeclarationInput::Proof(
        "kernel_accepts_tc_in_struct_eta",
        r"forall (tenv : KDeclEnv), KernelAcceptsTcIn projection_metadata_control_env tenv Bool.false accepts_struct_context
  accepts_struct_t (KExpr.bvar Nat.zero)",
        r"fun (tenv : KDeclEnv) =>
KernelAcceptsTcIn.struct_eta projection_metadata_control_env tenv accepts_struct_context
  accepts_struct_t (KExpr.bvar Nat.zero) projection_metadata_control_type projection_metadata_control_type
  projection_metadata_control_ind projection_metadata_control_ctor accepts_struct_ctor
  (KernelAcceptsTcIn.bvar projection_metadata_control_env tenv accepts_struct_context Nat.zero (CtxEntryIn.decl projection_metadata_control_type)
    (Eq.refl (OptionType CtxEntryIn) (OptionType.some CtxEntryIn (CtxEntryIn.decl projection_metadata_control_type))))
  (KernelAcceptsTcIn.cdp projection_metadata_control_env tenv accepts_struct_context
    projection_metadata_control_type projection_metadata_control_type
    (DefEqCDPIn.refl projection_metadata_control_env projection_metadata_control_type))
  (Eq.refl (OptionType Name) (OptionType.some Name Name.anonymous))
  (accepts_struct_fields tenv)",
    ),
    DeclarationInput::Proof(
        "accepts_struct_eta_sound",
        r"forall (tenv : KDeclEnv), TypingTcIn projection_metadata_control_env tenv Bool.false accepts_struct_context
  accepts_struct_t (KExpr.bvar Nat.zero)",
        r"fun (tenv : KDeclEnv) =>
kernel_accepts_tc_in_sound projection_metadata_control_env tenv Bool.false accepts_struct_context
  accepts_struct_t (KExpr.bvar Nat.zero) (kernel_accepts_tc_in_struct_eta tenv)",
    ),
    // ── let-local zeta: `let x : Sort 2 := Sort 1 in (fun (y : x) => y) (Sort 0)`.
    // The argument check `Sort 1 == x` holds only through x's VALUE, which is
    // what the deployed Let arm's let-local and whnf's FVar unfolding provide.
    DeclarationInput::Data(
        r"def accepts_tc_let_entry : CtxEntryIn := CtxEntryIn.defn (KExpr.sort (Level.succ (Level.succ Level.zero))) (KExpr.sort (Level.succ Level.zero))",
    ),
    DeclarationInput::Data(
        r"def accepts_tc_let_context : ListType CtxEntryIn := ListType.cons CtxEntryIn accepts_tc_let_entry (ListType.nil CtxEntryIn)",
    ),
    DeclarationInput::Data(
        r"def accepts_tc_let_body : KExpr := KExpr.app (KExpr.lam (KExpr.bvar Nat.zero) (KExpr.bvar Nat.zero)) (KExpr.sort Level.zero)",
    ),
    DeclarationInput::Proof(
        "accepts_tc_let_zeta_arg",
        r"forall (R : RedEnv) (tenv : KDeclEnv), KernelAcceptsTcIn R tenv Bool.false accepts_tc_let_context (KExpr.sort (Level.succ Level.zero)) (KExpr.bvar Nat.zero)",
        r"fun (R : RedEnv) (tenv : KDeclEnv) =>
KernelAcceptsTcIn.symm R tenv accepts_tc_let_context (KExpr.bvar Nat.zero) (KExpr.sort (Level.succ Level.zero))
  (KernelAcceptsTcIn.zeta_local R tenv accepts_tc_let_context Nat.zero (KExpr.sort (Level.succ (Level.succ Level.zero))) (KExpr.sort (Level.succ Level.zero))
    (Eq.refl (OptionType CtxEntryIn) (OptionType.some CtxEntryIn (CtxEntryIn.defn (KExpr.sort (Level.succ (Level.succ Level.zero))) (KExpr.sort (Level.succ Level.zero))))))",
    ),
    DeclarationInput::Proof(
        "kernel_accepts_tc_in_let_body",
        r"forall (R : RedEnv) (tenv : KDeclEnv), KernelAcceptsTcIn R tenv Bool.true accepts_tc_let_context accepts_tc_let_body (KExpr.bvar Nat.zero)",
        r"fun (R : RedEnv) (tenv : KDeclEnv) =>
KernelAcceptsTcIn.app R tenv accepts_tc_let_context (KExpr.lam (KExpr.bvar Nat.zero) (KExpr.bvar Nat.zero)) (KExpr.sort Level.zero) (KExpr.pi (KExpr.bvar Nat.zero) (KExpr.bvar (Nat.succ Nat.zero))) (KExpr.bvar Nat.zero) (KExpr.bvar (Nat.succ Nat.zero)) (KExpr.sort (Level.succ Level.zero))
  (KernelAcceptsTcIn.lam R tenv accepts_tc_let_context (KExpr.bvar Nat.zero) (KExpr.bvar Nat.zero) (KExpr.bvar (Nat.succ Nat.zero)) (KExpr.sort (Level.succ (Level.succ Level.zero))) (Level.succ (Level.succ Level.zero))
    (KernelAcceptsTcIn.bvar R tenv accepts_tc_let_context Nat.zero (CtxEntryIn.defn (KExpr.sort (Level.succ (Level.succ Level.zero))) (KExpr.sort (Level.succ Level.zero)))
      (Eq.refl (OptionType CtxEntryIn) (OptionType.some CtxEntryIn (CtxEntryIn.defn (KExpr.sort (Level.succ (Level.succ Level.zero))) (KExpr.sort (Level.succ Level.zero))))))
    (KernelAcceptsTcIn.cdp R tenv accepts_tc_let_context (KExpr.sort (Level.succ (Level.succ Level.zero))) (KExpr.sort (Level.succ (Level.succ Level.zero))) (DefEqCDPIn.refl R (KExpr.sort (Level.succ (Level.succ Level.zero)))))
    (KernelAcceptsTcIn.bvar R tenv (ListType.cons CtxEntryIn (CtxEntryIn.decl (KExpr.bvar Nat.zero)) accepts_tc_let_context) Nat.zero (CtxEntryIn.decl (KExpr.bvar Nat.zero))
      (Eq.refl (OptionType CtxEntryIn) (OptionType.some CtxEntryIn (CtxEntryIn.decl (KExpr.bvar Nat.zero))))))
  (KernelAcceptsTcIn.cdp R tenv accepts_tc_let_context (KExpr.pi (KExpr.bvar Nat.zero) (KExpr.bvar (Nat.succ Nat.zero))) (KExpr.pi (KExpr.bvar Nat.zero) (KExpr.bvar (Nat.succ Nat.zero))) (DefEqCDPIn.refl R (KExpr.pi (KExpr.bvar Nat.zero) (KExpr.bvar (Nat.succ Nat.zero)))))
  (KernelAcceptsTcIn.sort R tenv accepts_tc_let_context Level.zero)
  (accepts_tc_let_zeta_arg R tenv)",
    ),
    DeclarationInput::Proof(
        "kernel_accepts_tc_in_let_zeta",
        r"forall (R : RedEnv) (tenv : KDeclEnv), KernelAcceptsTcIn R tenv Bool.true (ListType.nil CtxEntryIn) (KExpr.let_ (KExpr.sort (Level.succ (Level.succ Level.zero))) (KExpr.sort (Level.succ Level.zero)) accepts_tc_let_body) (KExpr.sort (Level.succ Level.zero))",
        r"fun (R : RedEnv) (tenv : KDeclEnv) =>
KernelAcceptsTcIn.let_def R tenv (ListType.nil CtxEntryIn) (KExpr.sort (Level.succ (Level.succ Level.zero))) (KExpr.sort (Level.succ Level.zero)) accepts_tc_let_body (KExpr.sort (Level.succ (Level.succ (Level.succ Level.zero)))) (Level.succ (Level.succ (Level.succ Level.zero))) (KExpr.sort (Level.succ (Level.succ Level.zero))) (KExpr.bvar Nat.zero)
  (KernelAcceptsTcIn.sort R tenv (ListType.nil CtxEntryIn) (Level.succ (Level.succ Level.zero)))
  (KernelAcceptsTcIn.cdp R tenv (ListType.nil CtxEntryIn) (KExpr.sort (Level.succ (Level.succ (Level.succ Level.zero)))) (KExpr.sort (Level.succ (Level.succ (Level.succ Level.zero)))) (DefEqCDPIn.refl R (KExpr.sort (Level.succ (Level.succ (Level.succ Level.zero))))))
  (KernelAcceptsTcIn.sort R tenv (ListType.nil CtxEntryIn) (Level.succ Level.zero))
  (KernelAcceptsTcIn.cdp R tenv (ListType.nil CtxEntryIn) (KExpr.sort (Level.succ (Level.succ Level.zero))) (KExpr.sort (Level.succ (Level.succ Level.zero))) (DefEqCDPIn.refl R (KExpr.sort (Level.succ (Level.succ Level.zero)))))
  (kernel_accepts_tc_in_let_body R tenv)",
    ),
    DeclarationInput::Proof(
        "accepts_tc_let_zeta_sound",
        r"forall (R : RedEnv) (tenv : KDeclEnv), TypingTcIn R tenv Bool.true (ListType.nil CtxEntryIn) (KExpr.let_ (KExpr.sort (Level.succ (Level.succ Level.zero))) (KExpr.sort (Level.succ Level.zero)) accepts_tc_let_body) (KExpr.sort (Level.succ Level.zero))",
        r"fun (R : RedEnv) (tenv : KDeclEnv) =>
kernel_accepts_tc_in_sound R tenv Bool.true (ListType.nil CtxEntryIn) (KExpr.let_ (KExpr.sort (Level.succ (Level.succ Level.zero))) (KExpr.sort (Level.succ Level.zero)) accepts_tc_let_body) (KExpr.sort (Level.succ Level.zero))
  (kernel_accepts_tc_in_let_zeta R tenv)",
    ),
    // ── Nat literals: the deployed offset peel and the literal recursor major.
    DeclarationInput::Proof(
        "accepts_tc_offset_peel",
        r"forall (R : RedEnv) (tenv : KDeclEnv) (G : ListType CtxEntryIn) (n : Nat) (x : KExpr),
 KernelAcceptsTcIn R tenv Bool.false G (literal_nat n) x ->
 KernelAcceptsTcIn R tenv Bool.false G (literal_nat (Nat.succ n)) (KExpr.app (KExpr.const accepts_tc_nat_succ_name (ListType.nil Level)) x)",
        r"fun (R : RedEnv) (tenv : KDeclEnv) (G : ListType CtxEntryIn) (n : Nat) (x : KExpr)
 (h : KernelAcceptsTcIn R tenv Bool.false G (literal_nat n) x) =>
KernelAcceptsTcIn.trans R tenv G (literal_nat (Nat.succ n))
  (KExpr.app (KExpr.const accepts_tc_nat_succ_name (ListType.nil Level)) (literal_nat n))
  (KExpr.app (KExpr.const accepts_tc_nat_succ_name (ListType.nil Level)) x)
  (KernelAcceptsTcIn.lit_succ R tenv G n)
  (KernelAcceptsTcIn.app_cong R tenv G
    (KExpr.const accepts_tc_nat_succ_name (ListType.nil Level)) (KExpr.const accepts_tc_nat_succ_name (ListType.nil Level))
    (literal_nat n) x
    (KernelAcceptsTcIn.cdp R tenv G (KExpr.const accepts_tc_nat_succ_name (ListType.nil Level))
      (KExpr.const accepts_tc_nat_succ_name (ListType.nil Level))
      (DefEqCDPIn.refl R (KExpr.const accepts_tc_nat_succ_name (ListType.nil Level))))
    h)",
    ),
    DeclarationInput::Proof(
        "accepts_tc_iota_major_literal",
        r"forall (R : RedEnv) (tenv : KDeclEnv) (G : ListType CtxEntryIn) (f : KExpr) (n : Nat) (rhs : KExpr),
 DefEqCDPIn R (KExpr.app f (KExpr.app (KExpr.const accepts_tc_nat_succ_name (ListType.nil Level)) (literal_nat n))) rhs ->
 KernelAcceptsTcIn R tenv Bool.false G (KExpr.app f (literal_nat (Nat.succ n))) rhs",
        r"fun (R : RedEnv) (tenv : KDeclEnv) (G : ListType CtxEntryIn) (f : KExpr) (n : Nat) (rhs : KExpr)
 (h : DefEqCDPIn R (KExpr.app f (KExpr.app (KExpr.const accepts_tc_nat_succ_name (ListType.nil Level)) (literal_nat n))) rhs) =>
KernelAcceptsTcIn.trans R tenv G (KExpr.app f (literal_nat (Nat.succ n)))
  (KExpr.app f (KExpr.app (KExpr.const accepts_tc_nat_succ_name (ListType.nil Level)) (literal_nat n))) rhs
  (KernelAcceptsTcIn.app_cong R tenv G f f (literal_nat (Nat.succ n))
    (KExpr.app (KExpr.const accepts_tc_nat_succ_name (ListType.nil Level)) (literal_nat n))
    (KernelAcceptsTcIn.cdp R tenv G f f (DefEqCDPIn.refl R f))
    (KernelAcceptsTcIn.lit_succ R tenv G n))
  (KernelAcceptsTcIn.cdp R tenv G
    (KExpr.app f (KExpr.app (KExpr.const accepts_tc_nat_succ_name (ListType.nil Level)) (literal_nat n))) rhs h)",
    ),
    DeclarationInput::Proof(
        "kernel_accepts_tc_in_lit_two",
        r"forall (R : RedEnv) (tenv : KDeclEnv) (G : ListType CtxEntryIn),
 KernelAcceptsTcIn R tenv Bool.false G (literal_nat (Nat.succ (Nat.succ Nat.zero)))
  (KExpr.app (KExpr.const accepts_tc_nat_succ_name (ListType.nil Level))
    (KExpr.app (KExpr.const accepts_tc_nat_succ_name (ListType.nil Level))
      (KExpr.const accepts_tc_nat_zero_name (ListType.nil Level))))",
        r"fun (R : RedEnv) (tenv : KDeclEnv) (G : ListType CtxEntryIn) =>
accepts_tc_offset_peel R tenv G (Nat.succ Nat.zero)
  (KExpr.app (KExpr.const accepts_tc_nat_succ_name (ListType.nil Level)) (KExpr.const accepts_tc_nat_zero_name (ListType.nil Level)))
  (accepts_tc_offset_peel R tenv G Nat.zero (KExpr.const accepts_tc_nat_zero_name (ListType.nil Level))
    (KernelAcceptsTcIn.lit_zero R tenv G))",
    ),
    DeclarationInput::Proof(
        "accepts_tc_lit_two_sound",
        r"forall (R : RedEnv) (tenv : KDeclEnv) (G : ListType CtxEntryIn),
 TypingTcIn R tenv Bool.false G (literal_nat (Nat.succ (Nat.succ Nat.zero)))
  (KExpr.app (KExpr.const accepts_tc_nat_succ_name (ListType.nil Level))
    (KExpr.app (KExpr.const accepts_tc_nat_succ_name (ListType.nil Level))
      (KExpr.const accepts_tc_nat_zero_name (ListType.nil Level))))",
        r"fun (R : RedEnv) (tenv : KDeclEnv) (G : ListType CtxEntryIn) =>
kernel_accepts_tc_in_sound R tenv Bool.false G (literal_nat (Nat.succ (Nat.succ Nat.zero)))
  (KExpr.app (KExpr.const accepts_tc_nat_succ_name (ListType.nil Level))
    (KExpr.app (KExpr.const accepts_tc_nat_succ_name (ListType.nil Level))
      (KExpr.const accepts_tc_nat_zero_name (ListType.nil Level))))
  (kernel_accepts_tc_in_lit_two R tenv G)",
    ),
];
