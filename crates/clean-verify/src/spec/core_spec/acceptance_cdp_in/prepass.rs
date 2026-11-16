// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Non-seed witness for the major pre-pass: a recursor whose major is a
//! DEFINITION unfolding to the constructor, so head iota and head delta both
//! decline and only the pre-pass (steps on the major, then iota) reaches the
//! sort the Pi arm needs.

use super::DeclarationInput;

// The major pre-pass fixture: recursor `anon` (no params/motives/minors/indices)
// with one rule for the constructor `str anon 0`, and a DEFINITION `str anon 1`
// whose value is that constructor. The major `const (str anon 1) []` is not
// constructor-headed, so head iota declines until the major is delta-reduced.
pub(super) const DECLARATIONS: &[DeclarationInput] = &[
    DeclarationInput::Data(
        r"def accepts_prepass_recmeta : RecMeta := RecMeta.mk Nat.zero Nat.zero Nat.zero Nat.zero Bool.true
  (KConstSig.mk (@ListType.cons Name Name.anonymous (@ListType.nil Name)) (KExpr.sort Level.zero)) Nat.zero",
    ),
    DeclarationInput::Data(
        r"def accepts_prepass_env : RedEnv := RedEnv.mk
  (RecEnv.addRec RecEnv.empty Name.anonymous accepts_prepass_recmeta
    (RecRules.cons
      (RecRule.mk (Name.str Name.anonymous Nat.zero) Nat.zero
        (KExpr.sort (Level.param Name.anonymous))) RecRules.nil))
  (DefEnv.addDef DefEnv.empty (Name.str Name.anonymous (Nat.succ Nat.zero))
    (KDefSig.mk (KConstSig.mk (@ListType.nil Name) (KExpr.sort Level.zero))
      (KExpr.const (Name.str Name.anonymous Nat.zero) (@ListType.nil Level))))
  IndCtorEnv.empty",
    ),
    DeclarationInput::Data(
        r"def accepts_prepass_redex : KExpr :=
KExpr.app (KExpr.const Name.anonymous (@ListType.cons Level (Level.succ Level.zero) (@ListType.nil Level)))
  (KExpr.const (Name.str Name.anonymous (Nat.succ Nat.zero)) (@ListType.nil Level))",
    ),
    DeclarationInput::Data(
        r"def accepts_prepass_context : ListType KExpr := @ListType.cons KExpr accepts_prepass_redex (@ListType.nil KExpr)",
    ),
    DeclarationInput::Proof(
        "accepts_prepass_computes",
        r"@Eq (OptionType KExpr)
  (whnf_fuel_red_wh3 accepts_prepass_env (Nat.succ (Nat.succ (Nat.succ Nat.zero))) accepts_prepass_redex)
  (@OptionType.some KExpr (KExpr.sort (Level.succ Level.zero)))",
        r"@Eq.refl (OptionType KExpr) (@OptionType.some KExpr (KExpr.sort (Level.succ Level.zero)))",
    ),
    DeclarationInput::Proof(
        "accepts_prepass_starved",
        r"@Eq (OptionType KExpr)
  (whnf_fuel_red_wh3 accepts_prepass_env (Nat.succ (Nat.succ Nat.zero)) accepts_prepass_redex)
  (@OptionType.none KExpr)",
        r"@Eq.refl (OptionType KExpr) (@OptionType.none KExpr)",
    ),
    DeclarationInput::Proof(
        "accepts_prepass_head_iota_declines",
        r"@Eq (OptionType KExpr) (iota_reduct (red_rec accepts_prepass_env) accepts_prepass_redex) (@OptionType.none KExpr)",
        r"@Eq.refl (OptionType KExpr) (@OptionType.none KExpr)",
    ),
    DeclarationInput::Proof(
        "accepts_prepass_head_delta_declines",
        r"@Eq (OptionType KExpr) (delta_reduct (red_def accepts_prepass_env) accepts_prepass_redex) (@OptionType.none KExpr)",
        r"@Eq.refl (OptionType KExpr) (@OptionType.none KExpr)",
    ),
    DeclarationInput::Proof(
        "accepts_prepass_trace",
        r"par_reduces_cdp_star accepts_prepass_env accepts_prepass_redex (KExpr.sort (Level.succ Level.zero))",
        r"semantic_join_cdp_old_star accepts_prepass_env accepts_prepass_redex (KExpr.sort (Level.succ Level.zero))
  (whnf_fuel_red_wh3_par_in accepts_prepass_env (Nat.succ (Nat.succ (Nat.succ Nat.zero)))
    accepts_prepass_redex (KExpr.sort (Level.succ Level.zero)) accepts_prepass_computes)",
    ),
    DeclarationInput::Proof(
        "kernel_accepts_in_prepass_pi",
        r"forall (tenv : KDeclEnv), KernelAcceptsIn accepts_prepass_env tenv accepts_prepass_context
  (KExpr.pi (KExpr.bvar Nat.zero) (KExpr.sort Level.zero)) (KExpr.sort (Level.succ Level.zero))",
        r"fun (tenv : KDeclEnv) =>
@KernelAcceptsIn.pi accepts_prepass_env tenv accepts_prepass_context
  (KExpr.bvar Nat.zero) (KExpr.sort Level.zero) accepts_prepass_redex (Level.succ Level.zero)
  (KExpr.sort (Level.succ Level.zero)) (Level.succ Level.zero) (Level.succ Level.zero)
  (@KernelAcceptsIn.bvar accepts_prepass_env tenv accepts_prepass_context Nat.zero accepts_prepass_redex
    (@Eq.refl (OptionType KExpr) (@OptionType.some KExpr accepts_prepass_redex)))
  accepts_prepass_trace
  (@KernelAcceptsIn.sort accepts_prepass_env tenv
    (@ListType.cons KExpr (KExpr.bvar Nat.zero) accepts_prepass_context) Level.zero)
  (@par_reduces_cdp_star.refl accepts_prepass_env (KExpr.sort (Level.succ Level.zero)))
  acceptance_imax_one_one",
    ),
    DeclarationInput::Proof(
        "accepts_prepass_pi_sound",
        r"forall (tenv : KDeclEnv), TypingProjIn accepts_prepass_env tenv accepts_prepass_context
  (KExpr.pi (KExpr.bvar Nat.zero) (KExpr.sort Level.zero)) (KExpr.sort (Level.succ Level.zero))",
        r"fun (tenv : KDeclEnv) =>
kernel_accepts_in_sound accepts_prepass_env tenv accepts_prepass_context
  (KExpr.pi (KExpr.bvar Nat.zero) (KExpr.sort Level.zero)) (KExpr.sort (Level.succ Level.zero))
  (kernel_accepts_in_prepass_pi tenv)",
    ),
    DeclarationInput::Proof(
        "accepts_prepass_seed_has_no_anonymous_recursor",
        r"@Eq (OptionType RecMeta) (recmeta_for (red_rec the_red_env) Name.anonymous) (@OptionType.none RecMeta)",
        r"@Eq.refl (OptionType RecMeta) (@OptionType.none RecMeta)",
    ),
    DeclarationInput::Proof(
        "accepts_prepass_env_not_seed",
        r"@Eq RedEnv accepts_prepass_env the_red_env -> Empty",
        r"fun (same : @Eq RedEnv accepts_prepass_env the_red_env) =>
option_none_ne_some_type RecMeta accepts_prepass_recmeta Empty
  (Eq.trans (OptionType RecMeta) (@OptionType.none RecMeta)
    (recmeta_for (red_rec the_red_env) Name.anonymous)
    (@OptionType.some RecMeta accepts_prepass_recmeta)
    (Eq.symm (OptionType RecMeta)
      (recmeta_for (red_rec the_red_env) Name.anonymous) (@OptionType.none RecMeta)
      accepts_prepass_seed_has_no_anonymous_recursor)
    (Eq.symm (OptionType RecMeta) (@OptionType.some RecMeta accepts_prepass_recmeta)
      (recmeta_for (red_rec the_red_env) Name.anonymous)
      (Eq.cong RedEnv (OptionType RecMeta)
        (fun (R : RedEnv) => recmeta_for (red_rec R) Name.anonymous)
        accepts_prepass_env the_red_env same)))",
    ),
];
