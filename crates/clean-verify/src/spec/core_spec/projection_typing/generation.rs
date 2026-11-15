// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Additive projection typing prerequisites: generation.

use super::DeclarationInput;

pub(super) const DECLARATIONS: &[DeclarationInput] = &[
    DeclarationInput::Inductive(
        r"inductive SemanticTypingCDPAppReturn (R : RedEnv) (tenv : KDeclEnv)
 (G : ListType KExpr) (f : KExpr) (a : KExpr) (T : KExpr) : Type
| intro : forall (A : KExpr) (B : KExpr),
 TypingCDPCtxConvIn R tenv G f (KExpr.pi A B) -> TypingCDPCtxConvIn R tenv G a A ->
 DefEqCDPIn R (instantiate B a) T -> SemanticTypingCDPAppReturn R tenv G f a T",
    ),
    DeclarationInput::Inductive(
        r"inductive SemanticTypingCDPConstantReturn (R : RedEnv) (tenv : KDeclEnv)
 (n : Name) (us : ListType Level) (T : KExpr) : Type
| intro : forall (A : KExpr),
 Eq (OptionType KExpr) (kdecl_type_at tenv n us) (OptionType.some KExpr A) ->
 DefEqCDPIn R A T -> SemanticTypingCDPConstantReturn R tenv n us T",
    ),
    DeclarationInput::Inductive(
        r"inductive SemanticTypingCDPPiReturn (R : RedEnv) (tenv : KDeclEnv)
 (G : ListType KExpr) (A : KExpr) (B : KExpr) (T : KExpr) : Type
| intro : forall (u : Level) (v : Level),
 TypingCDPCtxConvIn R tenv G A (KExpr.sort u) ->
 TypingCDPCtxConvIn R tenv (ListType.cons KExpr A G) B (KExpr.sort v) ->
 DefEqCDPIn R (KExpr.sort (Level.imax u v)) T -> SemanticTypingCDPPiReturn R tenv G A B T",
    ),
    DeclarationInput::Data(
        "semantic_typing_cdp_generation",
        r"forall (R : RedEnv) (tenv : KDeclEnv)
 (G : ListType KExpr) (e : KExpr) (T : KExpr), Type",
        r"fun (R : RedEnv) (tenv : KDeclEnv)
 (G : ListType KExpr) (e : KExpr) (T : KExpr) => match e with
| KExpr.sort u => Nat
| KExpr.bvar i => Nat
| KExpr.app f a => SemanticTypingCDPAppReturn R tenv G f a T
| KExpr.lam A b => Nat
| KExpr.pi A B => SemanticTypingCDPPiReturn R tenv G A B T
| KExpr.const n us => SemanticTypingCDPConstantReturn R tenv n us T
| KExpr.let_ A v b => Nat
| KExpr.proj S i e => Nat
| KExpr.lit n => Nat",
    ),
    DeclarationInput::Proof(
        "semantic_typing_cdp_generation_convert",
        r"forall (R : RedEnv) (tenv : KDeclEnv)
 (G : ListType KExpr) (e : KExpr), forall (T : KExpr) (U : KExpr),
 semantic_typing_cdp_generation R tenv G e T -> DefEqCDPIn R T U ->
 semantic_typing_cdp_generation R tenv G e U",
        r"fun (R : RedEnv) (tenv : KDeclEnv)
 (G : ListType KExpr) (e : KExpr) =>
 KExpr.rec
  (fun (e0 : KExpr) => forall (T : KExpr) (U : KExpr),
   semantic_typing_cdp_generation R tenv G e0 T -> DefEqCDPIn R T U ->
   semantic_typing_cdp_generation R tenv G e0 U)
  (fun (_u : Level) (T : KExpr) (U : KExpr) (_p : Nat) (_h : DefEqCDPIn R T U) => Nat.zero)
  (fun (_i : Nat) (T : KExpr) (U : KExpr) (_p : Nat) (_h : DefEqCDPIn R T U) => Nat.zero)
  (fun (f : KExpr) (a : KExpr)
   (_ihf : forall (T : KExpr) (U : KExpr),
    semantic_typing_cdp_generation R tenv G f T -> DefEqCDPIn R T U ->
    semantic_typing_cdp_generation R tenv G f U)
   (_iha : forall (T : KExpr) (U : KExpr),
    semantic_typing_cdp_generation R tenv G a T -> DefEqCDPIn R T U ->
    semantic_typing_cdp_generation R tenv G a U) => fun (T : KExpr) (U : KExpr)
 (p : SemanticTypingCDPAppReturn R tenv G f a T) (h : DefEqCDPIn R T U) =>
 SemanticTypingCDPAppReturn.rec R tenv G f a T
  (fun (_p : SemanticTypingCDPAppReturn R tenv G f a T) => SemanticTypingCDPAppReturn R tenv G f a U)
  (fun (A : KExpr) (B : KExpr) (hf : TypingCDPCtxConvIn R tenv G f (KExpr.pi A B))
   (ha : TypingCDPCtxConvIn R tenv G a A) (result : DefEqCDPIn R (instantiate B a) T) =>
   SemanticTypingCDPAppReturn.intro R tenv G f a U A B hf ha
    (DefEqCDPIn.trans R (instantiate B a) T U result h)) p)
  (fun (A : KExpr) (b : KExpr)
   (_ihA : forall (T : KExpr) (U : KExpr),
    semantic_typing_cdp_generation R tenv G A T -> DefEqCDPIn R T U ->
    semantic_typing_cdp_generation R tenv G A U)
   (_ihb : forall (T : KExpr) (U : KExpr),
    semantic_typing_cdp_generation R tenv G b T -> DefEqCDPIn R T U ->
    semantic_typing_cdp_generation R tenv G b U)
   (T : KExpr) (U : KExpr) (_p : Nat) (_h : DefEqCDPIn R T U) => Nat.zero)
  (fun (A : KExpr) (B : KExpr)
   (_ihA : forall (T : KExpr) (U : KExpr),
    semantic_typing_cdp_generation R tenv G A T -> DefEqCDPIn R T U ->
    semantic_typing_cdp_generation R tenv G A U)
   (_ihB : forall (T : KExpr) (U : KExpr),
    semantic_typing_cdp_generation R tenv G B T -> DefEqCDPIn R T U ->
    semantic_typing_cdp_generation R tenv G B U) => fun (T : KExpr) (U : KExpr)
 (p : SemanticTypingCDPPiReturn R tenv G A B T) (h : DefEqCDPIn R T U) =>
 SemanticTypingCDPPiReturn.rec R tenv G A B T
  (fun (_p : SemanticTypingCDPPiReturn R tenv G A B T) => SemanticTypingCDPPiReturn R tenv G A B U)
  (fun (u : Level) (v : Level) (ha : TypingCDPCtxConvIn R tenv G A (KExpr.sort u))
   (hb : TypingCDPCtxConvIn R tenv (ListType.cons KExpr A G) B (KExpr.sort v))
   (result : DefEqCDPIn R (KExpr.sort (Level.imax u v)) T) =>
   SemanticTypingCDPPiReturn.intro R tenv G A B U u v ha hb
    (DefEqCDPIn.trans R (KExpr.sort (Level.imax u v)) T U result h)) p)
  (fun (n : Name) (us : ListType Level) => fun (T : KExpr) (U : KExpr)
 (p : SemanticTypingCDPConstantReturn R tenv n us T) (h : DefEqCDPIn R T U) =>
 SemanticTypingCDPConstantReturn.rec R tenv n us T
  (fun (_p : SemanticTypingCDPConstantReturn R tenv n us T) => SemanticTypingCDPConstantReturn R tenv n us U)
  (fun (A : KExpr)
   (get : Eq (OptionType KExpr) (kdecl_type_at tenv n us) (OptionType.some KExpr A))
   (result : DefEqCDPIn R A T) => SemanticTypingCDPConstantReturn.intro R tenv n us U A get
    (DefEqCDPIn.trans R A T U result h)) p)
  (fun (A : KExpr) (v : KExpr) (b : KExpr)
   (_ihA : forall (T : KExpr) (U : KExpr),
    semantic_typing_cdp_generation R tenv G A T -> DefEqCDPIn R T U ->
    semantic_typing_cdp_generation R tenv G A U)
   (_ihv : forall (T : KExpr) (U : KExpr),
    semantic_typing_cdp_generation R tenv G v T -> DefEqCDPIn R T U ->
    semantic_typing_cdp_generation R tenv G v U)
   (_ihb : forall (T : KExpr) (U : KExpr),
    semantic_typing_cdp_generation R tenv G b T -> DefEqCDPIn R T U ->
    semantic_typing_cdp_generation R tenv G b U)
   (T : KExpr) (U : KExpr) (_p : Nat) (_h : DefEqCDPIn R T U) => Nat.zero)
  (fun (_S : Name) (_i : Nat) (e0 : KExpr)
   (_ihe : forall (T : KExpr) (U : KExpr),
    semantic_typing_cdp_generation R tenv G e0 T -> DefEqCDPIn R T U ->
    semantic_typing_cdp_generation R tenv G e0 U)
   (T : KExpr) (U : KExpr) (_p : Nat) (_h : DefEqCDPIn R T U) => Nat.zero)
  (fun (_n : Nat) (T : KExpr) (U : KExpr) (_p : Nat) (_h : DefEqCDPIn R T U) => Nat.zero) e",
    ),
    DeclarationInput::Proof(
        "typingcdpctxconv_in_generation",
        r"forall (R : RedEnv) (tenv : KDeclEnv)
 (G : ListType KExpr) (e : KExpr) (T : KExpr) (h : TypingCDPCtxConvIn R tenv G e T), semantic_typing_cdp_generation R tenv G e T",
        r"fun (R : RedEnv) (tenv : KDeclEnv)
 (G : ListType KExpr) (e : KExpr) (T : KExpr) (h : TypingCDPCtxConvIn R tenv G e T) => TypingCDPCtxConvIn.rec R tenv
  (fun (G0 : ListType KExpr) (e0 : KExpr) (T0 : KExpr)
   (_h : TypingCDPCtxConvIn R tenv G0 e0 T0) => semantic_typing_cdp_generation R tenv G0 e0 T0)
  (fun (G0 : ListType KExpr) (i : Nat) (A : KExpr)
   (_get : Eq (OptionType KExpr) (ctx_lookup G0 i) (OptionType.some KExpr A)) => Nat.zero)
  (fun (_G0 : ListType KExpr) (_u : Level) => Nat.zero)
  (fun (G0 : ListType KExpr) (A : KExpr) (B : KExpr) (u : Level) (v : Level)
   (ha : TypingCDPCtxConvIn R tenv G0 A (KExpr.sort u))
   (hb : TypingCDPCtxConvIn R tenv (ListType.cons KExpr A G0) B (KExpr.sort v))
   (_iha : semantic_typing_cdp_generation R tenv G0 A (KExpr.sort u))
   (_ihb : semantic_typing_cdp_generation R tenv (ListType.cons KExpr A G0) B (KExpr.sort v)) =>
   SemanticTypingCDPPiReturn.intro R tenv G0 A B (KExpr.sort (Level.imax u v)) u v ha hb
    (DefEqCDPIn.refl R (KExpr.sort (Level.imax u v))))
  (fun (G0 : ListType KExpr) (A : KExpr) (b : KExpr) (B : KExpr) (u : Level)
   (_ha : TypingCDPCtxConvIn R tenv G0 A (KExpr.sort u))
   (_hb : TypingCDPCtxConvIn R tenv (ListType.cons KExpr A G0) b B)
   (_iha : semantic_typing_cdp_generation R tenv G0 A (KExpr.sort u))
   (_ihb : semantic_typing_cdp_generation R tenv (ListType.cons KExpr A G0) b B) => Nat.zero)
  (fun (G0 : ListType KExpr) (f : KExpr) (a : KExpr) (A : KExpr) (B : KExpr)
   (hf : TypingCDPCtxConvIn R tenv G0 f (KExpr.pi A B)) (ha : TypingCDPCtxConvIn R tenv G0 a A)
   (_ihf : semantic_typing_cdp_generation R tenv G0 f (KExpr.pi A B))
   (_iha : semantic_typing_cdp_generation R tenv G0 a A) =>
   SemanticTypingCDPAppReturn.intro R tenv G0 f a (instantiate B a) A B hf ha
    (DefEqCDPIn.refl R (instantiate B a)))
  (fun (G0 : ListType KExpr) (n : Name) (us : ListType Level) (A : KExpr)
   (get : Eq (OptionType KExpr) (kdecl_type_at tenv n us) (OptionType.some KExpr A)) =>
   SemanticTypingCDPConstantReturn.intro R tenv n us A A get (DefEqCDPIn.refl R A))
  (fun (G0 : ListType KExpr) (e0 : KExpr) (A : KExpr) (B : KExpr)
   (_typed : TypingCDPCtxConvIn R tenv G0 e0 A) (convert : DefEqCDPIn R A B)
   (ih : semantic_typing_cdp_generation R tenv G0 e0 A) =>
   semantic_typing_cdp_generation_convert R tenv G0 e0 A B ih convert)
  (fun (G0 : ListType KExpr) (A : KExpr) (v : KExpr) (b : KExpr) (B : KExpr) (u : Level)
   (_ht : TypingCDPCtxConvIn R tenv G0 A (KExpr.sort u)) (_hv : TypingCDPCtxConvIn R tenv G0 v A)
   (_hb : TypingCDPCtxConvIn R tenv (ListType.cons KExpr A G0) b B)
   (_iht : semantic_typing_cdp_generation R tenv G0 A (KExpr.sort u))
   (_ihv : semantic_typing_cdp_generation R tenv G0 v A)
   (_ihb : semantic_typing_cdp_generation R tenv (ListType.cons KExpr A G0) b B) => Nat.zero)
  (fun (_G0 : ListType KExpr) (_n : Nat) => Nat.zero)
  (fun (_G0 : ListType KExpr) (_n : Nat) => Nat.zero) G e T h",
    ),
    DeclarationInput::Proof(
        "typingcdpctxconv_in_app_gen",
        r"forall (R : RedEnv) (tenv : KDeclEnv)
 (G : ListType KExpr) (f : KExpr) (a : KExpr) (T : KExpr)
 (h : TypingCDPCtxConvIn R tenv G (KExpr.app f a) T) (C : Type)
 (consume : forall (A : KExpr) (B : KExpr), TypingCDPCtxConvIn R tenv G f (KExpr.pi A B) ->
 TypingCDPCtxConvIn R tenv G a A -> DefEqCDPIn R (instantiate B a) T -> C), C",
        r"fun (R : RedEnv) (tenv : KDeclEnv)
 (G : ListType KExpr) (f : KExpr) (a : KExpr) (T : KExpr)
 (h : TypingCDPCtxConvIn R tenv G (KExpr.app f a) T) (C : Type)
 (consume : forall (A : KExpr) (B : KExpr), TypingCDPCtxConvIn R tenv G f (KExpr.pi A B) ->
 TypingCDPCtxConvIn R tenv G a A -> DefEqCDPIn R (instantiate B a) T -> C) => SemanticTypingCDPAppReturn.rec R tenv G f a T
  (fun (_p : SemanticTypingCDPAppReturn R tenv G f a T) => C) consume
  (typingcdpctxconv_in_generation R tenv G (KExpr.app f a) T h)",
    ),
    DeclarationInput::Proof(
        "typingcdpctxconv_in_constant_gen",
        r"forall (R : RedEnv) (tenv : KDeclEnv)
 (G : ListType KExpr) (n : Name) (us : ListType Level) (T : KExpr)
 (h : TypingCDPCtxConvIn R tenv G (KExpr.const n us) T) (C : Type)
 (consume : forall (A : KExpr),
 Eq (OptionType KExpr) (kdecl_type_at tenv n us) (OptionType.some KExpr A) -> DefEqCDPIn R A T -> C), C",
        r"fun (R : RedEnv) (tenv : KDeclEnv)
 (G : ListType KExpr) (n : Name) (us : ListType Level) (T : KExpr)
 (h : TypingCDPCtxConvIn R tenv G (KExpr.const n us) T) (C : Type)
 (consume : forall (A : KExpr),
 Eq (OptionType KExpr) (kdecl_type_at tenv n us) (OptionType.some KExpr A) -> DefEqCDPIn R A T -> C) => SemanticTypingCDPConstantReturn.rec R tenv n us T
  (fun (_p : SemanticTypingCDPConstantReturn R tenv n us T) => C) consume
  (typingcdpctxconv_in_generation R tenv G (KExpr.const n us) T h)",
    ),
    DeclarationInput::Proof(
        "typingcdpctxconv_in_pi_gen",
        r"forall (R : RedEnv) (tenv : KDeclEnv)
 (G : ListType KExpr) (A : KExpr) (B : KExpr) (T : KExpr)
 (h : TypingCDPCtxConvIn R tenv G (KExpr.pi A B) T) (C : Type)
 (consume : forall (u : Level) (v : Level), TypingCDPCtxConvIn R tenv G A (KExpr.sort u) ->
 TypingCDPCtxConvIn R tenv (ListType.cons KExpr A G) B (KExpr.sort v) ->
 DefEqCDPIn R (KExpr.sort (Level.imax u v)) T -> C), C",
        r"fun (R : RedEnv) (tenv : KDeclEnv)
 (G : ListType KExpr) (A : KExpr) (B : KExpr) (T : KExpr)
 (h : TypingCDPCtxConvIn R tenv G (KExpr.pi A B) T) (C : Type)
 (consume : forall (u : Level) (v : Level), TypingCDPCtxConvIn R tenv G A (KExpr.sort u) ->
 TypingCDPCtxConvIn R tenv (ListType.cons KExpr A G) B (KExpr.sort v) ->
 DefEqCDPIn R (KExpr.sort (Level.imax u v)) T -> C) => SemanticTypingCDPPiReturn.rec R tenv G A B T
  (fun (_p : SemanticTypingCDPPiReturn R tenv G A B T) => C) consume
  (typingcdpctxconv_in_generation R tenv G (KExpr.pi A B) T h)",
    ),
    DeclarationInput::Proof(
        "typingcdpctxconv_in_constant_lookup_failure",
        r"forall (R : RedEnv) (tenv : KDeclEnv)
 (G : ListType KExpr) (n : Name) (us : ListType Level) (T : KExpr)
 (missing : Eq (OptionType KExpr) (kdecl_type_at tenv n us) (OptionType.none KExpr))
 (h : TypingCDPCtxConvIn R tenv G (KExpr.const n us) T), Empty",
        r"fun (R : RedEnv) (tenv : KDeclEnv)
 (G : ListType KExpr) (n : Name) (us : ListType Level) (T : KExpr)
 (missing : Eq (OptionType KExpr) (kdecl_type_at tenv n us) (OptionType.none KExpr))
 (h : TypingCDPCtxConvIn R tenv G (KExpr.const n us) T) => typingcdpctxconv_in_constant_gen R tenv G n us T h Empty
  (fun (A : KExpr)
   (get : Eq (OptionType KExpr) (kdecl_type_at tenv n us) (OptionType.some KExpr A))
   (_convert : DefEqCDPIn R A T) => option_none_ne_some_type KExpr A Empty
    (Eq.trans (OptionType KExpr) (OptionType.none KExpr) (kdecl_type_at tenv n us)
     (OptionType.some KExpr A)
     (Eq.symm (OptionType KExpr) (kdecl_type_at tenv n us) (OptionType.none KExpr) missing) get))",
    ),
    DeclarationInput::Data(
        "cgen_projection",
        r"KExpr",
        r"KExpr.proj kcre_prod_type_name Nat.zero (projection_universe_subject Level.zero)",
    ),
    DeclarationInput::Data(
        "cgen_signature",
        r"KConstSig",
        r"KConstSig.mk (ListType.nil Name) (KExpr.pi (KExpr.sort (Level.succ Level.zero)) cgen_projection)",
    ),
    DeclarationInput::Data(
        "cgen_tenv",
        r"KDeclEnv",
        r"fun (n : Name) => opt_pick KConstSig (name_eqb n Name.anonymous) cgen_signature (OptionType.none KConstSig)",
    ),
    DeclarationInput::Proof(
        "cgen_projection_converts",
        r"DefEqCDPIn the_red_env cgen_projection (KExpr.sort Level.zero)",
        r"DefEqCDPIn.raw the_red_env cgen_projection (KExpr.sort Level.zero)
  (par_reduces_cdp.projection_beta the_red_env kcre_prod_type_name Nat.zero
   (projection_universe_subject Level.zero) (KExpr.sort Level.zero)
   (Eq.refl (OptionType KExpr) (OptionType.some KExpr (KExpr.sort Level.zero))))",
    ),
    DeclarationInput::Proof(
        "cgen_constant_typed",
        r"TypingCDPCtxConvIn the_red_env cgen_tenv (ListType.nil KExpr)
 (KExpr.const Name.anonymous (ListType.nil Level))
 (KExpr.pi (KExpr.sort (Level.succ Level.zero)) cgen_projection)",
        r"TypingCDPCtxConvIn.const the_red_env cgen_tenv (ListType.nil KExpr)
  Name.anonymous (ListType.nil Level) (KExpr.pi (KExpr.sort (Level.succ Level.zero)) cgen_projection)
  (Eq.refl (OptionType KExpr) (OptionType.some KExpr (KExpr.pi (KExpr.sort (Level.succ Level.zero)) cgen_projection)))",
    ),
    DeclarationInput::Proof(
        "cgen_app_typed",
        r"TypingCDPCtxConvIn the_red_env cgen_tenv (ListType.nil KExpr)
 (KExpr.app (KExpr.const Name.anonymous (ListType.nil Level)) (KExpr.sort Level.zero))
 (KExpr.sort Level.zero)",
        r"TypingCDPCtxConvIn.conv the_red_env cgen_tenv (ListType.nil KExpr)
  (KExpr.app (KExpr.const Name.anonymous (ListType.nil Level)) (KExpr.sort Level.zero))
  cgen_projection (KExpr.sort Level.zero)
  (TypingCDPCtxConvIn.app the_red_env cgen_tenv (ListType.nil KExpr)
   (KExpr.const Name.anonymous (ListType.nil Level)) (KExpr.sort Level.zero)
   (KExpr.sort (Level.succ Level.zero)) cgen_projection cgen_constant_typed
   (TypingCDPCtxConvIn.sort the_red_env cgen_tenv (ListType.nil KExpr) Level.zero))
  cgen_projection_converts",
    ),
    DeclarationInput::Proof(
        "cgen_actual_app_generation",
        r"SemanticTypingCDPAppReturn the_red_env cgen_tenv (ListType.nil KExpr)
 (KExpr.const Name.anonymous (ListType.nil Level)) (KExpr.sort Level.zero) (KExpr.sort Level.zero)",
        r"typingcdpctxconv_in_generation the_red_env cgen_tenv (ListType.nil KExpr)
  (KExpr.app (KExpr.const Name.anonymous (ListType.nil Level)) (KExpr.sort Level.zero))
  (KExpr.sort Level.zero) cgen_app_typed",
    ),
    DeclarationInput::Proof(
        "cgen_actual_constant_generation",
        r"SemanticTypingCDPConstantReturn the_red_env cgen_tenv
 Name.anonymous (ListType.nil Level) (KExpr.pi (KExpr.sort (Level.succ Level.zero)) cgen_projection)",
        r"typingcdpctxconv_in_generation the_red_env cgen_tenv (ListType.nil KExpr)
  (KExpr.const Name.anonymous (ListType.nil Level))
  (KExpr.pi (KExpr.sort (Level.succ Level.zero)) cgen_projection) cgen_constant_typed",
    ),
    DeclarationInput::Proof(
        "cgen_actual_pi_generation",
        r"SemanticTypingCDPPiReturn the_red_env cgen_tenv (ListType.nil KExpr)
 (KExpr.sort Level.zero) (KExpr.sort Level.zero)
 (KExpr.sort (Level.imax (Level.succ Level.zero) (Level.succ Level.zero)))",
        r"typingcdpctxconv_in_generation the_red_env cgen_tenv (ListType.nil KExpr)
  (KExpr.pi (KExpr.sort Level.zero) (KExpr.sort Level.zero))
  (KExpr.sort (Level.imax (Level.succ Level.zero) (Level.succ Level.zero)))
  (TypingCDPCtxConvIn.pi the_red_env cgen_tenv (ListType.nil KExpr)
   (KExpr.sort Level.zero) (KExpr.sort Level.zero) (Level.succ Level.zero) (Level.succ Level.zero)
   (TypingCDPCtxConvIn.sort the_red_env cgen_tenv (ListType.nil KExpr) Level.zero)
   (TypingCDPCtxConvIn.sort the_red_env cgen_tenv (ListType.cons KExpr (KExpr.sort Level.zero) (ListType.nil KExpr)) Level.zero))",
    ),
];
#[cfg(test)]
pub(super) const NEGATIVE_CONTROLS: &[(&str, &str, &str)] = &[
    (
        "forged_cgen_wrong_result",
        r"TypingCDPCtxConvIn the_red_env cgen_tenv (ListType.nil KExpr)
 (KExpr.app (KExpr.const Name.anonymous (ListType.nil Level)) (KExpr.sort Level.zero))
 (KExpr.sort (Level.succ Level.zero))",
        r"cgen_app_typed",
    ),
    (
        "forged_cgen_conversion_is_raw_equality",
        r"Eq KExpr cgen_projection (KExpr.sort Level.zero)",
        r"cgen_projection_converts",
    ),
    (
        "forged_cgen_missing_whole_typing",
        r"SemanticTypingCDPAppReturn the_red_env cgen_tenv (ListType.nil KExpr)
 (KExpr.const Name.anonymous (ListType.nil Level)) (KExpr.sort Level.zero) (KExpr.sort Level.zero)",
        r"typingcdpctxconv_in_generation the_red_env cgen_tenv (ListType.nil KExpr)
  (KExpr.app (KExpr.const Name.anonymous (ListType.nil Level)) (KExpr.sort Level.zero)) (KExpr.sort Level.zero)",
    ),
];
#[cfg(test)]
pub(super) const PROOF_ROOTS: &[&str] = &[
    "semantic_typing_cdp_generation_convert",
    "typingcdpctxconv_in_generation",
    "typingcdpctxconv_in_app_gen",
    "typingcdpctxconv_in_constant_gen",
    "typingcdpctxconv_in_pi_gen",
    "typingcdpctxconv_in_constant_lookup_failure",
    "cgen_projection_converts",
    "cgen_constant_typed",
    "cgen_app_typed",
    "cgen_actual_app_generation",
    "cgen_actual_constant_generation",
    "cgen_actual_pi_generation",
];
#[cfg(test)]
pub(super) const DATA_NAMES: &[&str] = &[
    "semantic_typing_cdp_generation",
    "cgen_projection",
    "cgen_signature",
    "cgen_tenv",
];
#[cfg(test)]
pub(super) const INDUCTIVE_NAMES: &[&str] = &[
    "SemanticTypingCDPAppReturn",
    "SemanticTypingCDPConstantReturn",
    "SemanticTypingCDPPiReturn",
];
