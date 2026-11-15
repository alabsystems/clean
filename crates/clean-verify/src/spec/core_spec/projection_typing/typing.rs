// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Additive projection typing prerequisites: typing.

use super::DeclarationInput;

pub(super) const DECLARATIONS: &[DeclarationInput] = &[
    DeclarationInput::Inductive(
        r"inductive TypingCDPCtxConvIn (R : RedEnv) (tenv : KDeclEnv) : ListType KExpr -> KExpr -> KExpr -> Type
| var : forall (G : ListType KExpr) (i : Nat) (A : KExpr), Eq (OptionType KExpr) (ctx_lookup G i) (OptionType.some KExpr A) -> TypingCDPCtxConvIn R tenv G (KExpr.bvar i) (lift_at A Nat.zero (Nat.succ i))
| sort : forall (G : ListType KExpr) (u : Level), TypingCDPCtxConvIn R tenv G (KExpr.sort u) (KExpr.sort (Level.succ u))
| pi : forall (G : ListType KExpr) (A : KExpr) (B : KExpr) (u : Level) (v : Level), TypingCDPCtxConvIn R tenv G A (KExpr.sort u) -> TypingCDPCtxConvIn R tenv (ListType.cons KExpr A G) B (KExpr.sort v) -> TypingCDPCtxConvIn R tenv G (KExpr.pi A B) (KExpr.sort (Level.imax u v))
| lam : forall (G : ListType KExpr) (A : KExpr) (b : KExpr) (B : KExpr) (u : Level), TypingCDPCtxConvIn R tenv G A (KExpr.sort u) -> TypingCDPCtxConvIn R tenv (ListType.cons KExpr A G) b B -> TypingCDPCtxConvIn R tenv G (KExpr.lam A b) (KExpr.pi A B)
| app : forall (G : ListType KExpr) (f : KExpr) (a : KExpr) (A : KExpr) (B : KExpr), TypingCDPCtxConvIn R tenv G f (KExpr.pi A B) -> TypingCDPCtxConvIn R tenv G a A -> TypingCDPCtxConvIn R tenv G (KExpr.app f a) (instantiate B a)
| const : forall (G : ListType KExpr) (n : Name) (us : ListType Level) (A : KExpr), Eq (OptionType KExpr) (kdecl_type_at tenv n us) (OptionType.some KExpr A) -> TypingCDPCtxConvIn R tenv G (KExpr.const n us) A
| conv : forall (G : ListType KExpr) (e : KExpr) (A : KExpr) (B : KExpr), TypingCDPCtxConvIn R tenv G e A -> DefEqCDPIn R A B -> TypingCDPCtxConvIn R tenv G e B
| let_ : forall (G : ListType KExpr) (A : KExpr) (v : KExpr) (b : KExpr) (B : KExpr) (u : Level), TypingCDPCtxConvIn R tenv G A (KExpr.sort u) -> TypingCDPCtxConvIn R tenv G v A -> TypingCDPCtxConvIn R tenv (ListType.cons KExpr A G) b B -> TypingCDPCtxConvIn R tenv G (KExpr.let_ A v b) (instantiate B v)
| lit_nat : forall (G : ListType KExpr) (n : Nat), TypingCDPCtxConvIn R tenv G (literal_nat n) literal_nat_type
| lit_string : forall (G : ListType KExpr) (n : Nat), TypingCDPCtxConvIn R tenv G (literal_string n) literal_string_type",
    ),
    DeclarationInput::Proof(
        "typingctxconv_in_to_cdp_in",
        r"forall (R : RedEnv) (tenv : KDeclEnv) (G : ListType KExpr) (e T : KExpr),
 TypingCtxConvIn R tenv G e T -> TypingCDPCtxConvIn R tenv G e T",
        r"fun (R : RedEnv) (tenv : KDeclEnv) (G : ListType KExpr) (e T : KExpr)
 (h : TypingCtxConvIn R tenv G e T) =>
 TypingCtxConvIn.rec R tenv
  (fun (G0 : ListType KExpr) (e0 T0 : KExpr) (_h : TypingCtxConvIn R tenv G0 e0 T0) => TypingCDPCtxConvIn R tenv G0 e0 T0)
  (fun (G0 : ListType KExpr) (i : Nat) (A : KExpr) (get : Eq (OptionType KExpr) (ctx_lookup G0 i) (OptionType.some KExpr A)) => TypingCDPCtxConvIn.var R tenv G0 i A get)
  (fun (G0 : ListType KExpr) (u : Level) => TypingCDPCtxConvIn.sort R tenv G0 u)
  (fun (G0 : ListType KExpr) (A B : KExpr) (u v : Level)
   (_hA : TypingCtxConvIn R tenv G0 A (KExpr.sort u)) (_hB : TypingCtxConvIn R tenv (ListType.cons KExpr A G0) B (KExpr.sort v))
   (ihA : TypingCDPCtxConvIn R tenv G0 A (KExpr.sort u)) (ihB : TypingCDPCtxConvIn R tenv (ListType.cons KExpr A G0) B (KExpr.sort v)) => TypingCDPCtxConvIn.pi R tenv G0 A B u v ihA ihB)
  (fun (G0 : ListType KExpr) (A b B : KExpr) (u : Level)
   (_hA : TypingCtxConvIn R tenv G0 A (KExpr.sort u)) (_hb : TypingCtxConvIn R tenv (ListType.cons KExpr A G0) b B)
   (ihA : TypingCDPCtxConvIn R tenv G0 A (KExpr.sort u)) (ihb : TypingCDPCtxConvIn R tenv (ListType.cons KExpr A G0) b B) => TypingCDPCtxConvIn.lam R tenv G0 A b B u ihA ihb)
  (fun (G0 : ListType KExpr) (f a A B : KExpr)
   (_hf : TypingCtxConvIn R tenv G0 f (KExpr.pi A B)) (_ha : TypingCtxConvIn R tenv G0 a A)
   (ihf : TypingCDPCtxConvIn R tenv G0 f (KExpr.pi A B)) (iha : TypingCDPCtxConvIn R tenv G0 a A) => TypingCDPCtxConvIn.app R tenv G0 f a A B ihf iha)
  (fun (G0 : ListType KExpr) (n : Name) (us : ListType Level) (A : KExpr) (get : Eq (OptionType KExpr) (kdecl_type_at tenv n us) (OptionType.some KExpr A)) => TypingCDPCtxConvIn.const R tenv G0 n us A get)
  (fun (G0 : ListType KExpr) (e0 A B : KExpr) (_he : TypingCtxConvIn R tenv G0 e0 A) (heq : DefEqIn R A B)
   (ihe : TypingCDPCtxConvIn R tenv G0 e0 A) => TypingCDPCtxConvIn.conv R tenv G0 e0 A B ihe (def_eq_in_to_cdp_in R A B heq))
  (fun (G0 : ListType KExpr) (A v b B : KExpr) (u : Level)
   (_hA : TypingCtxConvIn R tenv G0 A (KExpr.sort u)) (_hv : TypingCtxConvIn R tenv G0 v A) (_hb : TypingCtxConvIn R tenv (ListType.cons KExpr A G0) b B)
   (ihA : TypingCDPCtxConvIn R tenv G0 A (KExpr.sort u)) (ihv : TypingCDPCtxConvIn R tenv G0 v A) (ihb : TypingCDPCtxConvIn R tenv (ListType.cons KExpr A G0) b B) => TypingCDPCtxConvIn.let_ R tenv G0 A v b B u ihA ihv ihb)
  (fun (G0 : ListType KExpr) (n : Nat) => TypingCDPCtxConvIn.lit_nat R tenv G0 n)
  (fun (G0 : ListType KExpr) (n : Nat) => TypingCDPCtxConvIn.lit_string R tenv G0 n)
  G e T h",
    ),
    DeclarationInput::Proof(
        "dp_cdp_field1_from_whole",
        r"forall (T D : KExpr),
 TypingCtxConvIn dp_R dp_tenv (ListType.nil KExpr) dp_subject T ->
 Eq (OptionType KExpr) dp_inferred_field1 (OptionType.some KExpr D) ->
 TypingCDPCtxConvIn dp_R dp_tenv (ListType.nil KExpr) dp_zero D",
        r"fun (T D : KExpr)
 (whole : TypingCtxConvIn dp_R dp_tenv (ListType.nil KExpr) dp_subject T)
 (domain_run : Eq (OptionType KExpr) dp_inferred_field1 (OptionType.some KExpr D)) =>
 dp_field1_connected T D whole domain_run (TypingCDPCtxConvIn dp_R dp_tenv (ListType.nil KExpr) dp_zero D)
  (fun (selected : TypingCtxConvIn dp_R dp_tenv (ListType.nil KExpr) dp_zero dp_nat)
   (converted : DefEqCDPIn dp_R dp_nat D) =>
   TypingCDPCtxConvIn.conv dp_R dp_tenv (ListType.nil KExpr) dp_zero dp_nat D
    (typingctxconv_in_to_cdp_in dp_R dp_tenv (ListType.nil KExpr) dp_zero dp_nat selected) converted)",
    ),
    DeclarationInput::Proof(
        "dp_cdp_field1_typed",
        r"TypingCDPCtxConvIn dp_R dp_tenv (ListType.nil KExpr) dp_zero dp_domain",
        r"dp_cdp_field1_from_whole dp_family dp_domain dp_actual_whole dp_inferred_field1_run",
    ),
    DeclarationInput::Proof(
        "dp_cdp_whole_typed",
        r"TypingCDPCtxConvIn dp_R dp_tenv (ListType.nil KExpr) dp_subject dp_family",
        r"typingctxconv_in_to_cdp_in dp_R dp_tenv (ListType.nil KExpr) dp_subject dp_family dp_actual_whole",
    ),
    DeclarationInput::Proof(
        "dp_cdp_old_beta_conversion_embeds",
        r"TypingCDPCtxConvIn dp_R dp_tenv (ListType.nil KExpr) dp_subject
 (KExpr.app (KExpr.lam (KExpr.sort Level.zero) dp_family) (KExpr.sort Level.zero))",
        r"typingctxconv_in_to_cdp_in dp_R dp_tenv (ListType.nil KExpr) dp_subject
 (KExpr.app (KExpr.lam (KExpr.sort Level.zero) dp_family) (KExpr.sort Level.zero))
 (TypingCtxConvIn.conv dp_R dp_tenv (ListType.nil KExpr) dp_subject dp_family
  (KExpr.app (KExpr.lam (KExpr.sort Level.zero) dp_family) (KExpr.sort Level.zero)) dp_actual_whole
  (DefEqIn.symm dp_R (KExpr.app (KExpr.lam (KExpr.sort Level.zero) dp_family) (KExpr.sort Level.zero)) dp_family
   (def_eq_in_beta dp_R (KExpr.sort Level.zero) dp_family (KExpr.sort Level.zero))))",
    ),
    DeclarationInput::Proof(
        "typing_cdp_open_var_embeds",
        r"forall (R : RedEnv) (tenv : KDeclEnv) (G : ListType KExpr),
 TypingCDPCtxConvIn R tenv (ListType.cons KExpr (KExpr.bvar Nat.zero) G)
 (KExpr.bvar Nat.zero) (KExpr.bvar (Nat.succ Nat.zero))",
        r"fun (R : RedEnv) (tenv : KDeclEnv) (G : ListType KExpr) =>
 typingctxconv_in_to_cdp_in R tenv (ListType.cons KExpr (KExpr.bvar Nat.zero) G)
  (KExpr.bvar Nat.zero) (KExpr.bvar (Nat.succ Nat.zero))
  (TypingCtxConvIn.var R tenv (ListType.cons KExpr (KExpr.bvar Nat.zero) G) Nat.zero (KExpr.bvar Nat.zero)
   (Eq.refl (OptionType KExpr) (OptionType.some KExpr (KExpr.bvar Nat.zero))))",
    ),
    DeclarationInput::Proof(
        "typing_cdp_nat_literal_embeds",
        r"forall (R : RedEnv) (tenv : KDeclEnv) (G : ListType KExpr) (n : Nat),
 TypingCDPCtxConvIn R tenv G (literal_nat n) literal_nat_type",
        r"fun (R : RedEnv) (tenv : KDeclEnv) (G : ListType KExpr) (n : Nat) =>
 typingctxconv_in_to_cdp_in R tenv G (literal_nat n) literal_nat_type (TypingCtxConvIn.lit_nat R tenv G n)",
    ),
    DeclarationInput::Proof(
        "typing_cdp_string_literal_embeds",
        r"forall (R : RedEnv) (tenv : KDeclEnv) (G : ListType KExpr) (n : Nat),
 TypingCDPCtxConvIn R tenv G (literal_string n) literal_string_type",
        r"fun (R : RedEnv) (tenv : KDeclEnv) (G : ListType KExpr) (n : Nat) =>
 typingctxconv_in_to_cdp_in R tenv G (literal_string n) literal_string_type (TypingCtxConvIn.lit_string R tenv G n)",
    ),
];

#[cfg(test)]
pub(super) const NEGATIVE_CONTROLS: &[(&str, &str, &str)] = &[
    (
        "typing_cdp_reject_old_result_cast",
        r"TypingCtxConvIn dp_R dp_tenv (ListType.nil KExpr) dp_zero dp_domain",
        r"dp_cdp_field1_typed",
    ),
    (
        "typing_cdp_reject_raw_domain_relabel",
        r"TypingCDPCtxConvIn dp_R dp_tenv (ListType.nil KExpr) dp_zero dp_nat",
        r"dp_cdp_field1_typed",
    ),
    (
        "typing_cdp_reject_reversed_conversion",
        r"TypingCDPCtxConvIn dp_R dp_tenv (ListType.nil KExpr) dp_zero dp_domain",
        r"TypingCDPCtxConvIn.conv dp_R dp_tenv (ListType.nil KExpr) dp_zero dp_nat dp_domain
 (typingctxconv_in_to_cdp_in dp_R dp_tenv (ListType.nil KExpr) dp_zero dp_nat dp_actual_selected)
 (DefEqCDPIn.symm dp_R dp_nat dp_domain dp_field1_domain_conversion)",
    ),
    (
        "typing_cdp_reject_selected_as_whole",
        r"TypingCDPCtxConvIn dp_R dp_tenv (ListType.nil KExpr) dp_zero dp_domain",
        r"dp_cdp_field1_from_whole dp_family dp_domain dp_actual_selected dp_inferred_field1_run",
    ),
];

#[cfg(test)]
pub(super) const PROOF_ROOTS: &[&str] = &[
    "typingctxconv_in_to_cdp_in",
    "dp_cdp_field1_from_whole",
    "dp_cdp_field1_typed",
    "dp_cdp_whole_typed",
    "dp_cdp_old_beta_conversion_embeds",
    "typing_cdp_open_var_embeds",
    "typing_cdp_nat_literal_embeds",
    "typing_cdp_string_literal_embeds",
];

#[cfg(test)]
pub(super) const DATA_NAMES: &[&str] = &[];

#[cfg(test)]
pub(super) const INDUCTIVE_NAMES: &[&str] = &["TypingCDPCtxConvIn"];
