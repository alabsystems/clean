// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Additive projection typing prerequisites: instantiation.

use super::DeclarationInput;

pub(super) const DECLARATIONS: &[DeclarationInput] = &[
    DeclarationInput::Proof(
        "def_eq_cdp_in_beta",
        r"forall (R : RedEnv) (A : KExpr) (b : KExpr) (v : KExpr), DefEqCDPIn R (KExpr.app (KExpr.lam A b) v) (instantiate b v)",
        r"fun (R : RedEnv) (A : KExpr) (b : KExpr) (v : KExpr) => @DefEqCDPIn.raw R (KExpr.app (KExpr.lam A b) v) (instantiate b v)
  (@par_reduces_cdp.beta R A A b b v v
   (@par_reduces_cdp.refl R A) (@par_reduces_cdp.refl R b) (@par_reduces_cdp.refl R v))",
    ),
    DeclarationInput::Proof(
        "def_eq_cdp_in_instantiate_congr",
        r"forall (R : RedEnv) (b : KExpr) (b2 : KExpr)
 (v : KExpr) (v2 : KExpr) (hb : DefEqCDPIn R b b2) (hv : DefEqCDPIn R v v2), DefEqCDPIn R (instantiate b v) (instantiate b2 v2)",
        r"fun (R : RedEnv) (b : KExpr) (b2 : KExpr)
 (v : KExpr) (v2 : KExpr) (hb : DefEqCDPIn R b b2) (hv : DefEqCDPIn R v v2) => @DefEqCDPIn.trans R (instantiate b v) (KExpr.app (KExpr.lam (KExpr.sort Level.zero) b) v)
  (instantiate b2 v2)
  (@DefEqCDPIn.symm R (KExpr.app (KExpr.lam (KExpr.sort Level.zero) b) v) (instantiate b v)
   (def_eq_cdp_in_beta R (KExpr.sort Level.zero) b v))
  (@DefEqCDPIn.trans R (KExpr.app (KExpr.lam (KExpr.sort Level.zero) b) v)
   (KExpr.app (KExpr.lam (KExpr.sort Level.zero) b2) v2) (instantiate b2 v2)
   (@DefEqCDPIn.app R (KExpr.lam (KExpr.sort Level.zero) b)
    (KExpr.lam (KExpr.sort Level.zero) b2) v v2
    (@DefEqCDPIn.lam R (KExpr.sort Level.zero) (KExpr.sort Level.zero) b b2
     (@DefEqCDPIn.refl R (KExpr.sort Level.zero)) hb) hv)
   (def_eq_cdp_in_beta R (KExpr.sort Level.zero) b2 v2))",
    ),
    DeclarationInput::Proof(
        "def_eq_cdp_in_instantiate_same",
        r"forall (R : RedEnv) (b : KExpr) (b2 : KExpr)
 (v : KExpr) (hb : DefEqCDPIn R b b2), DefEqCDPIn R (instantiate b v) (instantiate b2 v)",
        r"fun (R : RedEnv) (b : KExpr) (b2 : KExpr)
 (v : KExpr) (hb : DefEqCDPIn R b b2) => def_eq_cdp_in_instantiate_congr R b b2 v v hb (@DefEqCDPIn.refl R v)",
    ),
    DeclarationInput::Proof(
        "def_eq_cdp_in_instantiate_value",
        r"forall (R : RedEnv) (b : KExpr)
 (v : KExpr) (v2 : KExpr) (hv : DefEqCDPIn R v v2), DefEqCDPIn R (instantiate b v) (instantiate b v2)",
        r"fun (R : RedEnv) (b : KExpr)
 (v : KExpr) (v2 : KExpr) (hv : DefEqCDPIn R v v2) => def_eq_cdp_in_instantiate_congr R b b v v2 (@DefEqCDPIn.refl R b) hv",
    ),
    DeclarationInput::Proof(
        "semantic_typing_cdp_const_pi_conversion",
        r"forall (R : RedEnv) (tenv : KDeclEnv)
 (n : Name) (us : ListType Level) (A0 : KExpr) (B0 : KExpr) (F : KExpr) (A : KExpr) (B : KExpr)
 (canonical : @Eq (OptionType KExpr) (kdecl_type_at tenv n us)
  (@OptionType.some KExpr (KExpr.pi A0 B0)))
 (found : @Eq (OptionType KExpr) (kdecl_type_at tenv n us) (@OptionType.some KExpr F))
 (convert : DefEqCDPIn R F (KExpr.pi A B)), DefEqCDPIn R (KExpr.pi A0 B0) (KExpr.pi A B)",
        r"fun (R : RedEnv) (tenv : KDeclEnv)
 (n : Name) (us : ListType Level) (A0 : KExpr) (B0 : KExpr) (F : KExpr) (A : KExpr) (B : KExpr)
 (canonical : @Eq (OptionType KExpr) (kdecl_type_at tenv n us)
  (@OptionType.some KExpr (KExpr.pi A0 B0)))
 (found : @Eq (OptionType KExpr) (kdecl_type_at tenv n us) (@OptionType.some KExpr F))
 (convert : DefEqCDPIn R F (KExpr.pi A B)) => Eq.substType KExpr (fun (T : KExpr) => DefEqCDPIn R T (KExpr.pi A B)) F (KExpr.pi A0 B0)
  (option_some_inj KExpr F (KExpr.pi A0 B0)
   (Eq.trans (OptionType KExpr) (@OptionType.some KExpr F) (kdecl_type_at tenv n us)
    (@OptionType.some KExpr (KExpr.pi A0 B0))
    (Eq.symm (OptionType KExpr) (kdecl_type_at tenv n us) (@OptionType.some KExpr F) found)
    canonical)) convert",
    ),
    DeclarationInput::Proof(
        "typingcdpctxconv_in_const_app_gen",
        r"forall (R : RedEnv) (faithful : RedEnvFaithful R) (rigid : CtorMetadataRigid R (red_ind_ctor R))
 (tenv : KDeclEnv) (G : ListType KExpr) (n : Name) (us : ListType Level)
 (a : KExpr) (T : KExpr) (A0 : KExpr) (B0 : KExpr)
 (canonical : @Eq (OptionType KExpr) (kdecl_type_at tenv n us)
  (@OptionType.some KExpr (KExpr.pi A0 B0)))
 (typed : TypingCDPCtxConvIn R tenv G (KExpr.app (KExpr.const n us) a) T)
 (C : Type) (consume : TypingCDPCtxConvIn R tenv G a A0 ->
  DefEqCDPIn R (instantiate B0 a) T -> C), C",
        r"fun (R : RedEnv) (faithful : RedEnvFaithful R) (rigid : CtorMetadataRigid R (red_ind_ctor R))
 (tenv : KDeclEnv) (G : ListType KExpr) (n : Name) (us : ListType Level)
 (a : KExpr) (T : KExpr) (A0 : KExpr) (B0 : KExpr)
 (canonical : @Eq (OptionType KExpr) (kdecl_type_at tenv n us)
  (@OptionType.some KExpr (KExpr.pi A0 B0)))
 (typed : TypingCDPCtxConvIn R tenv G (KExpr.app (KExpr.const n us) a) T)
 (C : Type) (consume : TypingCDPCtxConvIn R tenv G a A0 ->
  DefEqCDPIn R (instantiate B0 a) T -> C) => typingcdpctxconv_in_app_gen R tenv G (KExpr.const n us) a T typed C
  (fun (A : KExpr) (B : KExpr)
   (hf : TypingCDPCtxConvIn R tenv G (KExpr.const n us) (KExpr.pi A B))
   (ha : TypingCDPCtxConvIn R tenv G a A) (result : DefEqCDPIn R (instantiate B a) T) =>
   typingcdpctxconv_in_constant_gen R tenv G n us (KExpr.pi A B) hf C
    (fun (F : KExpr)
     (found : @Eq (OptionType KExpr) (kdecl_type_at tenv n us) (@OptionType.some KExpr F))
     (convert : DefEqCDPIn R F (KExpr.pi A B)) =>
     def_eq_cdp_in_pi_components R faithful rigid A0 B0 A B
      (semantic_typing_cdp_const_pi_conversion R tenv n us A0 B0 F A B canonical found convert) C
      (fun (domains : DefEqCDPIn R A0 A) (bodies : DefEqCDPIn R B0 B) =>
       consume
        (@TypingCDPCtxConvIn.conv R tenv G a A A0 ha (@DefEqCDPIn.symm R A0 A domains))
        (@DefEqCDPIn.trans R (instantiate B0 a) (instantiate B a) T
         (def_eq_cdp_in_instantiate_same R B0 B a bodies) result))))",
    ),
    DeclarationInput::Proof(
        "dp_cdp_const_app_rigid",
        r"CtorMetadataRigid dp_R (red_ind_ctor dp_R)",
        r"ctor_metadata_rigid_add_ctor dp_R (IndCtorEnv.addInd IndCtorEnv.empty dp_family_name dp_ind_meta) dp_ctor_name dp_ctor_meta
  (ctor_metadata_rigid_add_ind dp_R IndCtorEnv.empty dp_family_name dp_ind_meta (ctor_metadata_rigid_empty dp_R))
  (@Eq.refl (OptionType KExpr) (@OptionType.none KExpr)) (@Eq.refl (OptionType RecMeta) (@OptionType.none RecMeta))",
    ),
    DeclarationInput::Proof(
        "dp_cdp_ctor_partial_typed",
        r"TypingCDPCtxConvIn dp_R dp_tenv (@ListType.nil KExpr)
 (KExpr.app dp_ctor dp_nat) (KExpr.pi dp_nat dp_family)",
        r"@TypingCDPCtxConvIn.app dp_R dp_tenv (@ListType.nil KExpr) dp_ctor dp_nat (KExpr.sort (Level.succ Level.zero)) (KExpr.pi (KExpr.bvar Nat.zero) dp_family)
  (@TypingCDPCtxConvIn.const dp_R dp_tenv (@ListType.nil KExpr) dp_ctor_name (@ListType.nil Level) (kconst_type dp_ctor_signature) dp_ctor_lookup)
  (@TypingCDPCtxConvIn.const dp_R dp_tenv (@ListType.nil KExpr) dp_nat_name (@ListType.nil Level) (KExpr.sort (Level.succ Level.zero))
   (@Eq.refl (OptionType KExpr) (@OptionType.some KExpr (KExpr.sort (Level.succ Level.zero)))))",
    ),
    DeclarationInput::Proof(
        "dp_cdp_ctor_partial_converted",
        r"TypingCDPCtxConvIn dp_R dp_tenv (@ListType.nil KExpr)
 (KExpr.app dp_ctor dp_nat) (KExpr.pi dp_domain dp_family)",
        r"@TypingCDPCtxConvIn.conv dp_R dp_tenv (@ListType.nil KExpr) (KExpr.app dp_ctor dp_nat)
  (KExpr.pi dp_nat dp_family) (KExpr.pi dp_domain dp_family) dp_cdp_ctor_partial_typed
  (def_eq_cdp_in_instantiate_value dp_R (KExpr.pi (KExpr.bvar Nat.zero) dp_family)
   dp_nat dp_domain dp_field1_domain_conversion)",
    ),
    DeclarationInput::Proof(
        "dp_cdp_const_app_argument",
        r"TypingCDPCtxConvIn dp_R dp_tenv (@ListType.nil KExpr) dp_nat (KExpr.sort (Level.succ Level.zero))",
        r"typingcdpctxconv_in_const_app_gen dp_R dp_faithful dp_cdp_const_app_rigid dp_tenv (@ListType.nil KExpr)
  dp_ctor_name (@ListType.nil Level) dp_nat (KExpr.pi dp_domain dp_family)
  (KExpr.sort (Level.succ Level.zero)) (KExpr.pi (KExpr.bvar Nat.zero) dp_family) dp_ctor_lookup dp_cdp_ctor_partial_converted
  (TypingCDPCtxConvIn dp_R dp_tenv (@ListType.nil KExpr) dp_nat (KExpr.sort (Level.succ Level.zero)))
  (fun (argument : TypingCDPCtxConvIn dp_R dp_tenv (@ListType.nil KExpr) dp_nat (KExpr.sort (Level.succ Level.zero)))
   (_result : DefEqCDPIn dp_R (KExpr.pi dp_nat dp_family) (KExpr.pi dp_domain dp_family)) => argument)",
    ),
    DeclarationInput::Proof(
        "dp_cdp_const_app_codomain",
        r"DefEqCDPIn dp_R (KExpr.pi dp_nat dp_family) (KExpr.pi dp_domain dp_family)",
        r"typingcdpctxconv_in_const_app_gen dp_R dp_faithful dp_cdp_const_app_rigid dp_tenv (@ListType.nil KExpr)
  dp_ctor_name (@ListType.nil Level) dp_nat (KExpr.pi dp_domain dp_family)
  (KExpr.sort (Level.succ Level.zero)) (KExpr.pi (KExpr.bvar Nat.zero) dp_family) dp_ctor_lookup dp_cdp_ctor_partial_converted
  (DefEqCDPIn dp_R (KExpr.pi dp_nat dp_family) (KExpr.pi dp_domain dp_family))
  (fun (_argument : TypingCDPCtxConvIn dp_R dp_tenv (@ListType.nil KExpr) dp_nat (KExpr.sort (Level.succ Level.zero)))
   (result : DefEqCDPIn dp_R (KExpr.pi dp_nat dp_family) (KExpr.pi dp_domain dp_family)) => result)",
    ),
    DeclarationInput::Proof(
        "dp_cdp_instantiate_beta_projection",
        r"DefEqCDPIn dp_R
 (KExpr.app (KExpr.lam (KExpr.sort Level.zero) (KExpr.bvar Nat.zero)) dp_domain) dp_nat",
        r"def_eq_cdp_in_instantiate_congr dp_R
  (KExpr.app (KExpr.lam (KExpr.sort Level.zero) (KExpr.bvar Nat.zero)) (KExpr.bvar Nat.zero))
  (KExpr.bvar Nat.zero) dp_domain dp_nat
  (def_eq_cdp_in_beta dp_R (KExpr.sort Level.zero) (KExpr.bvar Nat.zero) (KExpr.bvar Nat.zero))
  (@DefEqCDPIn.symm dp_R dp_nat dp_domain dp_field1_domain_conversion)",
    ),
    DeclarationInput::Proof(
        "cdp_instantiate_retains_outer_variable",
        r"@Eq KExpr
 (instantiate (KExpr.lam (KExpr.sort Level.zero) (KExpr.bvar (Nat.succ Nat.zero))) (KExpr.bvar Nat.zero))
 (KExpr.lam (KExpr.sort Level.zero) (KExpr.bvar (Nat.succ Nat.zero)))",
        r"@Eq.refl KExpr (KExpr.lam (KExpr.sort Level.zero) (KExpr.bvar (Nat.succ Nat.zero)))",
    ),
];
#[cfg(test)]
pub(super) const NEGATIVE_CONTROLS: &[(&str, &str, &str)] = &[
    (
        "cdp_term_reject_beta_endpoint",
        r"forall (R : RedEnv), DefEqCDPIn R (KExpr.app (KExpr.lam (KExpr.sort Level.zero) (KExpr.bvar Nat.zero))
  (KExpr.sort Level.zero)) (KExpr.bvar Nat.zero)",
        r"fun (R : RedEnv) => def_eq_cdp_in_beta R (KExpr.sort Level.zero) (KExpr.bvar Nat.zero) (KExpr.sort Level.zero)",
    ),
    (
        "cdp_term_reject_captured_variable",
        r"@Eq KExpr
 (instantiate (KExpr.lam (KExpr.sort Level.zero) (KExpr.bvar (Nat.succ Nat.zero))) (KExpr.bvar Nat.zero))
 (KExpr.lam (KExpr.sort Level.zero) (KExpr.bvar Nat.zero))",
        r"cdp_instantiate_retains_outer_variable",
    ),
    (
        "cdp_term_reject_wrong_argument_domain",
        r"TypingCDPCtxConvIn dp_R dp_tenv (@ListType.nil KExpr) dp_nat dp_nat",
        r"dp_cdp_const_app_argument",
    ),
    (
        "cdp_term_reject_wrong_arity_lookup",
        r"@Eq (OptionType KExpr)
 (kdecl_type_at dp_tenv dp_ctor_name (@ListType.cons Level Level.zero (@ListType.nil Level)))
 (@OptionType.some KExpr (kconst_type dp_ctor_signature))",
        r"@Eq.refl (OptionType KExpr) (@OptionType.some KExpr (kconst_type dp_ctor_signature))",
    ),
];
#[cfg(test)]
pub(super) const PROOF_ROOTS: &[&str] = &[
    "def_eq_cdp_in_beta",
    "def_eq_cdp_in_instantiate_congr",
    "def_eq_cdp_in_instantiate_same",
    "def_eq_cdp_in_instantiate_value",
    "semantic_typing_cdp_const_pi_conversion",
    "typingcdpctxconv_in_const_app_gen",
    "dp_cdp_const_app_rigid",
    "dp_cdp_ctor_partial_typed",
    "dp_cdp_ctor_partial_converted",
    "dp_cdp_const_app_argument",
    "dp_cdp_const_app_codomain",
    "dp_cdp_instantiate_beta_projection",
    "cdp_instantiate_retains_outer_variable",
];
#[cfg(test)]
pub(super) const DATA_NAMES: &[&str] = &[];
#[cfg(test)]
pub(super) const INDUCTIVE_NAMES: &[&str] = &[];
