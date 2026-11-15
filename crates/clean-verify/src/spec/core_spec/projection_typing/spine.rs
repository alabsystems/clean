// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Additive projection typing prerequisites: spine.

use super::DeclarationInput;

pub(super) const DECLARATIONS: &[DeclarationInput] = &[
    DeclarationInput::Inductive(
        r"inductive TypedRawPiSpineCDP (R : RedEnv) (tenv : KDeclEnv) (G : ListType KExpr) :
 KExpr -> ListType KExpr -> KExpr -> Type
| nil : forall (F : KExpr), TypedRawPiSpineCDP R tenv G F (ListType.nil KExpr) F
| cons : forall (A : KExpr) (B : KExpr) (a : KExpr) (rest : ListType KExpr) (U : KExpr),
 TypingCDPCtxConvIn R tenv G a A -> TypedRawPiSpineCDP R tenv G (instantiate B a) rest U ->
 TypedRawPiSpineCDP R tenv G (KExpr.pi A B) (ListType.cons KExpr a rest) U",
    ),
    DeclarationInput::Data(
        "RawPiHeadCanonicalCDP",
        r"forall (R : RedEnv) (tenv : KDeclEnv) (G : ListType KExpr)
 (h : KExpr) (F : KExpr), Type",
        r"fun (R : RedEnv) (tenv : KDeclEnv) (G : ListType KExpr)
 (h : KExpr) (F : KExpr) => forall (V : KExpr),
 TypingCDPCtxConvIn R tenv G h V -> DefEqCDPIn R F V",
    ),
    DeclarationInput::Proof(
        "raw_pi_head_canonical_cdp_const",
        r"forall (R : RedEnv) (tenv : KDeclEnv) (G : ListType KExpr)
 (n : Name) (us : ListType Level) (F : KExpr)
 (lookup : Eq (OptionType KExpr) (kdecl_type_at tenv n us) (OptionType.some KExpr F)), RawPiHeadCanonicalCDP R tenv G (KExpr.const n us) F",
        r"fun (R : RedEnv) (tenv : KDeclEnv) (G : ListType KExpr)
 (n : Name) (us : ListType Level) (F : KExpr)
 (lookup : Eq (OptionType KExpr) (kdecl_type_at tenv n us) (OptionType.some KExpr F)) => fun (V : KExpr)
 (typed : TypingCDPCtxConvIn R tenv G (KExpr.const n us) V) =>
 typingcdpctxconv_in_constant_gen R tenv G n us V typed (DefEqCDPIn R F V)
  (fun (F2 : KExpr)
   (found : Eq (OptionType KExpr) (kdecl_type_at tenv n us) (OptionType.some KExpr F2))
   (convert : DefEqCDPIn R F2 V) =>
   Eq.substType KExpr (fun (X : KExpr) => DefEqCDPIn R X V) F2 F
    (option_some_inj KExpr F2 F
     (Eq.trans (OptionType KExpr) (OptionType.some KExpr F2) (kdecl_type_at tenv n us)
      (OptionType.some KExpr F)
      (Eq.symm (OptionType KExpr) (kdecl_type_at tenv n us) (OptionType.some KExpr F2) found) lookup))
    convert)",
    ),
    DeclarationInput::Proof(
        "raw_pi_head_canonical_cdp_app",
        r"forall (R : RedEnv) (faithful : RedEnvFaithful R) (rigid : CtorMetadataRigid R (red_ind_ctor R))
 (tenv : KDeclEnv) (G : ListType KExpr) (h : KExpr) (A : KExpr) (B : KExpr) (a : KExpr)
 (canonical : RawPiHeadCanonicalCDP R tenv G h (KExpr.pi A B)), RawPiHeadCanonicalCDP R tenv G (KExpr.app h a) (instantiate B a)",
        r"fun (R : RedEnv) (faithful : RedEnvFaithful R) (rigid : CtorMetadataRigid R (red_ind_ctor R))
 (tenv : KDeclEnv) (G : ListType KExpr) (h : KExpr) (A : KExpr) (B : KExpr) (a : KExpr)
 (canonical : RawPiHeadCanonicalCDP R tenv G h (KExpr.pi A B)) => fun (V : KExpr)
 (typed : TypingCDPCtxConvIn R tenv G (KExpr.app h a) V) =>
 typingcdpctxconv_in_app_gen R tenv G h a V typed (DefEqCDPIn R (instantiate B a) V)
  (fun (A2 : KExpr) (B2 : KExpr) (hf : TypingCDPCtxConvIn R tenv G h (KExpr.pi A2 B2))
   (_ha : TypingCDPCtxConvIn R tenv G a A2) (result : DefEqCDPIn R (instantiate B2 a) V) =>
   def_eq_cdp_in_pi_components R faithful rigid A B A2 B2 (canonical (KExpr.pi A2 B2) hf)
    (DefEqCDPIn R (instantiate B a) V)
    (fun (_domains : DefEqCDPIn R A A2) (bodies : DefEqCDPIn R B B2) =>
     DefEqCDPIn.trans R (instantiate B a) (instantiate B2 a) V
      (def_eq_cdp_in_instantiate_same R B B2 a bodies) result))",
    ),
    DeclarationInput::Inductive(
        r"inductive SemanticTypedSpineCDPReturn (R : RedEnv) (tenv : KDeclEnv) (G : ListType KExpr)
 (h : KExpr) (F : KExpr) (args : ListType KExpr) (U : KExpr) (T : KExpr) : Type
| intro : TypingCDPCtxConvIn R tenv G h F -> TypedRawPiSpineCDP R tenv G F args U ->
 DefEqCDPIn R U T -> SemanticTypedSpineCDPReturn R tenv G h F args U T",
    ),
    DeclarationInput::Proof(
        "semantic_typed_spine_cdp_nil",
        r"forall (R : RedEnv) (tenv : KDeclEnv) (G : ListType KExpr)
 (F : KExpr) (h : KExpr) (canonical : RawPiHeadCanonicalCDP R tenv G h F) (T : KExpr)
 (typed : TypingCDPCtxConvIn R tenv G (apply_spine (ListType.nil KExpr) h) T), SemanticTypedSpineCDPReturn R tenv G h F (ListType.nil KExpr) F T",
        r"fun (R : RedEnv) (tenv : KDeclEnv) (G : ListType KExpr)
 (F : KExpr) (h : KExpr) (canonical : RawPiHeadCanonicalCDP R tenv G h F) (T : KExpr)
 (typed : TypingCDPCtxConvIn R tenv G (apply_spine (ListType.nil KExpr) h) T) => SemanticTypedSpineCDPReturn.intro R tenv G h F (ListType.nil KExpr) F T
  (TypingCDPCtxConvIn.conv R tenv G h T F typed (DefEqCDPIn.symm R F T (canonical T typed)))
  (TypedRawPiSpineCDP.nil R tenv G F) (canonical T typed)",
    ),
    DeclarationInput::Proof(
        "semantic_typed_spine_cdp_cons",
        r"forall (R : RedEnv) (faithful : RedEnvFaithful R) (rigid : CtorMetadataRigid R (red_ind_ctor R))
 (tenv : KDeclEnv) (G : ListType KExpr) (A : KExpr) (B : KExpr) (a : KExpr)
 (rest : ListType KExpr) (U : KExpr)
 (ih : forall (h : KExpr), RawPiHeadCanonicalCDP R tenv G h (instantiate B a) ->
  forall (T : KExpr), TypingCDPCtxConvIn R tenv G (apply_spine rest h) T ->
  SemanticTypedSpineCDPReturn R tenv G h (instantiate B a) rest U T)
 (h : KExpr) (canonical : RawPiHeadCanonicalCDP R tenv G h (KExpr.pi A B)) (T : KExpr)
 (typed : TypingCDPCtxConvIn R tenv G (apply_spine (ListType.cons KExpr a rest) h) T), SemanticTypedSpineCDPReturn R tenv G h (KExpr.pi A B) (ListType.cons KExpr a rest) U T",
        r"fun (R : RedEnv) (faithful : RedEnvFaithful R) (rigid : CtorMetadataRigid R (red_ind_ctor R))
 (tenv : KDeclEnv) (G : ListType KExpr) (A : KExpr) (B : KExpr) (a : KExpr)
 (rest : ListType KExpr) (U : KExpr)
 (ih : forall (h : KExpr), RawPiHeadCanonicalCDP R tenv G h (instantiate B a) ->
  forall (T : KExpr), TypingCDPCtxConvIn R tenv G (apply_spine rest h) T ->
  SemanticTypedSpineCDPReturn R tenv G h (instantiate B a) rest U T)
 (h : KExpr) (canonical : RawPiHeadCanonicalCDP R tenv G h (KExpr.pi A B)) (T : KExpr)
 (typed : TypingCDPCtxConvIn R tenv G (apply_spine (ListType.cons KExpr a rest) h) T) => SemanticTypedSpineCDPReturn.rec R tenv G (KExpr.app h a) (instantiate B a) rest U T
  (fun (_p : SemanticTypedSpineCDPReturn R tenv G (KExpr.app h a) (instantiate B a) rest U T) =>
   SemanticTypedSpineCDPReturn R tenv G h (KExpr.pi A B) (ListType.cons KExpr a rest) U T)
  (fun (head : TypingCDPCtxConvIn R tenv G (KExpr.app h a) (instantiate B a))
   (tail : TypedRawPiSpineCDP R tenv G (instantiate B a) rest U) (result : DefEqCDPIn R U T) =>
   typingcdpctxconv_in_app_gen R tenv G h a (instantiate B a) head
    (SemanticTypedSpineCDPReturn R tenv G h (KExpr.pi A B) (ListType.cons KExpr a rest) U T)
    (fun (A2 : KExpr) (B2 : KExpr) (hf : TypingCDPCtxConvIn R tenv G h (KExpr.pi A2 B2))
     (ha : TypingCDPCtxConvIn R tenv G a A2) (_convert : DefEqCDPIn R (instantiate B2 a) (instantiate B a)) =>
     def_eq_cdp_in_pi_components R faithful rigid A B A2 B2 (canonical (KExpr.pi A2 B2) hf)
      (SemanticTypedSpineCDPReturn R tenv G h (KExpr.pi A B) (ListType.cons KExpr a rest) U T)
      (fun (domains : DefEqCDPIn R A A2) (_bodies : DefEqCDPIn R B B2) =>
       SemanticTypedSpineCDPReturn.intro R tenv G h (KExpr.pi A B) (ListType.cons KExpr a rest) U T
        (TypingCDPCtxConvIn.conv R tenv G h (KExpr.pi A2 B2) (KExpr.pi A B) hf
         (DefEqCDPIn.symm R (KExpr.pi A B) (KExpr.pi A2 B2) (canonical (KExpr.pi A2 B2) hf)))
        (TypedRawPiSpineCDP.cons R tenv G A B a rest U
         (TypingCDPCtxConvIn.conv R tenv G a A2 A ha (DefEqCDPIn.symm R A A2 domains)) tail)
        result)))
  (ih (KExpr.app h a) (raw_pi_head_canonical_cdp_app R faithful rigid tenv G h A B a canonical) T typed)",
    ),
    DeclarationInput::Proof(
        "semantic_typed_spine_cdp_from_trace",
        r"forall (R : RedEnv) (faithful : RedEnvFaithful R) (rigid : CtorMetadataRigid R (red_ind_ctor R))
 (tenv : KDeclEnv) (G : ListType KExpr) (F : KExpr) (args : ListType KExpr) (U : KExpr)
 (trace : RawPiSpineTrace F args U), forall (h : KExpr), RawPiHeadCanonicalCDP R tenv G h F ->
 forall (T : KExpr), TypingCDPCtxConvIn R tenv G (apply_spine args h) T ->
 SemanticTypedSpineCDPReturn R tenv G h F args U T",
        r"fun (R : RedEnv) (faithful : RedEnvFaithful R) (rigid : CtorMetadataRigid R (red_ind_ctor R))
 (tenv : KDeclEnv) (G : ListType KExpr) (F : KExpr) (args : ListType KExpr) (U : KExpr)
 (trace : RawPiSpineTrace F args U) => RawPiSpineTrace.rec
  (fun (F0 : KExpr) (xs : ListType KExpr) (V : KExpr) (_tr : RawPiSpineTrace F0 xs V) =>
   forall (h : KExpr), RawPiHeadCanonicalCDP R tenv G h F0 -> forall (T : KExpr),
   TypingCDPCtxConvIn R tenv G (apply_spine xs h) T -> SemanticTypedSpineCDPReturn R tenv G h F0 xs V T)
  (fun (F0 : KExpr) => semantic_typed_spine_cdp_nil R tenv G F0)
  (fun (A : KExpr) (B : KExpr) (a : KExpr) (rest : ListType KExpr) (V : KExpr)
   (_tr : RawPiSpineTrace (instantiate B a) rest V)
   (ih : forall (h : KExpr), RawPiHeadCanonicalCDP R tenv G h (instantiate B a) ->
    forall (T : KExpr), TypingCDPCtxConvIn R tenv G (apply_spine rest h) T ->
    SemanticTypedSpineCDPReturn R tenv G h (instantiate B a) rest V T) =>
   semantic_typed_spine_cdp_cons R faithful rigid tenv G A B a rest V ih) F args U trace",
    ),
    DeclarationInput::Proof(
        "typingcdpctxconv_in_const_spine",
        r"forall (R : RedEnv) (faithful : RedEnvFaithful R) (rigid : CtorMetadataRigid R (red_ind_ctor R))
 (tenv : KDeclEnv) (G : ListType KExpr) (n : Name) (us : ListType Level) (F : KExpr)
 (args : ListType KExpr) (U : KExpr) (T : KExpr)
 (lookup : Eq (OptionType KExpr) (kdecl_type_at tenv n us) (OptionType.some KExpr F))
 (run : Eq (OptionType KExpr) (raw_pi_spine args F) (OptionType.some KExpr U))
 (typed : TypingCDPCtxConvIn R tenv G (apply_spine args (KExpr.const n us)) T), SemanticTypedSpineCDPReturn R tenv G (KExpr.const n us) F args U T",
        r"fun (R : RedEnv) (faithful : RedEnvFaithful R) (rigid : CtorMetadataRigid R (red_ind_ctor R))
 (tenv : KDeclEnv) (G : ListType KExpr) (n : Name) (us : ListType Level) (F : KExpr)
 (args : ListType KExpr) (U : KExpr) (T : KExpr)
 (lookup : Eq (OptionType KExpr) (kdecl_type_at tenv n us) (OptionType.some KExpr F))
 (run : Eq (OptionType KExpr) (raw_pi_spine args F) (OptionType.some KExpr U))
 (typed : TypingCDPCtxConvIn R tenv G (apply_spine args (KExpr.const n us)) T) => semantic_typed_spine_cdp_from_trace R faithful rigid tenv G F args U (raw_pi_spine_trace args F U run)
  (KExpr.const n us) (raw_pi_head_canonical_cdp_const R tenv G n us F lookup) T typed",
    ),
    DeclarationInput::Proof(
        "typingcdpctxconv_in_const_spine_gen",
        r"forall (R : RedEnv) (faithful : RedEnvFaithful R) (rigid : CtorMetadataRigid R (red_ind_ctor R))
 (tenv : KDeclEnv) (G : ListType KExpr) (n : Name) (us : ListType Level) (F : KExpr)
 (args : ListType KExpr) (U : KExpr) (T : KExpr)
 (lookup : Eq (OptionType KExpr) (kdecl_type_at tenv n us) (OptionType.some KExpr F))
 (run : Eq (OptionType KExpr) (raw_pi_spine args F) (OptionType.some KExpr U))
 (typed : TypingCDPCtxConvIn R tenv G (apply_spine args (KExpr.const n us)) T)
 (C : Type) (consume : TypingCDPCtxConvIn R tenv G (KExpr.const n us) F ->
  TypedRawPiSpineCDP R tenv G F args U -> DefEqCDPIn R U T -> C), C",
        r"fun (R : RedEnv) (faithful : RedEnvFaithful R) (rigid : CtorMetadataRigid R (red_ind_ctor R))
 (tenv : KDeclEnv) (G : ListType KExpr) (n : Name) (us : ListType Level) (F : KExpr)
 (args : ListType KExpr) (U : KExpr) (T : KExpr)
 (lookup : Eq (OptionType KExpr) (kdecl_type_at tenv n us) (OptionType.some KExpr F))
 (run : Eq (OptionType KExpr) (raw_pi_spine args F) (OptionType.some KExpr U))
 (typed : TypingCDPCtxConvIn R tenv G (apply_spine args (KExpr.const n us)) T)
 (C : Type) (consume : TypingCDPCtxConvIn R tenv G (KExpr.const n us) F ->
  TypedRawPiSpineCDP R tenv G F args U -> DefEqCDPIn R U T -> C) => SemanticTypedSpineCDPReturn.rec R tenv G (KExpr.const n us) F args U T
  (fun (_p : SemanticTypedSpineCDPReturn R tenv G (KExpr.const n us) F args U T) => C) consume
  (typingcdpctxconv_in_const_spine R faithful rigid tenv G n us F args U T lookup run typed)",
    ),
    DeclarationInput::Proof(
        "dp_cdp_partial_spine",
        r"SemanticTypedSpineCDPReturn dp_R dp_tenv (ListType.nil KExpr)
 dp_ctor (kconst_type dp_ctor_signature) (ListType.cons KExpr dp_nat (ListType.nil KExpr))
 (KExpr.pi dp_nat dp_family) (KExpr.pi dp_domain dp_family)",
        r"typingcdpctxconv_in_const_spine dp_R dp_faithful dp_cdp_const_app_rigid dp_tenv (ListType.nil KExpr)
  dp_ctor_name (ListType.nil Level) (kconst_type dp_ctor_signature) (ListType.cons KExpr dp_nat (ListType.nil KExpr))
  (KExpr.pi dp_nat dp_family) (KExpr.pi dp_domain dp_family) dp_ctor_lookup
  (Eq.refl (OptionType KExpr) (OptionType.some KExpr (KExpr.pi dp_nat dp_family))) dp_cdp_ctor_partial_converted",
    ),
    DeclarationInput::Proof(
        "dp_cdp_partial_arguments",
        r"TypedRawPiSpineCDP dp_R dp_tenv (ListType.nil KExpr)
 (kconst_type dp_ctor_signature) (ListType.cons KExpr dp_nat (ListType.nil KExpr)) (KExpr.pi dp_nat dp_family)",
        r"SemanticTypedSpineCDPReturn.rec dp_R dp_tenv (ListType.nil KExpr) dp_ctor (kconst_type dp_ctor_signature)
  (ListType.cons KExpr dp_nat (ListType.nil KExpr)) (KExpr.pi dp_nat dp_family) (KExpr.pi dp_domain dp_family)
  (fun (_p : SemanticTypedSpineCDPReturn dp_R dp_tenv (ListType.nil KExpr) dp_ctor (kconst_type dp_ctor_signature)
   (ListType.cons KExpr dp_nat (ListType.nil KExpr)) (KExpr.pi dp_nat dp_family) (KExpr.pi dp_domain dp_family)) =>
   TypedRawPiSpineCDP dp_R dp_tenv (ListType.nil KExpr) (kconst_type dp_ctor_signature)
    (ListType.cons KExpr dp_nat (ListType.nil KExpr)) (KExpr.pi dp_nat dp_family))
  (fun (_head : TypingCDPCtxConvIn dp_R dp_tenv (ListType.nil KExpr) dp_ctor (kconst_type dp_ctor_signature))
   (args : TypedRawPiSpineCDP dp_R dp_tenv (ListType.nil KExpr) (kconst_type dp_ctor_signature)
    (ListType.cons KExpr dp_nat (ListType.nil KExpr)) (KExpr.pi dp_nat dp_family))
   (_convert : DefEqCDPIn dp_R (KExpr.pi dp_nat dp_family) (KExpr.pi dp_domain dp_family)) => args) dp_cdp_partial_spine",
    ),
    DeclarationInput::Proof(
        "dp_cdp_partial_conversion",
        r"DefEqCDPIn dp_R (KExpr.pi dp_nat dp_family) (KExpr.pi dp_domain dp_family)",
        r"typingcdpctxconv_in_const_spine_gen dp_R dp_faithful dp_cdp_const_app_rigid dp_tenv (ListType.nil KExpr)
  dp_ctor_name (ListType.nil Level) (kconst_type dp_ctor_signature) (ListType.cons KExpr dp_nat (ListType.nil KExpr))
  (KExpr.pi dp_nat dp_family) (KExpr.pi dp_domain dp_family) dp_ctor_lookup
  (Eq.refl (OptionType KExpr) (OptionType.some KExpr (KExpr.pi dp_nat dp_family))) dp_cdp_ctor_partial_converted
  (DefEqCDPIn dp_R (KExpr.pi dp_nat dp_family) (KExpr.pi dp_domain dp_family))
  (fun (_head : TypingCDPCtxConvIn dp_R dp_tenv (ListType.nil KExpr) dp_ctor (kconst_type dp_ctor_signature))
   (_args : TypedRawPiSpineCDP dp_R dp_tenv (ListType.nil KExpr) (kconst_type dp_ctor_signature)
    (ListType.cons KExpr dp_nat (ListType.nil KExpr)) (KExpr.pi dp_nat dp_family))
   (convert : DefEqCDPIn dp_R (KExpr.pi dp_nat dp_family) (KExpr.pi dp_domain dp_family)) => convert)",
    ),
    DeclarationInput::Proof(
        "dp_cdp_full_through_projection",
        r"TypingCDPCtxConvIn dp_R dp_tenv (ListType.nil KExpr) dp_subject dp_family",
        r"TypingCDPCtxConvIn.app dp_R dp_tenv (ListType.nil KExpr) (KExpr.app dp_ctor dp_nat) dp_zero dp_domain dp_family
  dp_cdp_ctor_partial_converted dp_cdp_field1_typed",
    ),
    DeclarationInput::Proof(
        "dp_cdp_full_spine",
        r"SemanticTypedSpineCDPReturn dp_R dp_tenv (ListType.nil KExpr)
 dp_ctor (kconst_type dp_ctor_signature) dp_args dp_family dp_family",
        r"typingcdpctxconv_in_const_spine dp_R dp_faithful dp_cdp_const_app_rigid dp_tenv (ListType.nil KExpr)
  dp_ctor_name (ListType.nil Level) (kconst_type dp_ctor_signature) dp_args dp_family dp_family
  dp_ctor_lookup dp_raw_spine_run dp_cdp_full_through_projection",
    ),
    DeclarationInput::Proof(
        "dp_cdp_full_arguments",
        r"TypedRawPiSpineCDP dp_R dp_tenv (ListType.nil KExpr)
 (kconst_type dp_ctor_signature) dp_args dp_family",
        r"typingcdpctxconv_in_const_spine_gen dp_R dp_faithful dp_cdp_const_app_rigid dp_tenv (ListType.nil KExpr)
  dp_ctor_name (ListType.nil Level) (kconst_type dp_ctor_signature) dp_args dp_family dp_family
  dp_ctor_lookup dp_raw_spine_run dp_cdp_full_through_projection
  (TypedRawPiSpineCDP dp_R dp_tenv (ListType.nil KExpr) (kconst_type dp_ctor_signature) dp_args dp_family)
  (fun (_head : TypingCDPCtxConvIn dp_R dp_tenv (ListType.nil KExpr) dp_ctor (kconst_type dp_ctor_signature))
   (args : TypedRawPiSpineCDP dp_R dp_tenv (ListType.nil KExpr) (kconst_type dp_ctor_signature) dp_args dp_family)
   (_convert : DefEqCDPIn dp_R dp_family dp_family) => args)",
    ),
    DeclarationInput::Proof(
        "cdp_spine_capture_run",
        r"Eq (OptionType KExpr)
 (raw_pi_spine (ListType.cons KExpr (KExpr.bvar Nat.zero) (ListType.nil KExpr))
  (typed_spine_identity_type (Level.succ (Level.succ Level.zero))))
 (OptionType.some KExpr (KExpr.pi (KExpr.bvar Nat.zero) (KExpr.bvar (Nat.succ Nat.zero))))",
        r"Eq.refl (OptionType KExpr) (OptionType.some KExpr (KExpr.pi (KExpr.bvar Nat.zero) (KExpr.bvar (Nat.succ Nat.zero))))",
    ),
    DeclarationInput::Proof(
        "cdp_spine_capture_whole",
        r"TypingCDPCtxConvIn faithful_red_env typed_spine_identity_tenv
 (ListType.cons KExpr (KExpr.sort (Level.succ (Level.succ Level.zero))) (ListType.nil KExpr))
 (KExpr.app (KExpr.const Name.anonymous (ListType.nil Level)) (KExpr.bvar Nat.zero))
 (KExpr.pi (KExpr.bvar Nat.zero) (KExpr.bvar (Nat.succ Nat.zero)))",
        r"TypingCDPCtxConvIn.app faithful_red_env typed_spine_identity_tenv
  (ListType.cons KExpr (KExpr.sort (Level.succ (Level.succ Level.zero))) (ListType.nil KExpr))
  (KExpr.const Name.anonymous (ListType.nil Level)) (KExpr.bvar Nat.zero)
  (KExpr.sort (Level.succ (Level.succ Level.zero))) (KExpr.pi (KExpr.bvar Nat.zero) (KExpr.bvar (Nat.succ Nat.zero)))
  (TypingCDPCtxConvIn.const faithful_red_env typed_spine_identity_tenv
   (ListType.cons KExpr (KExpr.sort (Level.succ (Level.succ Level.zero))) (ListType.nil KExpr))
   Name.anonymous (ListType.nil Level) (typed_spine_identity_type (Level.succ (Level.succ Level.zero))) typed_spine_identity_lookup)
  (TypingCDPCtxConvIn.var faithful_red_env typed_spine_identity_tenv
   (ListType.cons KExpr (KExpr.sort (Level.succ (Level.succ Level.zero))) (ListType.nil KExpr)) Nat.zero
   (KExpr.sort (Level.succ (Level.succ Level.zero)))
   (Eq.refl (OptionType KExpr) (OptionType.some KExpr (KExpr.sort (Level.succ (Level.succ Level.zero))))))",
    ),
    DeclarationInput::Proof(
        "cdp_spine_capture_package",
        r"SemanticTypedSpineCDPReturn faithful_red_env typed_spine_identity_tenv
 (ListType.cons KExpr (KExpr.sort (Level.succ (Level.succ Level.zero))) (ListType.nil KExpr))
 (KExpr.const Name.anonymous (ListType.nil Level)) (typed_spine_identity_type (Level.succ (Level.succ Level.zero)))
 (ListType.cons KExpr (KExpr.bvar Nat.zero) (ListType.nil KExpr))
 (KExpr.pi (KExpr.bvar Nat.zero) (KExpr.bvar (Nat.succ Nat.zero)))
 (KExpr.pi (KExpr.bvar Nat.zero) (KExpr.bvar (Nat.succ Nat.zero)))",
        r"typingcdpctxconv_in_const_spine faithful_red_env faithful_red_env_faithful (ctor_metadata_rigid_empty faithful_red_env)
  typed_spine_identity_tenv (ListType.cons KExpr (KExpr.sort (Level.succ (Level.succ Level.zero))) (ListType.nil KExpr))
  Name.anonymous (ListType.nil Level) (typed_spine_identity_type (Level.succ (Level.succ Level.zero)))
  (ListType.cons KExpr (KExpr.bvar Nat.zero) (ListType.nil KExpr))
  (KExpr.pi (KExpr.bvar Nat.zero) (KExpr.bvar (Nat.succ Nat.zero)))
  (KExpr.pi (KExpr.bvar Nat.zero) (KExpr.bvar (Nat.succ Nat.zero)))
  typed_spine_identity_lookup cdp_spine_capture_run cdp_spine_capture_whole",
    ),
    DeclarationInput::Proof(
        "cdp_spine_capture_arguments",
        r"TypedRawPiSpineCDP faithful_red_env typed_spine_identity_tenv
 (ListType.cons KExpr (KExpr.sort (Level.succ (Level.succ Level.zero))) (ListType.nil KExpr))
 (typed_spine_identity_type (Level.succ (Level.succ Level.zero)))
 (ListType.cons KExpr (KExpr.bvar Nat.zero) (ListType.nil KExpr))
 (KExpr.pi (KExpr.bvar Nat.zero) (KExpr.bvar (Nat.succ Nat.zero)))",
        r"typingcdpctxconv_in_const_spine_gen faithful_red_env faithful_red_env_faithful (ctor_metadata_rigid_empty faithful_red_env)
  typed_spine_identity_tenv (ListType.cons KExpr (KExpr.sort (Level.succ (Level.succ Level.zero))) (ListType.nil KExpr))
  Name.anonymous (ListType.nil Level) (typed_spine_identity_type (Level.succ (Level.succ Level.zero)))
  (ListType.cons KExpr (KExpr.bvar Nat.zero) (ListType.nil KExpr))
  (KExpr.pi (KExpr.bvar Nat.zero) (KExpr.bvar (Nat.succ Nat.zero)))
  (KExpr.pi (KExpr.bvar Nat.zero) (KExpr.bvar (Nat.succ Nat.zero))) typed_spine_identity_lookup cdp_spine_capture_run cdp_spine_capture_whole
  (TypedRawPiSpineCDP faithful_red_env typed_spine_identity_tenv
   (ListType.cons KExpr (KExpr.sort (Level.succ (Level.succ Level.zero))) (ListType.nil KExpr))
   (typed_spine_identity_type (Level.succ (Level.succ Level.zero)))
   (ListType.cons KExpr (KExpr.bvar Nat.zero) (ListType.nil KExpr))
   (KExpr.pi (KExpr.bvar Nat.zero) (KExpr.bvar (Nat.succ Nat.zero))))
  (fun (_head : TypingCDPCtxConvIn faithful_red_env typed_spine_identity_tenv
    (ListType.cons KExpr (KExpr.sort (Level.succ (Level.succ Level.zero))) (ListType.nil KExpr))
    (KExpr.const Name.anonymous (ListType.nil Level)) (typed_spine_identity_type (Level.succ (Level.succ Level.zero))))
   (args : TypedRawPiSpineCDP faithful_red_env typed_spine_identity_tenv
    (ListType.cons KExpr (KExpr.sort (Level.succ (Level.succ Level.zero))) (ListType.nil KExpr))
    (typed_spine_identity_type (Level.succ (Level.succ Level.zero)))
    (ListType.cons KExpr (KExpr.bvar Nat.zero) (ListType.nil KExpr))
    (KExpr.pi (KExpr.bvar Nat.zero) (KExpr.bvar (Nat.succ Nat.zero))))
   (_convert : DefEqCDPIn faithful_red_env (KExpr.pi (KExpr.bvar Nat.zero) (KExpr.bvar (Nat.succ Nat.zero)))
    (KExpr.pi (KExpr.bvar Nat.zero) (KExpr.bvar (Nat.succ Nat.zero)))) => args)",
    ),
];
#[cfg(test)]
pub(super) const NEGATIVE_CONTROLS: &[(&str, &str, &str)] = &[
    (
        "cdp_spine_reject_capture",
        r"Eq (OptionType KExpr)
 (raw_pi_spine (ListType.cons KExpr (KExpr.bvar Nat.zero) (ListType.nil KExpr))
  (typed_spine_identity_type (Level.succ (Level.succ Level.zero))))
 (OptionType.some KExpr (KExpr.pi (KExpr.bvar Nat.zero) (KExpr.bvar Nat.zero)))",
        r"cdp_spine_capture_run",
    ),
    (
        "cdp_spine_reject_dropped_conversion",
        r"SemanticTypedSpineCDPReturn dp_R dp_tenv (ListType.nil KExpr)
 dp_ctor (kconst_type dp_ctor_signature) (ListType.cons KExpr dp_nat (ListType.nil KExpr))
 (KExpr.pi dp_nat dp_family) (KExpr.pi dp_nat dp_family)",
        r"dp_cdp_partial_spine",
    ),
    (
        "cdp_spine_reject_wrong_arity",
        r"Eq (OptionType KExpr)
 (kdecl_type_at dp_tenv dp_ctor_name (ListType.cons Level Level.zero (ListType.nil Level)))
 (OptionType.some KExpr (kconst_type dp_ctor_signature))",
        r"dp_ctor_lookup",
    ),
    (
        "cdp_spine_reject_trace_as_whole",
        r"SemanticTypedSpineCDPReturn dp_R dp_tenv (ListType.nil KExpr)
 dp_ctor (kconst_type dp_ctor_signature) dp_args dp_family dp_family",
        r"typingcdpctxconv_in_const_spine dp_R dp_faithful dp_cdp_const_app_rigid dp_tenv (ListType.nil KExpr)
  dp_ctor_name (ListType.nil Level) (kconst_type dp_ctor_signature) dp_args dp_family dp_family
  dp_ctor_lookup dp_raw_spine_run dp_cdp_full_arguments",
    ),
];
#[cfg(test)]
pub(super) const PROOF_ROOTS: &[&str] = &[
    "raw_pi_head_canonical_cdp_const",
    "raw_pi_head_canonical_cdp_app",
    "semantic_typed_spine_cdp_nil",
    "semantic_typed_spine_cdp_cons",
    "semantic_typed_spine_cdp_from_trace",
    "typingcdpctxconv_in_const_spine",
    "typingcdpctxconv_in_const_spine_gen",
    "dp_cdp_partial_spine",
    "dp_cdp_partial_arguments",
    "dp_cdp_partial_conversion",
    "dp_cdp_full_through_projection",
    "dp_cdp_full_spine",
    "dp_cdp_full_arguments",
    "cdp_spine_capture_run",
    "cdp_spine_capture_whole",
    "cdp_spine_capture_package",
    "cdp_spine_capture_arguments",
];
#[cfg(test)]
pub(super) const DATA_NAMES: &[&str] = &["RawPiHeadCanonicalCDP"];
#[cfg(test)]
pub(super) const INDUCTIVE_NAMES: &[&str] = &["TypedRawPiSpineCDP", "SemanticTypedSpineCDPReturn"];
