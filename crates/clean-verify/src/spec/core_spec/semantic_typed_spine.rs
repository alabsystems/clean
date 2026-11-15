// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! A computed raw-Pi telescope and typing recovered from a whole constant spine.
//!
//! The public theorem derives its head-canonicality invariant from the actual
//! guarded signature lookup. Argument typing is an output, never an oracle.
//! Raw non-Pi refusal does not imply untypability modulo conversion. No WHNF,
//! projection, declaration-admission or Rust-refinement claim is made.
//! Registered after semantic generation and term-instantiation conversion;
//! projection integration remains separate work.

use crate::spec::error::SpecError;
use crate::spec::Specification;

const DECLARATIONS: &[(&str, &str)] = &[
    (
        r"def raw_pi_spine_step (next : KExpr -> OptionType KExpr) (a : KExpr)
 (F : KExpr) : OptionType KExpr := match F with
| KExpr.sort u => OptionType.none KExpr
| KExpr.bvar i => OptionType.none KExpr
| KExpr.app f x => OptionType.none KExpr
| KExpr.lam A b => OptionType.none KExpr
| KExpr.pi A B => next (instantiate B a)
| KExpr.const n us => OptionType.none KExpr
| KExpr.let_ A v b => OptionType.none KExpr
| KExpr.proj S i e => OptionType.none KExpr
| KExpr.lit n => OptionType.none KExpr",
        "One actual raw-Pi telescope step: instantiate the body at the supplied argument or refuse every non-Pi shape. This does not run WHNF or imply untypability on refusal.",
    ),
    (
        r"def raw_pi_spine (args : ListType KExpr) (F : KExpr) : OptionType KExpr :=
 ListType.rec KExpr (fun (_ : ListType KExpr) => KExpr -> OptionType KExpr)
  (fun (current : KExpr) => OptionType.some KExpr current)
  (fun (a : KExpr) (_rest : ListType KExpr) (next : KExpr -> OptionType KExpr)
   (current : KExpr) => raw_pi_spine_step next a current) args F",
        "Finite left-to-right raw telescope computation, using the same actual instantiate operation as application typing. Empty arguments return the residual type, including a residual Pi.",
    ),
    (
        r"inductive RawPiSpineTrace : KExpr -> ListType KExpr -> KExpr -> Type
| nil : forall (F : KExpr), RawPiSpineTrace F (ListType.nil KExpr) F
| cons : forall (A : KExpr) (B : KExpr) (a : KExpr) (rest : ListType KExpr) (U : KExpr),
 RawPiSpineTrace (instantiate B a) rest U ->
 RawPiSpineTrace (KExpr.pi A B) (ListType.cons KExpr a rest) U",
        "Successful raw computation trace records each actual domain and instantiated residual; it carries no typing premise.",
    ),
    (
        r"def raw_pi_spine_trace_nil (F : KExpr) (U : KExpr)
 (h : Eq (OptionType KExpr) (raw_pi_spine (ListType.nil KExpr) F) (OptionType.some KExpr U)) :
 RawPiSpineTrace F (ListType.nil KExpr) U :=
 Eq.substType KExpr (fun (V : KExpr) => RawPiSpineTrace F (ListType.nil KExpr) V) F U
  (option_some_inj KExpr F U h) (RawPiSpineTrace.nil F)",
        "Extract the empty trace from the actual computation equation using some injectivity.",
    ),
    (
        r"def raw_pi_spine_trace_cons (a : KExpr) (rest : ListType KExpr)
 (ih : forall (F : KExpr) (U : KExpr),
  Eq (OptionType KExpr) (raw_pi_spine rest F) (OptionType.some KExpr U) -> RawPiSpineTrace F rest U)
 (F : KExpr) : forall (U : KExpr),
 Eq (OptionType KExpr) (raw_pi_spine (ListType.cons KExpr a rest) F) (OptionType.some KExpr U) ->
 RawPiSpineTrace F (ListType.cons KExpr a rest) U := match F with
| KExpr.sort u => fun (U : KExpr) (h : Eq (OptionType KExpr) (OptionType.none KExpr) (OptionType.some KExpr U)) =>
 option_none_ne_some_type KExpr U (RawPiSpineTrace (KExpr.sort u) (ListType.cons KExpr a rest) U) h
| KExpr.bvar i => fun (U : KExpr) (h : Eq (OptionType KExpr) (OptionType.none KExpr) (OptionType.some KExpr U)) =>
 option_none_ne_some_type KExpr U (RawPiSpineTrace (KExpr.bvar i) (ListType.cons KExpr a rest) U) h
| KExpr.app f x => fun (U : KExpr) (h : Eq (OptionType KExpr) (OptionType.none KExpr) (OptionType.some KExpr U)) =>
 option_none_ne_some_type KExpr U (RawPiSpineTrace (KExpr.app f x) (ListType.cons KExpr a rest) U) h
| KExpr.lam A b => fun (U : KExpr) (h : Eq (OptionType KExpr) (OptionType.none KExpr) (OptionType.some KExpr U)) =>
 option_none_ne_some_type KExpr U (RawPiSpineTrace (KExpr.lam A b) (ListType.cons KExpr a rest) U) h
| KExpr.pi A B => fun (U : KExpr)
 (h : Eq (OptionType KExpr) (raw_pi_spine rest (instantiate B a)) (OptionType.some KExpr U)) =>
 RawPiSpineTrace.cons A B a rest U (ih (instantiate B a) U h)
| KExpr.const n us => fun (U : KExpr) (h : Eq (OptionType KExpr) (OptionType.none KExpr) (OptionType.some KExpr U)) =>
 option_none_ne_some_type KExpr U (RawPiSpineTrace (KExpr.const n us) (ListType.cons KExpr a rest) U) h
| KExpr.let_ A v b => fun (U : KExpr) (h : Eq (OptionType KExpr) (OptionType.none KExpr) (OptionType.some KExpr U)) =>
 option_none_ne_some_type KExpr U (RawPiSpineTrace (KExpr.let_ A v b) (ListType.cons KExpr a rest) U) h
| KExpr.proj S i e => fun (U : KExpr) (h : Eq (OptionType KExpr) (OptionType.none KExpr) (OptionType.some KExpr U)) =>
 option_none_ne_some_type KExpr U (RawPiSpineTrace (KExpr.proj S i e) (ListType.cons KExpr a rest) U) h
| KExpr.lit n => fun (U : KExpr) (h : Eq (OptionType KExpr) (OptionType.none KExpr) (OptionType.some KExpr U)) =>
 option_none_ne_some_type KExpr U (RawPiSpineTrace (KExpr.lit n) (ListType.cons KExpr a rest) U) h",
        "All nine actual syntax cases of a successful nonempty raw computation: only Pi can supply a trace; impossible none/some equations eliminate the other eight.",
    ),
    (
        r"def raw_pi_spine_trace (args : ListType KExpr) : forall (F : KExpr) (U : KExpr),
 Eq (OptionType KExpr) (raw_pi_spine args F) (OptionType.some KExpr U) -> RawPiSpineTrace F args U :=
 ListType.rec KExpr (fun (xs : ListType KExpr) => forall (F : KExpr) (U : KExpr),
  Eq (OptionType KExpr) (raw_pi_spine xs F) (OptionType.some KExpr U) -> RawPiSpineTrace F xs U)
  raw_pi_spine_trace_nil raw_pi_spine_trace_cons args",
        "The finite computation actually produces its trace, by list induction; the public typing theorem does not take an unexplained telescope oracle.",
    ),
    (
        r"inductive TypedRawPiSpine (R : RedEnv) (tenv : KDeclEnv) (G : ListType KExpr) :
 KExpr -> ListType KExpr -> KExpr -> Type
| nil : forall (F : KExpr), TypedRawPiSpine R tenv G F (ListType.nil KExpr) F
| cons : forall (A : KExpr) (B : KExpr) (a : KExpr) (rest : ListType KExpr) (U : KExpr),
 TypingCtxConvIn R tenv G a A -> TypedRawPiSpine R tenv G (instantiate B a) rest U ->
 TypedRawPiSpine R tenv G (KExpr.pi A B) (ListType.cons KExpr a rest) U",
        "The derived typed mirror records the actual typing of every supplied argument at its canonical, previously instantiated domain. These proofs are outputs, not caller assumptions.",
    ),
    (
        r"def RawPiHeadCanonical (R : RedEnv) (tenv : KDeclEnv) (G : ListType KExpr)
 (h : KExpr) (F : KExpr) : Type := forall (V : KExpr),
 TypingCtxConvIn R tenv G h V -> DefEqIn R F V",
        "Internal induction invariant only. The public constant theorem below derives it from its actual guarded lookup and constant generation.",
    ),
    (
        r"def raw_pi_head_canonical_const (R : RedEnv) (tenv : KDeclEnv) (G : ListType KExpr)
 (n : Name) (us : ListType Level) (F : KExpr)
 (lookup : Eq (OptionType KExpr) (kdecl_type_at tenv n us) (OptionType.some KExpr F)) :
 RawPiHeadCanonical R tenv G (KExpr.const n us) F := fun (V : KExpr)
 (typed : TypingCtxConvIn R tenv G (KExpr.const n us) V) =>
 typingctxconv_in_constant_gen R tenv G n us V typed (DefEqIn R F V)
  (fun (F2 : KExpr)
   (found : Eq (OptionType KExpr) (kdecl_type_at tenv n us) (OptionType.some KExpr F2))
   (convert : DefEqIn R F2 V) =>
   Eq.substType KExpr (fun (X : KExpr) => DefEqIn R X V) F2 F
    (option_some_inj KExpr F2 F
     (Eq.trans (OptionType KExpr) (OptionType.some KExpr F2) (kdecl_type_at tenv n us)
      (OptionType.some KExpr F)
      (Eq.symm (OptionType KExpr) (kdecl_type_at tenv n us) (OptionType.some KExpr F2) found) lookup))
    convert)",
        "Derive canonicality for every typing of this actual constant: constant generation and equality of its two guarded lookup results, without environment validity or a supplied uniqueness oracle.",
    ),
    (
        r"def raw_pi_head_canonical_app (R : RedEnv) (faithful : RedEnvFaithful R)
 (tenv : KDeclEnv) (G : ListType KExpr) (h : KExpr) (A : KExpr) (B : KExpr) (a : KExpr)
 (canonical : RawPiHeadCanonical R tenv G h (KExpr.pi A B)) :
 RawPiHeadCanonical R tenv G (KExpr.app h a) (instantiate B a) := fun (V : KExpr)
 (typed : TypingCtxConvIn R tenv G (KExpr.app h a) V) =>
 typingctxconv_in_app_gen R tenv G h a V typed (DefEqIn R (instantiate B a) V)
  (fun (A2 : KExpr) (B2 : KExpr) (hf : TypingCtxConvIn R tenv G h (KExpr.pi A2 B2))
   (_ha : TypingCtxConvIn R tenv G a A2) (result : DefEqIn R (instantiate B2 a) V) =>
   def_eq_in_pi_components R faithful A B A2 B2 (canonical (KExpr.pi A2 B2) hf)
    (DefEqIn R (instantiate B a) V)
    (fun (_domains : DefEqIn R A A2) (bodies : DefEqIn R B B2) =>
     DefEqIn.trans R (instantiate B a) (instantiate B2 a) V
      (def_eq_in_instantiate_same R B B2 a bodies) result))",
        "Advance the private canonicality invariant through one actual application. RedEnvFaithful is used only for Pi-component conversion; beta-sandwich instantiation handles its codomain.",
    ),
    (
        r"inductive SemanticTypedSpineReturn (R : RedEnv) (tenv : KDeclEnv) (G : ListType KExpr)
 (h : KExpr) (F : KExpr) (args : ListType KExpr) (U : KExpr) (T : KExpr) : Type
| intro : TypingCtxConvIn R tenv G h F -> TypedRawPiSpine R tenv G F args U ->
 DefEqIn R U T -> SemanticTypedSpineReturn R tenv G h F args U T",
        "All three derived outputs: canonical head typing, canonical argument typings along the actual dependent telescope, and the trailing residual-to-observed-result conversion.",
    ),
    (
        r"def semantic_typed_spine_nil (R : RedEnv) (tenv : KDeclEnv) (G : ListType KExpr)
 (F : KExpr) (h : KExpr) (canonical : RawPiHeadCanonical R tenv G h F) (T : KExpr)
 (typed : TypingCtxConvIn R tenv G (apply_spine (ListType.nil KExpr) h) T) :
 SemanticTypedSpineReturn R tenv G h F (ListType.nil KExpr) F T :=
 SemanticTypedSpineReturn.intro R tenv G h F (ListType.nil KExpr) F T
  (TypingCtxConvIn.conv R tenv G h T F typed (DefEqIn.symm R F T (canonical T typed)))
  (TypedRawPiSpine.nil R tenv G F) (canonical T typed)",
        "Empty-spine extraction preserves trailing conversion and derives canonical head typing by converting the actual supplied derivation.",
    ),
    (
        r"def semantic_typed_spine_cons (R : RedEnv) (faithful : RedEnvFaithful R)
 (tenv : KDeclEnv) (G : ListType KExpr) (A : KExpr) (B : KExpr) (a : KExpr)
 (rest : ListType KExpr) (U : KExpr)
 (ih : forall (h : KExpr), RawPiHeadCanonical R tenv G h (instantiate B a) ->
  forall (T : KExpr), TypingCtxConvIn R tenv G (apply_spine rest h) T ->
  SemanticTypedSpineReturn R tenv G h (instantiate B a) rest U T)
 (h : KExpr) (canonical : RawPiHeadCanonical R tenv G h (KExpr.pi A B)) (T : KExpr)
 (typed : TypingCtxConvIn R tenv G (apply_spine (ListType.cons KExpr a rest) h) T) :
 SemanticTypedSpineReturn R tenv G h (KExpr.pi A B) (ListType.cons KExpr a rest) U T :=
 SemanticTypedSpineReturn.rec R tenv G (KExpr.app h a) (instantiate B a) rest U T
  (fun (_p : SemanticTypedSpineReturn R tenv G (KExpr.app h a) (instantiate B a) rest U T) =>
   SemanticTypedSpineReturn R tenv G h (KExpr.pi A B) (ListType.cons KExpr a rest) U T)
  (fun (head : TypingCtxConvIn R tenv G (KExpr.app h a) (instantiate B a))
   (tail : TypedRawPiSpine R tenv G (instantiate B a) rest U) (result : DefEqIn R U T) =>
   typingctxconv_in_app_gen R tenv G h a (instantiate B a) head
    (SemanticTypedSpineReturn R tenv G h (KExpr.pi A B) (ListType.cons KExpr a rest) U T)
    (fun (A2 : KExpr) (B2 : KExpr) (hf : TypingCtxConvIn R tenv G h (KExpr.pi A2 B2))
     (ha : TypingCtxConvIn R tenv G a A2) (_convert : DefEqIn R (instantiate B2 a) (instantiate B a)) =>
     def_eq_in_pi_components R faithful A B A2 B2 (canonical (KExpr.pi A2 B2) hf)
      (SemanticTypedSpineReturn R tenv G h (KExpr.pi A B) (ListType.cons KExpr a rest) U T)
      (fun (domains : DefEqIn R A A2) (_bodies : DefEqIn R B B2) =>
       SemanticTypedSpineReturn.intro R tenv G h (KExpr.pi A B) (ListType.cons KExpr a rest) U T
        (TypingCtxConvIn.conv R tenv G h (KExpr.pi A2 B2) (KExpr.pi A B) hf
         (DefEqIn.symm R (KExpr.pi A B) (KExpr.pi A2 B2) (canonical (KExpr.pi A2 B2) hf)))
        (TypedRawPiSpine.cons R tenv G A B a rest U
         (TypingCtxConvIn.conv R tenv G a A2 A ha (DefEqIn.symm R A A2 domains)) tail)
        result)))
  (ih (KExpr.app h a) (raw_pi_head_canonical_app R faithful tenv G h A B a canonical) T typed)",
        "Cons extraction from whole-spine typing: recurse at the applied head, then invert its derived canonical typing to recover the first argument and original head. Neither argument typing nor intermediate output typing is assumed.",
    ),
    (
        r"def semantic_typed_spine_from_trace (R : RedEnv) (faithful : RedEnvFaithful R)
 (tenv : KDeclEnv) (G : ListType KExpr) (F : KExpr) (args : ListType KExpr) (U : KExpr)
 (trace : RawPiSpineTrace F args U) : forall (h : KExpr), RawPiHeadCanonical R tenv G h F ->
 forall (T : KExpr), TypingCtxConvIn R tenv G (apply_spine args h) T ->
 SemanticTypedSpineReturn R tenv G h F args U T :=
 RawPiSpineTrace.rec
  (fun (F0 : KExpr) (xs : ListType KExpr) (V : KExpr) (_tr : RawPiSpineTrace F0 xs V) =>
   forall (h : KExpr), RawPiHeadCanonical R tenv G h F0 -> forall (T : KExpr),
   TypingCtxConvIn R tenv G (apply_spine xs h) T -> SemanticTypedSpineReturn R tenv G h F0 xs V T)
  (fun (F0 : KExpr) => semantic_typed_spine_nil R tenv G F0)
  (fun (A : KExpr) (B : KExpr) (a : KExpr) (rest : ListType KExpr) (V : KExpr)
   (_tr : RawPiSpineTrace (instantiate B a) rest V)
   (ih : forall (h : KExpr), RawPiHeadCanonical R tenv G h (instantiate B a) ->
    forall (T : KExpr), TypingCtxConvIn R tenv G (apply_spine rest h) T ->
    SemanticTypedSpineReturn R tenv G h (instantiate B a) rest V T) =>
   semantic_typed_spine_cons R faithful tenv G A B a rest V ih) F args U trace",
        "Finite trace induction generalizes the head and derives every canonical typing output. The private head predicate is discharged by the public constant wrapper.",
    ),
    (
        r"def typingctxconv_in_const_spine (R : RedEnv) (faithful : RedEnvFaithful R)
 (tenv : KDeclEnv) (G : ListType KExpr) (n : Name) (us : ListType Level) (F : KExpr)
 (args : ListType KExpr) (U : KExpr) (T : KExpr)
 (lookup : Eq (OptionType KExpr) (kdecl_type_at tenv n us) (OptionType.some KExpr F))
 (run : Eq (OptionType KExpr) (raw_pi_spine args F) (OptionType.some KExpr U))
 (typed : TypingCtxConvIn R tenv G (apply_spine args (KExpr.const n us)) T) :
 SemanticTypedSpineReturn R tenv G (KExpr.const n us) F args U T :=
 semantic_typed_spine_from_trace R faithful tenv G F args U (raw_pi_spine_trace args F U run)
  (KExpr.const n us) (raw_pi_head_canonical_const R tenv G n us F lookup) T typed",
        "Public no-oracle constant-spine theorem: actual guarded lookup, actual finite raw computation and actual whole typing suffice to derive canonical head/argument typings and residual conversion. No extra closure, context validity, fields_typed or head-uniqueness premise.",
    ),
    (
        r"def typingctxconv_in_const_spine_gen (R : RedEnv) (faithful : RedEnvFaithful R)
 (tenv : KDeclEnv) (G : ListType KExpr) (n : Name) (us : ListType Level) (F : KExpr)
 (args : ListType KExpr) (U : KExpr) (T : KExpr)
 (lookup : Eq (OptionType KExpr) (kdecl_type_at tenv n us) (OptionType.some KExpr F))
 (run : Eq (OptionType KExpr) (raw_pi_spine args F) (OptionType.some KExpr U))
 (typed : TypingCtxConvIn R tenv G (apply_spine args (KExpr.const n us)) T)
 (C : Type) (consume : TypingCtxConvIn R tenv G (KExpr.const n us) F ->
  TypedRawPiSpine R tenv G F args U -> DefEqIn R U T -> C) : C :=
 SemanticTypedSpineReturn.rec R tenv G (KExpr.const n us) F args U T
  (fun (_p : SemanticTypedSpineReturn R tenv G (KExpr.const n us) F args U T) => C) consume
  (typingctxconv_in_const_spine R faithful tenv G n us F args U T lookup run typed)",
        "CPS access to all three actual derived outputs without exposing the internal canonicality invariant.",
    ),
    (
        r"def typed_spine_identity_type (u : Level) : KExpr :=
 KExpr.pi (KExpr.sort u) (KExpr.pi (KExpr.bvar Nat.zero) (KExpr.bvar (Nat.succ Nat.zero)))",
        "The genuinely inhabited dependent identity type: forall A : Sort u, A -> A; the inner codomain refers to A under the argument binder.",
    ),
    (
        r"def typed_spine_identity_value (u : Level) : KExpr :=
 KExpr.lam (KExpr.sort u) (KExpr.lam (KExpr.bvar Nat.zero) (KExpr.bvar Nat.zero))",
        "Actual lambda body of dependent identity; not a postulated inhabitant of forall A, A.",
    ),
    (
        r"def typed_spine_identity_body_typed (R : RedEnv) (tenv : KDeclEnv)
 (G : ListType KExpr) (u : Level) :
 TypingCtxConvIn R tenv G (typed_spine_identity_value u) (typed_spine_identity_type u) :=
 TypingCtxConvIn.lam R tenv G (KExpr.sort u)
  (KExpr.lam (KExpr.bvar Nat.zero) (KExpr.bvar Nat.zero))
  (KExpr.pi (KExpr.bvar Nat.zero) (KExpr.bvar (Nat.succ Nat.zero))) (Level.succ u)
  (TypingCtxConvIn.sort R tenv G u)
  (TypingCtxConvIn.lam R tenv (ListType.cons KExpr (KExpr.sort u) G)
   (KExpr.bvar Nat.zero) (KExpr.bvar Nat.zero) (KExpr.bvar (Nat.succ Nat.zero)) u
   (TypingCtxConvIn.var R tenv (ListType.cons KExpr (KExpr.sort u) G) Nat.zero (KExpr.sort u)
    (Eq.refl (OptionType KExpr) (OptionType.some KExpr (KExpr.sort u))))
   (TypingCtxConvIn.var R tenv
    (ListType.cons KExpr (KExpr.bvar Nat.zero) (ListType.cons KExpr (KExpr.sort u) G))
    Nat.zero (KExpr.bvar Nat.zero)
    (Eq.refl (OptionType KExpr) (OptionType.some KExpr (KExpr.bvar Nat.zero)))))",
        "Construct the actual dependent identity body typing with two lambdas, sort and exact contextual variable lookups/lifts. Arbitrary R, tenv and G; no admission or supplied body-typing assumption.",
    ),
    (
        r"def typed_spine_identity_sig : KConstSig := KConstSig.mk (ListType.nil Name)
 (typed_spine_identity_type (Level.succ (Level.succ Level.zero)))",
        "Model-local zero-universe-parameter signature of the inhabited identity at u=2.",
    ),
    (
        r"def typed_spine_identity_definition : KDefSig := KDefSig.mk typed_spine_identity_sig
 (typed_spine_identity_value (Level.succ (Level.succ Level.zero)))",
        "One stored signature and actual lambda body, preserving the shared KDefSig record. This is not a production admission theorem.",
    ),
    (
        r"def typed_spine_identity_tenv : KDeclEnv := fun (n : Name) =>
 opt_pick KConstSig (name_eqb n Name.anonymous) typed_spine_identity_sig (OptionType.none KConstSig)",
        "Actual singleton declaration environment for the identity caller.",
    ),
    (
        r"def typed_spine_identity_stored_body_typed (R : RedEnv) :
 TypingCtxConvIn R typed_spine_identity_tenv (ListType.nil KExpr)
  (kdef_value typed_spine_identity_definition)
  (kconst_type (kdef_signature typed_spine_identity_definition)) :=
 typed_spine_identity_body_typed R typed_spine_identity_tenv (ListType.nil KExpr)
  (Level.succ (Level.succ Level.zero))",
        "The exact stored body has the exact stored schematic type in the empty context, derived from the lambda proof. No claim about full environment validity, source declaration admission or delta execution.",
    ),
    (
        r"def typed_spine_identity_lookup : Eq (OptionType KExpr)
 (kdecl_type_at typed_spine_identity_tenv Name.anonymous (ListType.nil Level))
 (OptionType.some KExpr (typed_spine_identity_type (Level.succ (Level.succ Level.zero)))) :=
 Eq.refl (OptionType KExpr)
  (OptionType.some KExpr (typed_spine_identity_type (Level.succ (Level.succ Level.zero))))",
        "The real guarded lookup computes the actual stored identity type; no universe argument is missing or erased.",
    ),
    (
        r"def typed_spine_identity_args : ListType KExpr :=
 ListType.cons KExpr (KExpr.sort (Level.succ Level.zero))
  (ListType.cons KExpr (KExpr.sort Level.zero) (ListType.nil KExpr))",
        "Actual arguments [Sort 1, Sort 0], so the dependent second argument has the type supplied by the first.",
    ),
    (
        r"def typed_spine_identity_run : Eq (OptionType KExpr)
 (raw_pi_spine typed_spine_identity_args (typed_spine_identity_type (Level.succ (Level.succ Level.zero))))
 (OptionType.some KExpr (KExpr.sort (Level.succ Level.zero))) :=
 Eq.refl (OptionType KExpr) (OptionType.some KExpr (KExpr.sort (Level.succ Level.zero)))",
        "The actual two-argument raw telescope computes Sort 1 by real binder substitution, not a supplied list of output types.",
    ),
    (
        r"def typed_spine_identity_result : KExpr :=
 KExpr.sort (Level.succ (Level.imax (Level.succ Level.zero) Level.zero))",
        "A syntactically different observed result, semantically Sort 1, for the trailing-conversion caller.",
    ),
    (
        r"def typed_spine_identity_result_convert (R : RedEnv) :
 DefEqIn R (KExpr.sort (Level.succ Level.zero)) typed_spine_identity_result :=
 DefEqIn.levels R (KExpr.sort (Level.succ Level.zero)) typed_spine_identity_result
  (KExprUniverseEq.sort (Level.succ Level.zero) (Level.succ (Level.imax (Level.succ Level.zero) Level.zero))
   (fun (_rho : Name -> Nat) => Eq.refl Nat (Nat.succ Nat.zero)))",
        "Actual semantic universe conversion from the computed canonical residual to the syntactically nontrivial observed result.",
    ),
    (
        r"def typed_spine_identity_applied (R : RedEnv) (G : ListType KExpr) :
 TypingCtxConvIn R typed_spine_identity_tenv G
 (apply_spine typed_spine_identity_args (KExpr.const Name.anonymous (ListType.nil Level)))
 (KExpr.sort (Level.succ Level.zero)) :=
 TypingCtxConvIn.app R typed_spine_identity_tenv G
  (KExpr.app (KExpr.const Name.anonymous (ListType.nil Level)) (KExpr.sort (Level.succ Level.zero)))
  (KExpr.sort Level.zero) (KExpr.sort (Level.succ Level.zero)) (KExpr.sort (Level.succ Level.zero))
  (TypingCtxConvIn.app R typed_spine_identity_tenv G (KExpr.const Name.anonymous (ListType.nil Level))
   (KExpr.sort (Level.succ Level.zero)) (KExpr.sort (Level.succ (Level.succ Level.zero)))
   (KExpr.pi (KExpr.bvar Nat.zero) (KExpr.bvar (Nat.succ Nat.zero)))
   (TypingCtxConvIn.const R typed_spine_identity_tenv G Name.anonymous (ListType.nil Level)
    (typed_spine_identity_type (Level.succ (Level.succ Level.zero))) typed_spine_identity_lookup)
   (TypingCtxConvIn.sort R typed_spine_identity_tenv G (Level.succ Level.zero)))
  (TypingCtxConvIn.sort R typed_spine_identity_tenv G Level.zero)",
        "Construct both dependent applications from the actual constant lookup and two sort typings. Neither argument typing nor the final application typing is a fixture assumption.",
    ),
    (
        r"def typed_spine_identity_applied_converted (R : RedEnv) (G : ListType KExpr) :
 TypingCtxConvIn R typed_spine_identity_tenv G
 (apply_spine typed_spine_identity_args (KExpr.const Name.anonymous (ListType.nil Level)))
 typed_spine_identity_result :=
 TypingCtxConvIn.conv R typed_spine_identity_tenv G
  (apply_spine typed_spine_identity_args (KExpr.const Name.anonymous (ListType.nil Level)))
  (KExpr.sort (Level.succ Level.zero)) typed_spine_identity_result
  (typed_spine_identity_applied R G) (typed_spine_identity_result_convert R)",
        "A whole-spine typing with a real trailing semantic conversion, for the public generation theorem to recover.",
    ),
    (
        r"def typed_spine_identity_package (R : RedEnv) (faithful : RedEnvFaithful R) (G : ListType KExpr) :
 SemanticTypedSpineReturn R typed_spine_identity_tenv G (KExpr.const Name.anonymous (ListType.nil Level))
 (typed_spine_identity_type (Level.succ (Level.succ Level.zero))) typed_spine_identity_args
 (KExpr.sort (Level.succ Level.zero)) typed_spine_identity_result :=
 typingctxconv_in_const_spine R faithful typed_spine_identity_tenv G Name.anonymous (ListType.nil Level)
  (typed_spine_identity_type (Level.succ (Level.succ Level.zero))) typed_spine_identity_args
  (KExpr.sort (Level.succ Level.zero)) typed_spine_identity_result typed_spine_identity_lookup
  typed_spine_identity_run (typed_spine_identity_applied_converted R G)",
        "Actual public-theorem caller with inhabited stored body, actual lookup, actual run and actual converted whole typing; no intermediate typing oracle.",
    ),
    (
        r"def typed_spine_identity_arguments (R : RedEnv) (faithful : RedEnvFaithful R) (G : ListType KExpr) :
 TypedRawPiSpine R typed_spine_identity_tenv G
 (typed_spine_identity_type (Level.succ (Level.succ Level.zero))) typed_spine_identity_args
 (KExpr.sort (Level.succ Level.zero)) :=
 typingctxconv_in_const_spine_gen R faithful typed_spine_identity_tenv G Name.anonymous (ListType.nil Level)
  (typed_spine_identity_type (Level.succ (Level.succ Level.zero))) typed_spine_identity_args
  (KExpr.sort (Level.succ Level.zero)) typed_spine_identity_result typed_spine_identity_lookup
  typed_spine_identity_run (typed_spine_identity_applied_converted R G)
  (TypedRawPiSpine R typed_spine_identity_tenv G
   (typed_spine_identity_type (Level.succ (Level.succ Level.zero))) typed_spine_identity_args
   (KExpr.sort (Level.succ Level.zero)))
  (fun (_head : TypingCtxConvIn R typed_spine_identity_tenv G
    (KExpr.const Name.anonymous (ListType.nil Level)) (typed_spine_identity_type (Level.succ (Level.succ Level.zero))))
   (arguments : TypedRawPiSpine R typed_spine_identity_tenv G
    (typed_spine_identity_type (Level.succ (Level.succ Level.zero))) typed_spine_identity_args
    (KExpr.sort (Level.succ Level.zero)))
   (_result : DefEqIn R (KExpr.sort (Level.succ Level.zero)) typed_spine_identity_result) => arguments)",
        "Extract the actual derived per-argument typing trace from the public constant-spine theorem, rather than reconstructing it by hand.",
    ),
    (
        r"def typed_spine_identity_conversion (R : RedEnv) (faithful : RedEnvFaithful R) (G : ListType KExpr) :
 DefEqIn R (KExpr.sort (Level.succ Level.zero)) typed_spine_identity_result :=
 typingctxconv_in_const_spine_gen R faithful typed_spine_identity_tenv G Name.anonymous (ListType.nil Level)
  (typed_spine_identity_type (Level.succ (Level.succ Level.zero))) typed_spine_identity_args
  (KExpr.sort (Level.succ Level.zero)) typed_spine_identity_result typed_spine_identity_lookup
  typed_spine_identity_run (typed_spine_identity_applied_converted R G)
  (DefEqIn R (KExpr.sort (Level.succ Level.zero)) typed_spine_identity_result)
  (fun (_head : TypingCtxConvIn R typed_spine_identity_tenv G
    (KExpr.const Name.anonymous (ListType.nil Level)) (typed_spine_identity_type (Level.succ (Level.succ Level.zero))))
   (_arguments : TypedRawPiSpine R typed_spine_identity_tenv G
    (typed_spine_identity_type (Level.succ (Level.succ Level.zero))) typed_spine_identity_args
    (KExpr.sort (Level.succ Level.zero)))
   (result : DefEqIn R (KExpr.sort (Level.succ Level.zero)) typed_spine_identity_result) => result)",
        "Recover the canonical-residual conversion from the whole-spine derivation, preserving its real trailing semantic conversion.",
    ),
    (
        r"def typed_spine_identity_recovered_head (R : RedEnv) (faithful : RedEnvFaithful R) (G : ListType KExpr) :
 TypingCtxConvIn R typed_spine_identity_tenv G (KExpr.const Name.anonymous (ListType.nil Level))
 (typed_spine_identity_type (Level.succ (Level.succ Level.zero))) :=
 typingctxconv_in_const_spine_gen R faithful typed_spine_identity_tenv G Name.anonymous (ListType.nil Level)
  (typed_spine_identity_type (Level.succ (Level.succ Level.zero))) typed_spine_identity_args
  (KExpr.sort (Level.succ Level.zero)) typed_spine_identity_result typed_spine_identity_lookup
  typed_spine_identity_run (typed_spine_identity_applied_converted R G)
  (TypingCtxConvIn R typed_spine_identity_tenv G (KExpr.const Name.anonymous (ListType.nil Level))
   (typed_spine_identity_type (Level.succ (Level.succ Level.zero))))
  (fun (head : TypingCtxConvIn R typed_spine_identity_tenv G
    (KExpr.const Name.anonymous (ListType.nil Level)) (typed_spine_identity_type (Level.succ (Level.succ Level.zero))))
   (_arguments : TypedRawPiSpine R typed_spine_identity_tenv G
    (typed_spine_identity_type (Level.succ (Level.succ Level.zero))) typed_spine_identity_args
    (KExpr.sort (Level.succ Level.zero)))
   (_result : DefEqIn R (KExpr.sort (Level.succ Level.zero)) typed_spine_identity_result) => head)",
        "Recover canonical head typing through the public spine generator, including its strengthened induction output.",
    ),
    (
        r"def raw_pi_spine_empty (F : KExpr) : Eq (OptionType KExpr)
 (raw_pi_spine (ListType.nil KExpr) F) (OptionType.some KExpr F) :=
 Eq.refl (OptionType KExpr) (OptionType.some KExpr F)",
        "An empty argument list succeeds even if F is itself Pi: no false saturation or missing-term-argument claim.",
    ),
    (
        r"def raw_pi_spine_sort_refuses (u : Level) (a : KExpr) (rest : ListType KExpr) :
 Eq (OptionType KExpr) (raw_pi_spine (ListType.cons KExpr a rest) (KExpr.sort u)) (OptionType.none KExpr) :=
 Eq.refl (OptionType KExpr) (OptionType.none KExpr)",
        "Concrete computation refusal at a non-Pi sort; this is not a general theorem that raw refusal implies untypability modulo conversion.",
    ),
];

#[cfg(test)]
pub(super) const PROOF_ROOTS: &[&str] = &[
    "raw_pi_spine_trace_nil",
    "raw_pi_spine_trace_cons",
    "raw_pi_spine_trace",
    "raw_pi_head_canonical_const",
    "raw_pi_head_canonical_app",
    "semantic_typed_spine_nil",
    "semantic_typed_spine_cons",
    "semantic_typed_spine_from_trace",
    "typingctxconv_in_const_spine",
    "typingctxconv_in_const_spine_gen",
    "typed_spine_identity_body_typed",
    "typed_spine_identity_stored_body_typed",
    "typed_spine_identity_lookup",
    "typed_spine_identity_run",
    "typed_spine_identity_result_convert",
    "typed_spine_identity_applied",
    "typed_spine_identity_applied_converted",
    "typed_spine_identity_package",
    "typed_spine_identity_arguments",
    "typed_spine_identity_conversion",
    "typed_spine_identity_recovered_head",
    "raw_pi_spine_empty",
    "raw_pi_spine_sort_refuses",
];

impl Specification {
    pub(super) fn add_semantic_typed_spine(&mut self) -> Result<(), SpecError> {
        for (source, description) in DECLARATIONS {
            if source.starts_with("inductive ") {
                self.add_inductive(source, description)?;
            } else {
                self.add_recursive_def(source, description)?;
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    const NEGATIVE_CONTROLS: &[&str] = &[
        r"def typed_spine_forged_argument_domain (R : RedEnv) (faithful : RedEnvFaithful R)
 (G : ListType KExpr) : TypedRawPiSpine R typed_spine_identity_tenv G
 (typed_spine_identity_type (Level.succ Level.zero)) typed_spine_identity_args
 (KExpr.sort (Level.succ Level.zero)) := typed_spine_identity_arguments R faithful G",
        r"def typed_spine_forged_result (R : RedEnv) (faithful : RedEnvFaithful R)
 (G : ListType KExpr) : DefEqIn R (KExpr.sort Level.zero) typed_spine_identity_result :=
 typed_spine_identity_conversion R faithful G",
    ];

    #[test]
    fn semantic_typed_spine_sources_parse() {
        for (source, _) in super::DECLARATIONS {
            crate::test_utils::parse_check(source).expect("raw typed-spine source parses");
        }
        for source in NEGATIVE_CONTROLS {
            crate::test_utils::parse_check(source).expect("forged typed-spine control parses");
        }
    }

    #[test]
    fn semantic_typed_spine_and_inhabited_identity_are_checked() {
        let mut spec = crate::test_utils::build_spec_with_stack();
        if !spec
            .definitions()
            .contains_key("typingctxconv_in_generation")
        {
            spec.add_semantic_typing_inversion()
                .expect("typing generation prerequisites check");
        }
        if !spec
            .definitions()
            .contains_key("def_eq_in_instantiate_congr")
        {
            spec.add_semantic_term_instantiation()
                .expect("term instantiation prerequisites check");
        }
        if !spec
            .definitions()
            .contains_key("typingctxconv_in_const_spine")
        {
            spec.add_semantic_typed_spine()
                .expect("raw typed-spine proof stage checks");
        }
        for name in super::PROOF_ROOTS {
            let definition = spec
                .definitions()
                .get(*name)
                .expect("checked proof present");
            assert!(!definition.is_axiom, "{name}");
            assert!(definition.elaborated_value.is_some(), "{name}");
            assert!(
                crate::spec_axiom_closure::computed_axiom_closure(&spec, name).is_empty(),
                "{name}"
            );
        }
        for source in NEGATIVE_CONTROLS {
            assert!(spec
                .add_recursive_def(source, "Reject forged canonical argument domain or result.")
                .is_err());
        }
    }
}
